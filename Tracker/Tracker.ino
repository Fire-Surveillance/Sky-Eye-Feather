#include <Arduino.h>
#include <math.h>
#include <Wire.h>
#include <SPI.h>
#include <LSM6DS3.h>
#include <SilabsMicrophoneAnalog.h>
#include <string.h>
#include <RadioLib.h>
#include <Adafruit_SPIFlash.h>

#define PIN_LORA_CS    D2
#define PIN_LORA_DIO0  D3
#define PIN_LORA_RST   D4
#define PIN_FLASH_CS   D1
#define PIN_GPS_RX     D7
#define PIN_GPS_TX     D6
#define PIN_GPS_RST    D5
#define PIN_PDM_DATA   D11
#define PIN_PDM_CLK    D12
#define PIN_LED_STA    D0
#define PIN_LED_ICL    D18
#define PIN_LED_GFX    D17
#define PIN_LED_RTX    D16
#define PIN_LED_RRX    D15

static const uint32_t USB_BAUD = 115200;
static const uint32_t GPS_BAUD = 9600;
static const bool RAW_NMEA_ECHO = false;

static const uint32_t STA_BLINK_MS      = 1000;
static const uint32_t ICL_BLINK_MS      = 1000;
static const uint32_t ACQ_BLINK_MS      = 1000;
static const uint32_t FIX_BLINK_PERIOD  = 5000;
static const uint32_t FIX_BLINK_WIDTH   = 100;
static const uint32_t FIX_STALE_MS      = 5000;
static const uint16_t RTX_PULSE_MS      = 15;

#define IMU_PWR_PIN   PD5
#define IMU_I2C_ADDR  0x6A
#ifndef I2C_MODE
#define I2C_MODE 0
#endif
LSM6DS3 myIMU(I2C_MODE, IMU_I2C_ADDR);
static const uint32_t IMU_SAMPLE_MS = 200;

static const uint32_t STAT_PERIOD_MS = 200;
static const uint32_t MIC_PRINT_MS   = 200;
static const uint32_t GPS_WAIT_PRINT_MS = 200;

#define USE_SERIAL1
#ifdef USE_SERIAL1
  #define GPS_SERIAL Serial1
#endif

#define MIC_DATA_PIN  PC9
#define MIC_PWR_PIN   PC8
#define NUM_SAMPLES   128
#define MIC_VALUE_MIN 735
#define MIC_VALUE_MAX 900
uint32_t mic_buffer[NUM_SAMPLES];
uint32_t mic_buffer_local[NUM_SAMPLES];
volatile bool mic_data_ready = false;
MicrophoneAnalog micAnalog(MIC_DATA_PIN, MIC_PWR_PIN);
bool     micOk = false;
uint32_t micRollingAvg = 0;
uint32_t micLastLevel = 0;
uint32_t micLastComputedAt = 0;
bool micDataEver = false;

SX1276 lora = new Module(PIN_LORA_CS, PIN_LORA_DIO0, PIN_LORA_RST, -1);
static const float   LORA_FREQ_MHZ = 915.0;
static const float   LORA_BW_KHZ   = 125.0;
static const uint8_t LORA_SF       = 7;
static const uint8_t LORA_CR       = 5;
static const int8_t  LORA_PWR_DBM  = 20;
static const uint32_t LORA_TX_MIN_PERIOD_MS = 100;
uint32_t lastLoRaTxAt = 0;
bool radioOk = false;
static const int FEATHER_TX_PWR_MIN_DBM = 1;
static const int FEATHER_TX_PWR_MAX_DBM = 23;
static const int FEATHER_TX_PWR_RSSI_LOW_DBM = -85;
static const int FEATHER_TX_PWR_RSSI_HIGH_DBM = -65;
int featherTxPowerDbm = LORA_PWR_DBM;

static const char* CTRL_START_PKT = "GS,START";
static const char* CTRL_ACK_PKT   = "GS,ACK";
static const uint16_t RRX_PULSE_MS = 15;
static const uint32_t CONTROL_RX_WINDOW_MS = 60;
static const uint32_t ACK_WAIT_TIMEOUT_MS = 260;

bool featherAwake = false;
bool awaitingGsAck = false;
bool telemetryInitialized = false;
uint32_t lastControlSeenAt = 0;

static const size_t GPS_LINE_MAX = 128;
char gpsLineBuf[GPS_LINE_MAX];
size_t gpsLineLen = 0;
bool gpsLineOverflow = false;
bool gpsUpdatedFlag = false;

#define PIN_BAT_EN   PD3
#define PIN_BAT_ADC  PD4
float lastBatV = NAN;
static const uint32_t BATTERY_READ_MS = 1000;
uint32_t lastBatReadAt = 0;
static const float BAT_ADC_VREF = 3.30f;
static const float BAT_RTOP = 100000.0f;
static const float BAT_RBOT = 100000.0f;
static const float BAT_DIODE_VF = 0.45f;
static const float BAT_CAL_M = 1.00f;
static const float BAT_CAL_B = 0.00f;

Adafruit_FlashTransport_SPI flashTransport(PIN_FLASH_CS, SPI);
Adafruit_SPIFlash flash(&flashTransport);

static bool     flashOk        = false;
static bool     flashWritePassed = false;
static uint32_t flashAddr      = 0;
static uint32_t flashSizeBytes = 0;

static const uint32_t FLASH_LOG_START = 0x000000;
static const uint32_t FLASH_LOG_END   = 0x0010000;
static const uint16_t FLASH_REC_SIZE  = 256;
static const uint32_t FLASH_SECTOR_SZ = 4096;

bool nmeaToDecimalDegrees(const String& ddmm, char hemi, double& out) {
  if (ddmm.length() < 4) return false;
  int dotIdx = ddmm.indexOf('.');
  int splitIdx = (dotIdx >= 0 ? dotIdx - 2 : int(ddmm.length()) - 2);
  if (splitIdx <= 0) return false;
  String degStr = ddmm.substring(0, splitIdx);
  String minStr = ddmm.substring(splitIdx);
  double deg = degStr.toDouble();
  double minutes = minStr.toDouble();
  double dd = deg + (minutes / 60.0);
  if (hemi == 'S' || hemi == 's' || hemi == 'W' || hemi == 'w') dd = -dd;
  out = dd;
  return true;
}

String nmeaField(const String& line, int index) {
  int start = 0, end = -1, from = 0, field = -1;
  if (line.length() > 0 && line[0] == '$') from = 1;
  while (true) {
    start = (end < 0 ? from : end + 1);
    end = line.indexOf(',', start);
    field++;
    if (field == index) {
      if (end < 0) {
        int star = line.indexOf('*', start);
        if (star >= 0) return line.substring(start, star);
        return line.substring(start);
      }
      return line.substring(start, end);
    }
    if (end < 0) break;
  }
  return String();
}

static inline void pinsInit() {
  pinMode(PIN_LED_STA, OUTPUT); digitalWrite(PIN_LED_STA, LOW);
  pinMode(PIN_LED_GFX, OUTPUT); digitalWrite(PIN_LED_GFX, LOW);
  pinMode(PIN_LED_ICL, OUTPUT); digitalWrite(PIN_LED_ICL, LOW);
  pinMode(PIN_LED_RTX, OUTPUT); digitalWrite(PIN_LED_RTX, LOW);
  pinMode(PIN_LED_RRX, OUTPUT); digitalWrite(PIN_LED_RRX, LOW);

  pinMode(PIN_FLASH_CS, OUTPUT);  digitalWrite(PIN_FLASH_CS, HIGH);
  pinMode(PIN_LORA_CS, OUTPUT);   digitalWrite(PIN_LORA_CS, HIGH);
  pinMode(PIN_LORA_RST, OUTPUT);  digitalWrite(PIN_LORA_RST, HIGH);
  pinMode(PIN_LORA_DIO0, INPUT);
}

static inline void gpsResetPulse() {
  pinMode(PIN_GPS_RST, OUTPUT);
  digitalWrite(PIN_GPS_RST, HIGH); delay(5);
  digitalWrite(PIN_GPS_RST, LOW);  delay(20);
  digitalWrite(PIN_GPS_RST, HIGH); delay(50);
}

uint32_t staLastToggleAt = 0; bool staState = false;
uint32_t iclLastToggleAt = 0; bool iclState = false;
uint32_t gfxLastToggleAt = 0;
uint32_t gfxLastFixBlinkStart = 0; bool gfxInFixPulse = false;

String    nmeaLine;
uint32_t  lastPosAt = 0; bool haveFix = false;
double lastLat = NAN, lastLon = NAN, lastAltM = NAN;
double lastHdop = NAN, lastSpdKt = NAN, lastCogDeg = NAN;
int    lastSats = -1;

uint32_t lastImuSampleAt = 0;
float aX=0, aY=0, aZ=0, gX=0, gY=0, gZ=0;

uint32_t lastStatAt = 0;
bool imuOk = false;
bool imuLive = false;
uint32_t lastMicPrintAt = 0;
uint32_t lastGpsPrintAt = 0;

void updateStaLed(uint32_t now) {
  bool gpsFixFresh = (haveFix && (now - lastPosAt) < FIX_STALE_MS);

  if (imuLive && gpsFixFresh) {
    staState = true;
    digitalWrite(PIN_LED_STA, HIGH);
    return;
  }

  if (now - staLastToggleAt >= STA_BLINK_MS) {
    staLastToggleAt = now;
    staState = !staState;
    digitalWrite(PIN_LED_STA, staState ? HIGH : LOW);
  }
}
void updateIclLed(uint32_t now) {
  if (!imuOk) {
    digitalWrite(PIN_LED_ICL, LOW);
    return;
  }

  if (!imuLive) {
    if (now - iclLastToggleAt >= ICL_BLINK_MS) {
      iclLastToggleAt = now;
      iclState = !iclState;
      digitalWrite(PIN_LED_ICL, iclState ? HIGH : LOW);
    }
    return;
  }

  iclState = true;
  digitalWrite(PIN_LED_ICL, HIGH);
}
void updateGpsLed(uint32_t now) {
  bool fixFresh = (haveFix && (now - lastPosAt) < FIX_STALE_MS);
  if (!fixFresh) {
    if (now - gfxLastToggleAt >= ACQ_BLINK_MS) {
      gfxLastToggleAt = now;
      digitalWrite(PIN_LED_GFX, !digitalRead(PIN_LED_GFX));
    }
    return;
  }

  digitalWrite(PIN_LED_GFX, HIGH);
  gfxInFixPulse = false;
}

void printIMU(uint32_t now) {
  Serial.print(F("IMU,"));  Serial.print(now);
  Serial.print(F(",ax=")); Serial.print(aX, 3);
  Serial.print(F(",ay=")); Serial.print(aY, 3);
  Serial.print(F(",az=")); Serial.print(aZ, 3);
  Serial.print(F(",gx=")); Serial.print(gX, 3);
  Serial.print(F(",gy=")); Serial.print(gY, 3);
  Serial.print(F(",gz=")); Serial.println(gZ, 3);
}
void printGPS(uint32_t now) {
  if (!haveFix || isnan(lastLat) || isnan(lastLon)) {
    Serial.print(F("GPS,")); Serial.print(now); Serial.println(F(",waiting_for_fix"));
    return;
  }
  Serial.print(F("GPS,"));  Serial.print(now);
  Serial.print(F(",lat="));     Serial.print(lastLat, 7);
  Serial.print(F(",lon="));     Serial.print(lastLon, 7);
  if (!isnan(lastAltM))  { Serial.print(F(",alt_m="));  Serial.print(lastAltM, 1); }
  if (!isnan(lastHdop))  { Serial.print(F(",hdop="));   Serial.print(lastHdop, 2); }
  if (lastSats >= 0)     { Serial.print(F(",sats="));   Serial.print(lastSats); }
  if (!isnan(lastSpdKt)) { Serial.print(F(",spd_kt=")); Serial.print(lastSpdKt, 2); }
  if (!isnan(lastCogDeg)){ Serial.print(F(",cog_deg="));Serial.print(lastCogDeg, 1); }
  Serial.println();
}
void printMIC(uint32_t now) {
  Serial.print(F("MIC,")); Serial.print(now); Serial.print(F(",level="));
  if (micOk) Serial.println(micRollingAvg);
  else       Serial.println(F("NaN"));
}

void mic_samples_ready_cb();
void radioPollControl(uint32_t now);
void serviceGPS(uint32_t now);
static inline void readBatterySafely(uint32_t now) {
  if (now - lastBatReadAt < BATTERY_READ_MS) return;
  lastBatReadAt = now;
  micAnalog.stopSampling();
  delayMicroseconds(50);
  int raw = analogRead(PIN_BAT_ADC);
  float v_adc = (float)raw * (BAT_ADC_VREF / 4095.0f);
  float v_sys = v_adc * ((BAT_RTOP + BAT_RBOT) / BAT_RBOT);
  float vbat  = v_sys + BAT_DIODE_VF;
  vbat = BAT_CAL_M * vbat + BAT_CAL_B;
  lastBatV = vbat;
  Serial.print("Voltage: "); Serial.print(vbat, 2); Serial.println(" V");
  delayMicroseconds(50);
  micAnalog.startSampling(mic_samples_ready_cb);
}

String buildLoRaPayload(uint32_t now, const char* gpsStatus) {
  char gpsC = 'W';
  if (gpsStatus) {
    if      (!strcmp(gpsStatus, "fixed")) gpsC = 'F';
    else if (!strcmp(gpsStatus, "stale")) gpsC = 'S';
    else gpsC = 'W';
  }
  char imuC   = imuOk   ? (imuLive ? '1' : 'T') : '0';
  char micC   = micOk   ? (micDataEver ? '1' : 'T') : '0';
  char flashC = flashOk ? (flashWritePassed ? '1' : 'T') : '0';

  auto fstr = [](float v, int dig) -> String { if (isnan(v)) return String(); return String(v, dig); };
  auto dstr = [](double v, int dig) -> String { if (isnan(v)) return String(); return String(v, dig); };
  auto istr = [](int v) -> String { if (v < 0) return String(); return String(v); };

  String p; p.reserve(140);
  p += F("L,");
  p += String(now);              p += ',';
  p += gpsC;                     p += ',';
  p += imuC;                     p += ',';
  p += micC;                     p += ',';
  p += flashC;                   p += ',';

  p += dstr(lastLat, 6);         p += ',';
  p += dstr(lastLon, 6);         p += ',';
  p += dstr(lastAltM, 1);        p += ',';
  p += dstr(lastHdop, 2);        p += ',';
  p += istr(lastSats);           p += ',';
  p += dstr(lastSpdKt, 2);       p += ',';
  p += dstr(lastCogDeg, 1);      p += ',';

  p += fstr(aX, 3);              p += ',';
  p += fstr(aY, 3);              p += ',';
  p += fstr(aZ, 3);              p += ',';
  p += fstr(gX, 2);              p += ',';
  p += fstr(gY, 2);              p += ',';
  p += fstr(gZ, 2);              p += ',';

  if (micOk) {
    p += String(micRollingAvg);
  }
  p += ',';

  if (!isnan(lastBatV)) {
    p += String(lastBatV, 1);
  }
  p += ',';
  p += String(featherTxPowerDbm);

  return p;
}

static inline void flashWait() { while (flash.isBusy()) { } }

void flashInitMinimal() {
  pinMode(PIN_LORA_CS, OUTPUT);   digitalWrite(PIN_LORA_CS, HIGH);
  pinMode(PIN_LORA_RST, OUTPUT);  digitalWrite(PIN_LORA_RST, LOW);
  Serial.println(F("FLASH,bringing_up"));

  if (!flash.begin()) {
    Serial.println(F("FLASH,init=fail"));
    flashOk = false;
    return;
  }
  flashSizeBytes = flash.size();
  flashAddr = FLASH_LOG_START;

  flash.eraseSector(FLASH_LOG_START / FLASH_SECTOR_SZ);
  flashWait();

  flashOk = true;
  Serial.println(F("FLASH,init=ok"));
  Serial.print(F("FLASH,jedec=0x")); Serial.println(flash.getJEDECID(), HEX);
  Serial.print(F("FLASH,size_kb=")); Serial.println(flashSizeBytes / 1024);
  Serial.print(F("FLASH,log=[0x")); Serial.print(FLASH_LOG_START, HEX);
  Serial.print(F(",0x")); Serial.print(FLASH_LOG_END, HEX);
  Serial.print(F("),next=0x")); Serial.println(flashAddr, HEX);
  Serial.println(F("FLASH,sector0=erased"));
}

static inline void flashEraseIfNeeded(uint32_t addr) {
  if ((addr % FLASH_SECTOR_SZ) == 0) {
    flash.eraseSector(addr / FLASH_SECTOR_SZ);
    flashWait();
  }
}

static uint8_t flashEchoCount = 0;

bool flashAppendRecord(uint32_t nowMs, const String& payload) {
  if (!flashOk) return false;

  if (flashAddr + FLASH_REC_SIZE > FLASH_LOG_END) {
    flashAddr = FLASH_LOG_START;
  }

  flashEraseIfNeeded(flashAddr);

  uint8_t rec[FLASH_REC_SIZE];
  memset(rec, 0x00, sizeof(rec));
  rec[0] = 0xAE; rec[1] = 0x01;
  rec[2] = (uint8_t)( nowMs        & 0xFF);
  rec[3] = (uint8_t)((nowMs >>  8) & 0xFF);
  rec[4] = (uint8_t)((nowMs >> 16) & 0xFF);
  rec[5] = (uint8_t)((nowMs >> 24) & 0xFF);
  uint16_t n = (uint16_t)min((size_t)240, payload.length());
  rec[6] = (uint8_t)( n       & 0xFF);
  rec[7] = (uint8_t)((n >> 8) & 0xFF);
  memcpy(&rec[8], payload.c_str(), n);

  int32_t wrote = flash.writeBuffer(flashAddr, rec, sizeof(rec));
  flashWait();

  if (wrote != (int32_t)sizeof(rec)) {
    Serial.print(F("FLASH,append=fail,addr=0x")); Serial.println(flashAddr, HEX);
    return false;
  }

  flashWritePassed = true;
  Serial.print(F("FLASH,append=ok,addr=0x")); Serial.print(flashAddr, HEX);
  Serial.print(F(",len=")); Serial.println(n);

  if (flashEchoCount < 3) {
    uint8_t hdr[8];
    flash.readBuffer(flashAddr, hdr, sizeof(hdr));
    flashWait();
    uint32_t ms = (uint32_t)hdr[2] | ((uint32_t)hdr[3] << 8) |
                  ((uint32_t)hdr[4] << 16) | ((uint32_t)hdr[5] << 24);
    uint16_t ln = (uint16_t)hdr[6] | ((uint16_t)hdr[7] << 8);
    if (ln > 240) ln = 240;
    char buf[241]; memset(buf, 0, sizeof(buf));
    if (ln > 0) { flash.readBuffer(flashAddr + 8, (uint8_t*)buf, ln); flashWait(); }
    Serial.print(F("LOG,addr=0x")); Serial.print(flashAddr, HEX);
    Serial.print(F(",ms=")); Serial.print(ms);
    Serial.print(F(",payload=")); Serial.println(buf);
    flashEchoCount++;
  }

  flashAddr += FLASH_REC_SIZE;
  return true;
}

void flashInfo() {
  Serial.print(F("FLASH,init=")); Serial.print(flashOk ? F("ok") : F("fail"));
  Serial.print(F(",jedec=0x")); Serial.print(flash.getJEDECID(), HEX);
  Serial.print(F(",size_kb=")); Serial.print(flash.size() / 1024);
  Serial.print(F(",log_start=0x")); Serial.print(FLASH_LOG_START, HEX);
  Serial.print(F(",log_end=0x")); Serial.print(FLASH_LOG_END, HEX);
  Serial.print(F(",next=0x")); Serial.println(flashAddr, HEX);
}
void flashEraseLog() {
  if (!flashOk) { Serial.println(F("FLASH,erase=fail,init=false")); return; }
  Serial.println(F("FLASH,erase=start"));
  for (uint32_t a = FLASH_LOG_START; a < FLASH_LOG_END; a += FLASH_SECTOR_SZ) {
    flash.eraseSector(a / FLASH_SECTOR_SZ);
    flashWait();
  }
  flashAddr = FLASH_LOG_START;
  Serial.println(F("FLASH,erase=done"));
}
void flashDump() {
  if (!flashOk) { Serial.println(F("FLASH,dump=fail,init=false")); return; }
  Serial.println(F("FLASH,dump=start"));
  uint8_t hdr[8];
  for (uint32_t a = FLASH_LOG_START; a + FLASH_REC_SIZE <= FLASH_LOG_END; a += FLASH_REC_SIZE) {
    flash.readBuffer(a, hdr, sizeof(hdr)); flashWait();
    if (hdr[0] != 0xAE || hdr[1] != 0x01) continue;
    uint32_t ms = (uint32_t)hdr[2] | ((uint32_t)hdr[3] << 8) |
                  ((uint32_t)hdr[4] << 16) | ((uint32_t)hdr[5] << 24);
    uint16_t n  = (uint16_t)hdr[6] | ((uint16_t)hdr[7] << 8);
    if (n > 240) n = 240;
    char buf[241]; memset(buf, 0, sizeof(buf));
    if (n > 0) { flash.readBuffer(a + 8, (uint8_t*)buf, n); flashWait(); }
    Serial.print(F("LOG,addr=0x")); Serial.print(a, HEX);
    Serial.print(F(",ms=")); Serial.print(ms);
    Serial.print(F(",payload=")); Serial.println(buf);
  }
  Serial.println(F("FLASH,dump=done"));
}
String cmdBuf;
void handleSerialCommands() {
  while (Serial.available()) {
    char c = (char)Serial.read();
    if (c == '\r') continue;
    if (c == '\n') {
      if (cmdBuf.length() == 0) continue;
      if (cmdBuf == "INFO") flashInfo();
      else if (cmdBuf == "DUMP") flashDump();
      else if (cmdBuf == "ERASE") flashEraseLog();
      else { Serial.print(F("CMD,unknown=")); Serial.println(cmdBuf); }
      cmdBuf = "";
    } else {
      if (cmdBuf.length() < 32) cmdBuf += c;
    }
  }
}

void applyFeatherTxPower() {
  if (featherTxPowerDbm < FEATHER_TX_PWR_MIN_DBM) featherTxPowerDbm = FEATHER_TX_PWR_MIN_DBM;
  if (featherTxPowerDbm > FEATHER_TX_PWR_MAX_DBM) featherTxPowerDbm = FEATHER_TX_PWR_MAX_DBM;
  lora.setOutputPower(featherTxPowerDbm);
}

void adjustFeatherTxPowerFromRssi(float rssiDbm) {
  if (isnan(rssiDbm)) return;
  int rssi = (int)roundf(rssiDbm);
  if (rssi < FEATHER_TX_PWR_RSSI_LOW_DBM && featherTxPowerDbm < FEATHER_TX_PWR_MAX_DBM) {
    featherTxPowerDbm++;
    applyFeatherTxPower();
  } else if (rssi > FEATHER_TX_PWR_RSSI_HIGH_DBM && featherTxPowerDbm > FEATHER_TX_PWR_MIN_DBM) {
    featherTxPowerDbm--;
    applyFeatherTxPower();
  }
}

void printAndSendLoRaTX(uint32_t now, const char* gpsStatus) {
  serviceGPS(now);
  String payload = buildLoRaPayload(now, gpsStatus);

  Serial.println(payload);

  if (flashOk) {
    if (!flashAppendRecord(now, payload)) {
      Serial.println(F("FLASH,append=fail"));
    }
  }

  if (radioOk) {
    int16_t err = lora.transmit((const uint8_t*)payload.c_str(), payload.length());
    if (err != RADIOLIB_ERR_NONE) {
      Serial.print(F("STAT,tx_err=")); Serial.println(err);
    }
  }

  digitalWrite(PIN_LED_RTX, HIGH);
  delay(RTX_PULSE_MS);
  digitalWrite(PIN_LED_RTX, LOW);

  serviceGPS(millis());

  if (radioOk) {
    lora.startReceive();
    uint32_t t0 = millis();
    while ((millis() - t0) < CONTROL_RX_WINDOW_MS) {
      uint32_t tNow = millis();
      serviceGPS(tNow);
      radioPollControl(tNow);
    }
  }
}

void mic_samples_ready_cb() {
  memcpy(mic_buffer_local, mic_buffer, NUM_SAMPLES * sizeof(uint32_t));
  mic_data_ready = true;
}
void mic_process_if_ready(uint32_t now) {
  if (!mic_data_ready) return;
  mic_data_ready = false;
  micAnalog.stopSampling();
  uint32_t voice_level = (uint32_t)micAnalog.getAverage(mic_buffer_local, NUM_SAMPLES);
  voice_level = constrain(voice_level, MIC_VALUE_MIN, MIC_VALUE_MAX);
  micRollingAvg = (voice_level + micRollingAvg) / 2u;
  micLastLevel = voice_level;
  micLastComputedAt = now;
  micDataEver = true;
  micAnalog.startSampling(mic_samples_ready_cb);
}

bool parseGGA(const String& line) {
  String latStr = nmeaField(line, 2);
  char   ns = nmeaField(line, 3).charAt(0);
  String lonStr = nmeaField(line, 4);
  char   ew = nmeaField(line, 5).charAt(0);
  String fix  = nmeaField(line, 6);
  String nsat = nmeaField(line, 7);
  String hdop = nmeaField(line, 8);
  String altM = nmeaField(line, 9);
  if (latStr.length() == 0 || lonStr.length() == 0) return false;
  if (fix == "0") return false;
  double latdd, londd;
  if (!nmeaToDecimalDegrees(latStr, ns, latdd)) return false;
  if (!nmeaToDecimalDegrees(lonStr, ew, londd)) return false;
  lastLat = latdd; lastLon = londd;
  lastSats = nsat.length() ? nsat.toInt() : lastSats;
  lastHdop = hdop.length() ? hdop.toFloat() : lastHdop;
  lastAltM = altM.length() ? altM.toFloat() : lastAltM;
  return true;
}
bool parseRMC(const String& line) {
  String status = nmeaField(line, 2);
  if (status != "A") return false;
  String latStr = nmeaField(line, 3);
  char   ns = nmeaField(line, 4).charAt(0);
  String lonStr = nmeaField(line, 5);
  char   ew = nmeaField(line, 6).charAt(0);
  String spd   = nmeaField(line, 7);
  String cog   = nmeaField(line, 8);
  if (latStr.length() == 0 || lonStr.length() == 0) return false;
  double latdd, londd;
  if (!nmeaToDecimalDegrees(latStr, ns, latdd)) return false;
  if (!nmeaToDecimalDegrees(lonStr, ew, londd)) return false;
  lastLat = latdd; lastLon = londd;
  lastSpdKt = spd.length() ? spd.toFloat() : lastSpdKt;
  lastCogDeg = cog.length() ? cog.toFloat() : lastCogDeg;
  return true;
}
bool parseGLL(const String& line) {
  String latStr = nmeaField(line, 1);
  char   ns = nmeaField(line, 2).charAt(0);
  String lonStr = nmeaField(line, 3);
  char   ew = nmeaField(line, 4).charAt(0);
  String status = nmeaField(line, 6);
  if (status != "A") return false;
  if (latStr.length() == 0 || lonStr.length() == 0) return false;
  double latdd, londd;
  if (!nmeaToDecimalDegrees(latStr, ns, latdd)) return false;
  if (!nmeaToDecimalDegrees(lonStr, ew, londd)) return false;
  lastLat = latdd; lastLon = londd;
  return true;
}

static inline int hexNibble(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
  if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
  return -1;
}

bool nmeaChecksumValid(const char* line) {
  if (!line || line[0] != '$') return false;
  const char* star = strchr(line, '*');
  if (!star) return false;
  if (!star[1] || !star[2]) return false;

  uint8_t cs = 0;
  for (const char* p = line + 1; p < star; ++p) cs ^= (uint8_t)(*p);

  int hi = hexNibble(star[1]);
  int lo = hexNibble(star[2]);
  if (hi < 0 || lo < 0) return false;
  uint8_t stated = (uint8_t)((hi << 4) | lo);
  return cs == stated;
}

bool isAcceptedNmeaSentence(const char* line) {
  if (!line || line[0] != '$') return false;
  return (strncmp(line, "$GPGGA", 6) == 0 || strncmp(line, "$GNGGA", 6) == 0 ||
          strncmp(line, "$GPRMC", 6) == 0 || strncmp(line, "$GNRMC", 6) == 0 ||
          strncmp(line, "$GPGLL", 6) == 0 || strncmp(line, "$GNGLL", 6) == 0);
}

void handleNmeaLine(const char* line, uint32_t now) {
  if (!line || !line[0]) return;
  if (!isAcceptedNmeaSentence(line)) return;
  if (!nmeaChecksumValid(line)) return;

  if (RAW_NMEA_ECHO) {
    Serial.print(F("NMEA,")); Serial.print(now); Serial.print(F(",")); Serial.println(line);
  }

  bool parsed = false;
  String nmea = String(line);
  if (nmea.startsWith("$GNGGA") || nmea.startsWith("$GPGGA")) parsed = parseGGA(nmea);
  else if (nmea.startsWith("$GNRMC") || nmea.startsWith("$GPRMC")) parsed = parseRMC(nmea);
  else if (nmea.startsWith("$GNGLL") || nmea.startsWith("$GPGLL")) parsed = parseGLL(nmea);

  if (parsed) {
    haveFix = true;
    lastPosAt = now;
    gpsUpdatedFlag = true;
  }
}

void serviceGPS(uint32_t now) {
  while (GPS_SERIAL.available()) {
    char c = (char)GPS_SERIAL.read();

    if (c == '\r') continue;

    if (c == '\n') {
      if (!gpsLineOverflow && gpsLineLen > 0) {
        gpsLineBuf[gpsLineLen] = '\0';
        handleNmeaLine(gpsLineBuf, now);
      }
      gpsLineLen = 0;
      gpsLineOverflow = false;
      continue;
    }

    if (gpsLineLen < (GPS_LINE_MAX - 1)) {
      gpsLineBuf[gpsLineLen++] = c;
    } else {
      gpsLineOverflow = true;
    }
  }
}

void radioInit() {
  int16_t err = lora.begin(LORA_FREQ_MHZ);
  if (err == RADIOLIB_ERR_NONE) {
    lora.setFrequency(LORA_FREQ_MHZ);
    lora.setBandwidth(LORA_BW_KHZ);
    lora.setSpreadingFactor(LORA_SF);
    lora.setCodingRate(LORA_CR);
    applyFeatherTxPower();
    lora.setSyncWord(0x12);
    lora.setCRC(true);
    lora.setPreambleLength(8);
    radioOk = true;
    lora.startReceive();
    Serial.println(F("STAT,0,radio_init=ok"));
  } else {
    Serial.print(F("STAT,0,radio_init=fail,err=")); Serial.println(err);
  }
}

void initTelemetrySubsystems() {
  if (telemetryInitialized) return;

  analogReadResolution(12);

  pinMode(IMU_PWR_PIN, OUTPUT);
  digitalWrite(IMU_PWR_PIN, HIGH);
  delay(300);
  Wire.begin();
  Wire.setClock(100000);
  delay(20);
  imuOk = (myIMU.begin() == 0);
  Serial.println(imuOk ? F("STAT,0,imu_init=ok") : F("STAT,0,imu_init=fail"));

  micAnalog.begin(mic_buffer, NUM_SAMPLES);
  micOk = true;
  micAnalog.startSampling(mic_samples_ready_cb);
  Serial.println(F("STAT,0,mic_init=ok"));

  gpsResetPulse();
  GPS_SERIAL.begin(GPS_BAUD);

  pinMode(PIN_BAT_EN, OUTPUT);
  digitalWrite(PIN_BAT_EN, HIGH);

  flashInitMinimal();

  Serial.println(F("STAT,0,boot=ok,mode=gps+imu+mic+tx+flash,serial=115200"));

  telemetryInitialized = true;
}

void pulseRrxLed() {
  digitalWrite(PIN_LED_RRX, HIGH);
  delay(RRX_PULSE_MS);
  digitalWrite(PIN_LED_RRX, LOW);
}

void processControlPacket(const String& pkt, uint32_t now) {
  if (pkt == CTRL_START_PKT) {
    lastControlSeenAt = now;
    pulseRrxLed();
    if (!featherAwake) {
      featherAwake = true;
      initTelemetrySubsystems();
      readBatterySafely(now);
      printAndSendLoRaTX(now, "waiting_for_fix");
    }
  } else if (pkt == CTRL_ACK_PKT) {
    lastControlSeenAt = now;
    awaitingGsAck = false;
    pulseRrxLed();
  }
}

void radioPollControl(uint32_t now) {
  if (!radioOk) return;
  if (digitalRead(PIN_LORA_DIO0) != HIGH) return;

  String pkt;
  int16_t err = lora.readData(pkt);
  float rxRssiDbm = lora.getRSSI();
  lora.startReceive();
  if (err != RADIOLIB_ERR_NONE) return;

  pkt.trim();
  processControlPacket(pkt, now);
  adjustFeatherTxPowerFromRssi(rxRssiDbm);
}

void setup() {
  Serial.begin(USB_BAUD);
  while (!Serial) {}

  pinsInit();

  digitalWrite(PIN_LED_STA, HIGH);
  digitalWrite(PIN_LED_GFX, HIGH);
  digitalWrite(PIN_LED_ICL, HIGH);
  digitalWrite(PIN_LED_RTX, HIGH);
  digitalWrite(PIN_LED_RRX, HIGH);
  delay(1000);
  digitalWrite(PIN_LED_STA, LOW);
  digitalWrite(PIN_LED_GFX, LOW);
  digitalWrite(PIN_LED_ICL, LOW);
  digitalWrite(PIN_LED_RTX, LOW);
  digitalWrite(PIN_LED_RRX, LOW);

  radioInit();
  Serial.println(F("STAT,0,boot=standby_waiting_for_gs_start"));
}

void loop() {
  uint32_t now = millis();

  serviceGPS(now);

  radioPollControl(now);
  if (!featherAwake) {
    digitalWrite(PIN_LED_STA, LOW);
    digitalWrite(PIN_LED_GFX, LOW);
    digitalWrite(PIN_LED_ICL, LOW);
    digitalWrite(PIN_LED_RTX, LOW);
    digitalWrite(PIN_LED_RRX, LOW);
    delay(5);
    return;
  }

  handleSerialCommands();

  updateStaLed(now);
  updateIclLed(now);
  updateGpsLed(now);

  serviceGPS(now);
  readBatterySafely(now);
  serviceGPS(now);

  bool gpsFresh = (haveFix && ((now - lastPosAt) < FIX_STALE_MS));

  if ((now - lastStatAt) >= STAT_PERIOD_MS) {
    lastStatAt = now;
    const char* gpsStatusW = (!haveFix) ? "waiting_for_fix" : (gpsFresh ? "fixed" : "stale");
    Serial.print(F("STAT,")); Serial.print(now); Serial.print(F(",gps=")); Serial.println(gpsStatusW);
  }

  if (gpsUpdatedFlag || (!haveFix && (now - lastGpsPrintAt) >= GPS_WAIT_PRINT_MS)) {
    lastGpsPrintAt = now;
    printGPS(now);
    gpsUpdatedFlag = false;
  }

  if ((now - lastImuSampleAt) >= IMU_SAMPLE_MS) {
    lastImuSampleAt = now;
    aX = -myIMU.readFloatAccelY();
    aY = myIMU.readFloatAccelX();
    aZ = myIMU.readFloatAccelZ();
    gX = myIMU.readFloatGyroY();
    gY = myIMU.readFloatGyroX();
    gZ = myIMU.readFloatGyroZ();
    imuLive = !(isnan(aX) || isnan(aY) || isnan(aZ) || isnan(gX) || isnan(gY) || isnan(gZ));
    printIMU(now);
  }

  mic_process_if_ready(now);
  if ((now - lastMicPrintAt) >= MIC_PRINT_MS) {
    lastMicPrintAt = now;
    printMIC(now);
  }

  const char* gpsStatus = (!haveFix) ? "waiting_for_fix"
                        : ((now - lastPosAt) < FIX_STALE_MS ? "fixed" : "stale");
  if (now - lastLoRaTxAt >= LORA_TX_MIN_PERIOD_MS) {
    lastLoRaTxAt = now;
    serviceGPS(now);
    printAndSendLoRaTX(now, gpsStatus);
    serviceGPS(millis());
  }
}
