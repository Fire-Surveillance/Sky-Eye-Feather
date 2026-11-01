#include <SPI.h>
#include <LoRa.h>
#include <Adafruit_GFX.h>
#include <Adafruit_HX8357.h>
#include <Adafruit_MAX1704X.h>
#include <Wire.h>
#include <TinyGPSPlus.h>
#include <Adafruit_Sensor.h>
#include <Adafruit_HMC5883_U.h>
#include <Adafruit_TSC2007.h>
#include <math.h>
#include <ctype.h>

#define GS_HW_VERSION "DEV 1A"
#define GS_SW_VERSION "DEV 1A"
#define CREDIT_LINE_1 "Hardware & Software by William Lewis Yuan"
#define CREDIT_LINE_2 "Copyright Sky Eye Innovations. All Rights Reserved."

#define LORA_CS    A3
#define LORA_RST   A4
#define LORA_IRQ   12
#define RF_FREQ    915E6
#define SPI_HZ     8000000

#define TFT_LITE   A2
#define TFT_CS     9
#define TFT_DC     10
Adafruit_HX8357 tft(TFT_CS, TFT_DC, -1);

#define SD_CS      5
#define SDDET_PIN  11

#define GS_GPS_RX_PIN   38
#define GS_GPS_TX_PIN   39
#define GS_GPS_BAUD     9600
HardwareSerial GS_GPS(1);
TinyGPSPlus gps;

Adafruit_MAX17048 maxlipo;

Adafruit_HMC5883_Unified hmc(12345);
static const float DECLINATION_DEG = 0.0f;

Adafruit_TSC2007 touch;

#define COLOR_ORANGE   0xFD20
#define COLOR_DARKGREY 0x7BEF

struct Telemetry {
  uint32_t ms = 0;
  String gps_status = "";
  String imu_status = "";
  String mic_status = "";
  String flash_status = "";

  float lat = NAN, lon = NAN, alt_m = NAN, hdop = NAN;
  int   sats = -1;
  float spd_kt = NAN, cog_deg = NAN;

  float ax = NAN, ay = NAN, az = NAN, gx = NAN, gy = NAN, gz = NAN;
  float mic = NAN;

  float bat_v = NAN;
  int   feather_tx_dbm = -1;
};

struct Ground {
  bool   haveFix = false;
  double lat = NAN, lon = NAN, alt_m = NAN;
  double hdop = NAN;
  int    sats = -1;
  double spd_kt = NAN;

  bool   haveVbat = false;
  float  vbat = NAN;
  float  soc  = NAN;

  bool   haveMag = false;
  float  heading_deg = NAN;
} gnd;

static const int TX_LINE_H = 12;
static const int TX_ROWS   = 17;
static const int GS_LINE_H = 12;

static const int LABEL_X = 8;
static const int VALUE_X = 140;

int TX_BASE_Y = 6;
int GS_BASE_Y = 0;

uint16_t bgColor   = HX8357_BLACK;
uint16_t okColor   = HX8357_GREEN;
uint16_t warnColor = HX8357_YELLOW;
uint16_t errColor  = HX8357_RED;
uint16_t txtColor  = HX8357_WHITE;
uint16_t labColor  = HX8357_CYAN;

String   prevValue[TX_ROWS];
uint16_t prevValColor[TX_ROWS];

bool uiActivated = false;
bool gsLabelsDrawn = false;
bool signalLostShown = false;

int pop_x = 0, pop_y = 0, pop_w = 0, pop_h = 0;

uint32_t bootAt = 0;
uint32_t lastPktAt = 0;
bool showedWaiting = false;

static const uint32_t LOSS_TIMEOUT_MS = 3000;

static const char* CTRL_START_PKT = "GS,START";
static const char* CTRL_ACK_PKT   = "GS,ACK";
static const uint32_t CTRL_START_PERIOD_MS = 1000;
static const uint32_t CTRL_ACK_PERIOD_MS = 5000;
uint32_t lastCtrlStartAt = 0;
uint32_t lastCtrlAckAt = 0;

uint32_t gsLastTxAt = 0;
uint32_t gsLastRxAt = 0;
static const uint32_t GS_RADIO_ACTIVE_MS = 250;

static const int GS_TX_PWR_MIN_DBM = 1;
static const int GS_TX_PWR_MAX_DBM = 23;
static const int GS_TX_PWR_RSSI_LOW_DBM = -85;
static const int GS_TX_PWR_RSSI_HIGH_DBM = -65;
int gsTxPowerDbm = GS_TX_PWR_MIN_DBM;

static const int CONNECT_BTN_W = 120;
static const int CONNECT_BTN_H = 32;
static const int CONNECT_BTN_X = 320 - CONNECT_BTN_W - 1;
static const int CONNECT_BTN_Y = (80 - 50 - 5) + 34 + 8;

static const uint16_t CONNECT_BTN_RAW_X_MIN = 0;
static const uint16_t CONNECT_BTN_RAW_X_MAX = 1500;
static const uint16_t CONNECT_BTN_RAW_Y_MIN = 2900;
static const uint16_t CONNECT_BTN_RAW_Y_MAX = 3400;

bool skyEyeConnectPressed = false;
bool connectCountdownActive = false;
uint32_t connectCountdownStartAt = 0;

static const uint32_t MAG_TEST_WINDOW_MS = 3000;
uint32_t magTestStartedAt = 0;
static const uint8_t MAG_GOOD_SAMPLES_REQUIRED = 3;
static const uint8_t MAG_BAD_SAMPLES_REQUIRED = 3;
uint8_t magGoodStreak = 0;
uint8_t magBadStreak = 0;

enum MagStatus : uint8_t { MAG_STATUS_TESTING = 0, MAG_STATUS_OK = 1, MAG_STATUS_FAIL = 2 };
MagStatus magStatus = MAG_STATUS_TESTING;
bool magI2cDetected = false;

bool requestFullRepaint = false;

Telemetry lastT;
int lastRSSI = 0;
float lastSNR = 0.0f;
bool haveLastT = false;

static inline float metersToFeet(float m) { return isnan(m) ? NAN : (m * 3.28084f); }
static inline float knotsToMph(float kt)  { return isnan(kt) ? NAN : (kt * 1.15078f); }
static inline float clamp01(float x)      { if (isnan(x)) return NAN; if (x < 0) return 0; if (x > 1) return 1; return x; }

static const float GS_BAT_EMPTY_V = 3.00f;
static const float GS_BAT_FULL_V  = 4.20f;
static const float GS_BAT_CAL_M   = 1.00f;
static const float GS_BAT_CAL_B   = 0.46f;
static const float GS_BAT_FILTER_ALPHA = 0.25f;

static inline float calibrateGroundBatteryVolts(float v_raw) {
  if (isnan(v_raw)) return NAN;
  return (v_raw * GS_BAT_CAL_M) + GS_BAT_CAL_B;
}

static inline float voltsToPct(float v) {
  if (isnan(v)) return NAN;
  const float span = (GS_BAT_FULL_V - GS_BAT_EMPTY_V);
  if (span <= 0.0f) return NAN;
  return clamp01((v - GS_BAT_EMPTY_V) / span) * 100.0f;
}

String fmtFloat(float v, int digits) { if (isnan(v)) return "NaN"; return String(v, digits); }

String formatGroundTxPower() {
  float mw = powf(10.0f, ((float)gsTxPowerDbm) / 10.0f);
  return String("GSP: ") + String(mw, 1) + String("mW");
}

String formatFeatherTxPower(const Telemetry& t) {
  if (t.feather_tx_dbm < 0) return String("TP: NaN");
  float mw = powf(10.0f, ((float)t.feather_tx_dbm) / 10.0f);
  return String("TP: ") + String(mw, 1) + String("mW");
}

String normalizeStatusDisplay(const String& raw) {
  String s = raw; s.toLowerCase();
  if (s == "ok") return "Nominal";
  if (s == "stale") return "Stale";
  if (s == "fixed") return "Fixed";
  if (s == "waiting_for_fix") return "No Fix";
  if (s == "testing") return "Testing";
  if (s.length()) { String out = s; out.setCharAt(0, toupper(out[0])); return out; }
  return raw;
}

void clearScreen() {
  tft.fillScreen(bgColor);
}

void drawGreenBanner(const char* msg) {
  const int bannerH = TX_LINE_H * 5;
  const int topY = 6;
  tft.fillRect(0, topY, tft.width(), bannerH, bgColor);

  tft.setTextSize(2);
  tft.setTextColor(okColor);
  int16_t x1, y1; uint16_t w, h;
  tft.getTextBounds(msg, 0, 0, &x1, &y1, &w, &h);
  int cx = (tft.width() - w) / 2;
  int cy = topY + (bannerH - h)/2;
  tft.setCursor(cx, cy);
  tft.print(msg);
}

void drawBootInfoBlock() {
  const int bannerH = TX_LINE_H * 5;
  const int topY = 6 + bannerH + 6;

  const char* lines[] = {
    "Ground Station Hardware Version: " GS_HW_VERSION,
    "Ground Station Software Version: " GS_SW_VERSION,
    CREDIT_LINE_1,
    CREDIT_LINE_2
  };
  const int N = sizeof(lines)/sizeof(lines[0]);

  tft.setTextSize(1);
  for (int i = 0; i < N; i++) {
    int16_t x1, y1; uint16_t w, h;
    tft.getTextBounds(lines[i], 0, 0, &x1, &y1, &w, &h);
    int cx = (tft.width() - w) / 2;
    int cy = topY + i * (h + 6);
    tft.fillRect(0, cy, tft.width(), h, bgColor);
    tft.setCursor(cx, cy);
    tft.setTextColor(HX8357_WHITE);
    tft.print(lines[i]);
  }
}

void drawCenteredPopupAuto(const char* msg) {
  digitalWrite(TFT_LITE, HIGH);

  tft.setTextSize(2);
  int16_t x1, y1; uint16_t tw, th;
  tft.getTextBounds(msg, 0, 0, &x1, &y1, &tw, &th);

  const int PAD_X = 24;
  const int PAD_Y = 16;
  int w = tw + PAD_X * 2;
  int h = th + PAD_Y * 2;

  if (w > (int)tft.width() - 20)  w = tft.width() - 20;
  if (h > (int)tft.height() - 20) h = tft.height() - 20;

  int x = (tft.width()  - w) / 2;
  int y = (tft.height() - h) / 2;

  tft.fillRect(x, y, w, h, HX8357_BLACK);
  tft.drawRect(x, y, w, h, HX8357_RED);
  tft.drawRect(x+1, y+1, w-2, h-2, HX8357_RED);

  int tx = x + (w - tw)/2;
  int ty = y + (h - th)/2;
  tft.setTextColor(HX8357_WHITE);
  tft.setCursor(tx, ty);
  tft.print(msg);

  pop_x = x; pop_y = y; pop_w = w; pop_h = h;
  signalLostShown = true;
}

void clearCenteredPopupAndRequestRepaint() {
  if (!signalLostShown) return;
  tft.fillRect(pop_x, pop_y, pop_w, pop_h, bgColor);
  signalLostShown = false;
  requestFullRepaint = true;
}

void computeActiveLayoutGeometry(int &out_txBaseY, int &out_gsBaseY) {
  tft.setTextSize(2);
  int16_t x1, y1; uint16_t w, h;
  tft.getTextBounds("Feather Telemetry", 0, 0, &x1, &y1, &w, &h);
  int headY = 8;
  int headerBottom = headY + h + 4;
  int txBaseY = headerBottom + 6;
  int txEndY  = txBaseY + (TX_ROWS * TX_LINE_H);

  tft.getTextBounds("Ground Station Telemetry", 0, 0, &x1, &y1, &w, &h);
  int gsHeaderY = txEndY + 10;
  int gsHeaderBottom = gsHeaderY + h + 2;
  int gsBaseY = gsHeaderBottom + 6;

  out_txBaseY = txBaseY;
  out_gsBaseY = gsBaseY;
}

void drawSkyEyeConnectButton(uint32_t now) {
  uint16_t border = skyEyeConnectPressed ? labColor : COLOR_DARKGREY;
  uint16_t textCol = skyEyeConnectPressed ? HX8357_BLACK : HX8357_WHITE;
  uint16_t fillCol = skyEyeConnectPressed ? labColor : HX8357_BLACK;
  tft.fillRect(CONNECT_BTN_X, CONNECT_BTN_Y, CONNECT_BTN_W, CONNECT_BTN_H, fillCol);
  tft.drawRect(CONNECT_BTN_X, CONNECT_BTN_Y, CONNECT_BTN_W, CONNECT_BTN_H, border);
  tft.drawRect(CONNECT_BTN_X + 1, CONNECT_BTN_Y + 1, CONNECT_BTN_W - 2, CONNECT_BTN_H - 2, border);
  tft.setTextSize(1);
  tft.setTextColor(textCol);

  if (connectCountdownActive) {
    int countdown = 3 - int((now - connectCountdownStartAt) / 1000UL);
    if (countdown < 1) countdown = 1;
    tft.setCursor(CONNECT_BTN_X + 58, CONNECT_BTN_Y + 11);
    tft.print(countdown);
  } else {
    tft.setCursor(CONNECT_BTN_X + 34, CONNECT_BTN_Y + 11);
    tft.print("Connect");
  }
}

static inline bool touchHitsConnectButton(uint16_t x, uint16_t y) {
  return (x >= CONNECT_BTN_RAW_X_MIN && x <= CONNECT_BTN_RAW_X_MAX &&
          y >= CONNECT_BTN_RAW_Y_MIN && y <= CONNECT_BTN_RAW_Y_MAX);
}

void drawGsRadioBox(uint32_t now, bool force = false, bool includeConnectButton = true) {
  const int boxW = 92;
  const int boxH = 34;
  const int boxX = tft.width() - boxW - 1;
  const int boxY = 80 - 50;

  tft.fillRect(boxX, boxY, boxW, boxH, HX8357_BLACK);
  tft.drawRect(boxX, boxY, boxW, boxH, COLOR_DARKGREY);
  tft.drawRect(boxX + 1, boxY + 1, boxW - 2, boxH - 2, COLOR_DARKGREY);
  tft.setTextSize(1);
  tft.setTextColor(HX8357_WHITE);
  tft.setCursor(boxX + 6, boxY + 6);
  tft.print("RTX:");
  tft.setCursor(boxX + 6, boxY + 20);
  tft.print("RRX:");

  bool txActive = ((now - gsLastTxAt) <= GS_RADIO_ACTIVE_MS);
  bool rxActive = ((now - gsLastRxAt) <= GS_RADIO_ACTIVE_MS);
  uint16_t txCol = txActive ? HX8357_RED : COLOR_DARKGREY;
  uint16_t rxCol = rxActive ? HX8357_GREEN : COLOR_DARKGREY;

  tft.fillCircle(boxX + 72, boxY + 9, 4, txCol);
  tft.fillCircle(boxX + 72, boxY + 23, 4, rxCol);

  if (includeConnectButton) {
    drawSkyEyeConnectButton(now);
  }
}

void drawWaitingFeatherInfoButton() {
  const int btnW = tft.width() - 8;
  const int btnH = 34;
  const int btnX = 4;
  const int btnY = tft.height() - btnH - 4;
  const int btnR = 6;

  tft.fillRoundRect(btnX, btnY, btnW, btnH, btnR, labColor);
  tft.drawRoundRect(btnX, btnY, btnW, btnH, btnR, HX8357_WHITE);
  tft.setTextSize(1);
  tft.setTextColor(HX8357_BLACK);
  const char* label = "Sky Eye Feather Info";
  int16_t x1, y1; uint16_t w, h;
  tft.getTextBounds(label, 0, 0, &x1, &y1, &w, &h);
  tft.setCursor(btnX + (btnW - (int)w)/2, btnY + (btnH - (int)h)/2 + 1);
  tft.print(label);
}

void drawWaitingCenteredContent(const char* statusMsg) {
  tft.setTextSize(2);
  tft.setTextColor(COLOR_ORANGE);
  const char* title1 = "Sky Eye Feather";
  const char* title2 = "  RX Groundstation";
  int16_t x1, y1; uint16_t w, h;
  tft.getTextBounds(title1, 0, 0, &x1, &y1, &w, &h);
  tft.setCursor((tft.width() - (int)w) / 2, 26);
  tft.print(title1);
  tft.getTextBounds(title2, 0, 0, &x1, &y1, &w, &h);
  tft.setCursor((tft.width() - (int)w) / 2, 50);
  tft.print(title2);

  tft.setTextSize(2);
  tft.setTextColor(okColor);
  tft.getTextBounds(statusMsg, 0, 0, &x1, &y1, &w, &h);
  int statusY = 90;
  tft.setCursor((tft.width() - (int)w) / 2, statusY);
  tft.print(statusMsg);

  tft.setTextSize(1);
  tft.setTextColor(HX8357_WHITE);
  const char* hardLine = "Ground Station Hardware Version: " GS_HW_VERSION;
  tft.getTextBounds(hardLine, 0, 0, &x1, &y1, &w, &h);
  int hardY = statusY + 28;
  tft.setCursor((tft.width() - (int)w) / 2, hardY);
  tft.print(hardLine);

  const char* softLine = "Ground Station Software Version: " GS_SW_VERSION;
  tft.getTextBounds(softLine, 0, 0, &x1, &y1, &w, &h);
  int softY = hardY + 14;
  tft.setCursor((tft.width() - (int)w) / 2, softY);
  tft.print(softLine);

  const char* creditLines[] = { CREDIT_LINE_1, CREDIT_LINE_2 };
  for (int i = 0; i < 2; i++) {
    tft.getTextBounds(creditLines[i], 0, 0, &x1, &y1, &w, &h);
    int cy = softY + 14 + i * 12;
    tft.setCursor((tft.width() - (int)w) / 2, cy);
    tft.print(creditLines[i]);
  }
}

void updateWaitingStatusOnly(const char* statusMsg) {
  tft.setTextSize(2);
  int16_t x1, y1; uint16_t w, h;
  tft.getTextBounds(statusMsg, 0, 0, &x1, &y1, &w, &h);
  int statusY = 90;
  tft.fillRect(0, statusY - 2, tft.width(), h + 4, bgColor);
  tft.setTextColor(okColor);
  tft.setCursor((tft.width() - (int)w) / 2, statusY);
  tft.print(statusMsg);
}

void drawWaitingRadioBox(uint32_t now) {
  const int boxW = 156;
  const int boxH = 52;
  const int boxX = (tft.width() - boxW) / 2;
  const int boxY = 176;

  tft.fillRect(boxX, boxY, boxW, boxH, HX8357_BLACK);
  tft.drawRect(boxX, boxY, boxW, boxH, COLOR_DARKGREY);
  tft.drawRect(boxX + 1, boxY + 1, boxW - 2, boxH - 2, COLOR_DARKGREY);
  tft.setTextSize(2);
  tft.setTextColor(HX8357_WHITE);
  tft.setCursor(boxX + 12, boxY + 8);
  tft.print("RTX:");
  tft.setCursor(boxX + 12, boxY + 30);
  tft.print("RRX:");

  bool txActive = ((now - gsLastTxAt) <= GS_RADIO_ACTIVE_MS);
  bool rxActive = ((now - gsLastRxAt) <= GS_RADIO_ACTIVE_MS);
  uint16_t txCol = txActive ? HX8357_RED : COLOR_DARKGREY;
  uint16_t rxCol = rxActive ? HX8357_GREEN : COLOR_DARKGREY;
  tft.fillCircle(boxX + boxW - 18, boxY + 14, 7, txCol);
  tft.fillCircle(boxX + boxW - 18, boxY + 38, 7, rxCol);
}

void drawActiveCopyrightFooter() {
  const char* line = CREDIT_LINE_2;
  int16_t x1, y1; uint16_t w, h;
  tft.setTextSize(1);
  tft.setTextColor(HX8357_WHITE);
  tft.getTextBounds(line, 0, 0, &x1, &y1, &w, &h);
  int y = tft.height() - (int)h - 2;
  tft.fillRect(0, y, tft.width(), h + 2, bgColor);
  tft.setCursor((tft.width() - (int)w) / 2, y);
  tft.print(line);
}

void drawWaitingLayoutOnce() {
  clearScreen();

  drawWaitingCenteredContent("Ground Station RX Ready...");
  drawWaitingRadioBox(millis());
  drawWaitingFeatherInfoButton();

  gsLabelsDrawn = false;
}

static inline bool isSdCardDetected() {
  return digitalRead(SDDET_PIN) == HIGH;
}

void drawDashboardGS() {
  if (!gsLabelsDrawn) return;
  int r = 0;
  {
    uint16_t col = gnd.haveFix ? okColor : errColor;
    tft.fillRect(130, GS_BASE_Y + r*GS_LINE_H, tft.width()-130, GS_LINE_H, bgColor);
    tft.setTextSize(1); tft.setTextColor(col);
    tft.setCursor(130, GS_BASE_Y + r*GS_LINE_H);
    tft.print(gnd.haveFix ? "Fixed" : "No Fix");
    r++;
  }
  {
    uint16_t col = (magStatus == MAG_STATUS_OK) ? okColor : ((magStatus == MAG_STATUS_TESTING) ? warnColor : errColor);
    tft.fillRect(130, GS_BASE_Y + r*GS_LINE_H, tft.width()-130, GS_LINE_H, bgColor);
    tft.setTextSize(1); tft.setTextColor(col);
    tft.setCursor(130, GS_BASE_Y + r*GS_LINE_H);
    tft.print((magStatus == MAG_STATUS_OK) ? "Nominal" : ((magStatus == MAG_STATUS_TESTING) ? "Testing" : "Fail"));
    r++;
  }
  {
    bool sdDetected = isSdCardDetected();
    uint16_t col = sdDetected ? okColor : errColor;
    tft.fillRect(130, GS_BASE_Y + r*GS_LINE_H, tft.width()-130, GS_LINE_H, bgColor);
    tft.setTextSize(1); tft.setTextColor(col);
    tft.setCursor(130, GS_BASE_Y + r*GS_LINE_H);
    tft.print(sdDetected ? "Detected" : "Not Detected");
    r++;
  }
  auto drawGSLine = [&](const String& v, uint16_t col = HX8357_WHITE) {
    tft.fillRect(130, GS_BASE_Y + r*GS_LINE_H, tft.width()-130, GS_LINE_H, bgColor);
    tft.setTextSize(1); tft.setTextColor(col);
    tft.setCursor(130, GS_BASE_Y + r*GS_LINE_H);
    tft.print(v);
    r++;
  };
  drawGSLine(fmtFloat((float)gnd.lat, 6));
  drawGSLine(fmtFloat((float)gnd.lon, 6));
  drawGSLine(fmtFloat(metersToFeet((float)gnd.alt_m), 1));
  drawGSLine(fmtFloat(knotsToMph((float)gnd.spd_kt), 2));
  drawGSLine((gnd.haveFix && gnd.sats >= 0) ? String(gnd.sats) : "NaN");
  drawGSLine(fmtFloat((float)gnd.hdop, 2));
  auto headingToCardinal8 = [](float deg)->String {
    static const char* dirs[8] = {"N","NE","E","SE","S","SW","W","NW"};
    while (deg < 0) deg += 360.0f;
    while (deg >= 360.0f) deg -= 360.0f;
    int idx = int((deg + 22.5f) / 45.0f) & 7;
    return String(dirs[idx]);
  };
  String headingStr = (magStatus == MAG_STATUS_OK) ? (String(gnd.heading_deg, 1) + " deg ("+headingToCardinal8(gnd.heading_deg)+")") : "NaN";
  drawGSLine(headingStr);
  String gsBat = "NaN";
  if (gnd.haveVbat && !isnan(gnd.vbat)) {
    float pct = voltsToPct(gnd.vbat);
    gsBat = fmtFloat(gnd.vbat, 2) + " V  (" + (isnan(pct) ? String("NaN") : String((int)roundf(pct))) + "%)";
  }
  drawGSLine(gsBat);
}

void drawBottomNavBarMock() {
  const int margin = 4;
  const int gap = 6;
  const int h = 24;
  const int r = 6;
  const int navRaisePx = 12;
  const int yRow1 = tft.height() - (h * 2) - gap - 6 - navRaisePx;
  const int yRow2 = yRow1 + h + gap;

  auto drawBtn = [&](int x, int y, int w, const char* txt, uint16_t fillColor = labColor) {
    tft.fillRoundRect(x, y, w, h, r, fillColor);
    tft.drawRoundRect(x, y, w, h, r, HX8357_WHITE);
    tft.setTextSize(1);
    tft.setTextColor(HX8357_BLACK);
    int16_t x1, y1; uint16_t tw, th;
    tft.getTextBounds(txt, 0, 0, &x1, &y1, &tw, &th);
    int tx = x + (w - (int)tw) / 2;
    int ty = y + (h - (int)th) / 2 + 1;
    tft.setCursor(tx, ty);
    tft.print(txt);
  };

  int w2 = (tft.width() - (2 * margin) - gap) / 2;
  drawBtn(margin, yRow1, w2, "Offload Flash", HX8357_GREEN);
  drawBtn(margin + w2 + gap, yRow1, w2, "Erase Flash", HX8357_RED);

  int w3 = (tft.width() - (2 * margin) - (2 * gap)) / 3;
  drawBtn(margin, yRow2, w3, "Telemetry");
  drawBtn(margin + w3 + gap, yRow2, w3, "Tracker");
  drawBtn(margin + (2 * (w3 + gap)), yRow2, w3, "RF Telemetry");
}

void drawActiveLayoutOnce() {
  clearScreen();
  drawGsRadioBox(millis(), true);

  tft.drawFastHLine(0, 2, tft.width(), COLOR_DARKGREY);
  tft.setTextSize(2);
  tft.setTextColor(COLOR_ORANGE);
  const char* top = "Feather Telemetry";
  int16_t x1, y1; uint16_t w, h;
  tft.getTextBounds(top, 0, 0, &x1, &y1, &w, &h);
  int cx = (tft.width() - w) / 2;
  int headY = 8;
  tft.setCursor(cx, headY);
  tft.print(top);

  int headerBottom = headY + h + 4;
  tft.setTextColor(txtColor);
  tft.drawFastHLine(0, headerBottom, tft.width(), COLOR_DARKGREY);
  TX_BASE_Y = headerBottom + 6;

  for (int i=0;i<TX_ROWS;i++){ prevValue[i] = ""; prevValColor[i] = 0xFFFF; }

  const char* labels[TX_ROWS] = {
    "GPS Fix:", "IMU:", "Microphone:", "Flash Chip:",
    "Latitude:", "Longitude:", "Altitude (ft):", "Speed (mph):",
    "Satellites:", "HDOP:", "COG (deg):", "aX/Y/Z:",
    "gX/Y/Z:", "Microphone ADC:", "RSSI/SNR:", "Tx Power:", "Battery:"
  };
  tft.setTextSize(1);
  tft.setTextColor(labColor);
  for (int row=0; row<TX_ROWS; row++) {
    int y = TX_BASE_Y + row * TX_LINE_H;
    tft.fillRect(0, y, tft.width(), TX_LINE_H, bgColor);
    tft.setCursor(LABEL_X, y);
    tft.print(labels[row]);
    tft.fillRect(VALUE_X, y, tft.width()-VALUE_X, TX_LINE_H, bgColor);
  }

  const int txEndY = TX_BASE_Y + (TX_ROWS * TX_LINE_H);
  tft.drawFastHLine(0, txEndY + 2, tft.width(), COLOR_DARKGREY);

  tft.setTextSize(2);
  tft.setTextColor(COLOR_ORANGE);
  const char* gsHeader = "Ground Station Telemetry";
  tft.getTextBounds(gsHeader, 0, 0, &x1, &y1, &w, &h);
  cx = (tft.width() - w) / 2;
  int gsHeaderY = txEndY + 10;
  tft.fillRect(0, gsHeaderY, tft.width(), h, bgColor);
  tft.setCursor(cx, gsHeaderY);
  tft.print(gsHeader);

  int gsHeaderBottom = gsHeaderY + h + 2;
  tft.drawFastHLine(0, gsHeaderBottom, tft.width(), COLOR_DARKGREY);
  GS_BASE_Y = gsHeaderBottom + 6;

  const char* gsLabels[] = {
    "GPS Fix:", "Magnetometer:", "SD Card:", "Latitude:", "Longitude:", "Altitude (ft):",
    "Speed (mph):", "Satellites:", "HDOP:", "Heading (deg):", "Battery:"
  };
  const int gsRows = sizeof(gsLabels)/sizeof(gsLabels[0]);
  tft.setTextSize(1);
  tft.setTextColor(labColor);
  for (int r=0; r<gsRows; r++) {
    int y = GS_BASE_Y + r * GS_LINE_H;
    tft.fillRect(0, y, tft.width(), GS_LINE_H, bgColor);
    tft.setCursor(8, y);
    tft.print(gsLabels[r]);
    tft.fillRect(130, y, tft.width()-130, GS_LINE_H, bgColor);
  }

  drawBottomNavBarMock();
  drawActiveCopyrightFooter();

  gsLabelsDrawn = true;
}

void drawValueDiff(int row, const String& value, uint16_t vColor = HX8357_WHITE) {
  if (value != prevValue[row] || vColor != prevValColor[row]) {
    int y = TX_BASE_Y + row * TX_LINE_H;
    tft.fillRect(VALUE_X, y, tft.width()-VALUE_X, TX_LINE_H, bgColor);
    tft.setTextSize(1);
    tft.setCursor(VALUE_X, y);
    tft.setTextColor(vColor);
    tft.print(value);
    prevValue[row]   = value;
    prevValColor[row]= vColor;
  }
}

void drawDashboardTX(const Telemetry& t, int rssi, float snr) {
  bool txHasNav = (t.gps_status == "fixed" || t.gps_status == "stale");
  uint16_t gpsCol = (t.gps_status == "fixed") ? okColor : ((t.gps_status == "stale") ? warnColor : errColor);
  uint16_t imuCol = (t.imu_status == "ok") ? okColor : ((t.imu_status == "testing") ? warnColor : errColor);
  uint16_t micCol = (t.mic_status == "ok") ? okColor : ((t.mic_status == "testing") ? warnColor : errColor);
  uint16_t flsCol = (t.flash_status == "ok") ? okColor : ((t.flash_status == "testing") ? warnColor : errColor);

  drawValueDiff(0,  normalizeStatusDisplay(t.gps_status),   gpsCol);
  drawValueDiff(1,  normalizeStatusDisplay(t.imu_status),   imuCol);
  drawValueDiff(2,  normalizeStatusDisplay(t.mic_status),   micCol);
  drawValueDiff(3,  normalizeStatusDisplay(t.flash_status), flsCol);
  drawValueDiff(4,  fmtFloat(t.lat, 6));
  drawValueDiff(5,  fmtFloat(t.lon, 6));
  drawValueDiff(6,  fmtFloat(metersToFeet(t.alt_m), 1));
  drawValueDiff(7,  fmtFloat(knotsToMph(t.spd_kt), 2));

  String txSatsStr = (txHasNav && t.sats >= 0) ? String(t.sats) : String("NaN");
  drawValueDiff(8,  txSatsStr);

  drawValueDiff(9,  fmtFloat(t.hdop, 2));
  drawValueDiff(10, fmtFloat(t.cog_deg, 1));
  drawValueDiff(11, String("x:") + fmtFloat(t.ax,3) + ",y:" + fmtFloat(t.ay,3) + ",z:" + fmtFloat(t.az,3));
  drawValueDiff(12, String("x:") + fmtFloat(t.gx,3) + ",y:" + fmtFloat(t.gy,3) + ",z:" + fmtFloat(t.gz,3));
  drawValueDiff(13, fmtFloat(t.mic,0));
  drawValueDiff(14, String(rssi) + " / " + String(snr, 1));
  drawValueDiff(15, String("(") + formatGroundTxPower() + " | " + formatFeatherTxPower(t) + ")");

  String txBat = "NaN";
  if (!isnan(t.bat_v)) {
    float pct = voltsToPct(t.bat_v);
    String pwrSrc = (t.bat_v > 4.5f) ? String("USB PWR") : String("BAT PWR");
    txBat = fmtFloat(t.bat_v, 2) + " V  (" + (isnan(pct) ? String("NaN") : String((int)roundf(pct))) + "%) (" + pwrSrc + ")";
  }
  drawValueDiff(16, txBat);
}

void updateBattery() {
  static float vFilt = NAN;
  float vRaw = maxlipo.cellVoltage();

  if (vRaw > 2.0f && vRaw < 5.5f) {
    float vCal = calibrateGroundBatteryVolts(vRaw);
    if (isnan(vFilt)) vFilt = vCal;
    else vFilt = (GS_BAT_FILTER_ALPHA * vCal) + ((1.0f - GS_BAT_FILTER_ALPHA) * vFilt);

    gnd.vbat = vFilt;
    float pct = voltsToPct(vFilt);
    gnd.soc = pct;
    gnd.haveVbat = true;
  } else {
    gnd.haveVbat = false;
    gnd.vbat = NAN;
    gnd.soc = NAN;
  }
}

void updateGroundGPSFromTinyGPS() {
  if (gps.location.isValid()) {
    gnd.lat = gps.location.lat();
    gnd.lon = gps.location.lng();
    gnd.haveFix = true;
  } else {
    gnd.haveFix = false;
  }
  if (gps.altitude.isValid())    gnd.alt_m = gps.altitude.meters();
  if (gps.hdop.isValid())        gnd.hdop  = gps.hdop.value() / 100.0;
  if (gps.satellites.isValid())  gnd.sats  = gps.satellites.value();
  if (gps.speed.isValid())       gnd.spd_kt = gps.speed.knots();

  if (!gnd.haveFix) {
    gnd.hdop   = NAN;
    gnd.sats   = -1;
    gnd.spd_kt = NAN;
  }
}

static inline float normDeg(float d) { while (d < 0) d += 360.0f; while (d >= 360.0f) d -= 360.0f; return d; }
void updateMag() {
  if (!magI2cDetected) {
    gnd.haveMag = false;
    if ((millis() - magTestStartedAt) >= MAG_TEST_WINDOW_MS) {
      magStatus = MAG_STATUS_FAIL;
    } else {
      magStatus = MAG_STATUS_TESTING;
    }
    return;
  }

  sensors_event_t evt;
  bool valid = false;
  if (hmc.getEvent(&evt)) {
    float mx = evt.magnetic.x;
    float my = evt.magnetic.y;
    float mz = evt.magnetic.z;
    float magNorm = sqrtf(mx*mx + my*my + mz*mz);
    valid = isfinite(mx) && isfinite(my) && isfinite(mz) && (magNorm > 0.05f) && (magNorm < 2000.0f);
  }

  if (valid) {
    float heading = atan2f(evt.magnetic.y, evt.magnetic.x) * 180.0f / PI;
    heading += DECLINATION_DEG;
    heading = normDeg(heading);
    heading = 360.0f - heading;
    if (heading >= 360.0f) heading -= 360.0f;

    gnd.heading_deg = heading;
    gnd.haveMag = true;
    if (magGoodStreak < 255) magGoodStreak++;
    magBadStreak = 0;
  } else {
    gnd.haveMag = false;
    if (magBadStreak < 255) magBadStreak++;
    magGoodStreak = 0;
  }

  uint32_t now = millis();
  if (magStatus == MAG_STATUS_TESTING) {
    if (magGoodStreak >= MAG_GOOD_SAMPLES_REQUIRED) {
      magStatus = MAG_STATUS_OK;
    } else if ((now - magTestStartedAt) >= MAG_TEST_WINDOW_MS) {
      magStatus = MAG_STATUS_FAIL;
    }
  } else if (magStatus == MAG_STATUS_OK) {
    if (magBadStreak >= MAG_BAD_SAMPLES_REQUIRED) {
      magStatus = MAG_STATUS_FAIL;
    }
  } else {
    if (magGoodStreak >= MAG_GOOD_SAMPLES_REQUIRED) {
      magStatus = MAG_STATUS_OK;
    }
  }
}

static inline bool strEmptyIsNaN(String s, float& out) {
  s.trim();
  if (s.length() == 0) { out = NAN; return true; }
  out = s.toFloat();
  return true;
}
static inline bool strEmptyIsInt(String s, int& out) {
  s.trim();
  if (s.length() == 0) return false;
  out = s.toInt();
  return true;
}

bool parseTelemetry(const String& pkt, Telemetry& t) {
  if (pkt.startsWith("L,")) {
    const int MAXF = 32;
    String f[MAXF];
    int nf = 0, start = 0, comma = -1;
    while (nf < MAXF) {
      comma = pkt.indexOf(',', start);
      if (comma < 0) { f[nf++] = pkt.substring(start); break; }
      f[nf++] = pkt.substring(start, comma);
      start = comma + 1;
    }
    if (nf < 6) return false;

    auto get = [&](int i)->String { return (i < nf) ? f[i] : String(); };

    if (get(1).length()) t.ms = (uint32_t)get(1).toInt();

    char gpsC = get(2).length() ? get(2)[0] : 'W';
    if      (gpsC == 'F') t.gps_status = "fixed";
    else if (gpsC == 'S') t.gps_status = "stale";
    else                  t.gps_status = "waiting_for_fix";

    if (get(3) == "1") t.imu_status = "ok";
    else if (get(3) == "T") t.imu_status = "testing";
    else t.imu_status = "fail";

    if (get(4) == "1") t.mic_status = "ok";
    else if (get(4) == "T") t.mic_status = "testing";
    else t.mic_status = "fail";

    if (get(5) == "1") t.flash_status = "ok";
    else if (get(5) == "T") t.flash_status = "testing";
    else t.flash_status = "fail";

    strEmptyIsNaN(get(6),  t.lat);
    strEmptyIsNaN(get(7),  t.lon);
    strEmptyIsNaN(get(8),  t.alt_m);
    strEmptyIsNaN(get(9),  t.hdop);
    { int s; if (strEmptyIsInt(get(10), s)) t.sats = s; else t.sats = -1; }
    strEmptyIsNaN(get(11), t.spd_kt);
    strEmptyIsNaN(get(12), t.cog_deg);

    strEmptyIsNaN(get(13), t.ax);
    strEmptyIsNaN(get(14), t.ay);
    strEmptyIsNaN(get(15), t.az);
    strEmptyIsNaN(get(16), t.gx);
    strEmptyIsNaN(get(17), t.gy);
    strEmptyIsNaN(get(18), t.gz);

    strEmptyIsNaN(get(19), t.mic);
    strEmptyIsNaN(get(20), t.bat_v);
    { int pwr; if (strEmptyIsInt(get(21), pwr)) t.feather_tx_dbm = pwr; else t.feather_tx_dbm = -1; }

    return true;
  }

  if (!pkt.startsWith("LORA_TX,")) {
    return false;
  }

  int start = 0;
  int comma = pkt.indexOf(',');
  if (comma < 0) return false;
  start = comma + 1;

  comma = pkt.indexOf(',', start);
  if (comma < 0) comma = pkt.length();
  String msStr = pkt.substring(start, comma);
  if (msStr.length()) t.ms = (uint32_t)msStr.toInt();
  start = (comma < (int)pkt.length()) ? (comma + 1) : pkt.length();

  while (start < (int)pkt.length()) {
    comma = pkt.indexOf(',', start);
    if (comma < 0) comma = pkt.length();
    String tok = pkt.substring(start, comma);
    int eq = tok.indexOf('=');
    if (eq > 0) {
      String key = tok.substring(0, eq);
      String val = tok.substring(eq + 1);
      key.trim(); val.trim();

      auto parseF = [&](String s, float& out){ if (s.length()==0 || s=="NaN") { out=NAN; } else { out=s.toFloat(); } };

      if (key == "gps_status") t.gps_status = val;
      else if (key == "imu_status") t.imu_status = val;
      else if (key == "mic_status") t.mic_status = val;

      else if (key == "lat")     parseF(val, t.lat);
      else if (key == "lon")     parseF(val, t.lon);
      else if (key == "alt_m")   parseF(val, t.alt_m);
      else if (key == "hdop")    parseF(val, t.hdop);
      else if (key == "spd_kt")  parseF(val, t.spd_kt);
      else if (key == "cog_deg") parseF(val, t.cog_deg);

      else if (key == "ax") parseF(val, t.ax);
      else if (key == "ay") parseF(val, t.ay);
      else if (key == "az") parseF(val, t.az);
      else if (key == "gx") parseF(val, t.gx);
      else if (key == "gy") parseF(val, t.gy);
      else if (key == "gz") parseF(val, t.gz);
      else if (key == "mic") parseF(val, t.mic);

      else if (key == "sats") { if (val.length()) t.sats = val.toInt(); else t.sats = -1; }
      else if (key == "bat_v" || key == "bat") parseF(val, t.bat_v);
      else if (key == "fp_dbm" || key == "tx_pwr_dbm") { if (val.length()) t.feather_tx_dbm = val.toInt(); else t.feather_tx_dbm = -1; }
    }
    start = comma + 1;
  }

  t.flash_status = "fail";
  return true;
}

void applyGroundTxPower() {
  if (gsTxPowerDbm < GS_TX_PWR_MIN_DBM) gsTxPowerDbm = GS_TX_PWR_MIN_DBM;
  if (gsTxPowerDbm > GS_TX_PWR_MAX_DBM) gsTxPowerDbm = GS_TX_PWR_MAX_DBM;
  LoRa.setTxPower(gsTxPowerDbm);
}

void adjustGroundTxPowerFromRssi(int rssiDbm) {
  if (rssiDbm < GS_TX_PWR_RSSI_LOW_DBM && gsTxPowerDbm < GS_TX_PWR_MAX_DBM) {
    gsTxPowerDbm++;
    applyGroundTxPower();
  } else if (rssiDbm > GS_TX_PWR_RSSI_HIGH_DBM && gsTxPowerDbm > GS_TX_PWR_MIN_DBM) {
    gsTxPowerDbm--;
    applyGroundTxPower();
  }
}

void sendControlPacket(const char* pkt) {
  gsLastTxAt = millis();
  LoRa.idle();
  LoRa.beginPacket();
  LoRa.print(pkt);
  LoRa.endPacket();
  LoRa.receive();
}

void sendStartIfDue(uint32_t now) {
  if (lastCtrlStartAt == 0 || (now - lastCtrlStartAt >= CTRL_START_PERIOD_MS)) {
    lastCtrlStartAt = now;
    sendControlPacket(CTRL_START_PKT);
  }
}

void setup() {
  pinMode(SD_CS,   OUTPUT); digitalWrite(SD_CS,   HIGH);
  pinMode(LORA_CS, OUTPUT); digitalWrite(LORA_CS, HIGH);
  pinMode(SDDET_PIN, INPUT_PULLUP);
  pinMode(TFT_LITE, OUTPUT); digitalWrite(TFT_LITE, HIGH);

  delay(50);
  SPI.begin();

  tft.begin(HX8357D);
  tft.setRotation(2);

  drawWaitingLayoutOnce();
  bootAt = millis();
  magTestStartedAt = bootAt;
  magStatus = MAG_STATUS_TESTING;
  magGoodStreak = 0;
  magBadStreak = 0;
  showedWaiting = false;
  uiActivated = false;
  signalLostShown = false;
  requestFullRepaint = false;
  haveLastT = false;

  Wire.begin(3, 4);
  Wire.setClock(400000);

  Wire.beginTransmission(0x1E);
  magI2cDetected = (Wire.endTransmission() == 0);

  if (!touch.begin()) {
    Serial.println("TSC2007 not found at 0x48");
  } else {
    Serial.println("TSC2007 found (0x48)");
  }

  maxlipo.begin(&Wire);
  if (magI2cDetected) {
    hmc.begin();
  }

  GS_GPS.begin(GS_GPS_BAUD, SERIAL_8N1, GS_GPS_RX_PIN, GS_GPS_TX_PIN);

  LoRa.setPins(LORA_CS, LORA_RST, LORA_IRQ);
  LoRa.setSPIFrequency(SPI_HZ);
  if (!LoRa.begin(RF_FREQ)) {
    drawGreenBanner("LoRa init failed!");
  } else {
    LoRa.setSpreadingFactor(7);
    LoRa.setSignalBandwidth(125E3);
    LoRa.setCodingRate4(5);
    LoRa.setSyncWord(0x12);
    LoRa.enableCrc();
    applyGroundTxPower();
  }
  LoRa.receive();
  lastCtrlStartAt = 0;
  lastCtrlAckAt = 0;

  sendControlPacket(CTRL_START_PKT);

  Serial.begin(115200);
  delay(150);
  Serial.println("Boot OK (TFT->I2C(400k)->GPS->LoRa->Serial->Touch).");
}

void loop() {
  uint32_t now = millis();

  if (connectCountdownActive && (now - connectCountdownStartAt >= 3000UL)) {
    connectCountdownActive = false;
    connectCountdownStartAt = 0;
    skyEyeConnectPressed = false;
    digitalWrite(TFT_LITE, LOW);
    Serial.println("Connect countdown done -> A2 LOW");
  }

  if (!uiActivated && !showedWaiting && (now - bootAt >= 1000)) {
    updateWaitingStatusOnly("Waiting For Feather TX...");
    showedWaiting = true;
  }

  while (GS_GPS.available()) {
    gps.encode((char)GS_GPS.read());
  }

  updateGroundGPSFromTinyGPS();
  updateMag();

  static uint32_t lastBat = 0;
  if (now - lastBat >= 1000) { lastBat = now; updateBattery(); }

  if (uiActivated) {
    drawGsRadioBox(now);
    if (!signalLostShown) {
      drawDashboardGS();
      if (haveLastT) {
        drawDashboardTX(lastT, lastRSSI, lastSNR);
      }
    }
  } else {
    drawWaitingRadioBox(now);
  }

  if (!uiActivated) {
    sendStartIfDue(now);
  }

  if (uiActivated && (now - lastCtrlAckAt >= CTRL_ACK_PERIOD_MS)) {
    lastCtrlAckAt = now;
    sendControlPacket(CTRL_ACK_PKT);
  }

  {
    uint16_t x, y, z1, z2;
    if (touch.read_touch(&x, &y, &z1, &z2)) {
      Serial.print("TOUCH,x="); Serial.print(x);
      Serial.print(",y=");      Serial.print(y);
      Serial.print(",z1=");     Serial.print(z1);
      Serial.print(",z2=");     Serial.println(z2);

      if (digitalRead(TFT_LITE) == LOW) {
        digitalWrite(TFT_LITE, HIGH);
        skyEyeConnectPressed = false;
        connectCountdownActive = false;
        connectCountdownStartAt = 0;
        if (uiActivated) drawSkyEyeConnectButton(now);
        Serial.println("Screen wake touch -> A2 HIGH");
      } else if (uiActivated && !signalLostShown && touchHitsConnectButton(x, y)) {
        if (connectCountdownActive) {
          connectCountdownActive = false;
          connectCountdownStartAt = 0;
          skyEyeConnectPressed = false;
          digitalWrite(TFT_LITE, HIGH);
          drawSkyEyeConnectButton(now);
          Serial.println("Connect countdown canceled");
        } else {
          connectCountdownActive = true;
          connectCountdownStartAt = now;
          skyEyeConnectPressed = true;
          digitalWrite(TFT_LITE, HIGH);
          drawSkyEyeConnectButton(now);
          Serial.println("Connect countdown start: 3..2..1");
        }
      }
    }
  }

  int packetSize = LoRa.parsePacket();
  if (packetSize) {
    gsLastRxAt = now;
    String pkt; pkt.reserve(packetSize + 8);
    while (LoRa.available()) pkt += (char)LoRa.read();

    Telemetry t;
    if (parseTelemetry(pkt, t)) {
      lastPktAt = now;

      if (!uiActivated) {
        clearCenteredPopupAndRequestRepaint();
        drawActiveLayoutOnce();
        uiActivated = true;
      }

      clearCenteredPopupAndRequestRepaint();

      lastT = t; lastRSSI = LoRa.packetRssi(); lastSNR = LoRa.packetSnr(); haveLastT = true;
      adjustGroundTxPowerFromRssi(lastRSSI);

      if (requestFullRepaint) {
        drawActiveLayoutOnce();
        requestFullRepaint = false;
      }

      drawDashboardTX(t, lastRSSI, lastSNR);
      drawDashboardGS();
    }
  }

  if (uiActivated) {
    if ((now - lastPktAt) > LOSS_TIMEOUT_MS) {
      sendStartIfDue(now);
      if (!signalLostShown) {
        drawCenteredPopupAuto("Signal Lost...");
      }
    } else {
      if (signalLostShown) {
        clearCenteredPopupAndRequestRepaint();
        if (haveLastT) {
          drawActiveLayoutOnce();
          drawDashboardTX(lastT, lastRSSI, lastSNR);
          drawDashboardGS();
        }
      }
    }
  }
}
