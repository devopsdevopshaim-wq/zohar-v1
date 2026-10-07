/* Hebrew calendar engine: dates, year types, the weekly Torah portion (Israel) and the holidays.
   Pure arithmetic, no network and no tables per year, so it is right for any year and
   needs no yearly update. Parsha algorithm after Dr. Irv Bromberg (as in pyluach / Hebcal).
   Days are counted as days since 1970-01-01 (UTC midnight). */
(function (root) {
  'use strict';
  var EPOCH_RD = -1373427;      // R.D. day number of the Hebrew calendar's day 1 (Reingold & Dershowitz)
  var UNIX_RD = 719163;         // R.D. of 1970-01-01

  var PARSHIOT = ['בראשית', 'נח', 'לך לך', 'וירא', 'חיי שרה', 'תולדות', 'ויצא', 'וישלח', 'וישב', 'מקץ', 'ויגש', 'ויחי', 'שמות', 'וארא', 'בא', 'בשלח', 'יתרו',
    'משפטים', 'תרומה', 'תצוה', 'כי תשא', 'ויקהל', 'פקודי', 'ויקרא', 'צו', 'שמיני', 'תזריע', 'מצורע', 'אחרי מות', 'קדושים', 'אמור', 'בהר', 'בחוקותי',
    'במדבר', 'נשא', 'בהעלותך', 'שלח', 'קרח', 'חוקת', 'בלק', 'פינחס', 'מטות', 'מסעי', 'דברים', 'ואתחנן', 'עקב', 'ראה', 'שופטים', 'כי תצא', 'כי תבוא',
    'ניצבים', 'וילך', 'האזינו', 'וזאת הברכה'];

  // month ids: 1 Nisan ... 6 Elul, 7 Tishrei ... 12 Adar (13 Adar II in a leap year, 12 = Adar I)
  var MONTH_NAMES = { 1: 'ניסן', 2: 'אייר', 3: 'סיוון', 4: 'תמוז', 5: 'אב', 6: 'אלול', 7: 'תשרי', 8: 'חשוון', 9: 'כסלו', 10: 'טבת', 11: 'שבט', 12: 'אדר', 13: 'אדר ב׳' };

  function isLeap(y) { return ((7 * y + 1) % 19) < 7; }

  var _cache = {};
  function elapsed(y) {
    var months = Math.floor((235 * y - 234) / 19);
    var parts = 12084 + 13753 * months;
    var day = months * 29 + Math.floor(parts / 25920);
    if ((3 * (day + 1)) % 7 < 3) day += 1;
    return day;
  }
  function delay(y) {
    var a = elapsed(y - 1), b = elapsed(y), c = elapsed(y + 1);
    if (c - b === 356) return 2;
    if (b - a === 382) return 1;
    return 0;
  }
  // R.D. of 1 Tishrei
  function newYearRD(y) { return EPOCH_RD + elapsed(y) + delay(y); }
  function newYearDay(y) { return newYearRD(y) - UNIX_RD; }
  function yearLength(y) { return newYearRD(y + 1) - newYearRD(y); }

  function monthLength(y, m) {
    var len = yearLength(y) % 10;   // 3 = deficient, 4 = regular, 5 = complete
    if (m === 8) return len === 5 ? 30 : 29;      // Cheshvan
    if (m === 9) return len === 3 ? 29 : 30;      // Kislev
    if (m === 12) return isLeap(y) ? 30 : 29;     // Adar I (30) or Adar
    return { 7: 30, 10: 29, 11: 30, 13: 29, 1: 30, 2: 29, 3: 30, 4: 29, 5: 30, 6: 29 }[m];
  }
  // months of a year in calendar order, starting from Tishrei
  function monthsOf(y) {
    var out = [7, 8, 9, 10, 11, 12];
    if (isLeap(y)) out.push(13);
    out.push(1, 2, 3, 4, 5, 6);
    return out;
  }
  function monthName(y, m) { return (m === 12 && isLeap(y)) ? 'אדר א׳' : MONTH_NAMES[m]; }

  // day (days since 1970) -> {y, m, d}
  function fromDay(day) {
    var y = Math.floor((day + UNIX_RD - EPOCH_RD) / 365.2468) ;
    while (newYearDay(y + 1) <= day) y++;
    while (newYearDay(y) > day) y--;
    var rest = day - newYearDay(y), ms = monthsOf(y);
    for (var i = 0; i < ms.length; i++) {
      var l = monthLength(y, ms[i]);
      if (rest < l) return { y: y, m: ms[i], d: rest + 1 };
      rest -= l;
    }
    throw new Error('hebrew date out of range');
  }
  function toDay(y, m, d) {
    var rest = 0, ms = monthsOf(y);
    for (var i = 0; i < ms.length; i++) {
      if (ms[i] === m) return newYearDay(y) + rest + d - 1;
      rest += monthLength(y, ms[i]);
    }
    throw new Error('no such month');
  }
  function dayOf(date) { return Math.floor(Date.UTC(date.getFullYear(), date.getMonth(), date.getDate()) / 86400000); }
  function dateOf(day) { var t = new Date(day * 86400000); return new Date(t.getUTCFullYear(), t.getUTCMonth(), t.getUTCDate()); }
  function weekday(day) { return ((day % 7) + 11) % 7; }   // 0 = Sunday (1970-01-01 was a Thursday)
  function iso(day) { return new Date(day * 86400000).toISOString().slice(0, 10); }

  // ---- Hebrew numerals (gematria)
  function numeral(n, quote) {
    if (n <= 0) return '';
    var t = [[400, 'ת'], [300, 'ש'], [200, 'ר'], [100, 'ק'], [90, 'צ'], [80, 'פ'], [70, 'ע'], [60, 'ס'], [50, 'נ'], [40, 'מ'], [30, 'ל'], [20, 'כ'], [10, 'י'], [9, 'ט'], [8, 'ח'], [7, 'ז'], [6, 'ו'], [5, 'ה'], [4, 'ד'], [3, 'ג'], [2, 'ב'], [1, 'א']];
    var s = '';
    while (n > 0) {
      if (n === 15) { s += 'טו'; break; }
      if (n === 16) { s += 'טז'; break; }
      for (var i = 0; i < t.length; i++) if (n >= t[i][0]) { s += t[i][1]; n -= t[i][0]; break; }
    }
    if (quote === false) return s;
    if (s.length === 1) return s + '׳';
    return s.slice(0, -1) + '״' + s.slice(-1);
  }
  function yearName(y) { return numeral(y % 1000); }       // 5787 -> תשפ״ז

  // ---- the weekly portion, Israel
  var YT = { VAYAKHEL: 21, TAZRIA: 26, ACHAREI: 28, BEHAR: 31, MATTOS: 41, NITZAVIM: 50 };
  function parshaless(h) {
    // Israel: one day of yom tov
    if (h.m === 7 && (h.d === 1 || h.d === 2 || h.d === 10 || (h.d >= 15 && h.d <= 22))) return true;
    if (h.m === 1 && h.d >= 15 && h.d <= 21) return true;
    if (h.m === 3 && h.d === 6) return true;
    return false;
  }
  var _tables = {};
  function parshaTable(y) {
    if (_tables[y]) return _tables[y];
    var list = [51, 52]; for (var i = 0; i < 52; i++) list.push(i);
    var leap = isLeap(y), rh = newYearDay(y), pesachDow = weekday(toDay(y, 1, 15));
    if (weekday(rh) > 3) list.shift();
    var sh = rh + ((6 - weekday(rh) + 7) % 7); if (weekday(rh) === 6) sh = rh;  // first Shabbat on or after Rosh Hashana
    var end = newYearDay(y + 1), table = [];
    for (; sh < end; sh += 7) {
      var h = fromDay(sh);
      if (parshaless(h)) { table.push({ day: sh, parts: null }); continue; }
      var p = list.shift(), parts = [p];
      var erevPesach = toDay(y, 1, 14), tishaBav9 = toDay(y, 5, 9);
      if ((p === YT.VAYAKHEL && Math.floor((erevPesach - sh) / 7) < 3) ||
          ((p === YT.TAZRIA || p === YT.ACHAREI) && !leap) ||
          (p === YT.BEHAR && !leap && pesachDow !== 6) ||
          (p === YT.MATTOS && Math.floor((tishaBav9 - sh) / 7) < 2) ||
          (p === YT.NITZAVIM && weekday(newYearDay(y + 1)) > 3)) parts.push(list.shift());
      table.push({ day: sh, parts: parts });
    }
    _tables[y] = table;
    return table;
  }
  function parshaName(parts) { return parts.map(function (i) { return PARSHIOT[i]; }).join('־'); }
  // the portion read on the Shabbat on or after `day`: {parts, name, day} or {parts:null, day}
  function parshaFor(day) {
    var sat = day + ((6 - weekday(day) + 7) % 7);
    var y = fromDay(sat).y, t = parshaTable(y);
    for (var i = 0; i < t.length; i++) if (t[i].day === sat) return { day: sat, parts: t[i].parts, name: t[i].parts ? parshaName(t[i].parts) : null };
    return { day: sat, parts: null, name: null };
  }
  function parshiotOfYear(y) {
    return parshaTable(y).filter(function (r) { return r.parts; }).map(function (r) { return { day: r.day, parts: r.parts, name: parshaName(r.parts) }; });
  }

  // ---- holidays (Israel)
  var DESC = {
    'ראש השנה': 'יום הדין ותחילת השנה העברית. תקיעת שופר, תפילות מיוחדות ותשובה.',
    'צום גדליה': 'צום לזכר רצח גדליה בן אחיקם, המושל היהודי האחרון ביהודה.',
    'יום כיפור': 'יום הכיפורים: יום הסליחה והתשובה. צום, תפילות וקבלת החלטות טובות.',
    'סוכות': 'חג הסוכות: ישיבה בסוכה, נטילת ארבעת המינים ושמחת בית השואבה.',
    'הושענא רבה': 'יום ההושענות האחרון בסוכות, וחתימת הדין.',
    'שמיני עצרת ושמחת תורה': 'שמיני עצרת ושמחת תורה: מסיימים את התורה ומתחילים מחדש.',
    'חנוכה': 'שמונה ימים של הדלקת נרות לזכר ניצחון החשמונאים וניס פך השמן.',
    'עשרה בטבת': 'צום לזכר תחילת המצור על ירושלים.',
    'ט״ו בשבט': 'ראש השנה לאילנות.',
    'תענית אסתר': 'צום לפני פורים, לזכר תעניתם של היהודים בימי המן.',
    'פורים': 'קריאת המגילה, משלוח מנות, מתנות לאביונים ומשתה.',
    'שושן פורים': 'פורים של ירושלים והערים המוקפות חומה.',
    'פסח': 'חג החירות: ליל הסדר, אכילת מצה, וביעור החמץ.',
    'יום השואה': 'יום הזיכרון לשואה ולגבורה.',
    'יום הזיכרון': 'יום הזיכרון לחללי מערכות ישראל ונפגעי פעולות האיבה.',
    'יום העצמאות': 'יום הכרזת העצמאות של מדינת ישראל.',
    'פסח שני': 'מועד לאלה שלא הקריבו את קרבן הפסח בזמנו.',
    'ל״ג בעומר': 'הילולת רבי שמעון בר יוחאי, ביום זה נגלה רזי תורת הסוד. מדורות ושמחה במירון.',
    'יום ירושלים': 'יום איחוד ירושלים.',
    'שבועות': 'חג מתן תורה וחג הביכורים. לימוד בליל שבועות.',
    'שבעה עשר בתמוז': 'צום לזכר הבקעת חומות ירושלים ותחילת שלושת השבועות.',
    'תשעה באב': 'צום לזכר חורבן שני הבתים.',
    'ט״ו באב': 'חג האהבה, יום של שמחה בימי המקדש.'
  };
  function hol(name, y, m, d, d2, type) { return { name: name, y: y, m: m, d: d, d2: d2 || d, type: type || 'holiday' }; }
  function holidaysOfYear(y) {
    var leap = isLeap(y), adar = leap ? 13 : 12, out = [];
    function add(h) { h.start = toDay(h.y, h.m, h.d); h.end = toDay(h.y, h.m, h.d2); out.push(h); }
    // fasts that never fall on Shabbat
    function fast(name, m, d, shiftTo) {
      var day = toDay(y, m, d);
      if (weekday(day) === 6) day += shiftTo;
      var hd = fromDay(day);
      return { name: name, y: hd.y, m: hd.m, d: hd.d, d2: hd.d, type: 'fast' };
    }
    // y is the year that starts at 1 Tishrei; Nisan..Elul belong to year y as well (counted from Tishrei)
    add(hol('ראש השנה', y, 7, 1, 2));
    add(fast('צום גדליה', 7, 3, 1));
    add(hol('יום כיפור', y, 7, 10, 10, 'fast'));
    add(hol('סוכות', y, 7, 15, 21));
    add(hol('הושענא רבה', y, 7, 21));
    add(hol('שמיני עצרת ושמחת תורה', y, 7, 22));
    add(hol('חנוכה', y, 9, 25, 25 + 7));
    add(fast('עשרה בטבת', 10, 10, 1));
    add(hol('ט״ו בשבט', y, 11, 15));
    // Ta'anit Esther: 13 Adar, Thursday before if Shabbat
    var te = toDay(y, adar, 13); if (weekday(te) === 6) te -= 2; var teh = fromDay(te);
    out.push({ name: 'תענית אסתר', y: y, m: teh.m, d: teh.d, d2: teh.d, type: 'fast', start: te, end: te });
    add(hol('פורים', y, adar, 14));
    add(hol('שושן פורים', y, adar, 15));
    add(hol('פסח', y, 1, 15, 21));
    // Yom HaZikaron / HaAtzmaut with the weekday shifts
    var ya = toDay(y, 2, 5), w = weekday(ya);
    if (w === 5) ya -= 1; else if (w === 6) ya -= 2; else if (w === 1) ya += 1;
    var yz = ya - 1, yah = fromDay(ya), yzh = fromDay(yz);
    out.push({ name: 'יום הזיכרון', y: y, m: yzh.m, d: yzh.d, d2: yzh.d, type: 'holiday', start: yz, end: yz });
    out.push({ name: 'יום העצמאות', y: y, m: yah.m, d: yah.d, d2: yah.d, type: 'holiday', start: ya, end: ya });
    add(hol('פסח שני', y, 2, 14));
    add(hol('ל״ג בעומר', y, 2, 18));
    add(hol('יום ירושלים', y, 2, 28));
    add(hol('שבועות', y, 3, 6));
    add(fast('שבעה עשר בתמוז', 4, 17, 1));
    add(fast('תשעה באב', 5, 9, 1));
    add(hol('ט״ו באב', y, 5, 15));
    // Yom HaShoah: 27 Nisan, moved if it would touch Shabbat
    var sh = toDay(y, 1, 27), sw = weekday(sh); if (sw === 5) sh -= 1; else if (sw === 0) sh += 1; var shh = fromDay(sh);
    out.push({ name: 'יום השואה', y: y, m: shh.m, d: shh.d, d2: shh.d, type: 'holiday', start: sh, end: sh });
    out.sort(function (a, b) { return a.start - b.start; });
    out.forEach(function (h) { h.desc = DESC[h.name] || ''; });
    return out;
  }
  function holidayOn(day) {
    var h = fromDay(day);
    var hy = (h.m >= 7) ? h.y : h.y; // Nisan..Elul share the year number with the preceding Tishrei
    var list = holidaysOfYear(hy);
    for (var i = 0; i < list.length; i++) if (day >= list[i].start && day <= list[i].end) {
      var x = list[i], idx = day - x.start + 1, len = x.end - x.start + 1;
      var label = x.name;
      if (x.name === 'חנוכה') label = 'חנוכה · נר ' + numeral(idx, false);
      else if (len > 1 && x.name === 'סוכות' ) label = 'סוכות' + (idx > 1 ? ' · חוה״מ' : '');
      else if (x.name === 'פסח') label = idx === 1 ? 'פסח · ליל הסדר בערב' : (idx === 7 ? 'שביעי של פסח' : 'פסח · חוה״מ');
      return { name: label, base: x.name, type: x.type, desc: x.desc, day: idx, of: len };
    }
    return null;
  }
  // rosh chodesh
  function roshChodesh(day) {
    var h = fromDay(day);
    if (h.d === 1 && h.m !== 7) return monthName(h.y, h.m);
    if (h.d === 30) { var nx = fromDay(day + 1); return monthName(nx.y, nx.m); }
    return null;
  }

  function describe(day) {
    var h = fromDay(day);
    return { y: h.y, m: h.m, d: h.d, text: numeral(h.d) + ' ב' + monthName(h.y, h.m), year: yearName(h.y), full: numeral(h.d) + ' ב' + monthName(h.y, h.m) + ' ' + yearName(h.y) };
  }


  // the day in the Kabbalah: sefirah of the weekday, the Omer count, Rosh Chodesh, the holiday
  var SEF = ['חסד', 'גבורה', 'תפארת', 'נצח', 'הוד', 'יסוד', 'מלכות'];
  var SEF_MEANING = ['חסד: נתינה ואהבה בלי גבול', 'גבורה: דין, גבול ושליטה עצמית', 'תפארת: איזון ואמת, הרמוניה בין החסד לגבורה', 'נצח: התמדה וניצחון על המכשולים', 'הוד: הודיה, ענווה והכנעה', 'יסוד: חיבור, שותפות והעברת השפע', 'מלכות: קבלה, ביטוי ומעשה בעולם'];
  var WEEKDAYS = ['ראשון', 'שני', 'שלישי', 'רביעי', 'חמישי', 'שישי', 'שבת'];
  function kabbalahToday(day) {
    var h = fromDay(day), w = weekday(day), out = [];
    out.push({ b: 'יום ' + WEEKDAYS[w], t: 'ספירת ' + SEF_MEANING[w] });
    var omer = day - toDay(h.y, 1, 15);
    if (omer >= 1 && omer <= 49) out.push({ b: 'היום ' + omer + ' לעומר', t: SEF[(omer - 1) % 7] + ' שב' + SEF[Math.ceil(omer / 7) - 1] });
    var rc = roshChodesh(day);
    if (rc) out.push({ b: 'ראש חודש ' + rc, t: 'זמן התחדשות, יום של התחלה חדשה' });
    var hol = holidayOn(day);
    if (hol) out.push({ b: hol.name, t: hol.desc });
    return out;
  }

  root.HebCal = {kabbalahToday: kabbalahToday, SEF: SEF,  EPOCH_RD: EPOCH_RD, isLeap: isLeap, newYearDay: newYearDay, yearLength: yearLength, monthLength: monthLength, monthsOf: monthsOf, monthName: monthName,
    fromDay: fromDay, toDay: toDay, dayOf: dayOf, dateOf: dateOf, weekday: weekday, iso: iso, numeral: numeral, yearName: yearName,
    parshaFor: parshaFor, parshiotOfYear: parshiotOfYear, PARSHIOT: PARSHIOT, holidaysOfYear: holidaysOfYear, holidayOn: holidayOn, roshChodesh: roshChodesh, describe: describe };
  if (typeof module !== 'undefined' && module.exports) module.exports = root.HebCal;
})(typeof window !== 'undefined' ? window : globalThis);
