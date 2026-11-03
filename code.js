/* Design System Checker – UI Audit | Design OS
 * Main-thread code, V1. Plain JavaScript, so there is no build step.
 *
 * What it does
 *   1. Automatically scans only selected frames and sections:
 *      - color:      solid fills/strokes not bound to a color variable
 *      - typography: fonts outside your brand list, text with no text style
 *      - spacing:    padding, gaps and measurable non-auto-layout insets off the allowed scale
 *   2. Suggests the nearest variable / text style / allowed spacing value.
 *   3. Applies an individual suggested fix.
 *   4. Marks flagged layers on the canvas (Dev Mode annotations, with
 *      outlined overlay boxes as a fallback) and clears them again.
 *
 * Everything runs locally. No network, no AI calls.
 */
'use strict';

var NS = 'designos_handoffcheck';
var MARK_PREFIX = 'Design OS: ';
var OVERLAY_NAME = 'Design OS marks';
var CATEGORY_LABEL = 'Design OS';
var MAX_NODES = 6000;          // scan cap per run
var MAX_ISSUES = 1500;         // issues sent to the UI
var MAX_PALETTE_IMPORTS = 600; // library color variables read per run
var PALETTE_TTL = 60000;       // ms the color palette is cached
var COLOR_CLOSE = 6;           // deltaE at or below: a token exists, it is just not bound
var EPS = 0.01;

var ANNOTATABLE = {
  COMPONENT: 1, COMPONENT_SET: 1, ELLIPSE: 1, FRAME: 1, INSTANCE: 1, LINE: 1,
  POLYGON: 1, RECTANGLE: 1, STAR: 1, TEXT: 1, VECTOR: 1
};

var DEFAULT_SCALE = [4, 8, 12, 16, 20, 24];
var settings = { spacing: DEFAULT_SCALE.slice(), fonts: [] };
var lastIssues = new Map();    // issue key -> { issue, ctx }
var markedKeys = new Set();
var runId = 0;
var queue = Promise.resolve();
var palette = null;
var paletteAt = 0;
var collectionCache = new Map();
var selectedRootIds = [];     // user-selected frame/section roots; finding clicks do not change them
var ignoreNextSelection = false;
var selectionTimer = null;
var markPage = null;

figma.showUI(__html__, { width: 340, height: 500 });

/* ------------------------------------------------------------------ */
/* Small helpers                                                       */
/* ------------------------------------------------------------------ */

function post(msg) { figma.ui.postMessage(msg); }
function pause() { return new Promise(function (r) { setTimeout(r, 0); }); }
function plural(n, w) { return n + ' ' + w + (n === 1 ? '' : 's'); }

function hex(c) {
  return '#' + [c.r, c.g, c.b].map(function (v) {
    var h = Math.round(v * 255).toString(16);
    return h.length < 2 ? '0' + h : h;
  }).join('').toUpperCase();
}

function toLab(c) {
  function lin(v) { return v <= 0.04045 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }
  var r = lin(c.r), g = lin(c.g), b = lin(c.b);
  var x = (0.4124564 * r + 0.3575761 * g + 0.1804375 * b) / 0.95047;
  var y = (0.2126729 * r + 0.7151522 * g + 0.0721750 * b);
  var z = (0.0193339 * r + 0.1191920 * g + 0.9503041 * b) / 1.08883;
  function f(t) { return t > 0.008856 ? Math.cbrt(t) : 7.787 * t + 16 / 116; }
  var fx = f(x), fy = f(y), fz = f(z);
  return { L: 116 * fy - 16, a: 500 * (fx - fy), b: 200 * (fy - fz) };
}

function deltaE(p, q) {
  var dl = p.L - q.L, da = p.a - q.a, db = p.b - q.b;
  return Math.sqrt(dl * dl + da * da + db * db);
}

function cleanSpacing(list) {
  var values = Array.isArray(list) ? list : String(list == null ? '' : list).split(',');
  var numbers = values.map(function (v) { return Number(String(v).trim()); })
    .filter(function (n) { return Number.isFinite(n) && n > 0 && n <= 10000; });
  var sorted = Array.from(new Set(numbers)).sort(function (a, b) { return a - b; });
  return sorted.length ? sorted.slice(0, 50) : DEFAULT_SCALE.slice();
}

function cleanFonts(list) {
  var out = [];
  (Array.isArray(list) ? list : []).forEach(function (f) {
    var t = String(f || '').trim();
    if (t && out.indexOf(t) < 0) out.push(t);
  });
  return out.slice(0, 30);
}

function rootsOf(selection) {
  var ids = new Set(selection.map(function (n) { return n.id; }));
  return selection.filter(function (n) {
    var p = n.parent;
    while (p && p.type !== 'PAGE' && p.type !== 'DOCUMENT') {
      if (ids.has(p.id)) return false;                                   // parent is selected too
      if (p.type === 'INSTANCE' || p.type === 'COMPONENT' || p.type === 'COMPONENT_SET') return false; // library internals
      p = p.parent;
    }
    return true;
  });
}

/* ------------------------------------------------------------------ */
/* Persistent settings and ignore list                                 */
/* ------------------------------------------------------------------ */

async function loadSettings() {
  try {
    var s = await figma.clientStorage.getAsync('settings');
    if (s && typeof s === 'object') {
      settings.spacing = cleanSpacing(s.spacing || (s.grid === 8 ? [8,16,24,32] : DEFAULT_SCALE));
      settings.fonts = cleanFonts(s.fonts);
    }
  } catch (e) { /* defaults */ }
}

function saveSettings() {
  try { figma.clientStorage.setAsync('settings', settings); } catch (e) { /* ignore */ }
}

/* ------------------------------------------------------------------ */
/* Color palette: local variables plus enabled library variables       */
/* ------------------------------------------------------------------ */

async function collectionOf(variable) {
  var id = variable.variableCollectionId;
  if (collectionCache.has(id)) return collectionCache.get(id);
  var c = null;
  try { c = await figma.variables.getVariableCollectionByIdAsync(id); } catch (e) { c = null; }
  collectionCache.set(id, c);
  return c;
}

async function resolveColor(variable, depth) {
  if (depth > 6) return null;
  var values = variable.valuesByMode || {};
  var col = await collectionOf(variable);
  var modeId = col && col.defaultModeId && (col.defaultModeId in values) ? col.defaultModeId : Object.keys(values)[0];
  var v = values[modeId];
  if (v == null) return null;
  if (typeof v === 'object' && v.type === 'VARIABLE_ALIAS') {
    var target = await figma.variables.getVariableByIdAsync(v.id);
    if (!target) return null;
    var inner = await resolveColor(target, depth + 1);
    return inner ? { rgb: inner.rgb, a: inner.a, alias: true } : null;
  }
  if (typeof v === 'object' && 'r' in v) {
    return { rgb: { r: v.r, g: v.g, b: v.b }, a: v.a == null ? 1 : v.a, alias: false };
  }
  return null;
}

async function buildPalette(force) {
  if (!force && palette && Date.now() - paletteAt < PALETTE_TTL) return palette;
  collectionCache = new Map();
  var entries = [];
  var seen = new Set();
  var notes = { library: 0, capped: false, libraryError: false };

  async function add(variable) {
    if (!variable || seen.has(variable.id)) return;
    seen.add(variable.id);
    var c = await resolveColor(variable, 0);
    if (!c || c.a < 1) return; // opaque colors only: a bound paint keeps its own opacity
    entries.push({ id: variable.id, name: variable.name, rgb: c.rgb, lab: toLab(c.rgb), alias: c.alias });
  }

  try {
    var locals = await figma.variables.getLocalVariablesAsync('COLOR');
    for (var i = 0; i < locals.length; i++) await add(locals[i]);
  } catch (e) { /* no variables API access */ }

  try {
    var cols = await figma.teamLibrary.getAvailableLibraryVariableCollectionsAsync();
    var imported = 0;
    for (var c = 0; c < cols.length && !notes.capped; c++) {
      var libVars = await figma.teamLibrary.getVariablesInLibraryCollectionAsync(cols[c].key);
      var colorVars = libVars.filter(function (v) { return v.resolvedType === 'COLOR'; });
      for (var j = 0; j < colorVars.length; j += 25) {
        if (imported >= MAX_PALETTE_IMPORTS) { notes.capped = true; break; }
        var batch = colorVars.slice(j, j + 25);
        imported += batch.length;
        var vars = await Promise.all(batch.map(function (lv) {
          return figma.variables.importVariableByKeyAsync(lv.key).catch(function () { return null; });
        }));
        for (var k = 0; k < vars.length; k++) { await add(vars[k]); notes.library++; }
      }
    }
  } catch (e) { notes.libraryError = true; }

  palette = { entries: entries, notes: notes };
  paletteAt = Date.now();
  return palette;
}

function nearestColors(rgb, pal, limit) {
  var lab = toLab(rgb);
  return pal.entries.map(function (e) {
    var d = deltaE(lab, e.lab);
    return { e: e, d: d, rank: d - (e.alias ? 0.75 : 0) }; // prefer semantic (alias) tokens on near ties
  }).sort(function (a, b) { return a.rank - b.rank; })
    .slice(0, limit);
}

/* ------------------------------------------------------------------ */
/* Text style candidates                                               */
/* ------------------------------------------------------------------ */

var WEIGHTS = [['thin', 100], ['hairline', 100], ['extralight', 200], ['ultralight', 200], ['light', 300],
  ['regular', 400], ['normal', 400], ['book', 400], ['medium', 500], ['semibold', 600], ['demibold', 600],
  ['bold', 700], ['extrabold', 800], ['ultrabold', 800], ['black', 900], ['heavy', 900]]
  .sort(function (a, b) { return b[0].length - a[0].length; });

function weightOf(style) {
  var s = String(style || '').toLowerCase().replace(/[^a-z]/g, '').replace('italic', '').replace('oblique', '');
  for (var i = 0; i < WEIGHTS.length; i++) if (s.indexOf(WEIGHTS[i][0]) >= 0) return WEIGHTS[i][1];
  return 400;
}

function lineRatio(lh, size) {
  if (lh && lh.unit === 'PIXELS' && size) return lh.value / size;
  if (lh && lh.unit === 'PERCENT') return lh.value / 100;
  return 1.2;
}

async function collectTextStyles() {
  var map = new Map();
  try {
    var local = await figma.getLocalTextStylesAsync();
    local.forEach(function (s) { map.set(s.id, s); });
  } catch (e) { /* ignore */ }
  try {
    // Styles from libraries show up on text already used in this file.
    var ids = new Set();
    // Only inspect text inside the chosen roots: never query the whole page.
    var todo = selectedRootIds.slice();
    var visited = 0;
    while (todo.length && visited++ < MAX_NODES) {
      var n = await figma.getNodeByIdAsync(todo.pop());
      if (!n || n.removed) continue;
      if (n.type === 'TEXT') {
        var styleId = n.textStyleId;
        if (styleId && typeof styleId === 'string') ids.add(styleId);
      }
      if ('children' in n && n.type !== 'INSTANCE' && n.type !== 'COMPONENT' && n.type !== 'COMPONENT_SET') {
        n.children.forEach(function (child) { todo.push(child.id); });
      }
    }
    var list = Array.from(ids);
    for (var i = 0; i < list.length; i++) {
      if (map.has(list[i])) continue;
      var st = await figma.getStyleByIdAsync(list[i]);
      if (st && st.type === 'TEXT') map.set(st.id, st);
    }
  } catch (e) { /* ignore */ }
  return Array.from(map.values());
}

function matchStyles(spec, styles) {
  var out = [];
  styles.forEach(function (st) {
    var sizeDiff = Math.abs(spec.size - st.fontSize);
    if (sizeDiff > 4) return;
    var sizeS = Math.max(0, 1 - sizeDiff / 6);
    var weightS = Math.max(0, 1 - Math.abs(weightOf(spec.style) - weightOf(st.fontName.style)) / 300);
    var lhS = 1 - Math.min(1, Math.abs(lineRatio(spec.lh, spec.size) - lineRatio(st.lineHeight, st.fontSize)) / 0.5);
    var famS = spec.family === st.fontName.family ? 1 : 0;
    var score = sizeS * 0.5 + weightS * 0.3 + lhS * 0.1 + famS * 0.1;
    if (score >= 0.6) out.push({ id: 'style:' + st.id, styleId: st.id, name: st.name, score: Math.min(0.99, score) });
  });
  return out.sort(function (a, b) { return b.score - a.score; }).slice(0, 3);
}

/* ------------------------------------------------------------------ */
/* Checks                                                              */
/* ------------------------------------------------------------------ */

function makeCollector() { return { issues: [] }; }

function addIssue(col, o) {
  var key = [o.check, o.node.id, o.prop, o.detail].join('|');
  var issue = {
    key: key, check: o.check, severity: o.severity, message: o.message,
    layer: o.node.name, frame: o.frame, nodeId: o.node.id, reason: o.reason || o.message
  };
  if (o.fix) issue.fix = { kind: o.fix.kind, options: o.fix.options.map(publicOption), similar: 1 };
  col.issues.push({ issue: issue, ctx: { check: o.check, nodeId: o.node.id, groupKey: o.groupKey || key, options: o.fix ? o.fix.options : [], data: o.data || {} } });
}

function publicOption(o) { return { id: o.id, name: o.name, score: o.score }; }

function checkColor(col, node, frame, pal) {
  if (node.type === 'SECTION') return;
  ['fills', 'strokes'].forEach(function (prop) {
    if (!(prop in node)) return;
    if (prop === 'strokes' && (!node.strokes || node.strokes === figma.mixed || !node.strokes.length || node.strokeWeight === 0)) return;
    var paints = node[prop];
    var entries = [];
    if (paints === figma.mixed) {
      if (node.type !== 'TEXT' || prop !== 'fills') return;
      try {
        node.getStyledTextSegments(['fills', 'fontName']).forEach(function (seg) {
          if (!Array.isArray(seg.fills)) return;
          seg.fills.forEach(function (paint, index) {
            entries.push({ paint: paint, index: index, start: seg.start, end: seg.end, font: seg.fontName });
          });
        });
      } catch (e) { return; }
    } else if (Array.isArray(paints)) {
      paints.forEach(function (paint, index) { entries.push({ paint: paint, index: index }); });
    }
    var seen = new Set();
    entries.forEach(function (entry) {
      var paint = entry.paint;
      if (!paint || paint.type !== 'SOLID' || paint.visible === false || paint.opacity === 0 ||
          paint.boundVariables && paint.boundVariables.color) return;
      var h = hex(paint.color);
      var entryKey = prop + '|' + entry.index + '|' + h + '|' + (entry.start || 0) + '|' + (entry.end || 0);
      if (seen.has(entryKey)) return;
      seen.add(entryKey);
      var near = nearestColors(paint.color, pal, 3);
      var severity = !pal.entries.length ? 'warn' : near.length && near[0].d <= COLOR_CLOSE ? 'warn' : 'error';
      var options = near.map(function (hit) {
        return { id: 'var:' + hit.e.id, variableId: hit.e.id, name: hit.e.name,
          score: Math.max(0.05, Math.min(0.99, 1 - hit.d / 80)) };
      });
      var label = prop === 'fills' ? 'Fill' : 'Stroke';
      addIssue(col, {
        check: 'color', severity: severity, node: node, frame: frame,
        prop: prop + entry.index + '@' + (entry.start || 0), detail: h,
        message: label + ' ' + h + ' is not bound to a variable',
        reason: 'This ' + label.toLowerCase() + ' uses a hard-coded color instead of a design-system color variable.',
        fix: { kind: 'token', options: options },
        data: { prop: prop, paintIndex: entry.index, hex: h,
          start: entry.start, end: entry.end, font: entry.font }
      });
    });
  });
}

function checkTypography(col, node, frame, ctx) {
  if (node.type !== 'TEXT' || !node.characters) return;
  var segs;
  try { segs = node.getStyledTextSegments(['fontName', 'fontSize', 'textStyleId', 'lineHeight']); } catch (e) { return; }
  if (!segs.length) return;
  var families = Array.from(new Set(segs.filter(function (seg) { return seg.fontName && seg.fontName.family; })
    .map(function (seg) { return seg.fontName.family; })));
  var off = ctx.brand.size ? families.filter(function (name) { return !ctx.brand.has(name.toLowerCase()); }) : [];
  var unstyled = segs.filter(function (seg) { return !seg.textStyleId; });
  var first = unstyled[0] || segs[0];
  var uniform = segs.length === 1 && !!first.fontName;
  var spec = first.fontName ? { family: first.fontName.family, style: first.fontName.style, size: first.fontSize, lh: first.lineHeight } : null;
  var options = uniform && spec ? matchStyles(spec, ctx.styles) : [];
  var group = spec ? 'type|' + spec.family + '|' + spec.style + '|' + spec.size : 'type|' + node.id;
  if (off.length) {
    addIssue(col, {
      check: 'typography', severity: 'error', node: node, frame: frame, prop: 'font', detail: off.join(','),
      message: 'Font "' + off.join('", "') + '" is outside Brand fonts',
      reason: 'The text uses ' + off.join(', ') + ', which is not in the allowed Brand fonts list.',
      fix: { kind: 'style', options: options }, groupKey: group, data: {}
    });
  }
  if (unstyled.length) {
    addIssue(col, {
      check: 'typography', severity: 'warn', node: node, frame: frame, prop: 'style',
      detail: spec ? spec.family + '|' + spec.style + '|' + spec.size : 'unstyled',
      message: 'Text has no text style applied',
      reason: 'One or more text ranges are not linked to a reusable design-system text style.',
      fix: { kind: 'style', options: options }, groupKey: group, data: {}
    });
  }
}

function isOffScale(v) {
  return typeof v === 'number' && Number.isFinite(v) && v > EPS &&
    !settings.spacing.some(function (allowed) { return Math.abs(v - allowed) <= EPS; });
}
function nearestValues(v) {
  return settings.spacing.slice().sort(function (a, b) {
    return Math.abs(a - v) - Math.abs(b - v) || a - b;
  }).slice(0, 3).map(function (value, i) {
    return { id: 'val:' + value, name: value + 'px', value: value, score: i === 0 ? 0.95 : 0.8 };
  });
}
function nearestValue(v) { return nearestValues(v)[0].value; }
function spacingReason(v, label) {
  return label + ' is ' + v + 'px, which is not in the allowed spacing scale (' + settings.spacing.join(', ') + ').';
}

function checkSpacing(col, node, frame) {
  var bv = node.boundVariables || {};
  if ('layoutMode' in node && (node.layoutMode === 'HORIZONTAL' || node.layoutMode === 'VERTICAL')) {
    function gap(prop, label) {
      var v = node[prop];
      if (bv[prop] || !isOffScale(v)) return;
      addIssue(col, {
        check: 'spacing', severity: 'warn', node: node, frame: frame, prop: prop, detail: String(v),
        message: label + ' ' + v + 'px is off-scale', reason: spacingReason(v, label),
        fix: { kind: 'value', options: nearestValues(v) }, groupKey: 'spacing|' + prop + '|' + v,
        data: { prop: prop, value: v }
      });
    }
    if (node.primaryAxisAlignItems !== 'SPACE_BETWEEN') gap('itemSpacing', 'Gap');
    if (node.layoutWrap === 'WRAP' && node.counterAxisSpacing != null) gap('counterAxisSpacing', 'Row gap');
    var props = ['paddingTop', 'paddingRight', 'paddingBottom', 'paddingLeft'];
    var current = {}, snapped = {}, offAny = false;
    props.forEach(function (prop) {
      var v = node[prop]; current[prop] = v;
      snapped[prop] = !bv[prop] && isOffScale(v) ? nearestValue(v) : v;
      if (snapped[prop] !== v) offAny = true;
    });
    if (offAny) {
      var label = props.map(function (p) { return current[p]; }).join(' / ');
      var changes = props.filter(function (p) { return current[p] !== snapped[p]; });
      addIssue(col, {
        check: 'spacing', severity: 'warn', node: node, frame: frame, prop: 'padding', detail: label,
        message: 'Padding ' + label + 'px contains off-scale values',
        reason: changes.map(function (p) { return spacingReason(current[p], p.replace('padding', 'Padding ')); }).join(' '),
        fix: { kind: 'value', options: [{ id: 'pad:' + props.map(function (p) { return snapped[p]; }).join(':'),
          name: props.map(function (p) { return snapped[p]; }).join(' / ') + 'px', values: snapped, score: 0.95 }] },
        data: { current: current }
      });
    }
  }
  // Figma has no native margin property. For manually positioned children of
  // non-auto-layout frames, the inset to the parent edge is a measurable margin.
  var parent = node.parent;
  if (!parent || parent.type !== 'FRAME' || parent.layoutMode !== 'NONE' ||
      node.type === 'SECTION' || node.type === 'SLICE' || node.type === 'GROUP' ||
      node.rotation !== 0 || !('x' in node) || !('width' in node)) return;
  var inset = [
    { edge: 'Left', axis: 'x', value: node.x },
    { edge: 'Top', axis: 'y', value: node.y },
    { edge: 'Right', axis: 'x', value: parent.width - node.x - node.width },
    { edge: 'Bottom', axis: 'y', value: parent.height - node.y - node.height }
  ];
  inset.forEach(function (side) {
    if (side.value > 256 || !isOffScale(side.value)) return; // exclude large intentional whitespace
    addIssue(col, {
      check: 'spacing', severity: 'warn', node: node, frame: frame,
      prop: 'margin' + side.edge, detail: String(side.value),
      message: side.edge + ' margin ' + Math.round(side.value * 100) / 100 + 'px is off-scale',
      reason: spacingReason(Math.round(side.value * 100) / 100, side.edge + ' inset to ' + parent.name),
      fix: { kind: 'value', options: nearestValues(side.value) },
      data: { prop: 'margin', edge: side.edge, axis: side.axis, value: side.value,
        originalPosition: node[side.axis], parentId: parent.id }
    });
  });
}

/* ------------------------------------------------------------------ */
/* Scan                                                                */
/* ------------------------------------------------------------------ */

async function resolveRoots() {
  var nodes = [];
  for (var i = 0; i < selectedRootIds.length; i++) {
    var n = await figma.getNodeByIdAsync(selectedRootIds[i]);
    if (n && !n.removed && (n.type === 'FRAME' || n.type === 'SECTION')) nodes.push(n);
  }
  return rootsOf(nodes);
}

function isOverlay(node) {
  return node.name === OVERLAY_NAME && node.getPluginData && node.getPluginData(NS) === 'overlay';
}

async function runScan() {
  var id = ++runId;
  var roots = await resolveRoots();
  roots = roots.filter(function (n) { return n.visible !== false && !isOverlay(n); });

  if (!roots.length) { post({ type: 'empty-selection' }); return; }
  post({ type: 'progress', text: 'Reading design-system variables…' });
  var pal = await buildPalette(false);
  var styles = await collectTextStyles();
  if (id !== runId) return;

  var brand = new Set(settings.fonts.map(function (f) { return f.toLowerCase(); }));
  var fontsSource = settings.fonts.length ? 'manual' : 'none';


  var col = makeCollector();
  var ctx = { brand: brand, styles: styles };
  var stack = roots.slice().reverse().map(function (n) { return { node: n, frame: n.name }; });
  var scanned = 0, skipped = 0, truncated = false;

  while (stack.length) {
    if (id !== runId) return; // a newer run (or cancel) replaced this one
    var item = stack.pop();
    var node = item.node;
    if (node.removed || node.visible === false || isOverlay(node)) continue;
    var t = node.type;
    if (t === 'INSTANCE' || t === 'COMPONENT' || t === 'COMPONENT_SET') { skipped++; continue; } // library internals are not ours to judge
    if (++scanned > MAX_NODES) { truncated = true; break; }

    try {
      checkColor(col, node, item.frame, pal);
      checkTypography(col, node, item.frame, ctx);
      checkSpacing(col, node, item.frame);
    } catch (e) { /* one odd layer must not stop the scan */ }

    if ('children' in node) {
      for (var i = node.children.length - 1; i >= 0; i--) stack.push({ node: node.children[i], frame: item.frame });
    }
    if (scanned % 250 === 0) {
      post({ type: 'progress', text: 'Detecting… ' + scanned + ' layers' });
      await pause();
    }
  }
  if (id !== runId) return;

  var order = { color: 0, typography: 1, spacing: 2 };
  col.issues.sort(function (a, b) {
    return order[a.issue.check] - order[b.issue.check] ||
      (a.issue.severity === b.issue.severity ? 0 : a.issue.severity === 'error' ? -1 : 1) ||
      (a.issue.frame + a.issue.layer).localeCompare(b.issue.frame + b.issue.layer);
  });
  var shown = col.issues.slice(0, MAX_ISSUES);

  lastIssues = new Map();
  shown.forEach(function (r) { lastIssues.set(r.issue.key, r); });
  markedKeys = new Set();

  var counts = { color: 0, typography: 0, spacing: 0 };
  var errors = 0, warns = 0;
  shown.forEach(function (r) {
    counts[r.issue.check]++;
    if (r.issue.severity === 'error') errors++; else warns++;
  });

  var hints = [];
  if (skipped) hints.push('Skipped ' + skipped + (skipped === 1 ? ' instance or component' : ' instances and components') + ' because they come from your library.');
  if (truncated) hints.push('Scan capped at ' + MAX_NODES + ' layers, so narrow the selection.');
  if (col.issues.length > MAX_ISSUES) hints.push('Showing the first ' + MAX_ISSUES + ' issues.');
  if (!pal.entries.length && counts.color) hints.push('No color variables found, so color fixes are not available.');
  else if (pal.notes.capped) hints.push('Large library: only the first ' + MAX_PALETTE_IMPORTS + ' color variables were read.');
  if (fontsSource === 'none') hints.push('Add Brand fonts under Reference settings to check font families.');
  if (!styles.length && counts.typography) hints.push('No text styles found, so style suggestions are not available.');

  post({
    type: 'result', scope: 'selection', selectionNames: roots.map(function (n) { return n.name; }), issues: shown.map(function (r) { return r.issue; }), counts: counts,
    errors: errors, warns: warns, score: Math.max(0, 100 - errors * 5 - warns * 2),
    ready: errors === 0 && warns <= 3, scanned: scanned, skipped: skipped, truncated: truncated,
    hints: hints, fontsSource: fontsSource
  });
}

/* ------------------------------------------------------------------ */
/* Apply fixes                                                         */
/* ------------------------------------------------------------------ */

async function applyOne(rec, opt) {
  var ctx = rec.ctx;
  var node = await figma.getNodeByIdAsync(ctx.nodeId);
  if (!node || node.removed) return false;

  if (ctx.check === 'color') {
    var variable = await figma.variables.getVariableByIdAsync(opt.variableId);
    if (!variable) return false;
    var paints = ctx.data.start != null && node.type === 'TEXT'
      ? node.getRangeFills(ctx.data.start, ctx.data.end) : node[ctx.data.prop];
    if (!Array.isArray(paints)) return false;
    var p = paints[ctx.data.paintIndex];
    if (!p || p.type !== 'SOLID' || hex(p.color) !== ctx.data.hex || (p.boundVariables && p.boundVariables.color)) return false; // changed since the scan
    var next = paints.slice();
    next[ctx.data.paintIndex] = figma.variables.setBoundVariableForPaint(p, 'color', variable);
    if (ctx.data.start != null && node.type === 'TEXT') {
      if (ctx.data.font) await figma.loadFontAsync(ctx.data.font);
      node.setRangeFills(ctx.data.start, ctx.data.end, next);
    } else node[ctx.data.prop] = next;
    return true;
  }

  if (ctx.check === 'typography') {
    if (node.type !== 'TEXT') return false;
    var style = await figma.getStyleByIdAsync(opt.styleId);
    if (!style || node.textStyleId === style.id) return false;
    var segs = node.getStyledTextSegments(['fontName', 'textStyleId']);
    if (segs.length !== 1) return false; // mixed style ranges need manual review
    await figma.loadFontAsync(segs[0].fontName);
    await figma.loadFontAsync(style.fontName);
    await node.setTextStyleIdAsync(style.id);
    return true;
  }

  if (ctx.check === 'spacing') {
    if (ctx.data.prop === 'margin') {
      var parent = await figma.getNodeByIdAsync(ctx.data.parentId);
      if (!parent || parent.removed || node.parent !== parent || node[ctx.data.axis] !== ctx.data.originalPosition || !Number.isFinite(opt.value)) return false;
      var next = ctx.data.edge === 'Left' || ctx.data.edge === 'Top'
        ? opt.value : node[ctx.data.axis] + ctx.data.value - opt.value;
      node[ctx.data.axis] = next;
      return true;
    }
    if (node.layoutMode !== 'HORIZONTAL' && node.layoutMode !== 'VERTICAL') return false;
    if (opt.values) {
      var cur = ctx.data.current;
      var same = Object.keys(cur).every(function (k) { return node[k] === cur[k]; });
      if (!same) return false;
      Object.keys(opt.values).forEach(function (k) { node[k] = opt.values[k]; });
      return true;
    }
    if (node[ctx.data.prop] !== ctx.data.value) return false;
    node[ctx.data.prop] = opt.value;
    return true;
  }
  return false;
}

async function applyFix(msg) {
  var rec = lastIssues.get(msg.key);
  if (!rec) { post({ type: 'applied', ok: false, key: msg.key, message: 'That result is out of date. Detect again.' }); return; }

  var targets = [rec];

  var done = [], skipped = 0, name = '';
  for (var i = 0; i < targets.length; i++) {
    var r = targets[i];
    var opt = r.ctx.options.filter(function (o) { return o.id === msg.optionId; })[0];
    if (!opt) { skipped++; continue; }
    try {
      if (await applyOne(r, opt)) { done.push(r.issue.key); name = opt.name; } else skipped++;
    } catch (e) { skipped++; }
  }

  if (!done.length) {
    post({ type: 'applied', ok: false, key: msg.key, message: 'Couldn’t apply that. The layer may have changed, so detect again.' });
    return;
  }
  done.forEach(function (k) { lastIssues.delete(k); markedKeys.delete(k); });
  await clearMarks();
  markedKeys = new Set();
  post({ type: 'cleared' });

  var text = done.length > 1 ? 'Fixed ' + plural(done.length, 'layer') + ' with ' + name + '.' : 'Applied ' + name + '.';
  if (skipped) text += ' ' + skipped + ' skipped because they changed.';
  post({ type: 'applied', ok: true, key: msg.key, keys: done, message: text });
}

/* ------------------------------------------------------------------ */
/* Marks on the canvas                                                 */
/* ------------------------------------------------------------------ */

function isMine(a) {
  var label = String(a.label || a.labelMarkdown || '');
  return label.indexOf(MARK_PREFIX) === 0 || label.indexOf('AI slop: ') === 0;
}

async function ensureCategory() {
  if (!figma.annotations) return null;
  try {
    var cats = await figma.annotations.getAnnotationCategoriesAsync();
    var c = cats.filter(function (x) { return x.label === CATEGORY_LABEL; })[0];
    if (!c) c = await figma.annotations.addAnnotationCategoryAsync({ label: CATEGORY_LABEL, color: 'red' });
    return c.id;
  } catch (e) { return null; }
}

function pinned(issue) {
  if (issue.check === 'color') return [{ type: issue.message.indexOf('Stroke') === 0 ? 'strokes' : 'fills' }];
  if (issue.check === 'typography') return [{ type: 'fontFamily' }, { type: 'fontSize' }];
  if (issue.check === 'spacing') return [{ type: issue.message.indexOf('Padding') === 0 ? 'padding' : 'itemSpacing' }];
  return [];
}

function annotationFor(rec, categoryId, withExtras) {
  var best = rec.issue.fix && rec.issue.fix.options && rec.issue.fix.options[0];
  var a = { label: MARK_PREFIX + rec.issue.message + '\nReason: ' + rec.issue.reason + (best ? '\nSuggested: ' + best.name : '') };
  if (withExtras) {
    if (categoryId) a.categoryId = categoryId;
    var props = pinned(rec.issue);
    if (props.length) a.properties = props;
  }
  return a;
}

async function loadMarkRegistry() {
  try { return JSON.parse(figma.currentPage.getPluginData(NS + '_marks') || '[]'); } catch (e) { return []; }
}

async function clearMarks() {
  var page = markPage && !markPage.removed ? markPage : figma.currentPage;
  page.findChildren(function (n) { return isOverlay(n); }).forEach(function (n) { n.remove(); });
  var ids = [];
  try { ids = JSON.parse(page.getPluginData(NS + '_marks') || '[]'); } catch (e) { ids = []; }
  for (var i = 0; i < ids.length; i++) {
    var n = await figma.getNodeByIdAsync(ids[i]);
    if (n && !n.removed && 'annotations' in n) {
      try { n.annotations = n.annotations.filter(function (a) { return !isMine(a); }); } catch (e) { /* ignore */ }
    }
  }
  page.setPluginData(NS + '_marks', '[]');
  markPage = null;
}

async function drawOverlay(items) {
  var red = { r: 0.949, g: 0.282, b: 0.133 };
  var box = figma.createFrame();
  box.name = OVERLAY_NAME;
  box.setPluginData(NS, 'overlay');
  box.fills = [];
  box.clipsContent = false;
  box.resize(1, 1);
  box.x = 0;
  box.y = 0;
  figma.currentPage.appendChild(box);

  var fontOk = false;
  try { await figma.loadFontAsync({ family: 'Inter', style: 'Regular' }); fontOk = true; } catch (e) { fontOk = false; }

  var n = 0;
  for (var i = 0; i < items.length; i++) {
    var node = items[i].node;
    var bb = node.absoluteBoundingBox;
    if (!bb) continue;
    n++;
    var r = figma.createRectangle();
    r.name = 'mark:' + node.id + ' — ' + items[i].reasons.join(' | ').slice(0, 220);
    r.setPluginData(NS + '_reason', items[i].reasons.join(' | '));
    r.fills = [];
    r.strokes = [{ type: 'SOLID', color: red }];
    r.strokeWeight = 2;
    r.strokeAlign = 'OUTSIDE';
    box.appendChild(r);
    r.resize(Math.max(bb.width, 1), Math.max(bb.height, 1));
    r.x = bb.x;
    r.y = bb.y;
    if (fontOk) {
      var reason = items[i].reasons.join(' • ').slice(0, 240);
      var label = figma.createText();
      label.name = 'Reason: ' + reason;
      box.appendChild(label);
      label.fontName = { family: 'Inter', style: 'Regular' };
      label.fontSize = 10;
      label.characters = reason;
      label.textAutoResize = 'HEIGHT';
      label.resize(Math.min(280, Math.max(160, bb.width)), 20);
      label.fills = [{ type: 'SOLID', color: red }];
      label.x = bb.x;
      label.y = bb.y - Math.max(18, label.height + 4);
    }
  }
  box.locked = true;
  return n;
}

async function markIssues(keys) {
  await clearMarks();
  markPage = figma.currentPage;
  var byNode = new Map();
  keys.forEach(function (k) {
    var rec = lastIssues.get(k);
    if (!rec) return;
    if (!byNode.has(rec.issue.nodeId)) byNode.set(rec.issue.nodeId, []);
    byNode.get(rec.issue.nodeId).push(rec);
  });

  var categoryId = await ensureCategory();
  var annotated = [], overlay = [], marked = 0;
  var entries = Array.from(byNode.entries());

  for (var i = 0; i < entries.length; i++) {
    var node = await figma.getNodeByIdAsync(entries[i][0]);
    var recs = entries[i][1];
    if (!node || node.removed) continue;
    var done = false;
    if (ANNOTATABLE[node.type] && 'annotations' in node) {
      var shown = recs; // Every finding retains its own reason.
      var keep = (node.annotations || []).filter(function (a) { return !isMine(a); });
      for (var attempt = 0; attempt < 2 && !done; attempt++) {
        try {
          var mine = shown.map(function (r) { return annotationFor(r, categoryId, attempt === 0); });
          node.annotations = keep.concat(mine);
          done = true;
        } catch (e) { done = false; }
      }
    }
    if (done) { annotated.push(node.id); marked++; } else overlay.push({ node: node, reasons: recs.map(function (r) { return r.issue.reason; }) });
    recs.forEach(function (r) { markedKeys.add(r.issue.key); });
  }

  var drawn = overlay.length ? await drawOverlay(overlay) : 0;
  figma.currentPage.setPluginData(NS + '_marks', JSON.stringify(annotated));
  return { count: marked + drawn, overlay: drawn };
}

async function refreshMarks() {
  if (!markedKeys.size) return;
  var keys = Array.from(markedKeys).filter(function (k) { return lastIssues.has(k); });
  await clearMarks();
  markedKeys = new Set();
  if (keys.length) await markIssues(keys);
}

/* ------------------------------------------------------------------ */
/* Messages from the UI                                                */
/* ------------------------------------------------------------------ */

function sendInit() {
  post({ type: 'init', settings: settings });
}
function validSelection() {
  var picked = figma.currentPage.selection.filter(function (n) {
    return n.type === 'FRAME' || n.type === 'SECTION';
  });
  return rootsOf(picked).map(function (n) { return n.id; });
}
function onUserSelection() {
  if (ignoreNextSelection) { ignoreNextSelection = false; return; }
  var ids = validSelection();
  var unchanged = ids.length === selectedRootIds.length && ids.every(function (id, i) { return id === selectedRootIds[i]; });
  if (unchanged) return;
  selectedRootIds = ids;
  ++runId; // invalidate any old scan
  clearTimeout(selectionTimer);
  lastIssues = new Map();
  markedKeys = new Set();
  post({ type: 'selection-reset' });
  queue = queue.then(function () { return clearMarks(); }).catch(function (e) { console.error(e); });
  if (!ids.length) { post({ type: 'empty-selection' }); return; }
  selectionTimer = setTimeout(function () {
    queue = queue.then(function () { return runScan(); }).catch(function (err) {
      console.error(err); post({ type: 'error', message: String(err && err.message || err) });
    });
  }, 120);
}
async function handle(msg) {
  switch (msg.type) {
    case 'ready':
      await loadSettings();
      sendInit();
      onUserSelection();
      break;
    case 'settings':
      if (msg.settings) {
        await clearMarks();
        markedKeys = new Set();
        post({ type: 'cleared' });
        settings.spacing = cleanSpacing(msg.settings.spacing);
        settings.fonts = cleanFonts(msg.settings.fonts);
        saveSettings();
        if (selectedRootIds.length) await runScan();
      }
      break;
    case 'select': {
      var n = await figma.getNodeByIdAsync(msg.id);
      if (n && !n.removed && n.type !== 'PAGE' && n.type !== 'DOCUMENT') {
        ignoreNextSelection = true;
        figma.currentPage.selection = [n];
        figma.viewport.scrollAndZoomIntoView([n]);
        // API event is asynchronous. Avoid suppressing subsequent user selections.
        setTimeout(function () { ignoreNextSelection = false; }, 120);
      } else post({ type: 'notice', message: 'That layer no longer exists.' });
      break;
    }
    case 'apply':
      await applyFix(msg);
      // Reread the same originally chosen frame/section after the edit.
      if (selectedRootIds.length) await runScan();
      break;
    case 'mark': {
      var keys = Array.isArray(msg.keys) ? msg.keys : [];
      var res = await markIssues(keys);
      post({ type: 'marked', count: res.count, overlay: res.overlay });
      break;
    }
    case 'clear-marks':
      await clearMarks();
      markedKeys = new Set();
      post({ type: 'cleared' });
      break;
  }
}
figma.ui.onmessage = function (msg) {
  if (!msg || !msg.type) return;
  if (msg.type === 'close') { figma.closePlugin(); return; }
  queue = queue.then(function () { return handle(msg); }).catch(function (err) {
    console.error(err);
    post({ type: 'error', message: String(err && err.message ? err.message : err) });
  });
};
figma.on('selectionchange', onUserSelection);
figma.on('currentpagechange', onUserSelection);
figma.on('close', function () {
  // Fallback outline boxes live in the user's file, so never leave them behind.
  try { figma.currentPage.findChildren(function (n) { return isOverlay(n); }).forEach(function (n) { n.remove(); }); } catch (e) { /* ignore */ }
});
