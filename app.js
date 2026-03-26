const gray2 = [0, 1, 3, 2];

const n = 4;
const total = 1 << n;

const appState = {
  outputs: new Array(total).fill("X"),
  exprMode: "SOP",
  varNames: ["A", "B", "C", "D"],
  lastError: "",
};

const $ = (sel) => document.querySelector(sel);

function popcount(x) {
  let c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
}

function bitIsSet(mask, i) {
  return ((mask >>> i) & 1) === 1;
}

function setBit(mask, i) {
  return mask | (1 << i);
}

function clearBit(mask, i) {
  return mask & ~(1 << i);
}

function maskToIndices(mask) {
  const res = [];
  let m = mask >>> 0;
  for (let i = 0; i < 32; i++) {
    if (m & 1) res.push(i);
    m = m >>> 1;
    if (!m) break;
  }
  return res;
}

function uniqueBy(arr, keyFn) {
  const map = new Map();
  for (const item of arr) map.set(keyFn(item), item);
  return [...map.values()];
}

function mintermCount() {
  return 1 << n;
}

function mintermToBits(m) {
  const bits = [];
  for (let i = n - 1; i >= 0; i--) bits.push((m >>> i) & 1);
  return bits;
}

function mintermToCellPos(m) {
  const A = (m >>> 3) & 1;
  const B = (m >>> 2) & 1;
  const C = (m >>> 1) & 1;
  const D = m & 1;
  const rowCode = (A << 1) | B;
  const colCode = (C << 1) | D;
  return { r: gray2.indexOf(rowCode), c: gray2.indexOf(colCode) };
}

function cellPosToMinterm(r, c) {
  const rowCode = gray2[r];
  const colCode = gray2[c];
  const A = (rowCode >>> 1) & 1;
  const B = rowCode & 1;
  const C = (colCode >>> 1) & 1;
  const D = colCode & 1;
  return (A << 3) | (B << 2) | (C << 1) | D;
}

function patternCoversMinterm(pattern, m) {
  const bits = mintermToBits(m);
  for (let i = 0; i < n; i++) {
    const p = pattern[i];
    if (p === "-") continue;
    if (Number(p) !== bits[i]) return false;
  }
  return true;
}

function patternFromMinterms(mintermMask) {
  const bitsByVar = new Array(n).fill(null).map(() => new Set());
  for (let m = 0; m < total; m++) {
    if (!bitIsSet(mintermMask, m)) continue;
    const bits = mintermToBits(m);
    for (let i = 0; i < n; i++) bitsByVar[i].add(bits[i]);
  }
  return bitsByVar
    .map((s) => {
      if (s.size === 1) return [...s][0] === 0 ? "0" : "1";
      return "-";
    })
    .join("");
}

function coverMaskFromPattern(pattern) {
  let mask = 0;
  for (let m = 0; m < total; m++) {
    if (patternCoversMinterm(pattern, m)) mask = setBit(mask, m);
  }
  return mask >>> 0;
}

function combinePossible(p, q) {
  let diff = 0;
  for (let i = 0; i < p.length; i++) {
    const a = p[i];
    const b = q[i];
    if (a === "-" || b === "-") {
      if (a !== b) return { ok: false };
      continue;
    }
    if (a !== b) diff++;
    if (diff > 1) return { ok: false };
  }
  return { ok: diff === 1 };
}

function combinePatterns(p, q) {
  let out = "";
  for (let i = 0; i < p.length; i++) {
    const a = p[i];
    const b = q[i];
    if (a === "-" && b === "-") out += "-";
    else if (a === b) out += a;
    else out += "-";
  }
  return out;
}

function literalCountFromPattern(pattern) {
  let c = 0;
  for (const ch of pattern) if (ch !== "-") c++;
  return c;
}

function implicantSortKey(pattern) {
  const lit = literalCountFromPattern(pattern);
  return `${lit.toString().padStart(2, "0")}:${pattern}`;
}

function qmSimplifySOP(onesMask, dcMask, forbiddenMask) {
  if (onesMask === 0) return { expression: "F = 0", terms: [], isConst: true, constValue: 0 };
  const initialIndices = [];
  for (let m = 0; m < total; m++) {
    const isInitial = bitIsSet(onesMask, m) || bitIsSet(dcMask, m);
    if (isInitial) initialIndices.push(m);
  }

  let current = initialIndices.map((m) => {
    const bits = mintermToBits(m);
    const pattern = bits.map((b) => (b === 0 ? "0" : "1")).join("");
    return { pattern, used: false };
  });
  current = uniqueBy(current, (x) => x.pattern);
  const primePatternSet = new Set();

  while (current.length > 0) {
    const groups = new Map();
    for (const imp of current) {
      let ones = 0;
      for (const ch of imp.pattern) if (ch === "1") ones++;
      if (!groups.has(ones)) groups.set(ones, []);
      groups.get(ones).push(imp);
    }

    const nextMap = new Map();
    let combinedSomething = false;
    const counts = [...groups.keys()].sort((a, b) => a - b);

    for (let i = 0; i < counts.length - 1; i++) {
      const c1 = counts[i];
      const c2 = counts[i + 1];
      if (c2 !== c1 + 1) continue;
      const list1 = groups.get(c1) || [];
      const list2 = groups.get(c2) || [];
      for (const a of list1) {
        for (const b of list2) {
          const comb = combinePossible(a.pattern, b.pattern);
          if (!comb.ok) continue;
          a.used = true;
          b.used = true;
          combinedSomething = true;
          const newPattern = combinePatterns(a.pattern, b.pattern);
          nextMap.set(newPattern, { pattern: newPattern, used: false });
        }
      }
    }

    for (const imp of current) if (!imp.used) primePatternSet.add(imp.pattern);
    current = [...nextMap.values()];
    if (!combinedSomething) break;
  }

  const primePatterns = [...primePatternSet];
  const validatedPrimes = [];

  for (const pattern of primePatterns) {
    const coverMask = coverMaskFromPattern(pattern);
    if ((coverMask & forbiddenMask) !== 0) continue;
    const coverOnesMask = coverMask & onesMask;
    if (coverOnesMask === 0) continue;
    validatedPrimes.push({
      pattern,
      coverMask: coverMask >>> 0,
      coverOnesMask: coverOnesMask >>> 0,
      literals: literalCountFromPattern(pattern),
    });
  }

  const onesIndices = maskToIndices(onesMask);
  const coverByPrime = onesIndices.map(() => []);
  for (let i = 0; i < validatedPrimes.length; i++) {
    const prime = validatedPrimes[i];
    for (let j = 0; j < onesIndices.length; j++) {
      const m = onesIndices[j];
      if (bitIsSet(prime.coverOnesMask, m)) coverByPrime[j].push(i);
    }
  }

  const essentialPrimeIdx = new Set();
  for (let j = 0; j < onesIndices.length; j++) if (coverByPrime[j].length === 1) essentialPrimeIdx.add(coverByPrime[j][0]);

  const essentialPrimes = [...essentialPrimeIdx].map((idx) => validatedPrimes[idx]);
  const essentialCoveredOnesMask = essentialPrimes.reduce((acc, p) => acc | p.coverOnesMask, 0) >>> 0;
  const remainingOnesMask = (onesMask & ~essentialCoveredOnesMask) >>> 0;

  const remainingPrimeIdx = validatedPrimes.map((p, idx) => idx).filter((idx) => !essentialPrimeIdx.has(idx));

  let best = null;

  if (remainingOnesMask === 0) {
    best = essentialPrimes;
  } else {
    let bestTermCount = Infinity;
    let bestLitSum = Infinity;
    let bestSubset = null;
    const rem = remainingPrimeIdx;
    const target = onesMask;

    function rec(pos, chosen, coverMask, litSum) {
      if (coverMask === (target >>> 0)) {
        const termCount = chosen.length + essentialPrimes.length;
        if (termCount < bestTermCount || (termCount === bestTermCount && litSum < bestLitSum)) {
          bestTermCount = termCount;
          bestLitSum = litSum;
          bestSubset = [...essentialPrimes, ...chosen];
        }
        return;
      }
      if (pos >= rem.length) return;
      const maxPossibleTerms = chosen.length + essentialPrimes.length + (rem.length - pos);
      if (maxPossibleTerms < bestTermCount) return;

      const idx = rem[pos];
      const p = validatedPrimes[idx];
      rec(pos + 1, [...chosen, p], (coverMask | p.coverOnesMask) >>> 0, litSum + p.literals);
      rec(pos + 1, chosen, coverMask, litSum);
    }

    const startCover = essentialCoveredOnesMask;
    const startLit = essentialPrimes.reduce((acc, p) => acc + p.literals, 0);
    rec(0, [], startCover, startLit);
    best = bestSubset || essentialPrimes;
  }

  if (!best || best.length === 0) return { expression: "F = 0", terms: [], isConst: true, constValue: 0 };
  if (best.some((t) => t.pattern.split("").every((ch) => ch === "-"))) return { expression: "F = 1", terms: best, isConst: true, constValue: 1 };

  return { mode: "SOP", terms: best };
}

function buildSOPExpression(terms, varNames) {
  if (!terms || terms.length === 0) return "F = 0";
  const ordered = [...terms].sort((a, b) => implicantSortKey(a.pattern).localeCompare(implicantSortKey(b.pattern)));
  const vars = varNames.slice(0, n);
  const termStr = (pattern) => {
    const parts = [];
    for (let i = 0; i < n; i++) {
      const ch = pattern[i];
      if (ch === "-") continue;
      const v = vars[i];
      if (ch === "1") parts.push(v);
      else parts.push(`${v}'`);
    }
    if (parts.length === 0) return "1";
    return parts.join("");
  };
  return `F = ${ordered.map((t) => termStr(t.pattern)).join(" + ")}`;
}

function buildPOSExpressionFromFprimeTerms(termsFprime, varNames) {
  if (!termsFprime || termsFprime.length === 0) return "F = 1";
  const vars = varNames.slice(0, n);
  const patternToSumLiteralList = (pattern) => {
    const lits = [];
    for (let i = 0; i < n; i++) {
      const ch = pattern[i];
      if (ch === "-") continue;
      const v = vars[i];
      if (ch === "1") lits.push(`${v}'`);
      else lits.push(`${v}`);
    }
    return lits;
  };
  const ordered = [...termsFprime].sort((a, b) => implicantSortKey(a.pattern).localeCompare(implicantSortKey(b.pattern)));
  const sumTerms = ordered.map((t) => {
    const lits = patternToSumLiteralList(t.pattern);
    if (lits.length === 0) return "0";
    if (lits.length === 1) return `(${lits[0]})`;
    return `(${lits.join(" + ")})`;
  });
  return `F = ${sumTerms.join("")}`;
}

function simplify(outputs, exprMode, varNames) {
  let onesMask = 0;
  let dcMask = 0;
  let zerosMask = 0;
  for (let m = 0; m < total; m++) {
    const v = outputs[m];
    if (v === 1) onesMask = setBit(onesMask, m);
    else if (v === "X") dcMask = setBit(dcMask, m);
    else zerosMask = setBit(zerosMask, m);
  }

  if (exprMode === "SOP") {
    const forbiddenMask = zerosMask;
    const res = qmSimplifySOP(onesMask, dcMask, forbiddenMask);
    if (res.isConst) return { expression: res.expression, terms: res.terms || [] };
    return { expression: buildSOPExpression(res.terms, varNames), terms: res.terms };
  }

  const onesPrimeMask = zerosMask;
  const forbiddenPrimeMask = onesMask;
  const resFprime = qmSimplifySOP(onesPrimeMask, dcMask, forbiddenPrimeMask);
  if (resFprime.isConst) {
    if (resFprime.constValue === 0) return { expression: "F = 1", terms: [] };
    return { expression: "F = 0", terms: resFprime.terms || [] };
  }
  return { expression: buildPOSExpressionFromFprimeTerms(resFprime.terms, varNames), terms: resFprime.terms };
}

function parseIndexList(text) {
  if (!text) return [];
  const trimmed = String(text).trim();
  if (!trimmed) return [];
  const matches = trimmed.match(/\d+/g);
  if (!matches) return [];
  const arr = matches.map((x) => Number(x)).filter((x) => Number.isFinite(x) && x >= 0 && x < total);
  return [...new Set(arr)].sort((a, b) => a - b);
}

function parseTruthSequence(text) {
  if (!text) return null;
  const tokens = String(text)
    .trim()
    .split(/[\s,]+/)
    .map((t) => t.trim())
    .filter(Boolean);
  if (tokens.length !== total) return null;
  const out = new Array(total).fill("X");
  for (let i = 0; i < total; i++) {
    const tok = tokens[i].toUpperCase();
    if (tok === "0") out[i] = 0;
    else if (tok === "1") out[i] = 1;
    else if (tok === "X" || tok === "-") out[i] = "X";
    else return null;
  }
  return out;
}

function setKmapCornerLabel() {
  const corner = $("#kmapCornerLabel");
  const [A, B, C, D] = appState.varNames;
  const ab = corner?.querySelector(".cornerAB");
  const cd = corner?.querySelector(".cornerCD");
  if (ab) ab.textContent = `${A}${B}`;
  if (cd) cd.textContent = `${C}${D}`;
}

function setTruthOrderHint() {
  const hint = $("#truthOrderHint");
  if (!hint) return;
  const [A, B, C, D] = appState.varNames;
  hint.textContent = `Sıra: ${A}${B}${C}${D}. Örn: m=1 → 0001`;
}

function cycleCellValue(v) {
  if (v === "X") return "0";
  if (v === "0") return "1";
  return "X";
}

function renderLegend() {
  const legend = $("#legend");
  legend.innerHTML = "";
  const items = [
    { label: "F=1", v: "1", sw: "rgba(34, 197, 94, .25)" },
    { label: "F=0", v: "0", sw: "rgba(148, 163, 184, .45)" },
    { label: "X (Don't care)", v: "X", sw: "rgba(245, 158, 11, .65)" },
  ];
  for (const it of items) {
    const el = document.createElement("div");
    el.className = "legendItem";
    el.innerHTML = `<span class="swatch" style="background:${it.sw}"></span>${it.label}`;
    legend.appendChild(el);
  }
}

function renderKmap() {
  const container = $("#kmapContainer");
  container.innerHTML = "";

  const { r: R, c: C } = { r: 4, c: 4 };
  const cellW = 92;
  const cellH = 66;
  const cornerW = 160;

  const grid = document.createElement("div");
  grid.className = "kmapGrid";
  grid.style.gridTemplateColumns = `${cornerW}px repeat(${C}, ${cellW}px)`;
  grid.style.gridTemplateRows = `40px repeat(${R}, ${cellH}px)`;

  const corner = document.createElement("div");
  corner.className = "kcorner kcornerDiag";
  corner.id = "kmapCornerLabel";
  corner.innerHTML = `<span class="cornerAB"></span><span class="cornerCD"></span>`;
  grid.appendChild(corner);

  const colCodes = gray2.map((code) => {
    const Cb = (code >>> 1) & 1;
    const Db = code & 1;
    return `${Cb}${Db}`;
  });
  const rowCodes = gray2.map((code) => {
    const A = (code >>> 1) & 1;
    const B = code & 1;
    return `${A}${B}`;
  });

  for (let c = 0; c < C; c++) {
    const h = document.createElement("div");
    h.className = "kheader";
    h.textContent = colCodes[c];
    grid.appendChild(h);
  }

  for (let r = 0; r < R; r++) {
    const rh = document.createElement("div");
    rh.className = "kcorner";
    rh.textContent = rowCodes[r];
    grid.appendChild(rh);

    for (let c = 0; c < C; c++) {
      const m = cellPosToMinterm(r, c);
      const cell = document.createElement("div");
      cell.className = "kcell";
      cell.dataset.m = String(m);
      cell.title = `m=${m}`;
      cell.innerHTML = `<div class="cellVal">X</div><div class="overlay" data-area="1"></div>`;
      cell.addEventListener("click", () => {
        const mm = Number(cell.dataset.m);
        const current = appState.outputs[mm];
        const next = cycleCellValue(String(current));
        appState.outputs[mm] = next === "X" ? "X" : Number(next);
        renderKmapValuesForAll();
        const seq = $("#truthSequence");
        if (seq) {
          seq.dataset.dirty = "0";
          seq.value = appState.outputs.map((v) => (v === "X" ? "X" : String(v))).join(" ");
        }
        computeAndRender();
      });
      grid.appendChild(cell);
    }
  }

  container.appendChild(grid);
  setKmapCornerLabel();
  renderKmapValuesForAll();
}

function renderKmapValuesForAll() {
  const cells = [...document.querySelectorAll(".kcell[data-m]")];
  for (const cell of cells) {
    const m = Number(cell.dataset.m);
    const v = appState.outputs[m];
    const base = v === "X" ? "X" : String(v);
    cell.dataset.base = base;
    const val = cell.querySelector(".cellVal");
    if (val) val.textContent = base;
    const overlay = cell.querySelector(".overlay");
    if (overlay) {
      overlay.classList.remove("is-on");
      overlay.dataset.area = "1";
    }
  }
}

function renderTruthTableUI() {
  const wrap = $("#truthTableWrap");
  if (!wrap) return;
  wrap.innerHTML = "";

  const [A, B, C, D] = appState.varNames;
  const table = document.createElement("table");
  table.className = "truthTable";
  table.innerHTML = `
    <thead>
      <tr>
        <th>m</th>
        <th>${A}</th>
        <th>${B}</th>
        <th>${C}</th>
        <th>${D}</th>
        <th>F</th>
      </tr>
    </thead>
    <tbody></tbody>
  `;
  const tbody = table.querySelector("tbody");

  for (let m = 0; m < total; m++) {
    const bits = mintermToBits(m);
    const v = appState.outputs[m];
    const vStr = v === "X" ? "X" : String(v);
    const tr = document.createElement("tr");
    tr.innerHTML = `
      <td>${m}</td>
      <td>${bits[0]}</td>
      <td>${bits[1]}</td>
      <td>${bits[2]}</td>
      <td>${bits[3]}</td>
      <td><button type="button" class="truthOutBtn" data-m="${m}" data-v="${vStr}">${vStr}</button></td>
    `;
    tbody.appendChild(tr);
  }

  wrap.appendChild(table);

  const btns = wrap.querySelectorAll(".truthOutBtn");
  for (const btn of btns) {
    btn.addEventListener("click", () => {
      const m = Number(btn.dataset.m);
      const current = btn.dataset.v || "X";
      const next = current === "X" ? "0" : current === "0" ? "1" : "X";
      btn.dataset.v = next;
      btn.textContent = next;
      appState.outputs[m] = next === "X" ? "X" : Number(next);
      renderKmapValuesForAll();
      computeAndRender();
    });
  }
}

function updateHighlightsFromTerms(terms) {
  const cellMaxArea = new Array(total).fill(0);
  if (terms && terms.length) {
    for (const t of terms) {
      const area = popcount(t.coverMask);
      for (let m = 0; m < total; m++) {
        if (!bitIsSet(t.coverMask, m)) continue;
        if (area > cellMaxArea[m]) cellMaxArea[m] = area;
      }
    }
  }

  const cells = [...document.querySelectorAll(".kcell[data-m]")];
  for (const cell of cells) {
    const m = Number(cell.dataset.m);
    const overlay = cell.querySelector(".overlay");
    if (!overlay) continue;
    const area = cellMaxArea[m];
    if (area > 0) {
      overlay.dataset.area = String(area);
      overlay.classList.add("is-on");
    } else {
      overlay.classList.remove("is-on");
      overlay.dataset.area = "1";
    }
  }
}

function renderVarNameInputs() {
  const wrap = $("#varNameInputs");
  if (!wrap) return;
  wrap.innerHTML = "";
  for (let i = 0; i < n; i++) {
    const [label, key] = [`${i + 1}. değişken`, i];
    const row = document.createElement("div");
    row.className = "varNameRow";
    row.innerHTML = `<label>${label}</label><input id="varName_${i}" value="${appState.varNames[i] || ""}" />`;
    const input = row.querySelector(`#varName_${i}`);
    input.addEventListener("input", () => {
      const v = String(input.value).trim().replace(/\s+/g, "");
      appState.varNames[i] = v || `V${i + 1}`;
      setKmapCornerLabel();
      setTruthOrderHint();
      renderTruthTableUI();
      computeAndRender();
    });
    wrap.appendChild(row);
  }
  setTruthOrderHint();
  renderTruthTableUI();
}

function setExpression(text) {
  $("#expressionBox").textContent = text;
}

function showError(msg) {
  appState.lastError = msg;
  setExpression(`F = ?  (${msg})`);
}

function computeAndRender() {
  const res = simplify(appState.outputs, appState.exprMode, appState.varNames);
  if (!res || !res.expression) {
    showError("Hesaplama başarısız.");
    return;
  }
  setExpression(res.expression);
  updateHighlightsFromTerms(res.terms || []);
}

function setOutputs(outputs) {
  if (!outputs || outputs.length !== total) return false;
  appState.outputs = outputs.map((v) => (v === "X" ? "X" : v === 1 ? 1 : 0));
  renderKmapValuesForAll();
  const seq = $("#truthSequence");
  if (seq) {
    seq.dataset.dirty = "0";
    seq.value = appState.outputs.map((v) => (v === "X" ? "X" : String(v))).join(" ");
  }
  computeAndRender();
  return true;
}

function parsePanelTruthAndApply() {
  computeAndRender();
}

function parsePanelSopAndApply() {
  const onesIdx = parseIndexList($("#onesInput").value);
  const dcIdx = parseIndexList($("#dcInputSop").value);
  const dcSet = new Set(dcIdx);
  const outputs = new Array(total).fill(0);
  for (let m = 0; m < total; m++) outputs[m] = dcSet.has(m) ? "X" : 0;
  for (const m of onesIdx) {
    if (dcSet.has(m)) continue;
    outputs[m] = 1;
  }
  setOutputs(outputs);
}

function parsePanelPosAndApply() {
  const zerosIdx = parseIndexList($("#zerosInput").value);
  const dcIdx = parseIndexList($("#dcInputPos").value);
  const dcSet = new Set(dcIdx);
  const outputs = new Array(total).fill(1);
  for (let m = 0; m < total; m++) outputs[m] = dcSet.has(m) ? "X" : 1;
  for (const m of zerosIdx) {
    if (dcSet.has(m)) continue;
    outputs[m] = 0;
  }
  setOutputs(outputs);
}

function tokenizeExpressionToSopTerms(expr) {
  const cleaned = String(expr ?? "")
    .replace(/[’]/g, "'")
    .replace(/[⋅·*]/g, " ")
    .replace(/\s+/g, " ")
    .trim();
  if (!cleaned) return null;
  const parts = cleaned.split("+").map((p) => p.trim()).filter(Boolean);
  if (parts.length === 0) return null;
  return parts;
}

function parseSopStringToOutputs(expr, varNames) {
  const cleaned = String(expr ?? "").trim();
  if (!cleaned) return { ok: false, error: "İfade boş olamaz." };
  const normalized = tokenizeExpressionToSopTerms(cleaned);
  if (!normalized) return { ok: false, error: "İfade okunamadı." };

  const vars = varNames.slice(0, n).map((v) => String(v).trim().replace(/\s+/g, ""));
  if (vars.some((v) => !v)) return { ok: false, error: "Değişken isimleri eksik." };

  const varsWithIndex = vars
    .map((name, idx) => ({ name, idx }))
    .sort((a, b) => b.name.length - a.name.length);

  if (normalized.length === 1) {
    const single = normalized[0].replace(/\s+/g, "");
    if (single === "1") {
      return { ok: true, outputs: new Array(total).fill(1) };
    }
    if (single === "0") {
      return { ok: true, outputs: new Array(total).fill(0) };
    }
  }

  const outputs = new Array(total).fill(0);

  for (const termRaw of normalized) {
    const term = termRaw.replace(/\s+/g, "");
    if (!term) continue;
    const constraints = {};
    let i = 0;
    while (i < term.length) {
      let matched = null;
      for (const v of varsWithIndex) {
        if (term.startsWith(v.name, i)) {
          matched = v;
          break;
        }
      }
      if (!matched) return { ok: false, error: `Geçersiz ifade parçası: '${term.slice(i)}'` };

      i += matched.name.length;
      let isNeg = false;
      if (i < term.length && term[i] === "'") {
        isNeg = true;
        i += 1;
      }
      const val = isNeg ? 0 : 1;
      const idx = matched.idx;
      if (constraints[idx] !== undefined && constraints[idx] !== val) {
        return { ok: false, error: "Aynı değişken çelişkili değerle yazıldı." };
      }
      constraints[idx] = val;
    }

    for (let m = 0; m < total; m++) {
      const bits = mintermToBits(m);
      let ok = true;
      for (const [idxStr, val] of Object.entries(constraints)) {
        const idx = Number(idxStr);
        if (bits[idx] !== val) {
          ok = false;
          break;
        }
      }
      if (ok) outputs[m] = 1;
    }
  }

  return { ok: true, outputs };
}

function parsePanelStringAndApply() {
  const expr = $("#stringInput").value;
  const parsed = parseSopStringToOutputs(expr, appState.varNames);
  if (!parsed.ok) {
    showError(parsed.error);
    return;
  }
  setOutputs(parsed.outputs);
}

function initVarNamesUI() {
  renderVarNameInputs();
}

function setActiveSegment(container, activeBtnId) {
  const btns = container.querySelectorAll(".segbtn");
  for (const b of btns) b.classList.toggle("is-active", b.id === activeBtnId);
}

function wireUI() {
  $("#exprModeSOP").addEventListener("click", () => {
    appState.exprMode = "SOP";
    setActiveSegment($("#exprModeSOP").closest(".segmented"), "exprModeSOP");
    computeAndRender();
  });
  $("#exprModePOS").addEventListener("click", () => {
    appState.exprMode = "POS";
    setActiveSegment($("#exprModePOS").closest(".segmented"), "exprModePOS");
    computeAndRender();
  });

  $("#inputBtnTruth").addEventListener("click", () => {
    setActiveSegment($("#inputBtnTruth").closest(".segmented"), "inputBtnTruth");
    $("#panelTruth").classList.remove("is-hidden");
    $("#panelSop").classList.add("is-hidden");
    $("#panelPos").classList.add("is-hidden");
  });
  $("#inputBtnSop").addEventListener("click", () => {
    setActiveSegment($("#inputBtnTruth").closest(".segmented"), "inputBtnSop");
    $("#panelTruth").classList.add("is-hidden");
    $("#panelSop").classList.remove("is-hidden");
    $("#panelPos").classList.add("is-hidden");
  });
  $("#inputBtnPos").addEventListener("click", () => {
    setActiveSegment($("#inputBtnTruth").closest(".segmented"), "inputBtnPos");
    $("#panelTruth").classList.add("is-hidden");
    $("#panelSop").classList.add("is-hidden");
    $("#panelPos").classList.remove("is-hidden");
  });

  $("#inputBtnString").addEventListener("click", () => {
    setActiveSegment($("#inputBtnTruth").closest(".segmented"), "inputBtnString");
    $("#panelTruth").classList.add("is-hidden");
    $("#panelSop").classList.add("is-hidden");
    $("#panelPos").classList.add("is-hidden");
    $("#panelString").classList.remove("is-hidden");
  });

  $("#applyTruthBtn").addEventListener("click", () => parsePanelTruthAndApply());
  $("#applySopBtn").addEventListener("click", () => parsePanelSopAndApply());
  $("#applyPosBtn").addEventListener("click", () => parsePanelPosAndApply());
  $("#applyStringBtn").addEventListener("click", () => parsePanelStringAndApply());
  $("#computeBtn").addEventListener("click", () => computeAndRender());
  $("#resetAllBtn").addEventListener("click", () => {
    appState.outputs = new Array(total).fill("X");
    renderKmapValuesForAll();
    renderTruthTableUI();
    computeAndRender();
  });
}

function init() {
  renderLegend();
  renderKmap();
  initVarNamesUI();
  wireUI();
  computeAndRender();
}

init();

