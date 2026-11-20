// Emits the Poseidon constants the Lean proofs use, for widths t = 3..7 (circomlib's
// Poseidon(2..6)), from circomlib 2.0.5's two constant files:
//   - poseidon_constants_old.circom: the standard round constants and MDS matrix, the
//     parameters of the arkworks sponge and of the Lean spec;
//   - poseidon_constants.circom: the optimized C, S, M, P that circomlib's Poseidon template uses.
// It also emits the certificates that let the Lean kernel check, by Nat arithmetic alone, that
// the optimized template computes the standard permutation (`Lhat`, `dhat`), and a JSON copy of
// the standard constants for the Rust test that pins `zkp/src/poseidon.rs` to them.
//
// Usage: node lean/scripts/poseidon_constants.mjs [--check]
// With --check it writes nothing and exits 1 if any emitted file differs from the one on disk.

import { readFileSync, writeFileSync, existsSync } from 'node:fs';

const root = new URL('../../', import.meta.url);
const circuits = new URL('zkp/node_modules/circomlib/circuits/', root);
const r = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
const WIDTHS = [3, 4, 5, 6, 7];
const FULL_ROUNDS = 8;

// Each POSEIDON_X(t) function is an if-chain of `t == k` branches returning one array literal.
// The literal's numbers keep their source spelling (decimal or 0x hex), so the Lean file reads
// side by side with circomlib.
function parseFunction(text, name) {
  const start = text.indexOf(`function ${name}(t)`);
  if (start < 0) throw new Error(`${name} not found`);
  const end = text.indexOf('\nfunction ', start + 1);
  const body = text.slice(start, end < 0 ? text.length : end);
  const out = new Map();
  const branch = /t\s*==\s*(\d+)\s*\)\s*\{\s*return\s*(\[[^;]*\])\s*;/g;
  for (const m of body.matchAll(branch)) {
    const json = m[2].replace(/0x[0-9a-fA-F]+|\d+/g, (s) => `"${s}"`);
    out.set(Number(m[1]), JSON.parse(json));
  }
  return out;
}

const oldText = readFileSync(new URL('poseidon_constants_old.circom', circuits), 'utf8');
const optText = readFileSync(new URL('poseidon_constants.circom', circuits), 'utf8');
const templateText = readFileSync(new URL('poseidon.circom', circuits), 'utf8');
const old = { C: parseFunction(oldText, 'POSEIDON_C'), M: parseFunction(oldText, 'POSEIDON_M') };
const opt = {
  C: parseFunction(optText, 'POSEIDON_C'),
  S: parseFunction(optText, 'POSEIDON_S'),
  M: parseFunction(optText, 'POSEIDON_M'),
  P: parseFunction(optText, 'POSEIDON_P'),
};
const nRoundsP = JSON.parse(templateText.match(/var N_ROUNDS_P\[16\] = (\[[^\]]*\]);/)[1]);

// Field arithmetic for the certificates and the self-checks below.
const mod = (x) => ((x % r) + r) % r;
const big = (s) => mod(BigInt(s));
function inv(a) {
  let [x, y, u, v] = [mod(a), r, 1n, 0n];
  while (x !== 0n) {
    const q = y / x;
    [x, y] = [y - q * x, x];
    [u, v] = [v - q * u, u];
  }
  if (y !== 1n) throw new Error('not invertible');
  return mod(v);
}
const matVec = (A, v) => A.map((row) => mod(row.reduce((acc, a, j) => acc + a * v[j], 0n)));
const matMul = (A, B) => A.map((row) => B[0].map((_, j) => mod(row.reduce((acc, a, k) => acc + a * B[k][j], 0n))));
const transpose = (A) => A[0].map((_, j) => A.map((row) => row[j]));
const identity = (t) => Array.from({ length: t }, (_, i) => Array.from({ length: t }, (_, j) => (i === j ? 1n : 0n)));
const vecAdd = (a, b) => a.map((x, i) => mod(x + b[i]));
const vecSub = (a, b) => a.map((x, i) => mod(x - b[i]));
const pow5 = (x) => mod(x * x * x * x * x);
function matInv(A) {
  const t = A.length;
  const m = A.map((row, i) => [...row, ...identity(t)[i]]);
  for (let c = 0; c < t; c++) {
    const p = m.findIndex((row, i) => i >= c && row[c] !== 0n);
    [m[c], m[p]] = [m[p], m[c]];
    const s = inv(m[c][c]);
    m[c] = m[c].map((x) => mod(x * s));
    for (let i = 0; i < t; i++) if (i !== c) m[i] = m[i].map((x, j) => mod(x - m[i][c] * m[c][j]));
  }
  return m.map((row) => row.slice(t));
}
const assert = (cond, what) => {
  if (!cond) throw new Error(`check failed: ${what}`);
};
const eqVec = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
const eqMat = (A, B) => A.length === B.length && A.every((row, i) => eqVec(row, B[i]));

function width(t) {
  const RP = nRoundsP[t - 2];
  const arkFlat = old.C.get(t);
  const mdsRows = old.M.get(t);
  const C = opt.C.get(t),
    S = opt.S.get(t),
    M = opt.M.get(t),
    P = opt.P.get(t);
  assert(arkFlat.length === t * (FULL_ROUNDS + RP), `ark length t=${t}`);
  assert(C.length === t * FULL_ROUNDS + RP && S.length === RP * (2 * t - 1), `C, S lengths t=${t}`);

  // The arkworks state update is s ← mds·s with mds[i][j] read row-major, as the old template's
  // Mix reads M[i][j]; the optimized Mix reads M[j][i].
  const A = mdsRows.map((row) => row.map(big));
  const ark = Array.from({ length: FULL_ROUNDS + RP }, (_, i) => arkFlat.slice(i * t, (i + 1) * t).map(big));
  const c = C.map(big),
    s = S.map(big),
    m = M.map((row) => row.map(big)),
    p = P.map((row) => row.map(big));
  const cv = (off) => c.slice(off, off + t);
  // MixS(t, S, k) as a dense matrix.
  const sparse = (k) =>
    Array.from({ length: t }, (_, i) =>
      Array.from({ length: t }, (_, j) => {
        const base = (2 * t - 1) * k;
        if (i === 0) return s[base + j];
        if (j === 0) return s[base + t + i - 1];
        return i === j ? 1n : 0n;
      }),
    );

  // The identities the Lean kernel checks, checked here first.
  assert(eqVec(cv(0), ark[0]), `C[0..t) = ark_0, t=${t}`);
  assert(eqMat(transpose(m), A), `Mᵀ = mds, t=${t}`);
  for (let k = 1; k <= 3; k++) assert(eqVec(matVec(A, cv(k * t)), ark[k]), `mds·C_${k} = ark_${k}, t=${t}`);
  for (let k = 0; k < 3; k++)
    assert(eqVec(matVec(A, cv(5 * t + RP + k * t)), ark[5 + RP + k]), `last full round ${k}, t=${t}`);

  // Partial rounds: the standard state before round 4+k's S-box is L_k·w_k + d_k, w_k being the
  // optimized one, with L_k = diag(1, L̂_k) and (d_k)_0 = 0. Backwards from L_RP = I, d_RP = 0:
  //   L_k = mds⁻¹·L_{k+1}·S_k,  d_k = mds⁻¹·(d_{k+1} − ark_{5+k}) + C[5t+k]·e_0.
  const Ainv = matInv(A);
  const L = new Array(RP + 1),
    d = new Array(RP + 1);
  L[RP] = identity(t);
  d[RP] = new Array(t).fill(0n);
  for (let k = RP - 1; k >= 0; k--) {
    L[k] = matMul(Ainv, matMul(L[k + 1], sparse(k)));
    d[k] = matVec(Ainv, vecSub(d[k + 1], ark[5 + k]));
    d[k][0] = mod(d[k][0] + c[5 * t + k]);
    assert(
      L[k][0].every((x, j) => x === (j === 0 ? 1n : 0n)),
      `L_${k} row 0, t=${t}`,
    );
    assert(
      L[k].every((row, i) => row[0] === (i === 0 ? 1n : 0n)),
      `L_${k} column 0, t=${t}`,
    );
    assert(d[k][0] === 0n, `(d_${k})_0 = 0, t=${t}`);
  }
  assert(eqMat(matMul(L[0], transpose(p)), A), `L_0·Pᵀ = mds, t=${t}`);
  assert(eqVec(vecAdd(matVec(A, cv(4 * t)), d[0]), ark[4]), `mds·C_4 + d_0 = ark_4, t=${t}`);

  return {
    t,
    RP,
    arkFlat,
    mdsRows,
    C,
    S,
    M,
    P,
    Lhat: L.slice(0, RP).map((Lk) => Lk.slice(1).map((row) => row.slice(1))),
    dhat: d.slice(0, RP).map((dk) => dk.slice(1)),
    std: { A, ark },
    opt: { c, m, p, sparse },
  };
}

// The two algorithms, to check both against circomlib's known Poseidon([1, 2]).
function stdPerm({ RP, std: { A, ark } }, state) {
  for (let i = 0; i < FULL_ROUNDS + RP; i++) {
    state = vecAdd(state, ark[i]);
    const full = i < FULL_ROUNDS / 2 || i >= FULL_ROUNDS / 2 + RP;
    state = state.map((x, j) => (full || j === 0 ? pow5(x) : x));
    state = matVec(A, state);
  }
  return state;
}
function optHash({ t, RP, opt: { c, m, p, sparse } }, state) {
  const mix = (X, x) => matVec(transpose(X), x);
  const cv = (off) => c.slice(off, off + t);
  let x = vecAdd(state, cv(0));
  for (let k = 0; k < 3; k++) x = mix(m, vecAdd(x.map(pow5), cv((k + 1) * t)));
  x = mix(p, vecAdd(x.map(pow5), cv(4 * t)));
  for (let k = 0; k < RP; k++) {
    x = [...x];
    x[0] = mod(pow5(x[0]) + c[5 * t + k]);
    x = matVec(sparse(k), x);
  }
  for (let k = 0; k < 3; k++) x = mix(m, vecAdd(x.map(pow5), cv(5 * t + RP + k * t)));
  return mix(m, x.map(pow5))[0];
}

const widths = WIDTHS.map(width);
const known = 7853200120776062878684798364095072458815029376092732009249414926327459813530n;
assert(stdPerm(widths[0], [0n, 1n, 2n])[0] === known, 'standard Poseidon([1, 2])');
assert(optHash(widths[0], [0n, 1n, 2n]) === known, 'optimized Poseidon([1, 2])');

// Lean list literals: one number per line for a vector, one row per line for a matrix.
const row = (xs) => `[${xs.join(', ')}]`;
const vec = (xs) => `[\n${xs.map((x) => `  ${x}`).join(',\n')}]`;
const mat = (rows) => `[\n${rows.map((r) => `  ${row(r)}`).join(',\n')}]`;
const mats = (ms) => `[\n${ms.map((rows) => `  [${rows.map(row).join(',\n   ')}]`).join(',\n')}]`;

function leanFile(w) {
  const { t } = w;
  return `/-!
# Poseidon constants for width ${t} (circomlib \`Poseidon(${t - 1})\`)

Generated by \`lean/scripts/poseidon_constants.mjs\` from circomlib 2.0.5; do not edit. Numbers
keep circomlib's spelling, so each list reads side by side with its source.
-/

namespace Zerc20.PoseidonConstants.T${t}

/-- \`N_ROUNDS_P[${t - 2}]\` of \`poseidon.circom\`. -/
def partialRounds : Nat := ${w.RP}

/-- \`POSEIDON_C(${t})\` of \`poseidon_constants_old.circom\`: the standard round constants, ${t} per
round. -/
def ark : List Nat := ${vec(w.arkFlat)}

/-- \`POSEIDON_M(${t})\` of \`poseidon_constants_old.circom\`: the standard MDS matrix, row by row. -/
def mds : List (List Nat) := ${mat(w.mdsRows)}

/-- \`POSEIDON_C(${t})\` of \`poseidon_constants.circom\`. -/
def C : List Nat := ${vec(w.C)}

/-- \`POSEIDON_S(${t})\` of \`poseidon_constants.circom\`. -/
def S : List Nat := ${vec(w.S)}

/-- \`POSEIDON_M(${t})\` of \`poseidon_constants.circom\`. -/
def M : List (List Nat) := ${mat(w.M)}

/-- \`POSEIDON_P(${t})\` of \`poseidon_constants.circom\`. -/
def P : List (List Nat) := ${mat(w.P)}

-- The nested literal below is deeper than the default recursion limit allows.
set_option maxRecDepth 10000 in
/-- Certificate: for each partial round \`k\`, the lower-right block \`L̂_k\` of \`L_k = diag(1, L̂_k)\`.
Before round \`k\`'s S-box the standard state is \`L_k·w + d_k\`, \`w\` being the optimized one. -/
def Lhat : List (List (List Nat)) := ${mats(w.Lhat)}

/-- Certificate: for each partial round \`k\`, entries \`1..t-1\` of \`d_k\`; entry 0 is 0. -/
def dhat : List (List Nat) := ${mat(w.dhat)}

end Zerc20.PoseidonConstants.T${t}
`;
}

const json = {};
for (const w of widths) {
  json[w.t] = {
    partialRounds: w.RP,
    ark: w.std.ark.map((row) => row.map(String)),
    mds: w.std.A.map((row) => row.map(String)),
  };
}

const outputs = new Map(widths.map((w) => [`lean/Zerc20/PoseidonConstants${w.t}.lean`, leanFile(w)]));
outputs.set('lean/scripts/poseidon_constants.json', JSON.stringify(json, null, 1) + '\n');

const check = process.argv.includes('--check');
let stale = false;
for (const [path, text] of outputs) {
  const url = new URL(path, root);
  if (check) {
    if (!existsSync(url) || readFileSync(url, 'utf8') !== text) {
      console.error(`${path} is out of date`);
      stale = true;
    }
  } else {
    writeFileSync(url, text);
  }
}
if (stale) process.exit(1);
