import Zerc20.Ark
import Mathlib.Data.Fin.VecNotation

/-!
# SHA-256 and the hash chain

FIPS 180-4 SHA-256 over 32-bit words, the arkworks gadget `Sha256Gadget` that computes it in a
circuit, and `hash_chain_var`, zERC20's in-circuit hash chain. The gadget's soundness and
completeness hold for messages of any length: its relation fixes the digest bytes to `hash` of the
message bytes, and every message has a satisfying witness.
-/

namespace Zerc20.Sha256

/-- `slice.chunks(k)`: consecutive pieces of `k`, the last one shorter when `k` does not divide the
length. The fuel is the length, which bounds the number of pieces for `k ≥ 1`. -/
def chunks {α : Type} (k : ℕ) (l : List α) : List (List α) := go l.length l
where
  go : ℕ → List α → List (List α)
    | 0, _ => []
    | _ + 1, [] => []
    | n + 1, l@(_ :: _) => l.take k :: go n (l.drop k)

/-! ## The specification (FIPS 180-4) -/

/-- The round constants `K₀ … K₆₃`. -/
def K : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value `H⁽⁰⁾`. -/
def H₀ : List (BitVec 32) :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! The six logical functions; `Σ₀`, `Σ₁`, `σ₀` and `σ₁` are spelled `BSIG0`, `BSIG1`, `SSIG0`
and `SSIG1`. -/

def Ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)
def Maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
/-- `Σ₀`. -/
def BSIG0 (x : BitVec 32) : BitVec 32 := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
/-- `Σ₁`. -/
def BSIG1 (x : BitVec 32) : BitVec 32 := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
/-- `σ₀`. -/
def SSIG0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3
/-- `σ₁`. -/
def SSIG1 (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10

/-- `n mod 2^64` as eight big-endian bytes: the last eight little-endian bytes, reversed. -/
def be64 (n : ℕ) : List UInt8 := (List.ofFn fun j : Fin 8 => UInt8.ofNat (n / 256 ^ (j : ℕ))).reverse

/-- What padding appends to an `n`-byte message: a `1` bit, zero bits up to 56 bytes mod 64, and
the message's length in bits as 64 big-endian bits. -/
def padding (n : ℕ) : List UInt8 :=
  0x80 :: List.replicate ((119 - n % 64) % 64) 0 ++ be64 (8 * n)

def pad (msg : List UInt8) : List UInt8 := msg ++ padding msg.length

/-- A big-endian word of four bytes. -/
def word (b : List UInt8) : BitVec 32 :=
  (b.getD 0 0).toBitVec ++ (b.getD 1 0).toBitVec ++ (b.getD 2 0).toBitVec ++ (b.getD 3 0).toBitVec

/-- `W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}`, appended to `W₀ … W_{t-1}`. -/
def scheduleStep (W : List (BitVec 32)) (t : ℕ) : List (BitVec 32) :=
  W ++ [SSIG1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 + SSIG0 (W.getD (t - 15) 0) + W.getD (t - 16) 0]

/-- The message schedule `W₀ … W₆₃` of a 64-byte block. -/
def schedule (block : List UInt8) : List (BitVec 32) :=
  (List.range' 16 48).foldl scheduleStep ((chunks 4 block).map word)

/-- Round `t` on the working variables `a … h`. -/
def round (W : List (BitVec 32)) (v : List (BitVec 32)) (t : ℕ) : List (BitVec 32) :=
  match v with
  | [a, b, c, d, e, f, g, h] =>
    let T₁ := h + BSIG1 e + Ch e f g + K.getD t 0 + W.getD t 0
    let T₂ := BSIG0 a + Maj a b c
    [T₁ + T₂, a, b, c, d + T₁, e, f, g]
  | v => v

/-- One 64-byte block into the hash value. -/
def compress (H : List (BitVec 32)) (block : List UInt8) : List (BitVec 32) :=
  List.zipWith (· + ·) H ((List.range 64).foldl (round (schedule block)) H)

/-- A word's four bytes, big-endian. -/
def bytesOfWord (x : BitVec 32) : List UInt8 :=
  [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8].map UInt8.ofBitVec

/-- SHA-256 of a byte string: the 32 bytes of the final hash value, big-endian. -/
def hash (msg : List UInt8) : List UInt8 :=
  ((chunks 64 (pad msg)).foldl compress H₀).flatMap bytesOfWord

/-! The standard test vectors (the empty message, one block and two blocks), checked by the
kernel. -/

/-- Bytes from numbers. -/
def ofHex (l : List ℕ) : List UInt8 := l.map UInt8.ofNat

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => UInt8.ofNat c.toNat

theorem hash_empty : hash [] = ofHex
    [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
     0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55] := by
  decide +kernel

theorem hash_abc : hash (ascii "abc") = ofHex
    [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
     0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad] := by
  decide +kernel

theorem hash_two_blocks :
    hash (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") = ofHex
    [0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8, 0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
     0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67, 0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1] := by
  decide +kernel

/-- A number's 32 bytes, big-endian: `abi.encodePacked` of a `uint256`, and `to_bytes_be` of a
field element. -/
def be32 (n : ℕ) : List UInt8 := (List.ofFn fun j : Fin 32 => UInt8.ofNat (n / 256 ^ (j : ℕ))).reverse

/-- A byte string as a big-endian number. -/
def ofBytesBE (l : List UInt8) : ℕ := l.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- The hash chain: `SHA256(be32 prev ‖ be32 v₁ ‖ …)` as a big-endian number, mod `2^248`. Solidity's
`uint256(sha256(abi.encodePacked(prev, v₁, …))) & (2^248 - 1)` and Rust's `hash_chain` compute it. -/
def hashChain (prev : ℕ) (vals : List ℕ) : ℕ :=
  ofBytesBE (hash ((prev :: vals).flatMap be32)) % 2 ^ 248

theorem hashChain_lt (prev : ℕ) (vals : List ℕ) : hashChain prev vals < 2 ^ 248 :=
  Nat.mod_lt _ (by norm_num)

/-! ## Lists in pieces -/

section chunks

variable {α β : Type} {k : ℕ}

theorem chunks.go_eq (hk : 0 < k) :
    ∀ (n m : ℕ) (l : List α), l.length ≤ n → l.length ≤ m → chunks.go k n l = chunks.go k m l
  | 0, m, l, h, _ => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    cases m <;> rfl
  | n + 1, 0, l, _, h => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    rfl
  | n + 1, m + 1, [], _, _ => rfl
  | n + 1, m + 1, a :: l, h1, h2 => by
    simp only [chunks.go]
    rw [chunks.go_eq hk n m _ (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)]

@[simp] theorem chunks_nil : chunks k ([] : List α) = [] := rfl

theorem chunks_cons (hk : 0 < k) (a : α) (l : List α) :
    chunks k (a :: l) = (a :: l).take k :: chunks k ((a :: l).drop k) := by
  simp only [chunks, chunks.go]
  rw [chunks.go_eq hk _ _ _ (by simp; omega) le_rfl]

theorem chunks_eq_cons (hk : 0 < k) {l : List α} (h0 : l ≠ []) :
    chunks k l = l.take k :: chunks k (l.drop k) := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h0
  exact chunks_cons hk a l

theorem chunks_of_length_le (hk : 0 < k) {l : List α} (h0 : l ≠ []) (h : l.length ≤ k) :
    chunks k l = [l] := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h0
  rw [chunks_cons hk, List.take_of_length_le h, List.drop_eq_nil_of_le h, chunks_nil]

theorem chunks_append (hk : 0 < k) :
    ∀ (q : ℕ) (l₁ l₂ : List α), l₁.length = k * q → chunks k (l₁ ++ l₂) = chunks k l₁ ++ chunks k l₂
  | 0, l₁, l₂, h => by
    obtain rfl : l₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    rfl
  | q + 1, l₁, l₂, h => by
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil (l := l₁)
      (by rintro rfl; simp at h; nlinarith)
    have hlen : k ≤ (a :: l).length := by rw [h]; nlinarith
    rw [List.cons_append, chunks_cons hk, chunks_cons hk, ← List.cons_append,
      List.take_append_of_le_length hlen, List.drop_append_of_le_length hlen,
      chunks_append hk q _ _ (by simp at h ⊢; rw [Nat.mul_succ] at h; omega)]
    rfl

theorem chunks_forall₂ (hk : 0 < k) {R : α → β → Prop} :
    ∀ (n : ℕ) {l₁ : List α} {l₂ : List β}, l₁.length ≤ n → List.Forall₂ R l₁ l₂ →
      List.Forall₂ (List.Forall₂ R) (chunks k l₁) (chunks k l₂)
  | _, [], [], _, .nil => .nil
  | n + 1, a :: l₁, b :: l₂, hn, h => by
    rw [chunks_cons hk, chunks_cons hk]
    exact .cons (List.forall₂_take _ h)
      (chunks_forall₂ hk n (by simp at hn ⊢; omega) (List.forall₂_drop _ h))
  | 0, _ :: _, _, hn, _ => by simp at hn

theorem length_of_mem_chunks (hk : 0 < k) :
    ∀ (q : ℕ) (l : List α), l.length = k * q → ∀ c ∈ chunks k l, c.length = k
  | 0, l, h, c, hc => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    simp at hc
  | q + 1, l, h, c, hc => by
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil (l := l) (by rintro rfl; simp at h; nlinarith)
    rw [chunks_cons hk] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp only [List.length_take, h]; rw [Nat.mul_succ]; omega
    · exact length_of_mem_chunks hk q _ (by simp at h ⊢; rw [Nat.mul_succ] at h; omega) c hc

end chunks

theorem length_be64 (n : ℕ) : (be64 n).length = 8 := by simp [be64]

theorem length_pad (msg : List UInt8) : (pad msg).length = 64 * ((msg.length + 72) / 64) := by
  simp only [pad, padding, List.length_append, List.length_cons, List.length_replicate, length_be64]
  omega

end Zerc20.Sha256

namespace Zerc20.Ark

/-! ## Loops with one witness per step -/

/-- A loop whose step `i` takes one witness and returns the next value and its constraints. It takes
exactly one witness per step; any other count leaves it unsatisfiable. -/
def loop {ι α W : Type} (step : ι → α → W → α × Prop) : List ι → List W → α → α × Prop
  | [], [], a => (a, True)
  | i :: is, x :: xs, a =>
    let s := step i a x
    ((loop step is xs s.1).1, s.2 ∧ (loop step is xs s.1).2)
  | _, _, a => (a, False)

theorem loop_sound {ι κ α β W : Type} {step : ι → α → W → α × Prop} {spec : β → κ → β}
    {Q : ι → κ → Prop} {S : α → β → Prop}
    (hstep : ∀ i j a b x, Q i j → S a b → (step i a x).2 → S (step i a x).1 (spec b j)) :
    ∀ {is : List ι} {js : List κ} {xs : List W} {a : α} {b : β}, List.Forall₂ Q is js → S a b →
      (loop step is xs a).2 → S (loop step is xs a).1 (js.foldl spec b)
  | [], [], [], _, _, .nil, hS, _ => hS
  | i :: _, j :: _, x :: _, a, b, .cons hq hQ, hS, h =>
    (loop_sound hstep hQ (hstep i j a b x hq hS h.1) h.2 :)
  | [], [], _ :: _, _, _, _, _, h => h.elim
  | _ :: _, _ :: _, [], _, _, _, _, h => h.elim

theorem loop_complete {ι κ α β W : Type} {step : ι → α → W → α × Prop} {spec : β → κ → β}
    {Q : ι → κ → Prop} {S : α → β → Prop}
    (hstep : ∀ i j a b, Q i j → S a b → ∃ x, (step i a x).2 ∧ S (step i a x).1 (spec b j)) :
    ∀ {is : List ι} {js : List κ} {a : α} {b : β}, List.Forall₂ Q is js → S a b →
      ∃ xs, (loop step is xs a).2
  | [], [], _, _, .nil, _ => ⟨[], trivial⟩
  | i :: _, j :: _, a, b, .cons hq hQ, hS => by
    obtain ⟨x, hx, hS'⟩ := hstep i j a b hq hS
    obtain ⟨xs, hxs⟩ := loop_complete hstep hQ hS'
    exact ⟨x :: xs, hx, hxs⟩

theorem forall₂_refl {α : Type} (l : List α) : List.Forall₂ (· = ·) l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons rfl ih

theorem forall₂_getD {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {d₁ : α} {d₂ : β} (hd : R d₁ d₂) (j : ℕ) :
    R (l₁.getD j d₁) (l₂.getD j d₂) := by
  induction h generalizing j with
  | nil => simpa using hd
  | cons hab _ ih =>
    cases j with
    | zero => exact hab
    | succ j => exact ih j

theorem forall₂_flatMap {α β γ δ : Type} {P : α → β → Prop} {R : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ P l₁ l₂)
    (hfg : ∀ a b, P a b → List.Forall₂ R (f a) (g b)) :
    List.Forall₂ R (l₁.flatMap f) (l₂.flatMap g) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => simpa using List.rel_append (hfg _ _ hab) ih

theorem forall₂_and_mem {α β : Type} {R : α → β → Prop} {P : β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (hP : ∀ b ∈ l₂, P b) : List.Forall₂ (fun a b => R a b ∧ P b) l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons ⟨hab, hP _ (by simp)⟩ (ih fun b hb => hP b (by simp [hb]))

/-! ## `Sha256Gadget` (ark-crypto-primitives) -/

namespace Sha256Gadget

open Sha256

/-- A byte variable carries a byte. -/
def ByteEnc (u : UInt 8) (b : _root_.UInt8) : Prop := UInt.Encodes u b.toBitVec

/-- The eight words of the state carry the eight words of a hash value. -/
def StateEnc (h : Fin 8 → UInt 32) (H : List (BitVec 32)) : Prop :=
  H.length = 8 ∧ ∀ j : Fin 8, UInt.Encodes (h j) (H.getD j 0)

/-- The witnesses of one schedule word: the `^`s of `s0` and `s1`, and the sum's bits. -/
structure SchedWit where
  s0x : Fin 32 → F
  s0 : Fin 32 → F
  s1x : Fin 32 → F
  s1 : Fin 32 → F
  sum : Fin (32 + UInt.log2 4) → F

/-- Word `i ≥ 16` of `update_state`'s schedule, `w[i-16] + s0 + w[i-7] + s1`, appended to the words
before it. arkworks writes it into a preallocated vector; appending gives the same words, as each
step reads only earlier ones. -/
def schedStep (i : ℕ) (w : List (UInt 32)) (x : SchedWit) : List (UInt 32) × Prop :=
  let a := w.getD (i - 15) (UInt.constant 0)
  let s0x := UInt.xor (UInt.rotate_right a 7) (UInt.rotate_right a 18) x.s0x
  let s0 := UInt.xor s0x (UInt.shr a 3) x.s0
  let b := w.getD (i - 2) (UInt.constant 0)
  let s1x := UInt.xor (UInt.rotate_right b 17) (UInt.rotate_right b 19) x.s1x
  let s1 := UInt.xor s1x (UInt.shr b 10) x.s1
  let ops := [w.getD (i - 16) (UInt.constant 0), s0, w.getD (i - 7) (UInt.constant 0), s1]
  (w ++ [UInt.wrapping_add_many ops x.sum],
    UInt.xor.Rel (UInt.rotate_right a 7) (UInt.rotate_right a 18) x.s0x ∧
    UInt.xor.Rel s0x (UInt.shr a 3) x.s0 ∧
    UInt.xor.Rel (UInt.rotate_right b 17) (UInt.rotate_right b 19) x.s1x ∧
    UInt.xor.Rel s1x (UInt.shr b 10) x.s1 ∧
    UInt.wrapping_add_many.Rel ops x.sum)

/-- The witnesses of one round: the `&`s and `^`s of `ch`, `ma`, `s0` and `s1`, and the bits of the
four sums. -/
structure RoundWit where
  ch₁ : Fin 32 → F
  ch₂ : Fin 32 → F
  ch : Fin 32 → F
  ma₁ : Fin 32 → F
  ma₂ : Fin 32 → F
  ma₃ : Fin 32 → F
  ma₄ : Fin 32 → F
  ma : Fin 32 → F
  s0x : Fin 32 → F
  s0 : Fin 32 → F
  s1x : Fin 32 → F
  s1 : Fin 32 → F
  t0 : Fin (32 + UInt.log2 5) → F
  t1 : Fin (32 + UInt.log2 2) → F
  e : Fin (32 + UInt.log2 2) → F
  a : Fin (32 + UInt.log2 2) → F

/-- Round `i` of `update_state` on the working words `h`, with the schedule `w`. -/
def roundStep (w : List (UInt 32)) (i : ℕ) (h : Fin 8 → UInt 32) (x : RoundWit) :
    (Fin 8 → UInt 32) × Prop :=
  let ch₁ := UInt.and (h 4) (h 5) x.ch₁
  let ch₂ := UInt.and (UInt.not (h 4)) (h 6) x.ch₂
  let ch := UInt.xor ch₁ ch₂ x.ch
  let ma₁ := UInt.and (h 0) (h 1) x.ma₁
  let ma₂ := UInt.and (h 0) (h 2) x.ma₂
  let ma₃ := UInt.and (h 1) (h 2) x.ma₃
  let ma₄ := UInt.xor ma₁ ma₂ x.ma₄
  let ma := UInt.xor ma₄ ma₃ x.ma
  let s0x := UInt.xor (UInt.rotate_right (h 0) 2) (UInt.rotate_right (h 0) 13) x.s0x
  let s0 := UInt.xor s0x (UInt.rotate_right (h 0) 22) x.s0
  let s1x := UInt.xor (UInt.rotate_right (h 4) 6) (UInt.rotate_right (h 4) 11) x.s1x
  let s1 := UInt.xor s1x (UInt.rotate_right (h 4) 25) x.s1
  let t0ops := [h 7, s1, ch, UInt.constant (K.getD i 0), w.getD i (UInt.constant 0)]
  let t0 := UInt.wrapping_add_many t0ops x.t0
  let t1 := UInt.wrapping_add s0 ma x.t1
  (![UInt.wrapping_add t0 t1 x.a, h 0, h 1, h 2, UInt.wrapping_add (h 3) t0 x.e, h 4, h 5, h 6],
    UInt.and.Rel (h 4) (h 5) x.ch₁ ∧ UInt.and.Rel (UInt.not (h 4)) (h 6) x.ch₂ ∧
    UInt.xor.Rel ch₁ ch₂ x.ch ∧
    UInt.and.Rel (h 0) (h 1) x.ma₁ ∧ UInt.and.Rel (h 0) (h 2) x.ma₂ ∧
    UInt.and.Rel (h 1) (h 2) x.ma₃ ∧ UInt.xor.Rel ma₁ ma₂ x.ma₄ ∧ UInt.xor.Rel ma₄ ma₃ x.ma ∧
    UInt.xor.Rel (UInt.rotate_right (h 0) 2) (UInt.rotate_right (h 0) 13) x.s0x ∧
    UInt.xor.Rel s0x (UInt.rotate_right (h 0) 22) x.s0 ∧
    UInt.xor.Rel (UInt.rotate_right (h 4) 6) (UInt.rotate_right (h 4) 11) x.s1x ∧
    UInt.xor.Rel s1x (UInt.rotate_right (h 4) 25) x.s1 ∧
    UInt.wrapping_add_many.Rel t0ops x.t0 ∧ UInt.wrapping_add_many.Rel [s0, ma] x.t1 ∧
    UInt.wrapping_add_many.Rel [h 3, t0] x.e ∧ UInt.wrapping_add_many.Rel [t0, t1] x.a)

/-- The witnesses of one block: the schedule's, the rounds', and the final additions'. -/
structure BlockWit where
  sched : List SchedWit
  rounds : List RoundWit
  final : Fin 8 → Fin (32 + UInt.log2 2) → F

/-- `Sha256Gadget::update_state`: the schedule `w`, 64 rounds on a copy `h` of the state, then
`state[i] += h[i]`. arkworks' tables `K` and `H` are the standard's, so the model reads them from
the specification. -/
def update_state (state : Fin 8 → UInt 32) (data : List (UInt 8)) (x : BlockWit) :
    (Fin 8 → UInt 32) × Prop :=
  let w := loop schedStep (List.range' 16 48) x.sched ((chunks 4 data).map UInt.from_bytes_be)
  let h := loop (roundStep w.1) (List.range 64) x.rounds state
  (fun j => UInt.wrapping_add (state j) (h.1 j) (x.final j),
    w.2 ∧ h.2 ∧ ∀ j, UInt.wrapping_add_many.Rel [state j, h.1 j] (x.final j))

/-- The byte-handling fields of `Sha256Gadget`. The model keeps them apart from `state`, which
only `update_state` changes, and records the blocks handed to `update_state` in order. -/
structure Buffer where
  completed_data_blocks : ℕ
  pending : List (UInt 8)
  num_pending : ℕ

/-- `update`'s loop over `data.chunks(64)`: a full chunk is compressed, a shorter one is copied into
`pending`. Returns the buffer and the blocks compressed. -/
def updateChunks : List (List (UInt 8)) → Buffer → Buffer × List (List (UInt 8))
  | [], s => (s, [])
  | c :: cs, s =>
    if c.length = 64 then
      let r := updateChunks cs { s with completed_data_blocks := s.completed_data_blocks + 1 }
      (r.1, c :: r.2)
    else
      updateChunks cs { s with
        pending := s.pending.take s.num_pending ++ c ++ s.pending.drop (s.num_pending + c.length)
        num_pending := s.num_pending + c.length }

/-- `Sha256Gadget::update`: when `data` completes the pending block, that block goes first; the
rest goes chunk by chunk. Returns the buffer and the blocks compressed. -/
def update (s : Buffer) (data : List (UInt 8)) : Buffer × List (List (UInt 8)) :=
  if 0 < s.num_pending ∧ 64 ≤ s.num_pending + data.length then
    let offset := 64 - s.num_pending
    let block := s.pending.take s.num_pending ++ data.take offset
    let r := updateChunks (chunks 64 (data.drop offset)) ⟨s.completed_data_blocks + 1, block, 0⟩
    (r.1, block :: r.2)
  else updateChunks (chunks 64 data) s

/-- `Sha256Gadget::finalize`'s padding: `0x80`, zeros, and the bit length as eight big-endian
constant bytes, up to the next block end with room for the length, through `update`. Returns the
blocks compressed. -/
def finalize (s : Buffer) : List (List (UInt 8)) :=
  let data_bitlen := s.completed_data_blocks * 512 + s.num_pending * 8
  let encoded_bitlen := (be64 data_bitlen).map fun b => UInt.constant b.toBitVec
  let pending := (List.replicate 72 (UInt.constant 0)).set 0 (UInt.constant 0x80)
  let offset := if s.num_pending < 56 then 56 - s.num_pending else 120 - s.num_pending
  let pending := pending.take offset ++ encoded_bitlen ++ pending.drop (offset + 8)
  (update s (pending.take (offset + 8))).2

/-- `Sha256Gadget::default`'s buffer: no block yet, and 64 constant zeros pending. -/
def Buffer.default : Buffer := ⟨0, List.replicate 64 (UInt.constant 0), 0⟩

/-- The blocks `digest` compresses: those of `update` on the data, then those of `finalize`. -/
def digest.blocks (data : List (UInt 8)) : List (List (UInt 8)) :=
  let r := update Buffer.default data
  r.2 ++ finalize r.1

/-- `Sha256Gadget::digest`: `default`, `update` and `finalize`. The state starts at the constant
`H`, `update_state` runs over the blocks, and the digest is the state's words as big-endian bytes. -/
def digest (data : List (UInt 8)) (xs : List BlockWit) : List (UInt 8) × Prop :=
  let st := loop (fun blk st x => update_state st blk x) (digest.blocks data) xs
    (fun j => UInt.constant (H₀.getD j 0))
  ((List.finRange 8).flatMap fun j => UInt.to_bytes_be (st.1 j), st.2)

/-! ### Soundness -/

theorem zero_add' {n : ℕ} (x : BitVec n) : (0 : BitVec n) + x = x := BitVec.zero_add x

theorem schedStep.sound {i : ℕ} {w : List (UInt 32)} {W : List (BitVec 32)} {x : SchedWit}
    (hw : List.Forall₂ UInt.Encodes w W) (h : (schedStep i w x).2) :
    List.Forall₂ UInt.Encodes (schedStep i w x).1 (scheduleStep W i) := by
  have get := forall₂_getD hw (UInt.constant_encodes 0)
  dsimp only [schedStep] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e0 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes (get (i - 15)) 7)
    (UInt.rotate_right_encodes (get (i - 15)) 18) h1) (UInt.shr_encodes (get (i - 15)) 3) h2
  have e1 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes (get (i - 2)) 17)
    (UInt.rotate_right_encodes (get (i - 2)) 19) h3) (UInt.shr_encodes (get (i - 2)) 10) h4
  have hs := UInt.wrapping_add_many.sound
    (.cons (get (i - 16)) (.cons e0 (.cons (get (i - 7)) (.cons e1 .nil)))) (UInt.size_le _ (by simp)) h5
  refine List.rel_append hw (.cons (hs.of_eq ?_) .nil)
  simp only [List.foldl_cons, List.foldl_nil, zero_add', SSIG0, SSIG1]
  ac_rfl

theorem eq_eight {α : Type} {v : List α} (hv : v.length = 8) :
    ∃ a b c d e f g h, v = [a, b, c, d, e, f, g, h] := by
  match v, hv with
  | [a, b, c, d, e, f, g, h], _ => exact ⟨a, b, c, d, e, f, g, h, rfl⟩

theorem roundStep.sound {w : List (UInt 32)} {W : List (BitVec 32)} {i : ℕ} {h : Fin 8 → UInt 32}
    {v : List (BitVec 32)} {x : RoundWit} (hw : List.Forall₂ UInt.Encodes w W)
    (hv : StateEnc h v) (hr : (roundStep w i h x).2) : StateEnc (roundStep w i h x).1 (round W v i) := by
  obtain ⟨hlen, hv⟩ := hv
  obtain ⟨a, b, c, d, e, f, g, hh, rfl⟩ := eq_eight hlen
  have h0 : UInt.Encodes (h 0) a := hv 0
  have h1 : UInt.Encodes (h 1) b := hv 1
  have h2 : UInt.Encodes (h 2) c := hv 2
  have h3 : UInt.Encodes (h 3) d := hv 3
  have h4 : UInt.Encodes (h 4) e := hv 4
  have h5 : UInt.Encodes (h 5) f := hv 5
  have h6 : UInt.Encodes (h 6) g := hv 6
  have h7 : UInt.Encodes (h 7) hh := hv 7
  dsimp only [roundStep] at hr ⊢
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16⟩ := hr
  have eCh := UInt.xor.sound (UInt.and.sound h4 h5 r1) (UInt.and.sound (UInt.not_encodes h4) h6 r2) r3
  have eMa := UInt.xor.sound (UInt.xor.sound (UInt.and.sound h0 h1 r4) (UInt.and.sound h0 h2 r5) r7)
    (UInt.and.sound h1 h2 r6) r8
  have eS0 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes h0 2)
    (UInt.rotate_right_encodes h0 13) r9) (UInt.rotate_right_encodes h0 22) r10
  have eS1 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes h4 6)
    (UInt.rotate_right_encodes h4 11) r11) (UInt.rotate_right_encodes h4 25) r12
  have eT0 := UInt.wrapping_add_many.sound (.cons h7 (.cons eS1 (.cons eCh
    (.cons (UInt.constant_encodes (K.getD i 0)) (.cons (forall₂_getD hw (UInt.constant_encodes 0) i)
    .nil))))) (UInt.size_le _ (by simp)) r13
  have eT1 := UInt.wrapping_add_many.sound (.cons eS0 (.cons eMa .nil)) (UInt.size_le _ (by simp)) r14
  have eE := UInt.wrapping_add_many.sound (.cons h3 (.cons eT0 .nil)) (UInt.size_le _ (by simp)) r15
  have eA := UInt.wrapping_add_many.sound (.cons eT0 (.cons eT1 .nil)) (UInt.size_le _ (by simp))
    r16
  simp only [List.foldl_cons, List.foldl_nil, zero_add'] at eT0 eT1 eE eA
  refine ⟨rfl, fun j => ?_⟩
  fin_cases j
  · exact eA
  · exact h0
  · exact h1
  · exact h2
  · exact eE
  · exact h4
  · exact h5
  · exact h6

theorem getD_zipWith {l₁ l₂ : List (BitVec 32)} (h₁ : l₁.length = 8) (h₂ : l₂.length = 8)
    (j : Fin 8) : (List.zipWith (· + ·) l₁ l₂).getD j 0 = l₁.getD j 0 + l₂.getD j 0 := by
  obtain ⟨a, b, c, d, e, f, g, h, rfl⟩ := eq_eight h₁
  obtain ⟨a', b', c', d', e', f', g', h', rfl⟩ := eq_eight h₂
  fin_cases j <;> rfl

theorem schedule_init {data : List (UInt 8)} {B : List _root_.UInt8}
    (hd : List.Forall₂ ByteEnc data B) (hB : B.length = 64) :
    List.Forall₂ UInt.Encodes ((chunks 4 data).map UInt.from_bytes_be) ((chunks 4 B).map word) := by
    have hc := forall₂_and_mem (P := fun c => c.length = 4)
      (chunks_forall₂ (k := 4) (by norm_num) _ le_rfl hd)
      (length_of_mem_chunks (by norm_num) 16 _ (by rw [hB]))
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine hc.imp fun c c' ⟨hcc, hl⟩ => ?_
    obtain ⟨y₀, y₁, y₂, y₃, rfl⟩ : ∃ y₀ y₁ y₂ y₃, c' = [y₀, y₁, y₂, y₃] := by
      match c', hl with
      | [y₀, y₁, y₂, y₃], _ => exact ⟨y₀, y₁, y₂, y₃, rfl⟩
    obtain ⟨b₀, c₁, hb₀, hc₁, rfl⟩ := List.forall₂_cons_right_iff.mp hcc
    obtain ⟨b₁, c₂, hb₁, hc₂, rfl⟩ := List.forall₂_cons_right_iff.mp hc₁
    obtain ⟨b₂, c₃, hb₂, hc₃, rfl⟩ := List.forall₂_cons_right_iff.mp hc₂
    obtain ⟨b₃, c₄, hb₃, hc₄, rfl⟩ := List.forall₂_cons_right_iff.mp hc₃
    obtain rfl := List.forall₂_nil_right_iff.mp hc₄
    exact UInt.from_bytes_be_encodes hb₀ hb₁ hb₂ hb₃

theorem update_state.sound {st : Fin 8 → UInt 32} {H : List (BitVec 32)} {data : List (UInt 8)}
    {B : List _root_.UInt8} {x : BlockWit} (hst : StateEnc st H)
    (hd : List.Forall₂ ByteEnc data B) (hB : B.length = 64) (h : (update_state st data x).2) :
    StateEnc (update_state st data x).1 (compress H B) := by
  dsimp only [update_state] at h ⊢
  obtain ⟨hs, hr, hf⟩ := h
  have hw := loop_sound (Q := (· = ·)) (S := List.Forall₂ UInt.Encodes) (spec := scheduleStep)
    (by rintro i _ w W y rfl hwW hy; exact schedStep.sound hwW hy) (forall₂_refl _)
    (schedule_init hd hB) hs
  have hv := loop_sound (Q := (· = ·)) (S := StateEnc) (spec := round (schedule B))
    (by rintro i _ h v y rfl hv hy; exact roundStep.sound hw hv hy) (forall₂_refl _) hst hr
  obtain ⟨hlen, hv⟩ := hv
  obtain ⟨hHlen, hst'⟩ := hst
  refine ⟨by simp [compress, hHlen, hlen], fun j => ?_⟩
  have := UInt.wrapping_add_many.sound (.cons (hst' j) (.cons (hv j) .nil))
    (UInt.size_le _ (by simp)) (hf j)
  simp only [List.foldl_cons, List.foldl_nil, zero_add'] at this
  rw [compress, getD_zipWith hHlen hlen]
  exact this

/-! ### The blocks `digest` compresses -/

/-- The constant bytes `finalize` appends to an `n`-byte message. -/
def gpad (n : ℕ) : List (UInt 8) := (padding n).map fun b => UInt.constant b.toBitVec

theorem updateChunks_full :
    ∀ (cs ds : List (List (UInt 8))) (s : Buffer), (∀ c ∈ cs, c.length = 64) →
      updateChunks (cs ++ ds) s =
        ((updateChunks ds ⟨s.completed_data_blocks + cs.length, s.pending, s.num_pending⟩).1,
          cs ++ (updateChunks ds ⟨s.completed_data_blocks + cs.length, s.pending, s.num_pending⟩).2)
  | [], ds, ⟨n, p, k⟩, _ => by simp
  | c :: cs, ds, ⟨n, p, k⟩, h => by
    simp only [List.cons_append, updateChunks, h c (by simp), if_true]
    rw [updateChunks_full cs ds _ (fun c hc => h c (by simp [hc]))]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem length_chunks {α : Type} {k : ℕ} (hk : 0 < k) :
    ∀ (q : ℕ) (l : List α), l.length = k * q → (chunks k l).length = q
  | 0, l, h => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    rfl
  | q + 1, l, h => by
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil (l := l) (by rintro rfl; simp at h; nlinarith)
    rw [chunks_cons hk, List.length_cons,
      length_chunks hk q _ (by simp at h ⊢; rw [Nat.mul_succ] at h; omega)]

theorem update_default (data : List (UInt 8)) :
    update Buffer.default data =
      (⟨data.length / 64, data.drop (64 * (data.length / 64)) ++
          (List.replicate 64 (UInt.constant 0)).drop (data.length % 64), data.length % 64⟩,
        chunks 64 (data.take (64 * (data.length / 64)))) := by
  have hfull : (data.take (64 * (data.length / 64))).length = 64 * (data.length / 64) := by
    simp only [List.length_take]; omega
  have hrem : (data.drop (64 * (data.length / 64))).length = data.length % 64 := by
    simp only [List.length_drop]; omega
  unfold update
  rw [if_neg (by simp [Buffer.default])]
  conv_lhs => rw [← List.take_append_drop (64 * (data.length / 64)) data]
  rw [chunks_append (by norm_num) _ _ _ hfull,
    updateChunks_full _ _ _ (length_of_mem_chunks (by norm_num) _ _ hfull),
    length_chunks (by norm_num) _ _ hfull]
  simp only [Buffer.default, Nat.zero_add]
  by_cases hm : data.length % 64 = 0
  · have : data.drop (64 * (data.length / 64)) = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this, hm]; simp [updateChunks]
  · rw [chunks_of_length_le (by norm_num) (by intro h; rw [h] at hrem; simp at hrem; omega)
      (by omega)]
    simp [updateChunks, hrem, show data.length % 64 ≠ 64 by omega]

theorem length_gpad (n : ℕ) : (gpad n).length = (119 - n % 64) % 64 + 9 := by
  simp only [gpad, padding, List.length_map, List.length_cons, List.length_append,
    List.length_replicate, length_be64]

theorem finalize_slice (q m : ℕ) (hm : m < 64) :
    (((List.replicate 72 (UInt.constant 0)).set 0 (UInt.constant 0x80)).take
        (if m < 56 then 56 - m else 120 - m) ++
      (be64 (q * 512 + m * 8)).map (fun b : _root_.UInt8 => UInt.constant b.toBitVec) ++
      ((List.replicate 72 (UInt.constant 0)).set 0 (UInt.constant 0x80)).drop
        ((if m < 56 then 56 - m else 120 - m) + 8)).take
      ((if m < 56 then 56 - m else 120 - m) + 8) = gpad (64 * q + m) := by
  set o := if m < 56 then 56 - m else 120 - m with ho
  clear_value o
  have ho1 : 1 ≤ o := by rw [ho]; split <;> omega
  have ho2 : o ≤ 64 := by rw [ho]; split <;> omega
  have hk : (119 - (64 * q + m) % 64) % 64 = o - 1 := by rw [ho]; split <;> omega
  have hp : (List.replicate 72 (UInt.constant 0)).set 0 (UInt.constant 0x80) =
      UInt.constant 0x80 :: List.replicate 71 (UInt.constant 0 : UInt 8) := rfl
  obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
  rw [hp, List.take_succ_cons, List.take_replicate, Nat.min_eq_left (by omega),
    List.take_left' (by simp only [List.length_cons, List.length_append, List.length_replicate,
      List.length_map, length_be64])]
  simp only [gpad, padding, hk, Nat.add_sub_cancel, List.map_cons, List.map_append,
    List.map_replicate, List.cons_append]
  rw [show 8 * (64 * q + m) = q * 512 + m * 8 by ring]
  rfl

theorem finalize_eq (q m : ℕ) (rem P : List (UInt 8)) (hm : m < 64) (hrem : rem.length = m)
    (hP : P.take m = rem) : finalize ⟨q, P, m⟩ = chunks 64 (rem ++ gpad (64 * q + m)) := by
  unfold finalize
  simp only []
  rw [finalize_slice q m hm]
  have hlen := length_gpad (64 * q + m)
  rw [show (64 * q + m) % 64 = m by omega] at hlen
  unfold update
  simp only [hlen]
  by_cases h0 : m = 0
  · subst h0
    obtain rfl : rem = [] := List.eq_nil_of_length_eq_zero hrem
    simp only [Nat.add_zero] at hlen ⊢
    rw [if_neg (by omega), List.nil_append]
    rw [chunks_of_length_le (by norm_num) (by intro h; rw [h] at hlen; simp at hlen) (by omega)]
    simp [updateChunks, hlen]
  · rw [if_pos (by omega), hP]
    by_cases h56 : m < 56
    · have : (gpad (64 * q + m)).drop (64 - m) = [] := List.drop_eq_nil_of_le (by omega)
      rw [this, chunks_nil, List.take_of_length_le (by omega),
        chunks_of_length_le (by norm_num) (by simp [← List.length_pos_iff]; omega)
          (by simp [hrem]; omega)]
      rfl
    · have hd : ((gpad (64 * q + m)).drop (64 - m)).length = 64 := by simp; omega
      have hne : (gpad (64 * q + m)).drop (64 - m) ≠ [] := by intro h; rw [h] at hd; simp at hd
      rw [chunks_of_length_le (by norm_num) hne (by omega)]
      simp only [updateChunks, hd, if_true]
      rw [chunks_eq_cons (by norm_num) (by
          intro h; have := congrArg List.length h
          simp only [List.length_append, hlen, List.length_nil] at this; omega),
        List.take_append, List.drop_append, List.take_of_length_le (l := rem) (by omega),
        List.drop_eq_nil_of_le (as := rem) (by omega), List.nil_append, hrem,
        chunks_of_length_le (by norm_num) hne (by omega)]

theorem blocks_eq (data : List (UInt 8)) :
    digest.blocks data = chunks 64 (data ++ gpad data.length) := by
  unfold digest.blocks
  simp only [update_default]
  rw [finalize_eq _ _ (data.drop (64 * (data.length / 64))) _ (by omega)
    (by simp only [List.length_drop]; omega)
    (by rw [List.take_left' (by simp only [List.length_drop]; omega)]),
    ← chunks_append (by norm_num) (data.length / 64) _ _ (by simp only [List.length_take]; omega),
    ← List.append_assoc, List.take_append_drop]
  congr 3
  omega

theorem gpad_enc (n : ℕ) : List.Forall₂ ByteEnc (gpad n) (padding n) := by
  rw [gpad, List.forall₂_map_left_iff]
  exact List.forall₂_same.mpr fun b _ => UInt.constant_encodes b.toBitVec

/-! ### The digest -/

theorem bytes_enc {u : UInt 32} {x : BitVec 32} (h : UInt.Encodes u x) :
    List.Forall₂ ByteEnc (UInt.to_bytes_be u) (bytesOfWord x) := by
  rw [bytesOfWord, List.forall₂_map_right_iff]
  exact UInt.to_bytes_be_encodes h

theorem output_enc {st : Fin 8 → UInt 32} {H : List (BitVec 32)} (h : StateEnc st H) :
    List.Forall₂ ByteEnc ((List.finRange 8).flatMap fun j => UInt.to_bytes_be (st j))
      (H.flatMap bytesOfWord) := by
  obtain ⟨hl, h⟩ := h
  obtain ⟨a, b, c, d, e, f, g, hh, rfl⟩ := eq_eight hl
  refine forall₂_flatMap (P := fun j x => UInt.Encodes (st j) x) ?_ fun j x hx => bytes_enc hx
  rw [show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  exact .cons (h 0) (.cons (h 1) (.cons (h 2) (.cons (h 3) (.cons (h 4) (.cons (h 5) (.cons (h 6)
    (.cons (h 7) .nil)))))))

theorem initial_enc : StateEnc (fun j => UInt.constant (H₀.getD j 0)) H₀ :=
  ⟨rfl, fun _ => UInt.constant_encodes _⟩

theorem blocks_enc {data : List (UInt 8)} {msg : List _root_.UInt8}
    (hd : List.Forall₂ ByteEnc data msg) :
    List.Forall₂ (fun blk B => List.Forall₂ ByteEnc blk B ∧ B.length = 64) (digest.blocks data)
      (chunks 64 (pad msg)) := by
  have hpad : List.Forall₂ ByteEnc (data ++ gpad data.length) (pad msg) := by
    rw [pad, ← hd.length_eq]; exact List.rel_append hd (gpad_enc _)
  rw [blocks_eq]
  exact forall₂_and_mem (P := fun B => B.length = 64)
    (chunks_forall₂ (k := 64) (by norm_num) _ le_rfl hpad)
    (length_of_mem_chunks (by norm_num) _ _ (length_pad msg))

/-- The gadget's digest bytes are SHA-256 of the message bytes. -/
theorem digest.sound {data : List (UInt 8)} {msg : List _root_.UInt8} {xs : List BlockWit}
    (hd : List.Forall₂ ByteEnc data msg) (h : (digest data xs).2) :
    List.Forall₂ ByteEnc (digest data xs).1 (hash msg) :=
  output_enc (loop_sound (S := StateEnc) (spec := compress)
    (by rintro blk B st H y ⟨hq, hB⟩ hst hy; exact update_state.sound hst hq hB hy)
    (blocks_enc hd) initial_enc h)

/-! ### Completeness -/

/-- The witnesses arkworks assigns in `schedStep`. -/
def schedStep.wit (i : ℕ) (w : List (UInt 32)) : SchedWit :=
  let a := w.getD (i - 15) (UInt.constant 0)
  let s0x := UInt.xor.wit (UInt.rotate_right a 7) (UInt.rotate_right a 18)
  let s0 := UInt.xor.wit (UInt.xor (UInt.rotate_right a 7) (UInt.rotate_right a 18) s0x) (UInt.shr a 3)
  let b := w.getD (i - 2) (UInt.constant 0)
  let s1x := UInt.xor.wit (UInt.rotate_right b 17) (UInt.rotate_right b 19)
  let s1 := UInt.xor.wit (UInt.xor (UInt.rotate_right b 17) (UInt.rotate_right b 19) s1x)
    (UInt.shr b 10)
  ⟨s0x, s0, s1x, s1, UInt.wrapping_add_many.wit [w.getD (i - 16) (UInt.constant 0),
    UInt.xor (UInt.xor (UInt.rotate_right a 7) (UInt.rotate_right a 18) s0x) (UInt.shr a 3) s0,
    w.getD (i - 7) (UInt.constant 0),
    UInt.xor (UInt.xor (UInt.rotate_right b 17) (UInt.rotate_right b 19) s1x) (UInt.shr b 10) s1]⟩

theorem schedStep.complete {i : ℕ} {w : List (UInt 32)} {W : List (BitVec 32)}
    (hw : List.Forall₂ UInt.Encodes w W) : (schedStep i w (schedStep.wit i w)).2 := by
  have get := forall₂_getD hw (UInt.constant_encodes 0)
  have e0 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes (get (i - 15)) 7)
    (UInt.rotate_right_encodes (get (i - 15)) 18) (UInt.xor.complete _ _))
    (UInt.shr_encodes (get (i - 15)) 3) (UInt.xor.complete _ _)
  have e1 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes (get (i - 2)) 17)
    (UInt.rotate_right_encodes (get (i - 2)) 19) (UInt.xor.complete _ _))
    (UInt.shr_encodes (get (i - 2)) 10) (UInt.xor.complete _ _)
  dsimp only [schedStep, schedStep.wit]
  exact ⟨UInt.xor.complete _ _, UInt.xor.complete _ _, UInt.xor.complete _ _, UInt.xor.complete _ _,
    UInt.wrapping_add_many.complete (.cons (get _) (.cons e0 (.cons (get _) (.cons e1 .nil))))
      (UInt.size_le _ (by simp))⟩

/-- The witnesses arkworks assigns in `roundStep`. -/
def roundStep.wit (w : List (UInt 32)) (i : ℕ) (h : Fin 8 → UInt 32) : RoundWit :=
  let ch₁w := UInt.and.wit (h 4) (h 5)
  let ch₁ := UInt.and (h 4) (h 5) ch₁w
  let ch₂w := UInt.and.wit (UInt.not (h 4)) (h 6)
  let ch₂ := UInt.and (UInt.not (h 4)) (h 6) ch₂w
  let chw := UInt.xor.wit ch₁ ch₂
  let ch := UInt.xor ch₁ ch₂ chw
  let ma₁w := UInt.and.wit (h 0) (h 1)
  let ma₁ := UInt.and (h 0) (h 1) ma₁w
  let ma₂w := UInt.and.wit (h 0) (h 2)
  let ma₂ := UInt.and (h 0) (h 2) ma₂w
  let ma₃w := UInt.and.wit (h 1) (h 2)
  let ma₃ := UInt.and (h 1) (h 2) ma₃w
  let ma₄w := UInt.xor.wit ma₁ ma₂
  let ma₄ := UInt.xor ma₁ ma₂ ma₄w
  let maw := UInt.xor.wit ma₄ ma₃
  let ma := UInt.xor ma₄ ma₃ maw
  let s0xw := UInt.xor.wit (UInt.rotate_right (h 0) 2) (UInt.rotate_right (h 0) 13)
  let s0x := UInt.xor (UInt.rotate_right (h 0) 2) (UInt.rotate_right (h 0) 13) s0xw
  let s0w := UInt.xor.wit s0x (UInt.rotate_right (h 0) 22)
  let s0 := UInt.xor s0x (UInt.rotate_right (h 0) 22) s0w
  let s1xw := UInt.xor.wit (UInt.rotate_right (h 4) 6) (UInt.rotate_right (h 4) 11)
  let s1x := UInt.xor (UInt.rotate_right (h 4) 6) (UInt.rotate_right (h 4) 11) s1xw
  let s1w := UInt.xor.wit s1x (UInt.rotate_right (h 4) 25)
  let s1 := UInt.xor s1x (UInt.rotate_right (h 4) 25) s1w
  let t0ops := [h 7, s1, ch, UInt.constant (K.getD i 0), w.getD i (UInt.constant 0)]
  let t0w := UInt.wrapping_add_many.wit t0ops
  let t0 := UInt.wrapping_add_many t0ops t0w
  let t1w := UInt.wrapping_add_many.wit [s0, ma]
  let t1 := UInt.wrapping_add s0 ma t1w
  ⟨ch₁w, ch₂w, chw, ma₁w, ma₂w, ma₃w, ma₄w, maw, s0xw, s0w, s1xw, s1w, t0w, t1w,
    UInt.wrapping_add_many.wit [h 3, t0], UInt.wrapping_add_many.wit [t0, t1]⟩

theorem roundStep.complete {w : List (UInt 32)} {W : List (BitVec 32)} {i : ℕ}
    {h : Fin 8 → UInt 32} {v : List (BitVec 32)} (hw : List.Forall₂ UInt.Encodes w W)
    (hv : StateEnc h v) : (roundStep w i h (roundStep.wit w i h)).2 := by
  obtain ⟨hlen, hv⟩ := hv
  obtain ⟨a, b, c, d, e, f, g, hh, rfl⟩ := eq_eight hlen
  have h0 : UInt.Encodes (h 0) a := hv 0
  have h1 : UInt.Encodes (h 1) b := hv 1
  have h2 : UInt.Encodes (h 2) c := hv 2
  have h3 : UInt.Encodes (h 3) d := hv 3
  have h4 : UInt.Encodes (h 4) e := hv 4
  have h5 : UInt.Encodes (h 5) f := hv 5
  have h6 : UInt.Encodes (h 6) g := hv 6
  have h7 : UInt.Encodes (h 7) hh := hv 7
  have eCh := UInt.xor.sound (UInt.and.sound h4 h5 (UInt.and.complete _ _))
    (UInt.and.sound (UInt.not_encodes h4) h6 (UInt.and.complete _ _)) (UInt.xor.complete _ _)
  have eMa := UInt.xor.sound (UInt.xor.sound (UInt.and.sound h0 h1 (UInt.and.complete _ _))
    (UInt.and.sound h0 h2 (UInt.and.complete _ _)) (UInt.xor.complete _ _))
    (UInt.and.sound h1 h2 (UInt.and.complete _ _)) (UInt.xor.complete _ _)
  have eS0 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes h0 2)
    (UInt.rotate_right_encodes h0 13) (UInt.xor.complete _ _)) (UInt.rotate_right_encodes h0 22)
    (UInt.xor.complete _ _)
  have eS1 := UInt.xor.sound (UInt.xor.sound (UInt.rotate_right_encodes h4 6)
    (UInt.rotate_right_encodes h4 11) (UInt.xor.complete _ _)) (UInt.rotate_right_encodes h4 25)
    (UInt.xor.complete _ _)
  have hT0 := List.Forall₂.cons h7 (.cons eS1 (.cons eCh (.cons (UInt.constant_encodes (K.getD i 0))
    (.cons (forall₂_getD hw (UInt.constant_encodes 0) i) .nil))))
  have eT0 := UInt.wrapping_add_many.sound hT0 (UInt.size_le _ (by simp))
    (UInt.wrapping_add_many.complete hT0 (UInt.size_le _ (by simp)))
  have hT1 := List.Forall₂.cons eS0 (.cons eMa .nil)
  have eT1 := UInt.wrapping_add_many.sound hT1 (UInt.size_le _ (by simp))
    (UInt.wrapping_add_many.complete hT1 (UInt.size_le _ (by simp)))
  dsimp only [roundStep, roundStep.wit]
  exact ⟨UInt.and.complete _ _, UInt.and.complete _ _, UInt.xor.complete _ _,
    UInt.and.complete _ _, UInt.and.complete _ _, UInt.and.complete _ _,
    UInt.xor.complete _ _, UInt.xor.complete _ _, UInt.xor.complete _ _, UInt.xor.complete _ _,
    UInt.xor.complete _ _, UInt.xor.complete _ _,
    UInt.wrapping_add_many.complete hT0 (UInt.size_le _ (by simp)),
    UInt.wrapping_add_many.complete hT1 (UInt.size_le _ (by simp)),
    UInt.wrapping_add_many.complete (.cons h3 (.cons eT0 .nil)) (UInt.size_le _ (by simp)),
    UInt.wrapping_add_many.complete (.cons eT0 (.cons eT1 .nil)) (UInt.size_le _ (by simp))⟩

theorem update_state.complete {st : Fin 8 → UInt 32} {H : List (BitVec 32)}
    {data : List (UInt 8)} {B : List _root_.UInt8} (hst : StateEnc st H)
    (hd : List.Forall₂ ByteEnc data B) (hB : B.length = 64) : ∃ x, (update_state st data x).2 := by
  obtain ⟨sched, hs⟩ := loop_complete (Q := (· = ·)) (S := List.Forall₂ UInt.Encodes)
    (spec := scheduleStep) (step := schedStep)
    (by rintro i _ w W rfl hw
        exact ⟨_, schedStep.complete hw, schedStep.sound hw (schedStep.complete hw)⟩)
    (forall₂_refl (List.range' 16 48)) (schedule_init hd hB)
  have hw := loop_sound (Q := (· = ·)) (S := List.Forall₂ UInt.Encodes) (spec := scheduleStep)
    (by rintro i _ w W y rfl hwW hy; exact schedStep.sound hwW hy) (forall₂_refl _)
    (schedule_init hd hB) hs
  obtain ⟨rounds, hr⟩ := loop_complete (Q := (· = ·)) (S := StateEnc) (spec := round (schedule B))
    (step := roundStep (loop schedStep (List.range' 16 48) sched
      ((chunks 4 data).map UInt.from_bytes_be)).1)
    (by rintro i _ h v rfl hv
        exact ⟨_, roundStep.complete hw hv, roundStep.sound hw hv (roundStep.complete hw hv)⟩)
    (forall₂_refl (List.range 64)) hst
  have hv := loop_sound (Q := (· = ·)) (S := StateEnc) (spec := round (schedule B))
    (by rintro i _ h v y rfl hv hy; exact roundStep.sound hw hv hy) (forall₂_refl _) hst hr
  exact ⟨⟨sched, rounds, fun j => _⟩, hs, hr, fun j =>
    UInt.wrapping_add_many.complete (.cons (hst.2 j) (.cons (hv.2 j) .nil)) (UInt.size_le _ (by simp))⟩

/-- Every message has witnesses satisfying the gadget. -/
theorem digest.complete {data : List (UInt 8)} {msg : List _root_.UInt8}
    (hd : List.Forall₂ ByteEnc data msg) : ∃ xs, (digest data xs).2 :=
  loop_complete (S := StateEnc) (spec := compress)
    (by
      rintro blk B st H ⟨hq, hB⟩ hst
      obtain ⟨x, hx⟩ := update_state.complete hst hq hB
      exact ⟨x, hx, update_state.sound hst hq hB hx⟩)
    (blocks_enc hd) initial_enc

end Sha256Gadget

end Zerc20.Ark

namespace Zerc20.Sha256

theorem getD_append_left {α : Type} (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {α : Type} (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem ofBytesBE_concat (l : List UInt8) (b : UInt8) :
    ofBytesBE (l ++ [b]) = 2 ^ 8 * ofBytesBE l + b.toNat := by
  simp [ofBytesBE, List.foldl_append]

/-- Bit `i` of a big-endian number is bit `i mod 8` of byte `i / 8` from the end. -/
theorem testBit_ofBytesBE (l : List UInt8) (i : ℕ) :
    (ofBytesBE l).testBit i =
      if i / 8 < l.length then (l.getD (l.length - 1 - i / 8) 0).toNat.testBit (i % 8) else false := by
  induction l using List.reverseRecOn generalizing i with
  | nil => simp [ofBytesBE]
  | append_singleton l b ih =>
    rw [ofBytesBE_concat, Nat.testBit_two_pow_mul_add _ (UInt8.toNat_lt b), ih]
    simp only [List.length_append, List.length_singleton]
    by_cases hi : i < 8
    · have : i / 8 = 0 := by omega
      simp only [hi, if_true, this, Nat.mod_eq_of_lt hi, Nat.lt_add_one_iff, Nat.zero_le,
        Nat.add_sub_cancel, Nat.sub_zero]
      rw [getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
    · have h1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have h2 : (i - 8) % 8 = i % 8 := by omega
      simp only [hi, if_false, h1, h2]
      by_cases hl : i / 8 - 1 < l.length
      · rw [if_pos hl, if_pos (by omega), getD_append_left _ _ _ _ (by omega)]
        congr 3; omega
      · rw [if_neg hl, if_neg (by omega)]

end Zerc20.Sha256

/-! ## `hash_chain_var` (zkp/src/primitives.rs) -/

namespace Zerc20.Zkp.primitives

open Zerc20.Ark Zerc20.Sha256

/-- The witnesses of `hash_chain_var`: `to_bits_le`'s for the `k`-th input (`prev`, then the
values), and the SHA-256 blocks'. -/
structure HashChainWit where
  bits : ℕ → FpVar.ToBitsWit
  sha : List Sha256Gadget.BlockWit

/-- The SHA-256 input: each input's `to_bytes_le`, reversed into 32 big-endian bytes. -/
def hash_chain_var.input (inputs : List F) (bits : ℕ → FpVar.ToBitsWit) : List (UInt 8) :=
  (List.ofFn fun k : Fin inputs.length =>
    (FpVar.to_bytes_le (.var inputs[k]) (bits k)).reverse).flatten

/-- `hash_chain_var`, on allocated inputs: both step circuits pass state variables and witnesses.
`input[0] = 0` bounds `prev` below `2^248`, and the result is the digest without its first byte, as
a big-endian number: bit `i` is bit `i mod 8` of byte `31 - i / 8`. -/
def hash_chain_var (prev : F) (values : List F) (w : HashChainWit) : FpVar × Prop :=
  let input := hash_chain_var.input (prev :: values) w.bits
  let digest := Sha256Gadget.digest input w.sha
  let bits : Fin 248 → Boolean := fun i =>
    (digest.1.getD (31 - i / 8) (UInt.constant 0)) ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩
  (Boolean.le_bits_to_fp bits,
    (∀ k : Fin (prev :: values).length,
      FpVar.to_bits_le.Rel (.var (prev :: values)[k]) (w.bits k)) ∧
    UInt.enforce_equal.Rel (input.getD 0 (UInt.constant 0)) (UInt.constant 0) ∧ digest.2)

theorem forall₂_flatten {α β : Type} {R : α → β → Prop} {L₁ : List (List α)} {L₂ : List (List β)}
    (h : List.Forall₂ (List.Forall₂ R) L₁ L₂) : List.Forall₂ R L₁.flatten L₂.flatten := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact List.rel_append hab ih

theorem to_bytes_enc {v : F} {w : FpVar.ToBitsWit} (h : FpVar.to_bits_le.Rel (.var v) w) :
    List.Forall₂ Sha256Gadget.ByteEnc (FpVar.to_bytes_le (.var v) w).reverse (be32 v.val) := by
  rw [be32, List.forall₂_reverse_iff]
  have e : (List.ofFn fun j : Fin 32 => UInt8.ofNat (v.val / 256 ^ (j : ℕ))) =
      (List.ofFn fun j : Fin 32 => BitVec.ofNat 8 (v.val / 256 ^ (j : ℕ))).map UInt8.ofBitVec := by
    rw [List.map_ofFn]; rfl
  rw [e, List.forall₂_map_right_iff]
  exact FpVar.to_bytes_le.sound h

theorem input_enc {inputs : List F} {bits : ℕ → FpVar.ToBitsWit}
    (h : ∀ k : Fin inputs.length, FpVar.to_bits_le.Rel (.var inputs[k]) (bits k)) :
    List.Forall₂ Sha256Gadget.ByteEnc (hash_chain_var.input inputs bits)
      (inputs.flatMap fun v => be32 v.val) := by
  rw [hash_chain_var.input, List.flatMap_def]
  conv_rhs => rw [← List.ofFn_getElem (xs := inputs), List.map_ofFn]
  exact forall₂_flatten (FpVar.forall₂_ofFn fun k => to_bytes_enc (h k))

theorem isConst_of_var {n : ℕ} {u : UInt n} (k : Fin n) (hk : (u k).isConst = false) :
    UInt.isConst u = false := by
  simp only [UInt.isConst, List.all_eq_false]
  exact ⟨k, List.mem_finRange k, by simp [hk]⟩

theorem input_head (prev : F) (values : List F) (bits : ℕ → FpVar.ToBitsWit) :
    (hash_chain_var.input (prev :: values) bits).getD 0 (UInt.constant 0) =
      (FpVar.to_bytes_le (.var prev) (bits 0)).reverse.getD 0 (UInt.constant 0) := by
  rw [hash_chain_var.input, List.ofFn_succ, List.flatten_cons,
    getD_append_left _ _ _ _ (by simp [FpVar.to_bytes_le])]
  rfl

/-- The first input byte has variable bits, so `enforce_equal` constrains it. -/
theorem input_head_isConst (prev : F) (values : List F) (bits : ℕ → FpVar.ToBitsWit) :
    UInt.isConst ((hash_chain_var.input (prev :: values) bits).getD 0 (UInt.constant 0)) = false := by
  rw [input_head]
  apply isConst_of_var 0
  simp [FpVar.to_bytes_le, List.getD_eq_getElem?_getD, FpVar.to_bits_le, FpVar.to_non_unique_bits_le,
    Boolean.isConst]

theorem be32_head (n : ℕ) : (be32 n).getD 0 0 = UInt8.ofNat (n / 256 ^ 31) := by
  simp [be32, List.getD_eq_getElem?_getD]

/-- `prev`'s top byte is zero exactly below `2^248`. -/
theorem top_byte_zero {x : F} : (UInt8.ofNat (x.val / 256 ^ 31)).toBitVec = 0 ↔ x.val < 2 ^ 248 := by
  have hx : x.val < 2 ^ 254 := FpVar.val_lt_two_pow_254 x
  rw [UInt8.toBitVec_ofNat', ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    show (0 : BitVec 8).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

theorem flatMap_be32 (prev : F) (values : List F) :
    (prev.val :: values.map ZMod.val).flatMap be32 = (prev :: values).flatMap fun v => be32 v.val := by
  simp [List.flatMap_map]

theorem length_digest (data : List (UInt 8)) (xs : List Sha256Gadget.BlockWit) :
    (Sha256Gadget.digest data xs).1.length = 32 := by
  simp [Sha256Gadget.digest, UInt.to_bytes_be, UInt.to_bytes_le]

/-- Soundness: the constraints bound `prev` below `2^248` and fix the result to the hash chain. -/
theorem hash_chain_var.sound {prev : F} {values : List F} {w : HashChainWit}
    (h : (hash_chain_var prev values w).2) :
    prev.val < 2 ^ 248 ∧
      (hash_chain_var prev values w).1.val.val = hashChain prev.val (values.map ZMod.val) := by
  obtain ⟨hbits, heq, hsha⟩ := h
  have hin := input_enc hbits
  have h0 := forall₂_getD (d₁ := UInt.constant 0) (d₂ := (0 : _root_.UInt8)) hin
    (UInt.constant_encodes 0) 0
  rw [List.flatMap_cons, getD_append_left _ _ _ _ (by simp [be32]), be32_head] at h0
  refine ⟨top_byte_zero.mp (UInt.enforce_equal.sound (by norm_num) h0 (UInt.constant_encodes 0)
    (input_head_isConst prev values w.bits) heq), ?_⟩
  have hd := Sha256Gadget.digest.sound hin hsha
  have hlen : (Sha256.hash ((prev :: values).flatMap fun v : F => be32 v.val)).length = 32 :=
    hd.length_eq.symm.trans (length_digest _ _)
  set D := Sha256.hash ((prev :: values).flatMap fun v : F => be32 v.val)
  have hbit : ∀ i : Fin 248,
      ((Sha256Gadget.digest (hash_chain_var.input (prev :: values) w.bits) w.sha).1.getD
        (31 - i / 8) (UInt.constant 0) ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩).val =
        bit ((ofBytesBE D).testBit i) := by
    intro i
    have := forall₂_getD (d₁ := UInt.constant 0) (d₂ := (0 : _root_.UInt8)) hd
      (UInt.constant_encodes 0) (31 - i / 8) ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩
    rw [this, testBit_ofBytesBE, hlen, if_pos (by omega), show 32 - 1 - (i : ℕ) / 8 = 31 - i / 8 by omega]
    rfl
  have hval := Boolean.le_bits_to_fp_of_bits hbit
  simp only [hash_chain_var]
  rw [hval, natOfBits_testBit, val_natCast_of_lt
    (lt_trans (Nat.mod_lt _ (by norm_num)) (by have := two_pow_253_lt_r; omega)), hashChain,
    flatMap_be32]

/-- Completeness: below `2^248`, the honest witnesses satisfy the constraints. -/
theorem hash_chain_var.complete {prev : F} {values : List F} (hprev : prev.val < 2 ^ 248) :
    ∃ w, (hash_chain_var prev values w).2 := by
  let bits : ℕ → FpVar.ToBitsWit := fun k => FpVar.to_bits_le.wit (.var ((prev :: values).getD k 0))
  have hbits : ∀ k : Fin (prev :: values).length,
      FpVar.to_bits_le.Rel (.var (prev :: values)[k]) (bits k) := by
    intro k
    show FpVar.to_bits_le.Rel _ (FpVar.to_bits_le.wit (.var ((prev :: values).getD k 0)))
    rw [show (prev :: values).getD k 0 = (prev :: values)[k] by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k.isLt]]
    exact FpVar.to_bits_le.complete _
  have hin := input_enc hbits
  obtain ⟨xs, hxs⟩ := Sha256Gadget.digest.complete hin
  refine ⟨⟨bits, xs⟩, hbits, ?_, hxs⟩
  have h0 := forall₂_getD (d₁ := UInt.constant 0) (d₂ := (0 : _root_.UInt8)) hin
    (UInt.constant_encodes 0) 0
  rw [List.flatMap_cons, getD_append_left _ _ _ _ (by simp [be32]), be32_head] at h0
  exact UInt.enforce_equal.complete (h0.of_eq (top_byte_zero.mpr hprev)) (UInt.constant_encodes 0)

end Zerc20.Zkp.primitives

