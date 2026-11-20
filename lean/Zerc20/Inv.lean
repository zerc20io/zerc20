import Zerc20.Hyp
import Zerc20.Frame

/-!
# Invariants of a run

What every state of a run satisfies under the run's hypotheses: the ledger's hash chain, checkpoints
and proved roots are the canonical ones of its leaves; every note leaf has the opening that
committed it; every spent position is opened by a key whose nullifier is spent; and every token's
underlying covers its supply and the notes committed, less what spends consumed.
-/

namespace Zerc20

open scoped Classical

noncomputable section

/-! ## Values below the field -/

theorem two_pow_le_r {n : ℕ} (hn : n ≤ 253) : 2 ^ n < r := by
  calc 2 ^ n ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) hn
    _ < r := by unfold r; norm_num

theorem amount_lt_r : AMOUNT_BOUND < r := two_pow_le_r (by norm_num)
theorem address_lt_r : ADDRESS_BOUND < r := two_pow_le_r (by norm_num)
theorem address_le_amount : ADDRESS_BOUND ≤ AMOUNT_BOUND := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem val_cast {a : ℕ} (ha : a < r) : ((a : F)).val = a := ZMod.val_cast_of_lt ha

theorem cast_inj {a b : ℕ} (ha : a < r) (hb : b < r) : (a : F) = b ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem field0_lt {tag t : ℕ} (htag : tag < 2 ^ 32) (ht : t < TOKEN_BOUND) :
    field0 tag t < 2 ^ 64 := by
  unfold field0 TOKEN_BOUND at *
  calc tag * 2 ^ 32 + t < tag * 2 ^ 32 + 2 ^ 32 := by omega
    _ = (tag + 1) * 2 ^ 32 := by ring
    _ ≤ 2 ^ 32 * 2 ^ 32 := Nat.mul_le_mul_right _ htag
    _ = 2 ^ 64 := by norm_num

theorem field0_lt_r {tag t : ℕ} (htag : tag < 2 ^ 32) (ht : t < TOKEN_BOUND) : field0 tag t < r :=
  (field0_lt htag ht).trans (two_pow_le_r (by norm_num))

theorem field0_inj {tag t tag' t' : ℕ} (ht : t < TOKEN_BOUND) (ht' : t' < TOKEN_BOUND)
    (he : field0 tag t = field0 tag' t') : tag = tag' ∧ t = t' := by
  unfold field0 TOKEN_BOUND at *
  omega

theorem TRANSFER_TAG_lt : TRANSFER_TAG < 2 ^ 32 := by unfold TRANSFER_TAG; norm_num
theorem NOTE_HASH_TAG_lt : NOTE_HASH_TAG < 2 ^ 32 := by unfold NOTE_HASH_TAG; norm_num
theorem TAGS_ne : TRANSFER_TAG ≠ NOTE_HASH_TAG := by unfold TRANSFER_TAG NOTE_HASH_TAG; norm_num

/-! ## Hash chains -/

section chains

variable (h : Hashes)

theorem chainCalls_append (c : ℕ) (xs : List (List ℕ)) (x : List ℕ) :
    chainCalls h c (xs ++ [x]) = chainCalls h c xs ∪ {(xs.foldl h.hc c, x)} := by
  induction xs generalizing c with
  | nil => simp [chainCalls]
  | cons y ys ih => simp [chainCalls, ih]

/-- Two hash chains of the same length that end at the same value, with no collision among their
inputs, start at the same value and absorb the same inputs. -/
theorem chain_inj (S : Set (ℕ × List ℕ)) (hinj : ∀ p ∈ S, ∀ q ∈ S, h.hc p.1 p.2 = h.hc q.1 q.2 → p = q) :
    ∀ (xs ys : List (List ℕ)) (a b : ℕ), xs.length = ys.length →
      chainCalls h a xs ⊆ S → chainCalls h b ys ⊆ S → xs.foldl h.hc a = ys.foldl h.hc b →
      a = b ∧ xs = ys := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
    intro ys a b hl _ _ he
    cases ys with
    | nil => exact ⟨by simpa using he, rfl⟩
    | cons _ _ => simp at hl
  | append_singleton xs x ih =>
    intro ys a b hl hx hy he
    induction ys using List.reverseRecOn with
    | nil => simp at hl
    | append_singleton ys y _ =>
      simp only [List.length_append, List.length_singleton, add_left_inj] at hl
      rw [chainCalls_append] at hx hy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at he
      have hp := hinj _ (hx (Or.inr rfl)) _ (hy (Or.inr rfl)) he
      simp only [Prod.mk.injEq] at hp
      obtain ⟨hab, hxy⟩ := ih ys a b hl (fun p hp => hx (Or.inl hp)) (fun p hp => hy (Or.inl hp))
        hp.1
      exact ⟨hab, by rw [hxy, hp.2]⟩

theorem chainCalls_foldl_append (c : ℕ) (xs ys : List (List ℕ)) :
    chainCalls h c (xs ++ ys) = chainCalls h c xs ∪ chainCalls h (xs.foldl h.hc c) ys := by
  induction xs generalizing c with
  | nil => simp [chainCalls]
  | cons y ys' ih => simp [chainCalls, ih, Set.insert_union]

end chains

/-! ## Ledger leaves -/

section leaves

variable (h : Hashes)

/-- The leaves' tree. -/
def hashes (ls : List Leaf) : List F := ls.map (Leaf.hash h)

theorem chainOf_append (ls : List Leaf) (l : Leaf) :
    chainOf h (ls ++ [l]) = h.hc (chainOf h ls) l.words := by
  simp [chainOf]

theorem chainOf_eq_foldl (ls : List Leaf) : chainOf h ls = (ls.map Leaf.words).foldl h.hc 0 := by
  simp [chainOf, List.foldl_map]

/-- A ledger leaf as `ZERC20` builds it: ranges checked, real accounts, non-zero transfers. -/
def Leaf.Valid : Leaf → Prop
  | .transfer t a b v =>
    t < TOKEN_BOUND ∧ a ≠ 0 ∧ a < ADDRESS_BOUND ∧ b ≠ 0 ∧ b < ADDRESS_BOUND ∧ v ≠ 0 ∧
      v < AMOUNT_BOUND
  | .note t _ => t < TOKEN_BOUND

/-- A valid leaf's fields, read back from the field elements the circuits hash. -/
theorem words_note {l : Leaf} (hl : l.Valid) {t : ℕ} {nh : F} (ht : t < TOKEN_BOUND)
    (he : (l.words.map (↑) : List F) = [↑(field0 NOTE_HASH_TAG t), nh, 0, 0]) :
    l = .note t nh := by
  cases l with
  | transfer t' a b v =>
    simp only [Leaf.words, List.map_cons, List.map_nil, List.cons.injEq] at he
    have := (cast_inj (field0_lt_r TRANSFER_TAG_lt hl.1) (field0_lt_r NOTE_HASH_TAG_lt ht)).mp he.1
    exact absurd (field0_inj hl.1 ht this).1 TAGS_ne
  | note t' nh' =>
    simp only [Leaf.words, List.map_cons, List.map_nil, List.cons.injEq,
      ZMod.natCast_zmod_val] at he
    have := (cast_inj (field0_lt_r NOTE_HASH_TAG_lt hl) (field0_lt_r NOTE_HASH_TAG_lt ht)).mp he.1
    rw [(field0_inj hl ht this).2, he.2.1]

theorem words_transfer {l : Leaf} (hl : l.Valid) {t : ℕ} {a b v : F} (ht : t < TOKEN_BOUND)
    (he : (l.words.map (↑) : List F) = [↑(field0 TRANSFER_TAG t), a, b, v]) :
    ∃ a' b' v', l = .transfer t a' b' v' ∧ (a' : F) = a ∧ (b' : F) = b ∧ (v' : F) = v := by
  cases l with
  | transfer t' a' b' v' =>
    simp only [Leaf.words, List.map_cons, List.map_nil, List.cons.injEq] at he
    have := (cast_inj (field0_lt_r TRANSFER_TAG_lt hl.1) (field0_lt_r TRANSFER_TAG_lt ht)).mp he.1
    exact ⟨a', b', v', by rw [(field0_inj hl.1 ht this).2], he.2.1, he.2.2.1, he.2.2.2.1⟩
  | note t' nh' =>
    simp only [Leaf.words, List.map_cons, List.map_nil, List.cons.injEq] at he
    have := (cast_inj (field0_lt_r NOTE_HASH_TAG_lt hl) (field0_lt_r TRANSFER_TAG_lt ht)).mp he.1
    exact absurd (field0_inj hl ht this).1 TAGS_ne.symm

end leaves

/-! ## The invariant -/

section inv

variable {h : Hashes} {E : Env} {A : Attest} (R : Run h E A)

/-- The key `(akh, nk)` opens ledger position `j`: the note there belongs to its public key, or
the transfer there pays a burn address the key derives. -/
def Opens (s : State) (j : ℕ) (akh nk : F) : Prop :=
  [DOMAIN_PUBLIC_KEY, akh, nk] ∈ R.calls ∧
    ((∃ t nh o, s.ledger.leaves[j]? = some (.note t nh) ∧ s.ghost.notes j = some o ∧
        o.pk = publicKey h akh nk) ∨
      (∃ t a v salt, s.ledger.leaves[j]? =
          some (.transfer t a (addressOf (burnDigest h E.chain (publicKey h akh nk) salt)) v) ∧
        (E.chain, publicKey h akh nk, salt) ∈ R.openings))

/-- The value of the note at position `j`, if it is one of token `t`. -/
def noteValueAt (s : State) (t j : ℕ) : ℕ :=
  match s.ledger.leaves[j]?, s.ghost.notes j with
  | some (.note t' _), some o => if t' = t then o.value.val else 0
  | _, _ => 0

/-- What spending position `j` consumes of token `t`: the note's value or the deposit. -/
def leafValueAt (s : State) (t j : ℕ) : ℕ :=
  match s.ledger.leaves[j]? with
  | some (.transfer t' _ _ v) => if t' = t then v else 0
  | _ => noteValueAt s t j

/-- The value of every note of `t` committed so far. -/
def created (s : State) (t : ℕ) : ℕ := ((List.range s.ledger.leaves.length).map (noteValueAt s t)).sum

/-- The value of every input of `t` spent so far. -/
def consumed (s : State) (t : ℕ) : ℕ := (s.ghost.spent.map (leafValueAt s t)).sum

/-- What the ledger's transfers paid to `a` in token `t`. -/
def deposits (s : State) (t : ℕ) (a : Addr) : ℕ :=
  (s.ledger.leaves.map fun l => match l with
    | .transfer t' _ b v => if t' = t ∧ b = a then v else 0
    | .note .. => 0).sum

structure Inv (s : State) : Prop where
  registered : ∀ t, s.tokens t ≠ none → t ≠ 0 ∧ t < TOKEN_BOUND
  head : s.ledger.head = chainOf h s.ledger.leaves
  cap : s.ledger.leaves.length ≤ TREE_SIZE
  checkpoints : ∀ i, s.ledger.checkpoints i ≠ 0 →
    i ≤ s.ledger.leaves.length ∧ s.ledger.checkpoints i = chainOf h (s.ledger.leaves.take i)
  proved : ∀ i ρ, s.ledger.provedIn i ρ ≠ 0 →
    i ≤ s.ledger.leaves.length ∧ ρ = treeRoot h (hashes h (s.ledger.leaves.take i))
  rootState : s.ledger.rootState.index ≤ s.ledger.leaves.length ∧
    s.ledger.rootState.chain = chainOf h (s.ledger.leaves.take s.ledger.rootState.index) ∧
    s.ledger.rootState.root = treeRoot h (hashes h (s.ledger.leaves.take s.ledger.rootState.index))
  valid : ∀ l ∈ s.ledger.leaves, Leaf.Valid l ∧ s.tokens l.token ≠ none
  notes : ∀ j (t : ℕ) nh, s.ledger.leaves[j]? = some (.note t nh) →
    ∃ o, s.ghost.notes j = some o ∧ nh = noteHash h E.chain o.pk o.value (t : F) o.salt ∧
      o.value.val < AMOUNT_BOUND ∧ [DOMAIN_NOTE, E.chain, o.pk, o.value, (t : F), o.salt] ∈ R.calls
  nodup : s.ghost.spent.Nodup
  spent : ∀ j ∈ s.ghost.spent, j < s.ledger.leaves.length ∧
    ∃ akh nk, Opens R s j akh nk ∧ nullifier h E.chain j nk ∈ s.verifier.used
  books : ∀ t tk, s.tokens t = some tk → tk.Books ∧
    tk.supply + created s t ≤ tk.underlying + consumed s t ∧
    ∀ a ∈ R.burnAddrs, deposits s t a ≤ tk.bal a

theorem Inv.init (p : Addr) : Inv R (State.init h p) where
  registered t ht := by simp [State.init] at ht
  head := rfl
  cap := by simp [State.init]
  checkpoints i hi := by simp [State.init] at hi
  proved i ρ hi := by
    simp only [State.init, ne_eq, ite_eq_right_iff, Classical.not_imp] at hi
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hi
    simp [hashes]
  rootState := by simp [State.init, chainOf, hashes]
  valid l hl := by simp [State.init] at hl
  notes j t nh hj := by simp [State.init] at hj
  nodup := List.nodup_nil
  spent j hj := by simp [State.init] at hj
  books t tk ht := by simp [State.init] at ht

/-! ### Extending the ledger -/

section extend

variable {R} {s s' : State} {new : List Leaf}

/-- `s'` extends `s`: leaves appended, and the earlier positions' openings kept. -/
structure Extends (s s' : State) (new : List Leaf) : Prop where
  leaves : s'.ledger.leaves = s.ledger.leaves ++ new
  notes : ∀ j < s.ledger.leaves.length, s'.ghost.notes j = s.ghost.notes j

theorem Extends.getElem? (he : Extends s s' new) {j : ℕ} (hj : j < s.ledger.leaves.length) :
    s'.ledger.leaves[j]? = s.ledger.leaves[j]? := by
  rw [he.leaves, List.getElem?_append_left hj]

theorem Extends.noteValueAt (he : Extends s s' new) {t j : ℕ} (hj : j < s.ledger.leaves.length) :
    noteValueAt s' t j = noteValueAt s t j := by
  unfold Zerc20.noteValueAt; rw [he.getElem? hj, he.notes j hj]

theorem Extends.leafValueAt (he : Extends s s' new) {t j : ℕ} (hj : j < s.ledger.leaves.length) :
    leafValueAt s' t j = leafValueAt s t j := by
  unfold Zerc20.leafValueAt; rw [he.getElem? hj, he.noteValueAt hj]

theorem Extends.opens (he : Extends s s' new) {j : ℕ} (hj : j < s.ledger.leaves.length) {akh nk : F} :
    Opens R s' j akh nk ↔ Opens R s j akh nk := by
  unfold Opens; rw [he.getElem? hj, he.notes j hj]

theorem Extends.created (he : Extends s s' new) (t : ℕ) :
    Zerc20.created s' t = Zerc20.created s t +
      ((List.range new.length).map fun k => Zerc20.noteValueAt s' t (s.ledger.leaves.length + k)).sum := by
  unfold Zerc20.created
  rw [he.leaves, List.length_append, List.range_add, List.map_append, List.sum_append,
    List.map_map]
  congr 1
  apply congrArg
  apply List.map_congr_left
  intro j hj
  exact he.noteValueAt (List.mem_range.mp hj)

theorem Extends.consumed (he : Extends s s' new) (t : ℕ) (hsp : s'.ghost.spent = s.ghost.spent ++ js)
    (hlt : ∀ j ∈ s.ghost.spent, j < s.ledger.leaves.length) :
    Zerc20.consumed s' t = Zerc20.consumed s t + (js.map (Zerc20.leafValueAt s' t)).sum := by
  unfold Zerc20.consumed
  rw [hsp, List.map_append, List.sum_append]
  congr 1
  apply congrArg
  apply List.map_congr_left
  intro j hj
  exact he.leafValueAt (hlt j hj)

theorem Extends.deposits (he : Extends s s' new) (t : ℕ) (a : Addr) :
    Zerc20.deposits s' t a = Zerc20.deposits s t a + Zerc20.deposits { s with ledger :=
      { s.ledger with leaves := new } } t a := by
  simp [Zerc20.deposits, he.leaves]

theorem Extends.refl (s' : State) (hl : s'.ledger.leaves = s.ledger.leaves)
    (hn : s'.ghost.notes = s.ghost.notes) : Extends s s' [] :=
  ⟨by simp [hl], fun j _ => by rw [hn]⟩

end extend

/-! ### What the hashes of a run bind -/

section bind

variable {R} {S : Set (List F)} {O : Set (F × F × F)} {s : State}

theorem Inv.provedRoots (hI : Inv R s) {i : ℕ} {ρ : F} (hp : s.provedRoots i ρ) :
    i ≤ s.ledger.leaves.length ∧ ρ = treeRoot h (hashes h (s.ledger.leaves.take i)) :=
  hI.proved i ρ hp.2.1

theorem Inv.hashChainAt (hI : Inv R s) {i c : ℕ} (hc : s.hashChainAt i = some c) :
    i ≤ s.ledger.leaves.length ∧ c = chainOf h (s.ledger.leaves.take i) := by
  obtain ⟨hi, hc⟩ := hashChainAt_eq.mp hc
  refine ⟨hi, ?_⟩
  split_ifs at hc with h1 h2
  · rw [hc, hI.head, h1, List.take_length]
  · rw [hc, h2]; rfl
  · rw [hc.2]; exact (hI.checkpoints i hc.1).2

theorem Injective.mono {S T : Set (List F)} (hT : Injective h T) (hST : S ⊆ T) : Injective h S :=
  fun x hx y hy => hT x (hST hx) y (hST hy)

/-- A Merkle path that reaches a proved root, its leaf a hash the run evaluates, opens a ledger
leaf: the hash's input is that leaf's fields. -/
theorem Inv.member (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {ri : ℕ} {ρ : F} (hp : s.provedRoots ri ρ) {x : List F} (hx : x ∈ R.calls ∪ S) {idx : ℕ}
    {sib : Fin DEPTH → F} (hidx : idx < 2 ^ DEPTH) (hpath : pathCalls h (h.H x) idx sib ⊆ R.calls)
    (hm : merkleRoot h (h.H x) idx sib = ρ) :
    ∃ l, s.ledger.leaves[idx]? = some l ∧ x = l.words.map (↑) ∧ idx < ri := by
  obtain ⟨hri, rfl⟩ := hI.provedRoots hp
  have htake : s.ledger.leaves.take ri = R.leaves.take ri := by
    obtain ⟨u, hu⟩ := hpre
    rw [← hu, List.take_append_of_le_length hri]
  have hsub : treeCalls h (hashes h (s.ledger.leaves.take ri)) ∪ pathCalls h (h.H x) idx sib ⊆
      R.calls ∪ S := by
    rintro y (hy | hy)
    · refine Or.inl (Or.inl (Or.inr ⟨ri, (List.IsPrefix.length_le hpre).trans' hri, ?_⟩))
      rw [← htake]; exact hy
    · exact Or.inl (hpath hy)
  obtain ⟨hleaf, -⟩ := binding h _ _ _ _ hidx (hyp.inj.mono hsub) hm
  simp only [node, hashes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take] at hleaf
  by_cases hlt : idx < ri
  · simp only [hlt, if_true] at hleaf
    cases hl : s.ledger.leaves[idx]? with
    | none => simp [hl] at hleaf; exact absurd hleaf (hyp.ne0 x hx)
    | some l =>
      simp only [hl, Option.map_some, Option.getD_some, Leaf.hash] at hleaf
      have hlm : l ∈ R.leaves := hpre.subset (List.mem_of_getElem? hl)
      exact ⟨l, rfl, hyp.inj x hx _ (Or.inl (Or.inr ⟨l, hlm, rfl⟩)) hleaf, hlt⟩
  · simp only [hlt, if_false, Option.map_none, Option.getD_none] at hleaf
    exact absurd hleaf (hyp.ne0 x hx)

/-- The merge steps' states: `k` steps in. -/
def mergeAlong (h : Hashes) (z : Merge.Z) (ws : List Merge.Wit) (k : ℕ) : Merge.Z :=
  (ws.take k).foldl (Merge.next h) z

theorem Merge.callsAlong_mem {z : Merge.Z} {ws : List Merge.Wit} {k : ℕ} (hk : k < ws.length) :
    Merge.calls h (mergeAlong h z ws k) ws[k] ⊆ Merge.callsAlong h z ws := by
  induction ws generalizing z k with
  | nil => simp at hk
  | cons w ws ih =>
    cases k with
    | zero => intro x hx; exact Or.inl (by simpa [mergeAlong] using hx)
    | succ k =>
      intro x hx
      exact Or.inr (ih (z := Merge.next h z w) (by simpa using hk) (by simpa [mergeAlong] using hx))

/-- A merge step leaves every field but the chain, the note and the count where it was. -/
theorem mergeAlong_fixed (z : Merge.Z) (ws : List Merge.Wit) (k : ℕ) :
    let z' := mergeAlong h z ws k
    z'.token = z.token ∧ z'.chain = z.chain ∧ z'.root = z.root ∧ z'.asp = z.asp ∧
      z'.signedChain = z.signedChain ∧ z'.fee = z.fee ∧ z'.feeRecipient = z.feeRecipient := by
  induction ws generalizing z k with
  | nil => simp [mergeAlong]
  | cons w ws ih =>
    cases k with
    | zero => simp [mergeAlong]
    | succ k =>
      have := ih (Merge.next h z w) k
      simp only [mergeAlong, List.take_succ_cons, List.foldl_cons] at this ⊢
      simpa [Merge.next] using this

/-- Every burn opening a run proves is a burn digest the run hashes. -/
theorem Run.openings_calls {o : F × F × F} (ho : o ∈ R.openings) :
    [DOMAIN_BURN, o.1, o.2.1, o.2.2, 0] ∈ R.calls := by
  obtain ⟨i, hi, ho⟩ := ho
  refine Or.inl (Or.inl ⟨i, hi, ?_⟩)
  cases ha : R.a i <;> rw [ha] at ho <;> simp only [Action.openings, Set.mem_empty_iff_false] at ho
  case transact req w =>
    split_ifs at ho
    · obtain rfl := ho
      simp [Action.calls, JS.calls]
    · exact absurd ho (Set.notMem_empty _)
  case merge req ws =>
    obtain ⟨w, hw, -, rfl⟩ := ho
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    simp only [Action.calls]
    apply Merge.callsAlong_mem hk
    have := (mergeAlong_fixed (h := h) (req.z0 h E) ws k).2.1
    simp only [Merge.calls, Set.mem_union, Set.mem_insert_iff]
    left; left; right; right; right; right; left
    rw [this]; rfl
  case rageExit req w =>
    obtain rfl := ho
    simp [Action.calls, RE.calls, Env.chain]

/-- Two keys that open the same position are the same key. -/
theorem Run.opens_unique (hyp : RunHyp R S O) {j : ℕ} {akh nk akh' nk' : F}
    (h1 : Opens R s j akh nk) (h2 : Opens R s j akh' nk') : akh = akh' ∧ nk = nk' := by
  have pk_inj : publicKey h akh nk = publicKey h akh' nk' → akh = akh' ∧ nk = nk' := fun he => by
    have := hyp.inj _ (Or.inl h1.1) _ (Or.inl h2.1) he
    simp only [List.cons.injEq] at this
    exact ⟨this.2.1, this.2.2.1⟩
  obtain ⟨-, ⟨t, nh, o, hl, ho, hpk⟩ | ⟨t, a, v, salt, hl, hop⟩⟩ := h1 <;>
    obtain ⟨-, ⟨t', nh', o', hl', ho', hpk'⟩ | ⟨t', a', v', salt', hl', hop'⟩⟩ := h2
  · rw [ho] at ho'; cases ho'
    exact pk_inj (hpk.symm.trans hpk')
  · rw [hl] at hl'; cases hl'
  · rw [hl] at hl'; cases hl'
  · rw [hl] at hl'
    simp only [Option.some.injEq, Leaf.transfer.injEq] at hl'
    have hd := hyp.burnAddr _ (Or.inl hop) _ (Or.inl hop') hl'.2.2.1
    have := hyp.inj _ (Or.inl (R.openings_calls hop)) _ (Or.inl (R.openings_calls hop')) hd
    simp only [List.cons.injEq] at this
    exact pk_inj this.2.2.1

end bind

/-! ### What the hash chain binds -/

section chain

variable (h)

/-- The canonical chain's inputs over `L`. -/
def canonCalls (L : List Leaf) : Set (ℕ × List ℕ) :=
  {p | ∃ m < L.length, p = (chainOf h (L.take m), (L[m]?.map Leaf.words).getD [])}

theorem chainOf_take_succ (L : List Leaf) {m : ℕ} (hm : m < L.length) :
    chainOf h (L.take (m + 1)) = h.hc (chainOf h (L.take m)) L[m].words := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, chainOf_append]

theorem chainCalls_canon (L : List Leaf) :
    ∀ m ≤ L.length, chainCalls h (chainOf h (L.take m)) ((L.drop m).map Leaf.words) ⊆ canonCalls h L := by
  intro m hm
  induction hn : L.length - m generalizing m with
  | zero =>
    have : L.drop m = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, chainCalls]
  | succ n ih =>
    have hlt : m < L.length := by omega
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, chainCalls, ← chainOf_take_succ h L hlt]
    rintro p (rfl | hp)
    · exact ⟨m, hlt, by simp [List.getElem?_eq_getElem hlt]⟩
    · exact ih (m + 1) hlt (by omega) hp

/-- A segment of commitments hashed onto `prev` that reaches the canonical chain at `end_`, with no
collision among the hashes involved, is the ledger's own segment before `end_`, and `prev` the
chain before it. -/
theorem segment_binds (L : List Leaf) (S : Set (ℕ × List ℕ))
    (hinj : ∀ p ∈ S, ∀ q ∈ S, h.hc p.1 p.2 = h.hc q.1 q.2 → p = q) (hcanon : canonCalls h L ⊆ S)
    {end_ prev : ℕ} {commits : List (List ℕ)} (hend : end_ ≤ L.length)
    (hcalls : chainCalls h prev commits ⊆ S) (hlen : commits.length ≤ end_)
    (he : commits.foldl h.hc prev = chainOf h (L.take end_)) :
    prev = chainOf h (L.take (end_ - commits.length)) ∧
      commits = ((L.take end_).drop (end_ - commits.length)).map Leaf.words := by
  set start := end_ - commits.length
  have hsplit : L.take end_ = L.take start ++ (L.take end_).drop start := by
    have := (List.take_append_drop start (L.take end_)).symm
    rwa [List.take_take, min_eq_left (by omega : start ≤ end_)] at this
  rw [hsplit, chainOf_eq_foldl, List.map_append, List.foldl_append, ← chainOf_eq_foldl] at he
  refine (chain_inj h S hinj commits _ prev _ ?_ hcalls ?_ he)
  · simp [List.length_drop, List.length_take]; omega
  · intro p hp
    apply hcanon
    apply chainCalls_canon h L start (by omega)
    have : (L.take end_).drop start = (L.drop start).take (end_ - start) := by
      rw [List.drop_take]
    rw [this, List.map_take] at hp
    have hsub := chainCalls_foldl_append h (chainOf h (L.take start))
      (((L.drop start).map Leaf.words).take (end_ - start))
      (((L.drop start).map Leaf.words).drop (end_ - start))
    rw [List.take_append_drop] at hsub
    rw [hsub]; exact Or.inl hp

end chain

/-! ### The ledger only grows -/

section grows

variable {s s' : State}

theorem update_grows {t : ℕ} {a b : Addr} {v : ℕ} (hs : ZERC20.update h E t a b v s = some s') :
    s.ledger.leaves <+: s'.ledger.leaves := by
  obtain ⟨tk, -, -, -, -, -, -, -, -, hs⟩ := update_eq.mp hs
  split_ifs at hs
  · subst hs; exact List.prefix_refl _
  · rw [hs.2]; exact List.prefix_append _ _

theorem paid_grows {t d : ℕ} (hp : PaidOut t d s s') : s.ledger.leaves <+: s'.ledger.leaves := by
  rw [hp.1.ledger]

set_option linter.unusedTactic false in
/-- Everything an admin can do leaves the leaves, the ghost and the spent nullifiers alone. -/
theorem admin_frame {op : AdminOp} (hs : op.exec s = some s') :
    s'.ledger.leaves = s.ledger.leaves ∧ s'.ghost = s.ghost ∧ s'.verifier.used = s.verifier.used ∧
      ∀ t, s.tokens t ≠ none → s'.tokens t = s.tokens t := by
  cases op <;>
    simp only [AdminOp.exec, CommitmentLedger.enterEmergency, CommitmentLedger.recover, bind,
      Option.bind_eq_some_iff, guard_eq_some_unit, exists_const, Option.pure_def,
      Option.some.injEq] at hs
  all_goals first
    | (obtain ⟨-, rfl⟩ := hs; simp; done)
    | (subst hs; simp; done)
    | (subst hs; split_ifs <;> simp; done)
    | (obtain ⟨-, -, rfl⟩ := hs; simp; done)
    | (obtain ⟨-, -, -, c, -, rfl⟩ := hs; simp; done)
    | (obtain ⟨-, c, -, -, rfl⟩ := hs; simp; done)
    | (obtain ⟨⟨h1, -⟩, rfl⟩ := hs
       refine ⟨rfl, rfl, rfl, fun t ht => ?_⟩
       simp only [Function.update_apply]; split_ifs with h2 <;> simp_all)

theorem exec_grows {a : Action} (hs : exec h E A a s = some s') :
    s.ledger.leaves <+: s'.ledger.leaves := by
  cases a with
  | wrap t c rc v =>
    simp only [exec, ZERC20.wrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const, Option.pure_def] at hs
    obtain ⟨-, tk, -, s1, h1, h2⟩ := hs
    have g1 := update_grows h1
    simp only [State.setToken] at g1
    split_ifs at h2
    · exact g1.trans (update_grows h2)
    · cases h2; exact g1
  | unwrap t c rc v =>
    simp only [exec, ZERC20.unwrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, -, s1, h1, h2⟩ := hs
    exact (update_grows h1).trans (paid_grows (release_paid h2))
  | transfer t a b v =>
    simp only [exec, ZERC20.transfer, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    exact update_grows hs.2
  | donate t v =>
    simp only [exec, donate, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hs
    obtain ⟨tk, -, rfl⟩ := hs
    exact List.prefix_refl _
  | reserveHashChain =>
    simp only [exec, CommitmentLedger.reserveHashChain] at hs
    split_ifs at hs
    · cases hs; exact List.prefix_refl _
    · simp only [bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
        Option.pure_def, Option.some.injEq] at hs
      obtain ⟨-, rfl⟩ := hs; exact List.prefix_refl _
  | checkpointBefore e p cs =>
    simp only [exec, CommitmentLedger.checkpointBefore, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, rfl⟩ := hs; exact List.prefix_refl _
  | proveRoot new ws =>
    simp only [exec, CommitmentLedger.proveRootTransition, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs; exact List.prefix_refl _
  | transact req w =>
    obtain ⟨-, -, s4, hp, rfl⟩ := transact_spec hs
    have := paid_grows hp
    simp only [Verifier.recordSpent, Verifier.recordNote]
    refine List.IsPrefix.trans ?_ this
    simp [State.append, State.spendAll]
  | merge req ws =>
    obtain ⟨-, -, -, s3, hp, rfl⟩ := merge_spec hs
    have := paid_grows hp
    simp only [Verifier.recordSpent, Verifier.recordNote]
    refine List.IsPrefix.trans ?_ this
    simp [State.append, State.spendAll]
  | rageExit req w =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, s2, h2, rfl⟩ := rageExit_spec hs
    have := paid_grows (payOut_paid h2)
    simpa [Verifier.recordSpent, State.spendAll] using this
  | publishAspRoot c a =>
    simp only [exec, Verifier.publishAspRoot, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs; exact List.prefix_refl _
  | claimFees t rc =>
    simp only [exec, Verifier.claimFees] at hs
    split_ifs at hs
    · cases hs; exact List.prefix_refl _
    · simp only [ZERC20.transfer, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
        exists_const] at hs
      simpa using update_grows hs.2
  | sign m =>
    simp only [exec, Option.some.injEq] at hs
    subst hs; exact List.prefix_refl _
  | admin op =>
    rw [(admin_frame hs).1]

end grows

theorem Run.prefix (R : Run h E A) : ∀ i ≤ R.n, (R.s i).ledger.leaves <+: R.leaves := by
  intro i hi
  induction hk : R.n - i generalizing i with
  | zero => rw [show i = R.n by omega]; exact List.prefix_refl _
  | succ k ih =>
    exact (exec_grows (R.step i (by omega))).trans (ih (i + 1) (by omega) (by omega))

theorem canonCalls_mono {L L' : List Leaf} (hp : L <+: L') : canonCalls h L ⊆ canonCalls h L' := by
  rintro p ⟨m, hm, rfl⟩
  obtain ⟨u, rfl⟩ := hp
  refine ⟨m, by simp; omega, ?_⟩
  rw [List.take_append_of_le_length hm.le, List.getElem?_append_left hm]

/-! ### Step chains -/

section steps

variable {Z W : Type} (next : Z → W → Z)

theorem foldl_take_succ (z : Z) (ws : List W) {k : ℕ} (hk : k < ws.length) :
    (ws.take (k + 1)).foldl next z = next ((ws.take k).foldl next z) ws[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- A chain of steps whose relation fixes the next state goes through the states `next` folds. -/
theorem Chain.along {S : Z → W → Z → Prop} (hnext : ∀ z w z', S z w z' → z' = next z w) :
    ∀ {z : Z} {ws : List W} {z' : Z}, Chain S z ws z' →
      (∀ k (hk : k < ws.length), S ((ws.take k).foldl next z) ws[k] ((ws.take (k + 1)).foldl next z))
        ∧ z' = ws.foldl next z := by
  intro z ws z' hc
  induction hc with
  | nil z => exact ⟨fun k hk => absurd hk (by simp), rfl⟩
  | @cons z z1 z2 w ws hs _ ih =>
    have h1 := hnext _ _ _ hs
    subst h1
    refine ⟨fun k hk => ?_, by simpa using ih.2⟩
    cases k with
    | zero => simpa using hs
    | succ k => simpa using ih.1 k (by simpa using hk)

end steps

/-! ### Root proofs -/

section root

variable {R} {S : Set (List F)} {O : Set (F × F × F)}

theorem chainOf_lt (L : List Leaf) : chainOf h L < AMOUNT_BOUND := by
  induction L using List.reverseRecOn with
  | nil => simp [chainOf, AMOUNT_BOUND]
  | append_singleton L l _ => rw [chainOf_append]; exact h.hc_lt _ _

theorem hc_val (c : ℕ) (vs : List ℕ) : ((h.hc c vs : ℕ) : F).val = h.hc c vs :=
  val_cast ((h.hc_lt c vs).trans amount_lt_r)

/-- The field values a root step hashes. -/
def Root.fieldVals (w : Root.Wit) : List ℕ := List.ofFn fun i => (w.fields i).val

theorem Root.shaAlong_eq (z : Root.Z) (ws : List Root.Wit) :
    Root.shaAlong h z ws = chainCalls h z.chain.val (ws.map Root.fieldVals) := by
  induction ws generalizing z with
  | nil => rfl
  | cons w ws ih =>
    simp only [Root.shaAlong, ih, List.map_cons, chainCalls, Root.shaCall, Root.fieldVals]
    rw [show (Root.next h z w).chain.val = h.hc z.chain.val (List.ofFn fun i => (w.fields i).val)
      from hc_val _ _]

theorem Root.callsAlong_mem {z : Root.Z} {ws : List Root.Wit} {k : ℕ} (hk : k < ws.length) :
    Root.calls h ((ws.take k).foldl (Root.next h) z) ws[k] ⊆ Root.callsAlong h z ws := by
  induction ws generalizing z k with
  | nil => simp at hk
  | cons w ws ih =>
    cases k with
    | zero => intro x hx; exact Or.inl (by simpa using hx)
    | succ k =>
      intro x hx
      exact Or.inr (ih (z := Root.next h z w) (by simpa using hk) (by simpa using hx))

/-- A root proof from the ledger's root at `oi` to its chain at `ni`, with no collision among the
hashes involved, proves the ledger's own root at `ni`. -/
theorem root_chain (hyp : RunHyp R S O) {L : List Leaf} (hpre : L <+: R.leaves) {oi ni : ℕ}
    {ws : List Root.Wit} {nr : F} (hoi : oi ≤ ni) (hlen : ws.length = ni - oi) (hni : ni ≤ L.length)
    (hcap : ni ≤ TREE_SIZE)
    (hcalls : Root.callsAlong h ⟨oi, chainOf h (L.take oi), treeRoot h (hashes h (L.take oi))⟩ ws ⊆
      R.calls)
    (hsha : Root.shaAlong h ⟨oi, chainOf h (L.take oi), treeRoot h (hashes h (L.take oi))⟩ ws ⊆
      R.shaCalls)
    (hc : Chain (Root.Spec h) ⟨oi, chainOf h (L.take oi), treeRoot h (hashes h (L.take oi))⟩ ws
      ⟨ni, chainOf h (L.take ni), nr⟩) :
    nr = treeRoot h (hashes h (L.take ni)) := by
  set z0 : Root.Z := ⟨oi, chainOf h (L.take oi), treeRoot h (hashes h (L.take oi))⟩
  obtain ⟨hstep, hend⟩ := Chain.along (Root.next h) (fun _ _ _ hs => hs.next) hc
  set zs := fun k => (ws.take k).foldl (Root.next h) z0
  -- The chain: the steps absorb the ledger's own fields.
  have hfields : ws.map Root.fieldVals = ((L.take ni).drop oi).map Leaf.words := by
    have hz0 : z0.chain.val = chainOf h (L.take oi) := val_cast ((chainOf_lt _).trans amount_lt_r)
    have hfold : ∀ k ≤ ws.length, (zs k).chain.val =
        ((ws.take k).map Root.fieldVals).foldl h.hc (chainOf h (L.take oi)) := by
      intro k hk
      induction k with
      | zero => simpa [zs] using hz0
      | succ k ih =>
        simp only [zs, foldl_take_succ _ _ _ (by omega : k < ws.length)] at ih ⊢
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega : k < ws.length),
          Option.toList_some, List.map_append, List.map_singleton, List.foldl_append,
          List.foldl_cons, List.foldl_nil, ← ih (by omega)]
        exact hc_val _ _
    have hn := hfold ws.length le_rfl
    rw [List.take_length, show zs ws.length = ws.foldl (Root.next h) z0 by simp [zs], ← hend,
      val_cast ((chainOf_lt _).trans amount_lt_r)] at hn
    have hseg := segment_binds h L R.shaCalls hyp.sha
      ((canonCalls_mono hpre).trans (fun p hp => Or.inr hp)) hni
      (by rw [← hz0, ← Root.shaAlong_eq]; exact hsha) (by simp; omega) hn.symm
    simpa [hlen, show ni - (ni - oi) = oi by omega] using hseg.2
  -- The roots: each step puts the ledger's next leaf in its slot.
  have hroot : ∀ k ≤ ws.length, (zs k).root = treeRoot h (hashes h (L.take (oi + k))) ∧
      (zs k).index = ((oi + k : ℕ) : F) := by
    intro k hk
    induction k with
    | zero => simp [zs, z0]
    | succ k ih =>
      obtain ⟨ihr, ihi⟩ := ih (by omega)
      have hk' : k < ws.length := by omega
      have hs := hstep k hk'
      set m := oi + k
      have hm : m < ni := by omega
      have hmr : m < r := lt_of_lt_of_le hm (hcap.trans (by unfold TREE_SIZE DEPTH; exact
        (two_pow_le_r (by norm_num)).le))
      have hmv : (zs k).index.val = m := by rw [ihi]; exact val_cast hmr
      have hls : (hashes h (L.take m)).length = m := by simp [hashes]; omega
      have htake : L.take m = R.leaves.take m := by
        obtain ⟨u, hu⟩ := hpre
        rw [← hu, List.take_append_of_le_length (by omega)]
      -- The empty slot's path is the tree's own, so its siblings are the tree's.
      have hinj : Injective h (treeCalls h (hashes h (L.take m)) ∪ pathCalls h 0 m ws[k].sib) := by
        apply hyp.inj.mono
        rintro y (hy | hy)
        · exact Or.inl (Or.inl (Or.inr ⟨m, (hpre.length_le).trans' (by omega),
            by rw [← htake]; exact hy⟩))
        · exact Or.inl (hcalls (Root.callsAlong_mem hk' (Or.inl (Or.inr (by rwa [hmv])))))
      have hempty : merkleRoot h 0 (zs k).index.val ws[k].sib = (zs k).root := hs.empty
      rw [hmv, ihr] at hempty
      have hsib := (binding h (hashes h (L.take m)) 0 m ws[k].sib
        (by unfold TREE_SIZE at hcap; omega) hinj hempty).2
      have hmL : m < L.length := by omega
      have hfk : List.ofFn ws[k].fields = L[m].words.map (↑) := by
        have := congrArg (fun l => l[k]?) hfields
        simp only [List.getElem?_map, List.getElem?_drop, List.getElem?_take,
          List.getElem?_eq_getElem hk', show oi + k < ni by omega, if_true,
          List.getElem?_eq_getElem (show oi + k < L.length by omega), Option.map_some,
          Option.some.injEq, Root.fieldVals] at this
        rw [← this, List.map_ofFn]
        congr 1; funext i; simp
      refine ⟨?_, ?_⟩
      · simp only [zs, foldl_take_succ _ _ _ hk', Root.next]
        have happ := treeRoot_append h (hashes h (L.take m)) (h.H (L[m].words.map (↑)))
          (by rw [hls]; unfold TREE_SIZE at hcap; omega)
        rw [hls] at happ
        rw [show (ws.take k).foldl (Root.next h) z0 = zs k from rfl, hmv, hsib, Root.leaf, hfk,
          happ, show oi + (k + 1) = m + 1 by omega]
        congr 1
        simp only [hashes]
        rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem hmL, Option.toList_some,
          List.map_singleton]
        rfl
      · simp only [zs, foldl_take_succ _ _ _ hk', Root.next]
        rw [show (ws.take k).foldl (Root.next h) z0 = zs k from rfl, ihi]
        simp only [m, Nat.cast_add, Nat.cast_one]; ring
  have := (hroot ws.length le_rfl).1
  rw [show zs ws.length = ws.foldl (Root.next h) z0 by simp [zs], ← hend, hlen,
    show oi + (ni - oi) = ni by omega] at this
  exact this

end root

end inv

end

end Zerc20
