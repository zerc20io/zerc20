import Zerc20.Inv

/-!
# Every action keeps the invariant

One lemma per action. A run's hypotheses enter only through the values the action evaluates,
which the run's sets contain.
-/

namespace Zerc20

open scoped Classical

noncomputable section

variable {h : Hashes} {E : Env} {A : Attest} {R : Run h E A}

/-- What a run's step may use about its action. -/
structure StepCtx (R : Run h E A) (s : State) (a : Action) : Prop where
  calls : a.calls h E s ⊆ R.calls
  sha : a.shaCalls h E s ⊆ R.shaCalls
  openings : a.openings h E ⊆ R.openings
  frozen : ∀ x ∈ a.debits E, x ∉ R.burnAddrs

theorem RunHyp.ctx {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O) {i : ℕ}
    (hi : i < R.n) : StepCtx R (R.s i) (R.a i) where
  calls _ hx := Or.inl (Or.inl ⟨i, hi, hx⟩)
  sha _ hx := Or.inl ⟨i, hi, hx⟩
  openings _ ho := ⟨i, hi, ho⟩
  frozen := hyp.frozen i hi

/-! ## Extending the ledger -/

section extend

variable {s s' : State} {new : List Leaf}

theorem take_extends {L new : List Leaf} {i : ℕ} (hi : i ≤ L.length) :
    (L ++ new).take i = L.take i := List.take_append_of_le_length hi

/-- The invariant after an action that appends `new`, records their openings, spends some
positions, and keeps the checkpoints and roots: all the action-specific facts left to show. -/
theorem Inv.extend (hI : Inv R s) (he : Extends s s' new)
    (registered : ∀ t, s'.tokens t ≠ none → t ≠ 0 ∧ t < TOKEN_BOUND)
    (keeps : ∀ t, s.tokens t ≠ none → s'.tokens t ≠ none)
    (head : s'.ledger.head = chainOf h s'.ledger.leaves)
    (cap : s'.ledger.leaves.length ≤ TREE_SIZE)
    (same : s'.ledger.checkpoints = s.ledger.checkpoints ∧ s'.ledger.provedIn = s.ledger.provedIn ∧
      s'.ledger.rootState = s.ledger.rootState)
    (valid : ∀ l ∈ new, Leaf.Valid l ∧ s'.tokens l.token ≠ none)
    (notes : ∀ j (t : ℕ) nh, s.ledger.leaves.length ≤ j → s'.ledger.leaves[j]? = some (.note t nh) →
      ∃ o, s'.ghost.notes j = some o ∧ nh = noteHash h E.chain o.pk o.value t o.salt ∧
        o.value.val < AMOUNT_BOUND ∧ [DOMAIN_NOTE, E.chain, o.pk, o.value, (t : F), o.salt] ∈ R.calls)
    {js : List ℕ} (hsp : s'.ghost.spent = s.ghost.spent ++ js)
    (used : s.verifier.used ⊆ s'.verifier.used)
    (nodup : (s.ghost.spent ++ js).Nodup)
    (spent : ∀ j ∈ js, j < s'.ledger.leaves.length ∧
      ∃ akh nk, Opens R s' j akh nk ∧ nullifier h E.chain j nk ∈ s'.verifier.used)
    (books : ∀ t tk, s'.tokens t = some tk → tk.Books ∧
      tk.supply + created s' t ≤ tk.underlying + consumed s' t ∧
      ∀ a ∈ R.burnAddrs, deposits s' t a ≤ tk.bal a) :
    Inv R s' where
  registered := registered
  head := head
  cap := cap
  checkpoints i hi := by
    rw [same.1] at hi ⊢
    obtain ⟨h1, h2⟩ := hI.checkpoints i hi
    rw [he.leaves, take_extends h1]
    exact ⟨by rw [List.length_append]; omega, h2⟩
  proved i ρ hi := by
    rw [same.2.1] at hi
    obtain ⟨h1, h2⟩ := hI.proved i ρ hi
    rw [he.leaves, take_extends h1]
    exact ⟨by rw [List.length_append]; omega, h2⟩
  rootState := by
    rw [same.2.2, he.leaves, take_extends hI.rootState.1]
    exact ⟨by rw [List.length_append]; exact hI.rootState.1.trans (by omega), hI.rootState.2⟩
  valid l hl := by
    rw [he.leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ⟨(hI.valid l hl).1, keeps _ (hI.valid l hl).2⟩
    · exact valid l hl
  notes j t nh hj := by
    by_cases hlt : j < s.ledger.leaves.length
    · rw [he.getElem? hlt] at hj
      obtain ⟨o, ho, rest⟩ := hI.notes j t nh hj
      exact ⟨o, by rw [he.notes j hlt, ho], rest⟩
    · exact notes j t nh (by omega) hj
  nodup := hsp ▸ nodup
  spent j hj := by
    rw [hsp, List.mem_append] at hj
    rcases hj with hj | hj
    · obtain ⟨hlt, akh, nk, hop, hnf⟩ := hI.spent j hj
      exact ⟨by rw [he.leaves, List.length_append]; omega, akh, nk, (he.opens hlt).mpr hop,
        used hnf⟩
    · exact spent j hj
  books := books

end extend

/-! ## Spends open the ledger -/

section opens

variable {S : Set (List F)} {O : Set (F × F × F)} {s : State}

theorem address_lt (d : F) : addressOf d < ADDRESS_BOUND := Nat.mod_lt _ (by unfold ADDRESS_BOUND; positivity)

/-- A note leaf proved in a root, its owner the public key of `(akh, nk)`, is the ledger's note
at that position, opened by that key, worth the value it opens with. -/
theorem Inv.note_member (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {ri : ℕ} {ρ : F} (hp : s.provedRoots ri ρ) {t : ℕ} (ht : t < TOKEN_BOUND)
    {akh nk v salt : F} {idx : ℕ} {sib : Fin DEPTH → F} (hidx : idx < 2 ^ DEPTH)
    (hcalls : [↑(field0 NOTE_HASH_TAG t),
        noteHash h E.chain (publicKey h akh nk) v (t : F) salt, 0, 0] ∈ R.calls ∧
      [DOMAIN_NOTE, E.chain, publicKey h akh nk, v, (t : F), salt] ∈ R.calls ∧
      [DOMAIN_PUBLIC_KEY, akh, nk] ∈ R.calls)
    (hpath : pathCalls h (h.H [↑(field0 NOTE_HASH_TAG t),
        noteHash h E.chain (publicKey h akh nk) v (t : F) salt, 0, 0]) idx sib ⊆ R.calls)
    (hm : merkleRoot h (h.H [↑(field0 NOTE_HASH_TAG t),
        noteHash h E.chain (publicKey h akh nk) v (t : F) salt, 0, 0]) idx sib = ρ) :
    idx < s.ledger.leaves.length ∧ Opens R s idx akh nk ∧
      ∃ nh o, s.ledger.leaves[idx]? = some (.note t nh) ∧ s.ghost.notes idx = some o ∧
        o.value = v := by
  obtain ⟨l, hl, hx, hri⟩ := hI.member hyp hpre hp (Or.inl hcalls.1) hidx hpath hm
  have hlv := (hI.valid l (List.mem_of_getElem? hl)).1
  have hln := words_note hlv ht hx.symm
  subst hln
  obtain ⟨o, ho, hnh, -, hoc⟩ := hI.notes idx t _ hl
  have := hyp.inj _ (Or.inl hcalls.2.1) _ (Or.inl hoc) (by unfold noteHash at hnh; exact hnh)
  simp only [List.cons.injEq] at this
  refine ⟨(List.getElem?_eq_some_iff.mp hl).1, ⟨hcalls.2.2, Or.inl ⟨t, _, o, hl, ho, this.2.2.1.symm⟩⟩,
    _, o, hl, ho, this.2.2.2.1.symm⟩

/-- A transfer leaf proved in a root, paying the burn address an opening derives, is the ledger's
transfer at that position, opened by the opening's key. -/
theorem Inv.burn_member (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {ri : ℕ} {ρ : F} (hp : s.provedRoots ri ρ) {t : ℕ} (ht : t < TOKEN_BOUND)
    {akh nk salt src value : F} {idx : ℕ} {sib : Fin DEPTH → F} (hidx : idx < 2 ^ DEPTH)
    (hcalls : [↑(field0 TRANSFER_TAG t), src,
        ↑(addressOf (burnDigest h E.chain (publicKey h akh nk) salt)), value] ∈ R.calls ∧
      [DOMAIN_PUBLIC_KEY, akh, nk] ∈ R.calls)
    (hop : (E.chain, publicKey h akh nk, salt) ∈ R.openings)
    (hpath : pathCalls h (h.H [↑(field0 TRANSFER_TAG t), src,
        ↑(addressOf (burnDigest h E.chain (publicKey h akh nk) salt)), value]) idx sib ⊆ R.calls)
    (hm : merkleRoot h (h.H [↑(field0 TRANSFER_TAG t), src,
        ↑(addressOf (burnDigest h E.chain (publicKey h akh nk) salt)), value]) idx sib = ρ) :
    idx < s.ledger.leaves.length ∧ Opens R s idx akh nk ∧
      ∃ a v, s.ledger.leaves[idx]? = some (.transfer t a
        (addressOf (burnDigest h E.chain (publicKey h akh nk) salt)) v) ∧ (a : F) = src ∧
        (v : F) = value := by
  obtain ⟨l, hl, hx, hri⟩ := hI.member hyp hpre hp (Or.inl hcalls.1) hidx hpath hm
  have hlv := (hI.valid l (List.mem_of_getElem? hl)).1
  obtain ⟨a, b, v, rfl, ha, hb, hv⟩ := words_transfer hlv ht hx.symm
  have hb' : b = addressOf (burnDigest h E.chain (publicKey h akh nk) salt) :=
    (cast_inj (hlv.2.2.2.2.1.trans address_lt_r) ((address_lt _).trans address_lt_r)).mp hb
  subst hb'
  exact ⟨(List.getElem?_eq_some_iff.mp hl).1, ⟨hcalls.2, Or.inr ⟨t, a, v, salt, hl, hop⟩⟩,
    a, v, hl, ha, hv⟩

/-- A position spent before has its nullifier spent: a key that opens it again finds its
nullifier taken. -/
theorem Inv.fresh (hI : Inv R s) (hyp : RunHyp R S O) {j : ℕ} {akh nk : F}
    (hop : Opens R s j akh nk) (hnf : nullifier h E.chain j nk ∉ s.verifier.used) :
    j ∉ s.ghost.spent := by
  intro hj
  obtain ⟨-, akh', nk', hop', hnf'⟩ := hI.spent j hj
  obtain ⟨-, rfl⟩ := R.opens_unique hyp hop' hop
  exact hnf hnf'

end opens

/-! ## JoinSplit -/

section transact

variable {S : Set (List F)} {O : Set (F × F × F)} {s s' : State}

/-- What a spend proves about one of its inputs: a ledger position below the root, opened by the
prover's key, worth the value the circuit conserves, and only of the proof's token. -/
structure Opened (R : Run h E A) (s : State) (t j : ℕ) (akh nk : F) (value : ℕ) : Prop where
  lt : j < s.ledger.leaves.length
  opens : Opens R s j akh nk
  value : leafValueAt s t j = value
  other : ∀ t', t' ≠ t → leafValueAt s t' j = 0

theorem Opened.of_note {t j : ℕ} {akh nk : F} {v : F}
    (h1 : j < s.ledger.leaves.length ∧ Opens R s j akh nk ∧
      ∃ nh o, s.ledger.leaves[j]? = some (.note t nh) ∧ s.ghost.notes j = some o ∧ o.value = v) :
    Opened R s t j akh nk v.val := by
  obtain ⟨hlt, hop, nh, o, hl, ho, hv⟩ := h1
  refine ⟨hlt, hop, ?_, fun t' ht' => ?_⟩
  · simp [leafValueAt, noteValueAt, hl, ho, hv]
  · simp [leafValueAt, noteValueAt, hl, ho, Ne.symm ht']

theorem Opened.of_transfer {t j : ℕ} {akh nk : F} {b : ℕ} {value : F}
    (h1 : j < s.ledger.leaves.length ∧ Opens R s j akh nk ∧
      ∃ a v, s.ledger.leaves[j]? = some (.transfer t a b v) ∧ (a : F) = src ∧ (v : F) = value)
    (hI : Inv R s) : Opened R s t j akh nk value.val := by
  obtain ⟨hlt, hop, a, v, hl, -, hv⟩ := h1
  have hvalid := (hI.valid _ (List.mem_of_getElem? hl)).1
  have hvv : value.val = v := by rw [← hv]; exact val_cast (hvalid.2.2.2.2.2.2.trans amount_lt_r)
  refine ⟨hlt, hop, ?_, fun t' ht' => ?_⟩
  · simp [leafValueAt, hl, hvv]
  · simp [leafValueAt, hl, Ne.symm ht']

/-- JoinSplit's `in0`, opened. -/
theorem Inv.transact_in0 (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {req : Verifier.TransactReq} {w : JS.Wit} (hc : StepCtx R s (.transact req w))
    (hok : Verifier.TransactOK h E A req w s) :
    Opened R s req.pub.token.val w.idx0.val w.akh0 (JS.nk0 (h := h) w) (JS.value0 w) := by
  have hsp := hok.proof
  have hchain : req.pub.chain = E.chain := by
    rw [Env.chain, ← hok.chain, ZMod.natCast_zmod_val]
  have htok : ((req.pub.token.val : ℕ) : F) = req.pub.token := ZMod.natCast_zmod_val _
  have ht := hok.token.1
  have hcalls := hc.calls
  simp only [Action.calls] at hcalls
  have hidx := hsp.idx0_lt
  have hm := hsp.member0
  unfold JS.leaf0 at hm
  cases hb : w.in0IsBurn
  · obtain ⟨hpk, -⟩ := hsp.note0 hb
    replace hpk : w.note0.pk = publicKey h w.akh0 (JS.nk0 (h := h) w) := hpk
    simp only [hb, Bool.false_eq_true, if_false] at hm
    have := Opened.of_note (R := R) (s := s) (hI.note_member hyp hpre hok.root ht (akh := w.akh0)
      (nk := JS.nk0 (h := h) w) (v := w.note0.value) (salt := w.note0.salt) hidx
      ⟨by rw [← hpk, hchain.symm, htok]; exact hcalls (by simp [JS.calls]),
        by rw [← hpk, hchain.symm, htok]; exact hcalls (by simp [JS.calls]),
        hcalls (by simp [JS.calls])⟩
      (by rw [← hpk, hchain.symm, htok]
          exact fun y hy => hcalls (Or.inl (Or.inl (Or.inr (by simpa [JS.leaf0, hb] using hy)))))
      (by rw [← hpk, hchain.symm, htok]; exact hm))
    simpa [JS.value0, hb] using this
  · obtain ⟨hpk, -, -, -, -⟩ := hsp.burn0 hb
    replace hpk : w.burnPk = publicKey h w.akh0 (JS.nk0 (h := h) w) := hpk
    simp only [hb, if_true] at hm
    have := Opened.of_transfer (R := R) (src := w.burnFrom) (hI.burn_member hyp hpre hok.root ht
      (akh := w.akh0) (nk := JS.nk0 (h := h) w) (salt := w.burnSalt) (src := w.burnFrom)
      (value := w.burnValue) hidx
      ⟨by rw [← hpk, hchain.symm]; exact hcalls (by simp [JS.calls]), hcalls (by simp [JS.calls])⟩
      (by
        have ho := hc.openings
        simp only [Action.openings, hb, if_true, Set.singleton_subset_iff] at ho
        rw [← hpk, hchain.symm]; exact ho)
      (by rw [← hpk, hchain.symm]
          exact fun y hy => hcalls (Or.inl (Or.inl (Or.inr (by simpa [JS.leaf0, hb] using hy)))))
      (by rw [← hpk, hchain.symm]; exact hm)) hI
    simpa [JS.value0, hb] using this

/-- JoinSplit's `in1`, opened when it is real. -/
theorem Inv.transact_in1 (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {req : Verifier.TransactReq} {w : JS.Wit} (hc : StepCtx R s (.transact req w))
    (hok : Verifier.TransactOK h E A req w s) (hreal : w.in1IsDummy = false) :
    Opened R s req.pub.token.val w.idx1.val w.akh1 (JS.nk1 (h := h) w) (JS.value1 w) := by
  have hsp := hok.proof
  have hchain : req.pub.chain = E.chain := by
    rw [Env.chain, ← hok.chain, ZMod.natCast_zmod_val]
  have htok : ((req.pub.token.val : ℕ) : F) = req.pub.token := ZMod.natCast_zmod_val _
  have hcalls := hc.calls
  simp only [Action.calls] at hcalls
  obtain ⟨hpk, hm, -⟩ := hsp.real1 hreal
  replace hpk : w.note1.pk = publicKey h w.akh1 (JS.nk1 (h := h) w) := hpk
  unfold JS.leaf1 at hm
  have := Opened.of_note (R := R) (s := s) (hI.note_member hyp hpre hok.root hok.token.1
    (akh := w.akh1) (nk := JS.nk1 (h := h) w) (v := w.note1.value) (salt := w.note1.salt)
    hsp.idx1_lt
    ⟨by rw [← hpk, hchain.symm, htok]; exact hcalls (by simp [JS.calls]),
      by rw [← hpk, hchain.symm, htok]; exact hcalls (by simp [JS.calls]),
      hcalls (by simp [JS.calls])⟩
    (by rw [← hpk, hchain.symm, htok]
        exact fun y hy => hcalls (Or.inl (Or.inr (by simpa [JS.leaf1] using hy))))
    (by rw [← hpk, hchain.symm, htok]; exact hm))
  simpa [JS.value1, hreal] using this

/-- A payout keeps the set of registered tokens. -/
theorem PaidOut.tokens_iff {t d : ℕ} {s s' : State} (hp : PaidOut t d s s') (t' : ℕ) :
    s'.tokens t' ≠ none ↔ s.tokens t' ≠ none := by
  obtain ⟨-, ho, tk, tk', htk, htk', -⟩ := hp
  by_cases ht : t' = t
  · subst ht; simp [htk, htk']
  · rw [ho t' ht]

/-- The books after a step that pays out `d` of token `t` (from `s3` to `s4`), commits notes worth
`c` and consumes inputs worth `u` of it, with `c + d ≤ u`, and leaves every other token alone. -/
theorem books_step {t d c u : ℕ} {s s' s3 s4 : State} (hI : Inv R s) (hp : PaidOut t d s3 s4)
    (h3 : s3.tokens = s.tokens) (h' : s'.tokens = s4.tokens) (hcu : c + d ≤ u)
    (hcreated : ∀ t', created s' t' = created s t' + if t' = t then c else 0)
    (hconsumed : ∀ t', consumed s' t' = consumed s t' + if t' = t then u else 0)
    (hdeposits : ∀ t' a, deposits s' t' a = deposits s t' a) :
    ∀ t' tk', s'.tokens t' = some tk' → tk'.Books ∧
      tk'.supply + created s' t' ≤ tk'.underlying + consumed s' t' ∧
      ∀ a ∈ R.burnAddrs, deposits s' t' a ≤ tk'.bal a := by
  obtain ⟨-, ho, tk, tk4, htk, htk4, hpay⟩ := hp
  rw [h3] at htk
  intro t' tk' ht'
  rw [h'] at ht'
  rw [hcreated, hconsumed]
  by_cases htt : t' = t
  · subst htt
    rw [htk4] at ht'; cases ht'
    obtain ⟨hb, hbook, hdep⟩ := hI.books _ tk htk
    refine ⟨hpay.erc20 hb, ?_, fun a ha => (hdeposits _ a ▸ hdep a ha).trans (hpay.grows a)⟩
    have := hpay.books
    simp only [if_true]
    omega
  · rw [ho t' htt, h3] at ht'
    obtain ⟨hb, hbook, hdep⟩ := hI.books _ tk' ht'
    simp only [htt, if_false, add_zero]
    exact ⟨hb, hbook, fun a ha => hdeposits _ a ▸ hdep a ha⟩

/-- The positions a transact spends. -/
def transactSpent (w : JS.Wit) : List ℕ := w.idx0.val :: if w.in1IsDummy then [] else [w.idx1.val]

theorem Inv.transact (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {req : Verifier.TransactReq} {w : JS.Wit} (hc : StepCtx R s (.transact req w))
    (hs : Verifier.transact h E A req w s = some s') : Inv R s' := by
  obtain ⟨hok, hcap2, s4, hp, rfl⟩ := transact_spec hs
  have hsp := hok.proof
  have hchain : req.pub.chain = E.chain := by
    rw [Env.chain, ← hok.chain, ZMod.natCast_zmod_val]
  have htok : ((req.pub.token.val : ℕ) : F) = req.pub.token := ZMod.natCast_zmod_val _
  have hcalls := hc.calls
  simp only [Action.calls] at hcalls
  set t := req.pub.token.val with ht
  set L := s.ledger.leaves.length with hL
  set s3 := ((s.spendAll [req.pub.nf0, req.pub.nf1]).append h (.note t req.pub.nh1)).append h
    (.note t req.pub.nh2) with hs3
  have o0 := hI.transact_in0 hyp hpre hc hok
  have hfr := hp.1
  -- The final state, field by field.
  have f_leaves : (Verifier.recordSpent (transactSpent w) (Verifier.recordNote (L + 1) w.out2
      (Verifier.recordNote L w.out1 s4))).ledger = s4.ledger := rfl
  have f_tokens : (Verifier.recordSpent (transactSpent w) (Verifier.recordNote (L + 1) w.out2
      (Verifier.recordNote L w.out1 s4))).tokens = s4.tokens := rfl
  have f_used : (Verifier.recordSpent (transactSpent w) (Verifier.recordNote (L + 1) w.out2
      (Verifier.recordNote L w.out1 s4))).verifier.used = s4.verifier.used := rfl
  have f_spent : (Verifier.recordSpent (transactSpent w) (Verifier.recordNote (L + 1) w.out2
      (Verifier.recordNote L w.out1 s4))).ghost.spent = s.ghost.spent ++ transactSpent w := by
    simp [Verifier.recordSpent, Verifier.recordNote, hfr.ghost, hs3, State.append, State.spendAll]
  have f_notes : (Verifier.recordSpent (transactSpent w) (Verifier.recordNote (L + 1) w.out2
      (Verifier.recordNote L w.out1 s4))).ghost.notes =
      Function.update (Function.update s.ghost.notes L (some w.out1)) (L + 1) (some w.out2) := by
    simp [Verifier.recordSpent, Verifier.recordNote, hfr.ghost, hs3, State.append, State.spendAll]
  have h4l : s4.ledger.leaves = s.ledger.leaves ++ [.note t req.pub.nh1, .note t req.pub.nh2] := by
    rw [hfr.ledger]; simp [hs3, State.append, State.spendAll]
  have h4h : s4.ledger.head = h.hc (h.hc s.ledger.head (Leaf.note t req.pub.nh1).words)
      (Leaf.note t req.pub.nh2).words := by
    rw [hfr.ledger]; simp [hs3, State.append, State.spendAll]
  have h4u : s4.verifier.used = s.verifier.used ∪ {nf | nf ∈ [req.pub.nf0, req.pub.nf1]} := by
    rw [hfr.used]; simp [hs3, State.append, State.spendAll]
  have h4m : s4.ledger.checkpoints = s.ledger.checkpoints ∧ s4.ledger.provedIn = s.ledger.provedIn ∧
      s4.ledger.rootState = s.ledger.rootState := by
    rw [hfr.ledger]; simp [hs3, State.append, State.spendAll]
  have h3t : s3.tokens = s.tokens := by simp [hs3, State.append, State.spendAll]
  have he : Extends s (Verifier.recordSpent (transactSpent w) (Verifier.recordNote (L + 1) w.out2
      (Verifier.recordNote L w.out1 s4))) [.note t req.pub.nh1, .note t req.pub.nh2] :=
    ⟨by rw [f_leaves, h4l], fun j hj => by
      rw [f_notes, Function.update_apply, Function.update_apply, if_neg (by omega),
        if_neg (by omega)]⟩
  -- The nullifiers are the inputs' own, and fresh.
  have hnf0 : nullifier h E.chain (w.idx0.val : F) (JS.nk0 (h := h) w) = req.pub.nf0 := by
    rw [hsp.nf0, ZMod.natCast_zmod_val, hchain]
  have hnf1 (hd : w.in1IsDummy = false) :
      nullifier h E.chain (w.idx1.val : F) (JS.nk1 (h := h) w) = req.pub.nf1 := by
    rw [(hsp.real1 hd).2.2, ZMod.natCast_zmod_val, hchain]
  have hmem : ∀ j ∈ transactSpent w, j < L ∧ ∃ akh nk, Opens R s j akh nk ∧
      nullifier h E.chain j nk ∈ ({nf | nf ∈ [req.pub.nf0, req.pub.nf1]} : Set F) := by
    intro j hj
    simp only [transactSpent, List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨o0.lt, _, _, o0.opens, by rw [hnf0]; simp⟩
    · cases hd : w.in1IsDummy
      · simp only [hd, Bool.false_eq_true, if_false, List.mem_singleton] at hj
        subst hj
        have o1 := hI.transact_in1 hyp hpre hc hok hd
        exact ⟨o1.lt, _, _, o1.opens, by rw [hnf1 hd]; simp⟩
      · simp [hd] at hj
  -- The value the inputs consume, in token `t` only.
  have hval : ∀ t', ((transactSpent w).map (leafValueAt s t')).sum =
      if t' = t then JS.value0 w + JS.value1 w else 0 := by
    intro t'
    cases hd : w.in1IsDummy
    · have o1 := hI.transact_in1 hyp hpre hc hok hd
      simp only [transactSpent, hd, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      split_ifs with htt
      · rw [htt, o0.value, o1.value]
      · rw [o0.other t' htt, o1.other t' htt]
    · simp only [transactSpent, hd, if_true, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, JS.value1]
      split_ifs with htt
      · rw [htt, o0.value]
      · exact o0.other t' htt
  have htokn : s4.tokens t ≠ none := (hp.tokens_iff t).mpr (by rw [h3t]; exact hok.token.2.1)
  apply hI.extend he
  · intro t' ht'
    rw [f_tokens] at ht'
    exact hI.registered t' (by rw [← h3t]; exact (hp.tokens_iff t').mp ht')
  · intro t' ht'
    rw [f_tokens]
    exact (hp.tokens_iff t').mpr (by rw [h3t]; exact ht')
  · rw [f_leaves, h4h, h4l, hI.head,
      show s.ledger.leaves ++ [Leaf.note t req.pub.nh1, Leaf.note t req.pub.nh2] =
        (s.ledger.leaves ++ [Leaf.note t req.pub.nh1]) ++ [Leaf.note t req.pub.nh2] by simp,
      chainOf_append, chainOf_append]
  · rw [f_leaves, h4l, List.length_append]
    simpa using hcap2
  · rw [f_leaves]; exact h4m
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact ⟨hok.token.1, by rw [f_tokens]; exact htokn⟩
  · intro j t' nh hj hl
    rw [f_leaves, h4l] at hl
    rw [f_notes]
    have hjL : j = L ∨ j = L + 1 := by
      have := (List.getElem?_eq_some_iff.mp hl).1
      simp at this; omega
    rcases hjL with rfl | rfl
    · rw [List.getElem?_append_right le_rfl] at hl
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Leaf.note.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨w.out1, by simp, ?_, hsp.out1_lt, ?_⟩
      · rw [hsp.nh1, hchain, htok]
      · rw [← hchain, htok]; exact hcalls (by simp [JS.calls])
    · rw [List.getElem?_append_right (by omega)] at hl
      simp only [hL, Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Leaf.note.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨w.out2, by simp, ?_, hsp.out2_lt, ?_⟩
      · rw [hsp.nh2, hchain, htok]
      · rw [← hchain, htok]; exact hcalls (by simp [JS.calls])
  · exact f_spent
  · intro x hx
    rw [f_used, h4u]
    exact Or.inl hx
  · -- The positions spent are distinct, and new.
    rw [List.nodup_append]
    refine ⟨hI.nodup, ?_, ?_⟩
    · cases hd : w.in1IsDummy
      · have o1 := hI.transact_in1 hyp hpre hc hok hd
        simp only [transactSpent, hd, Bool.false_eq_true, if_false, List.nodup_cons,
          List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
          and_true]
        intro heq
        obtain ⟨-, hnk⟩ := R.opens_unique hyp o0.opens (heq ▸ o1.opens)
        apply hok.nfs.1
        rw [← hnf0, ← hnf1 hd, hnk, heq]
      · simp [transactSpent, hd]
    · intro j hj j' hj' hjj
      subst hjj
      obtain ⟨-, akh, nk, hop, hnf⟩ := hmem j hj'
      refine hI.fresh hyp hop ?_ hj
      intro hu
      simp only [List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_setOf_eq] at hnf
      rcases hnf with h0 | h1
      · exact hok.nfs.2.1 (h0 ▸ hu)
      · exact hok.nfs.2.2 (h1 ▸ hu)
  · intro j hj
    obtain ⟨hlt, akh, nk, hop, hnf⟩ := hmem j hj
    refine ⟨by rw [he.leaves, List.length_append]; omega, akh, nk, (he.opens hlt).mpr hop, ?_⟩
    rw [f_used, h4u]; exact Or.inr hnf
  · apply books_step hI hp h3t f_tokens (c := w.out1.value.val + w.out2.value.val)
      (u := JS.value0 w + JS.value1 w)
    · have := hsp.conserve; omega
    · intro t'
      have hn : ∀ k, k < 2 → noteValueAt (Verifier.recordSpent (transactSpent w)
          (Verifier.recordNote (L + 1) w.out2 (Verifier.recordNote L w.out1 s4))) t'
          (s.ledger.leaves.length + k) =
          if t = t' then (if k = 0 then w.out1 else w.out2).value.val else 0 := by
        intro k hk
        unfold noteValueAt
        rw [f_leaves, h4l, f_notes, List.getElem?_append_right (by omega)]
        interval_cases k <;> simp [hL, Function.update_apply]
      rw [he.created, show [Leaf.note t req.pub.nh1, Leaf.note t req.pub.nh2].length = 2 from rfl,
        show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [show s.ledger.leaves.length = s.ledger.leaves.length + 0 from rfl, hn 0 (by norm_num),
        hn 1 (by norm_num)]
      by_cases htt : t' = t
      · subst htt; simp
      · simp [htt, Ne.symm htt]
    · intro t'
      rw [he.consumed t' f_spent (fun j hj => (hI.spent j hj).1), ← hval t']
      congr 2
      apply List.map_congr_left
      intro j hj
      exact he.leafValueAt (hmem j hj).1
    · intro t' a
      rw [he.deposits]
      simp [deposits]

end transact

/-! ## Merge -/

section mergeSteps

/-- The nullifiers a chain of merge steps spends, in order. -/
def mergeNfs (h : Hashes) : Merge.Z → List Merge.Wit → List F
  | _, [] => []
  | z, w :: ws => Merge.nf h z w :: mergeNfs h (Merge.next h z w) ws

theorem mergeNfs_length (z : Merge.Z) (ws : List Merge.Wit) : (mergeNfs h z ws).length = ws.length := by
  induction ws generalizing z with
  | nil => rfl
  | cons w ws ih => simp [mergeNfs, ih]

theorem mergeNfs_getElem (z : Merge.Z) (ws : List Merge.Wit) {k : ℕ} (hk : k < ws.length) :
    (mergeNfs h z ws)[k]'(by rw [mergeNfs_length]; exact hk) =
      Merge.nf h (mergeAlong h z ws k) ws[k] := by
  induction ws generalizing z k with
  | nil => simp at hk
  | cons w ws ih =>
    cases k with
    | zero => simp [mergeNfs, mergeAlong]
    | succ k => simpa [mergeNfs, mergeAlong] using ih (Merge.next h z w) (by simpa using hk)

theorem Merge.shaAlong_eq (z : Merge.Z) (ws : List Merge.Wit) :
    Merge.shaAlong h z ws = chainCalls h z.nfChain.val ((mergeNfs h z ws).map fun nf => [nf.val]) := by
  induction ws generalizing z with
  | nil => rfl
  | cons w ws ih =>
    simp only [Merge.shaAlong, ih, mergeNfs, List.map_cons, chainCalls, Merge.shaCall]
    rw [show (Merge.next h z w).nfChain.val = h.hc z.nfChain.val [(Merge.nf h z w).val]
      from hc_val _ _]

theorem mergeFold_nfChain (z : Merge.Z) (ws : List Merge.Wit) :
    (ws.foldl (Merge.next h) z).nfChain.val =
      ((mergeNfs h z ws).map fun nf => [nf.val]).foldl h.hc z.nfChain.val := by
  induction ws generalizing z with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons, ih, mergeNfs, List.map_cons]
    rw [show (Merge.next h z w).nfChain.val = h.hc z.nfChain.val [(Merge.nf h z w).val]
      from hc_val _ _]

theorem mergeAlong_succ (z : Merge.Z) (ws : List Merge.Wit) {k : ℕ} (hk : k < ws.length) :
    mergeAlong h z ws (k + 1) = Merge.next h (mergeAlong h z ws k) ws[k] :=
  foldl_take_succ _ _ _ hk

theorem mergeAlong_remaining (z : Merge.Z) (ws : List Merge.Wit) {k : ℕ} (hk : k ≤ ws.length) :
    (mergeAlong h z ws k).remaining = z.remaining - k := by
  induction k with
  | zero => simp [mergeAlong]
  | succ k ih =>
    rw [mergeAlong_succ _ _ (by omega), Merge.next]
    simp only [ih (by omega)]
    push_cast; ring

end mergeSteps

section mergeProof

variable {S : Set (List F)} {O : Set (F × F × F)} {s : State}

theorem foldl_hc_lt (xs : List (List ℕ)) {c : ℕ} (hc : c < AMOUNT_BOUND) :
    xs.foldl h.hc c < AMOUNT_BOUND := by
  induction xs generalizing c with
  | nil => exact hc
  | cons x xs ih => exact ih (h.hc_lt _ _)

theorem mergeChain {req : Verifier.MergeReq} {ws : List Merge.Wit}
    (hok : Verifier.MergeOK h E A req ws s) :
    (∀ k (hk : k < ws.length),
      Merge.Spec h (mergeAlong h (req.z0 h E) ws k) ws[k] (mergeAlong h (req.z0 h E) ws (k + 1))) ∧
      req.zi h E = mergeAlong h (req.z0 h E) ws ws.length := by
  obtain ⟨hstep, hend⟩ := Chain.along (Merge.next h) (fun _ _ _ hs => hs.next) hok.proof.2
  exact ⟨hstep, by rw [hend]; simp [mergeAlong]⟩

/-- The nullifiers the merge steps spend are the request's, in order. -/
theorem merge_nfs (hyp : RunHyp R S O) {req : Verifier.MergeReq} {ws : List Merge.Wit}
    (hok : Verifier.MergeOK h E A req ws s)
    (hsha : (Action.merge req ws).shaCalls h E s ⊆ R.shaCalls) :
    mergeNfs h (req.z0 h E) ws = req.nullifiers := by
  have hlen := hok.proof.1
  have hend := (mergeChain hok).2
  have hnc : (Verifier.nullifierChain h req.nullifiers) =
      (req.nullifiers.map fun nf => [nf.val]).foldl h.hc 0 := by
    simp [Verifier.nullifierChain, List.foldl_map]
  have hz0 : (req.z0 h E).nfChain = 0 := rfl
  have hzi : (req.zi h E).nfChain = (Verifier.nullifierChain h req.nullifiers : F) := rfl
  have h1 := mergeFold_nfChain (h := h) (req.z0 h E) ws
  rw [show ws.foldl (Merge.next h) (req.z0 h E) = mergeAlong h (req.z0 h E) ws ws.length by
    simp [mergeAlong], ← hend, hzi, hz0, ZMod.val_zero,
    val_cast ((by rw [hnc]; exact foldl_hc_lt _ (by unfold AMOUNT_BOUND; positivity) :
      Verifier.nullifierChain h req.nullifiers < AMOUNT_BOUND).trans amount_lt_r), hnc] at h1
  simp only [Action.shaCalls] at hsha
  have hsa := Merge.shaAlong_eq (h := h) (req.z0 h E) ws
  rw [hz0, ZMod.val_zero] at hsa
  have := chain_inj h R.shaCalls hyp.sha _ _ 0 0 (by simp [mergeNfs_length, hlen])
    (by rw [← hsa]; exact fun p hp => hsha (Or.inl hp)) (fun p hp => hsha (Or.inr hp)) h1.symm
  have hinj : Function.Injective fun nf : F => [nf.val] := fun a b hab => by
    simpa using ZMod.val_injective _ (by simpa using hab)
  exact (List.map_injective_iff.mpr hinj) this.2

theorem sum_take_succ {α M : Type} [AddMonoid M] (f : α → M) (l : List α) {k : ℕ}
    (hk : k < l.length) : ((l.take (k + 1)).map f).sum = ((l.take k).map f).sum + f l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton]

/-- The merged note: worth the inputs less the fee, under the owner and salt every step signed. -/
theorem merge_output (hyp : RunHyp R S O) {req : Verifier.MergeReq} {ws : List Merge.Wit}
    (hok : Verifier.MergeOK h E A req ws s) (hnd : req.nullifiers.Nodup)
    (hcalls : (Action.merge req ws).calls h E s ⊆ R.calls) :
    req.noteHash = noteHash h E.chain (Verifier.mergeOpening req ws).pk
        (Verifier.mergeOpening req ws).value (req.token : F) (Verifier.mergeOpening req ws).salt ∧
      (Verifier.mergeOpening req ws).value.val + req.fee = (ws.map fun w => (Merge.value w).val).sum ∧
      (Verifier.mergeOpening req ws).value.val < AMOUNT_BOUND ∧
      [DOMAIN_NOTE, E.chain, (Verifier.mergeOpening req ws).pk, (Verifier.mergeOpening req ws).value,
        (req.token : F), (Verifier.mergeOpening req ws).salt] ∈ R.calls ∧
      ∀ w ∈ ws, w.outPk = (Verifier.mergeOpening req ws).pk ∧
        w.outSalt = (Verifier.mergeOpening req ws).salt := by
  have hlen := hok.proof.1
  obtain ⟨hstep, hend⟩ := mergeChain hok
  simp only [Action.calls] at hcalls
  set z0 := req.z0 h E with hz0
  have hn0 : 0 < ws.length := by rw [hlen]; exact List.length_pos_iff.mpr hok.nfs.1
  have hnr : ws.length ≤ r := by rw [hlen]; simpa [ZMod.card] using hnd.length_le_card
  have fixed := fun k => mergeAlong_fixed (h := h) z0 ws k
  have hrem : ∀ k ≤ ws.length, (mergeAlong h z0 ws k).remaining = (ws.length : F) - k :=
    fun k hk => by rw [mergeAlong_remaining _ _ hk]; simp [hz0, Verifier.MergeReq.z0, hlen]
  -- The last step is the only one that takes the fee.
  have hlast : ∀ k < ws.length, ((mergeAlong h z0 ws k).remaining = 1 ↔ k + 1 = ws.length) := by
    intro k hk
    rw [hrem k hk.le, sub_eq_iff_eq_add, ← Nat.cast_one, ← Nat.cast_add]
    constructor
    · intro he
      have := (ZMod.natCast_eq_natCast_iff' ws.length (1 + k) r).mp he
      rcases Nat.lt_or_ge ws.length r with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show 1 + k < r by omega)] at this; omega
      · have hr : ws.length = r := le_antisymm hnr hge
        rcases Nat.lt_or_ge (1 + k) r with hk1 | hk1
        · rw [hr, Nat.mod_self, Nat.mod_eq_of_lt hk1] at this; omega
        · omega
    · intro he; rw [show 1 + k = ws.length by omega]
  have hval_lt : ∀ k (hk : k < ws.length), (Merge.value ws[k]).val < AMOUNT_BOUND := by
    intro k hk
    have := hstep k hk
    unfold Merge.value; split_ifs
    · exact this.burnValue_lt
    · exact this.noteValue_lt
  have hcall : ∀ k (hk : k < ws.length), Merge.calls h (mergeAlong h z0 ws k) ws[k] ⊆ R.calls :=
    fun k hk => (Merge.callsAlong_mem hk).trans hcalls
  have hnext_nh : ∀ k (hk : k < ws.length), (mergeAlong h z0 ws (k + 1)).noteHash =
      noteHash h (mergeAlong h z0 ws k).chain ws[k].outPk (Merge.out (mergeAlong h z0 ws k) ws[k])
        (mergeAlong h z0 ws k).token ws[k].outSalt := by
    intro k hk
    rw [mergeAlong_succ _ _ hk]; rfl
  have hadd : ∀ a b : F, a.val < AMOUNT_BOUND → b.val < AMOUNT_BOUND → (a + b).val = a.val + b.val :=
    fun a b ha hb => ZMod.val_add_of_lt (by
      have := two_pow_le_r (n := 249) (by norm_num); unfold AMOUNT_BOUND at *; omega)
  -- Step by step: the running sum, and one owner and salt.
  have hacc : ∀ k (hk : k < ws.length), ws[k].prevSum = ((ws.take k).map Merge.value).sum ∧
      ws[k].outPk = ws[0].outPk ∧ ws[k].outSalt = ws[0].outSalt ∧
      (((ws.take k).map Merge.value).sum).val = ((ws.take k).map fun w => (Merge.value w).val).sum ∧
      (((ws.take k).map Merge.value).sum).val < AMOUNT_BOUND := by
    intro k hk
    induction k with
    | zero =>
      have h0 := (hstep 0 hk).first (by simp [mergeAlong, hz0, Verifier.MergeReq.z0])
      simp [h0, AMOUNT_BOUND]
    | succ k ih =>
      obtain ⟨ip, ipk, ips, iv, ilt⟩ := ih (by omega)
      have hs := hstep (k + 1) hk
      have hnh := hnext_nh k (by omega)
      have hne : (mergeAlong h z0 ws (k + 1)).noteHash ≠ 0 := by
        rw [hnh]
        exact hyp.ne0 _ (Or.inl (hcall k (by omega) (by simp [Merge.calls])))
      have hl := hs.later hne
      rw [hnh] at hl
      unfold noteHash at hl
      have heq := hyp.inj _ (Or.inl (hcall (k + 1) hk (by simp [Merge.calls]))) _
        (Or.inl (hcall k (by omega) (by simp [Merge.calls]))) hl
      simp only [List.cons.injEq] at heq
      have hout : Merge.out (mergeAlong h z0 ws k) ws[k] =
          ((ws.take k).map Merge.value).sum + Merge.value ws[k] := by
        unfold Merge.out
        rw [if_neg (by rw [hlast k (by omega)]; omega), ip]
      refine ⟨by rw [heq.2.2.2.1, hout, sum_take_succ _ _ (by omega)], by rw [heq.2.2.1, ipk],
        by rw [heq.2.2.2.2.2.1, ips], ?_, ?_⟩
      · rw [sum_take_succ _ _ (by omega), sum_take_succ _ _ (by omega),
          hadd _ _ ilt (hval_lt k (by omega)), iv]
      · rw [sum_take_succ _ _ (by omega), ← hout]; exact (hstep k (by omega)).out_lt
  -- The last step pays the fee.
  set m := ws.length - 1 with hm
  have hmn : m < ws.length := by omega
  have hws : ws.take (m + 1) = ws := by rw [show m + 1 = ws.length by omega, List.take_length]
  obtain ⟨ip, ipk, ips, iv, ilt⟩ := hacc m hmn
  have hfm := fixed m
  simp only at hfm
  have hout : Merge.out (mergeAlong h z0 ws m) ws[m] = (ws.map Merge.value).sum - (req.fee : F) := by
    unfold Merge.out
    rw [if_pos ((hlast m hmn).mpr (by omega)), ip, ← sum_take_succ _ _ hmn, hws, hfm.2.2.2.2.2.1]
    rfl
  have hopen : Verifier.mergeOpening req ws =
      ⟨ws[m].outPk, (ws.map Merge.value).sum - req.fee, ws[m].outSalt⟩ := by
    unfold Verifier.mergeOpening
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hmn]
  have hnh := hnext_nh m hmn
  rw [show m + 1 = ws.length by omega, ← hend, hout] at hnh
  have hfee : ((req.fee : ℕ) : F).val = req.fee := val_cast (hok.ranges.1.trans amount_lt_r)
  have hlt := (hstep m hmn).out_lt
  rw [hout] at hlt
  have hS : ((ws.map Merge.value).sum).val =
      ((ws.map Merge.value).sum - (req.fee : F)).val + req.fee := by
    have := hadd _ ((req.fee : ℕ) : F) hlt (by rw [hfee]; exact hok.ranges.1)
    rw [sub_add_cancel, hfee] at this
    exact this
  have hSv : ((ws.map Merge.value).sum).val = (ws.map fun w => (Merge.value w).val).sum := by
    calc ((ws.map Merge.value).sum).val
        = (((ws.take m).map Merge.value).sum + Merge.value ws[m]).val := by
          rw [← sum_take_succ _ _ hmn, hws]
      _ = ((ws.take m).map fun w => (Merge.value w).val).sum + (Merge.value ws[m]).val := by
          rw [hadd _ _ ilt (hval_lt m hmn), iv]
      _ = (ws.map fun w => (Merge.value w).val).sum := by
          rw [← sum_take_succ (fun w => (Merge.value w).val) _ hmn, hws]
  rw [hopen]
  refine ⟨?_, ?_, hlt, ?_, ?_⟩
  · rw [show req.noteHash = (req.zi h E).noteHash from rfl, hnh, hfm.2.1, hfm.1]
    rfl
  · simp only; omega
  · have := hcall m hmn (show [DOMAIN_NOTE, (mergeAlong h z0 ws m).chain, ws[m].outPk,
      Merge.out (mergeAlong h z0 ws m) ws[m], (mergeAlong h z0 ws m).token, ws[m].outSalt] ∈
      Merge.calls h (mergeAlong h z0 ws m) ws[m] by simp [Merge.calls])
    rw [hout, hfm.2.1, hfm.1] at this
    exact this
  · intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    obtain ⟨-, hpk, hsalt, -⟩ := hacc k hk
    exact ⟨hpk.trans ipk.symm, hsalt.trans ips.symm⟩

end mergeProof

section mergeInv

variable {S : Set (List F)} {O : Set (F × F × F)} {s s' : State}

/-- A merge step's input, opened. -/
theorem Inv.merge_in (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {req : Verifier.MergeReq} {ws : List Merge.Wit} (hc : StepCtx R s (.merge req ws))
    (hok : Verifier.MergeOK h E A req ws s) {k : ℕ} (hk : k < ws.length) :
    Opened R s req.token ws[k].idx.val (authKeyHash h ws[k].ak) ws[k].nk
      (Merge.value ws[k]).val := by
  have hs := (mergeChain hok).1 k hk
  have hcalls := hc.calls
  simp only [Action.calls] at hcalls
  have hcall := (Merge.callsAlong_mem hk).trans hcalls
  have fk := mergeAlong_fixed (h := h) (req.z0 h E) ws k
  simp only at fk
  have ht := hok.token.1
  have htok : (mergeAlong h (req.z0 h E) ws k).token.val = req.token := by
    rw [fk.1]; exact val_cast (ht.trans (two_pow_le_r (by norm_num)))
  have hchain : (mergeAlong h (req.z0 h E) ws k).chain = E.chain := fk.2.1
  have hroot : (mergeAlong h (req.z0 h E) ws k).root = req.root := fk.2.2.1
  have htokF : ((req.token : ℕ) : F) = (mergeAlong h (req.z0 h E) ws k).token := fk.1.symm
  have hm := hs.member
  rw [hroot] at hm
  unfold Merge.leaf at hm
  unfold Merge.calls at hcall
  cases hb : ws[k].isBurn
  · simp only [hb, Bool.false_eq_true, if_false] at hm
    rw [htok, hchain, ← htokF] at hm
    have := Opened.of_note (R := R) (s := s) (hI.note_member hyp hpre hok.root ht
      (akh := authKeyHash h ws[k].ak) (nk := ws[k].nk) (v := ws[k].noteValue)
      (salt := ws[k].noteSalt) hs.idx_lt
      ⟨by have := hcall (by simp : [↑(field0 NOTE_HASH_TAG (mergeAlong h (req.z0 h E) ws k).token.val),
            noteHash h (mergeAlong h (req.z0 h E) ws k).chain (Merge.pk (h := h) ws[k])
              ws[k].noteValue (mergeAlong h (req.z0 h E) ws k).token ws[k].noteSalt, 0, 0] ∈ _)
          rwa [htok, hchain, ← htokF] at this,
        by have := hcall (by simp : [DOMAIN_NOTE, (mergeAlong h (req.z0 h E) ws k).chain,
            Merge.pk (h := h) ws[k], ws[k].noteValue, (mergeAlong h (req.z0 h E) ws k).token,
            ws[k].noteSalt] ∈ _)
           rwa [hchain, ← htokF] at this,
        hcall (by simp)⟩
      (by
        intro y hy
        apply hcall
        right
        simp only [Merge.leaf, hb, Bool.false_eq_true, if_false]
        rwa [htok, hchain, ← htokF])
      hm)
    simpa [Merge.value, hb] using this
  · simp only [hb, if_true] at hm
    rw [htok, hchain] at hm
    have := Opened.of_transfer (R := R) (src := ws[k].burnFrom) (hI.burn_member hyp hpre hok.root ht
      (akh := authKeyHash h ws[k].ak) (nk := ws[k].nk) (salt := ws[k].burnSalt)
      (src := ws[k].burnFrom) (value := ws[k].burnValue) hs.idx_lt
      ⟨by have := hcall (by simp : [↑(field0 TRANSFER_TAG (mergeAlong h (req.z0 h E) ws k).token.val),
            ws[k].burnFrom, ↑(addressOf (burnDigest h (mergeAlong h (req.z0 h E) ws k).chain
            (Merge.pk (h := h) ws[k]) ws[k].burnSalt)), ws[k].burnValue] ∈ _)
          rwa [htok, hchain] at this,
        hcall (by simp)⟩
      (by
        have ho := hc.openings
        exact ho ⟨ws[k], List.getElem_mem hk, hb, rfl⟩)
      (by
        intro y hy
        apply hcall
        right
        simp only [Merge.leaf, hb, if_true]
        rwa [htok, hchain])
      hm) hI
    simpa [Merge.value, hb] using this

/-- The nullifier of a merge step's input is the request's at that place. -/
theorem merge_nf (hyp : RunHyp R S O) {req : Verifier.MergeReq} {ws : List Merge.Wit}
    (hc : StepCtx R s (.merge req ws)) (hok : Verifier.MergeOK h E A req ws s) {k : ℕ}
    (hk : k < ws.length) :
    nullifier h E.chain (ws[k].idx.val : F) ws[k].nk =
      req.nullifiers[k]'(by rw [← hok.proof.1]; exact hk) := by
  have hn := merge_nfs hyp hok hc.sha
  have := mergeNfs_getElem (h := h) (req.z0 h E) ws hk
  have fk := (mergeAlong_fixed (h := h) (req.z0 h E) ws k).2.1
  simp only [hn] at this
  rw [this, Merge.nf, fk, ZMod.natCast_zmod_val]
  rfl

theorem Inv.merge (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {req : Verifier.MergeReq} {ws : List Merge.Wit} (hc : StepCtx R s (.merge req ws))
    (hs : Verifier.merge h E A req ws s = some s') : Inv R s' := by
  obtain ⟨hok, hnd, hcap1, s3, hp, rfl⟩ := merge_spec hs
  have hlen := hok.proof.1
  obtain ⟨hnh, hval, hvlt, hcallo, -⟩ := merge_output hyp hok hnd hc.calls
  set t := req.token with ht
  set L := s.ledger.leaves.length with hL
  set o := Verifier.mergeOpening req ws
  have hfr := hp.1
  set s2 := (s.spendAll req.nullifiers).append h (.note t req.noteHash) with hs2
  have f_leaves : (Verifier.recordSpent (ws.map fun w => w.idx.val)
      (Verifier.recordNote L o s3)).ledger = s3.ledger := rfl
  have f_tokens : (Verifier.recordSpent (ws.map fun w => w.idx.val)
      (Verifier.recordNote L o s3)).tokens = s3.tokens := rfl
  have f_used : (Verifier.recordSpent (ws.map fun w => w.idx.val)
      (Verifier.recordNote L o s3)).verifier.used = s3.verifier.used := rfl
  have f_spent : (Verifier.recordSpent (ws.map fun w => w.idx.val)
      (Verifier.recordNote L o s3)).ghost.spent = s.ghost.spent ++ ws.map fun w => w.idx.val := by
    simp [Verifier.recordSpent, Verifier.recordNote, hfr.ghost, hs2, State.append, State.spendAll]
  have f_notes : (Verifier.recordSpent (ws.map fun w => w.idx.val)
      (Verifier.recordNote L o s3)).ghost.notes = Function.update s.ghost.notes L (some o) := by
    simp [Verifier.recordSpent, Verifier.recordNote, hfr.ghost, hs2, State.append, State.spendAll]
  have h3l : s3.ledger.leaves = s.ledger.leaves ++ [.note t req.noteHash] := by
    rw [hfr.ledger]; simp [hs2, State.append, State.spendAll]
  have h3h : s3.ledger.head = h.hc s.ledger.head (Leaf.note t req.noteHash).words := by
    rw [hfr.ledger]; simp [hs2, State.append, State.spendAll]
  have h3u : s3.verifier.used = s.verifier.used ∪ {nf | nf ∈ req.nullifiers} := by
    rw [hfr.used]; simp [hs2, State.append, State.spendAll]
  have h3m : s3.ledger.checkpoints = s.ledger.checkpoints ∧ s3.ledger.provedIn = s.ledger.provedIn ∧
      s3.ledger.rootState = s.ledger.rootState := by
    rw [hfr.ledger]; simp [hs2, State.append, State.spendAll]
  have h2t : s2.tokens = s.tokens := by simp [hs2, State.append, State.spendAll]
  have he : Extends s (Verifier.recordSpent (ws.map fun w => w.idx.val)
      (Verifier.recordNote L o s3)) [.note t req.noteHash] :=
    ⟨by rw [f_leaves, h3l], fun j hj => by rw [f_notes, Function.update_apply, if_neg (by omega)]⟩
  have hin := fun k (hk : k < ws.length) => hI.merge_in hyp hpre hc hok hk
  have hmem : ∀ j ∈ ws.map (fun w => w.idx.val), j < L ∧ ∃ akh nk, Opens R s j akh nk ∧
      nullifier h E.chain j nk ∈ ({nf | nf ∈ req.nullifiers} : Set F) := by
    intro j hj
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hj
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨(hin k hk).lt, _, _, (hin k hk).opens, by
      rw [merge_nf hyp hc hok hk]; exact List.getElem_mem _⟩
  have htokn : s3.tokens t ≠ none := (hp.tokens_iff t).mpr (by rw [h2t]; exact hok.token.2.1)
  apply hI.extend he
  · intro t' ht'
    rw [f_tokens] at ht'
    exact hI.registered t' (by rw [← h2t]; exact (hp.tokens_iff t').mp ht')
  · intro t' ht'
    rw [f_tokens]
    exact (hp.tokens_iff t').mpr (by rw [h2t]; exact ht')
  · rw [f_leaves, h3h, h3l, hI.head, chainOf_append]
  · rw [f_leaves, h3l, List.length_append]; simpa using hcap1
  · rw [f_leaves]; exact h3m
  · intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact ⟨hok.token.1, by rw [f_tokens]; exact htokn⟩
  · intro j t' nh hj hl
    rw [f_leaves, h3l] at hl
    rw [f_notes]
    have hjL : j = L := by
      have := (List.getElem?_eq_some_iff.mp hl).1
      simp at this; omega
    subst hjL
    rw [List.getElem?_append_right le_rfl] at hl
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Leaf.note.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨o, by simp, hnh, hvlt, hcallo⟩
  · exact f_spent
  · intro x hx
    rw [f_used, h3u]; exact Or.inl hx
  · rw [List.nodup_append]
    refine ⟨hI.nodup, ?_, ?_⟩
    · rw [List.nodup_iff_injective_get]
      intro a b hab
      simp only [List.get_eq_getElem, List.getElem_map] at hab
      have ha : a.val < ws.length := by simpa using a.isLt
      have hb : b.val < ws.length := by simpa using b.isLt
      obtain ⟨-, hnk⟩ := R.opens_unique hyp (hin a ha).opens (hab ▸ (hin b hb).opens)
      have h1 := merge_nf hyp hc hok ha
      have h2 := merge_nf hyp hc hok hb
      rw [hnk, hab] at h1
      rw [h1] at h2
      exact Fin.ext (by simpa using (List.Nodup.getElem_inj_iff hnd).mp h2)
    · intro j hj j' hj' hjj
      subst hjj
      obtain ⟨-, akh, nk, hop, hnf⟩ := hmem j hj'
      refine hI.fresh hyp hop ?_ hj
      intro hu
      exact hok.nfs.2 _ hnf hu
  · intro j hj
    obtain ⟨hlt, akh, nk, hop, hnf⟩ := hmem j hj
    refine ⟨by rw [he.leaves, List.length_append]; omega, akh, nk, (he.opens hlt).mpr hop, ?_⟩
    rw [f_used, h3u]; exact Or.inr hnf
  · apply books_step hI hp h2t f_tokens (c := o.value.val)
      (u := (ws.map fun w => (Merge.value w).val).sum)
    · omega
    · intro t'
      rw [he.created]
      simp only [List.length_cons, List.length_nil, zero_add, List.range_one, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, noteValueAt, f_leaves, h3l, f_notes]
      rw [List.getElem?_append_right le_rfl]
      by_cases htt : t' = t
      · subst htt; rw [← hL]; simp
      · rw [← hL]; simp [htt, Ne.symm htt]
    · intro t'
      rw [he.consumed t' f_spent (fun j hj => (hI.spent j hj).1)]
      congr 1
      rw [List.map_map]
      have : ∀ k (hk : k < ws.length),
          leafValueAt (Verifier.recordSpent (ws.map fun w => w.idx.val)
            (Verifier.recordNote L o s3)) t' ws[k].idx.val =
            if t' = t then (Merge.value ws[k]).val else 0 := by
        intro k hk
        rw [he.leafValueAt (hin k hk).lt]
        split_ifs with htt
        · rw [htt]; exact (hin k hk).value
        · exact (hin k hk).other t' htt
      split_ifs with htt
      · apply congrArg
        apply List.ext_getElem (by simp)
        intro k h1 h2
        simp only [List.getElem_map, Function.comp]
        rw [this k (by simpa using h1), if_pos htt]
      · apply List.sum_eq_zero
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        simp only [List.getElem_map, Function.comp]
        rw [this k (by simpa using hk), if_neg htt]
    · intro t' a
      rw [he.deposits]
      simp [deposits]

end mergeInv

/-! ## Rage exit -/

section rageInv

variable {S : Set (List F)} {O : Set (F × F × F)} {s s' : State}

theorem decode_field0 {tag t : ℕ} (htag : tag < 2 ^ 32) (ht : t < TOKEN_BOUND) :
    Verifier.decode (field0 tag t) = (tag, t) := by
  unfold Verifier.decode field0 TOKEN_BOUND at *
  ext <;> simp <;> omega

/-- The deposit a rage exit refunds: the ledger's transfer at the segment's start, whose burn
address the proof's key derives. -/
theorem Inv.rage_deposit (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {req : Verifier.RageReq} {w : RE.Wit} (hc : StepCtx R s (.rageExit req w))
    (hcommits : req.commits ≠ []) (hlen : req.commits.length ≤ req.checkpointIndex)
    (hchain : s.hashChainAt req.checkpointIndex = some (req.commits.foldl h.hc req.prev))
    (htag : (Verifier.decode ((req.commits.headD []).getD 0 0)).1 = TRANSFER_TAG)
    (haddr : (req.commits.headD []).getD 2 0 < r)
    (hspec : RE.Spec h ⟨req.nf, E.chainId, req.index, (req.commits.headD []).getD 2 0⟩ w) :
    ∃ t a v, s.ledger.leaves[req.index]? = some (.transfer t a
        (addressOf (burnDigest h E.chain (RE.pk h w) w.salt)) v) ∧
      (Verifier.decode ((req.commits.headD []).getD 0 0)).2 = t ∧
      (req.commits.headD []).getD 1 0 = a ∧ (req.commits.headD []).getD 3 0 = v ∧
      Opened R s t req.index w.akh (nullifyingKey h w.sk) v ∧
      req.nf = nullifier h E.chain (req.index : F) (nullifyingKey h w.sk) := by
  obtain ⟨hend, hc0⟩ := hI.hashChainAt hchain
  have hseg := segment_binds h s.ledger.leaves R.shaCalls hyp.sha
    ((canonCalls_mono hpre).trans (fun p hp => Or.inr hp)) hend
    (fun p hp => hc.sha (by simpa [Action.shaCalls] using hp)) hlen (hc0.trans rfl)
  have hidx : req.index < req.checkpointIndex := by
    unfold Verifier.RageReq.index
    have := List.length_pos_iff.mpr hcommits; omega
  have hidxL : req.index < s.ledger.leaves.length := lt_of_lt_of_le hidx hend
  -- The segment's first commitment is the ledger's leaf at its start.
  have hhead : req.commits.headD [] = s.ledger.leaves[req.index].words := by
    have := congrArg (fun l => l.headD []) hseg.2
    simp only at this
    rw [this, show req.checkpointIndex - req.commits.length = req.index from rfl]
    rw [List.headD_eq_head?_getD, List.head?_map, List.head?_drop, List.getElem?_take,
      if_pos hidx, List.getElem?_eq_getElem hidxL]
    rfl
  have hl := List.getElem?_eq_getElem hidxL
  have hvalid := (hI.valid _ (List.getElem_mem hidxL)).1
  rw [hhead] at htag haddr hspec ⊢
  cases hleaf : s.ledger.leaves[req.index] with
  | note t nh =>
    rw [hleaf] at htag hvalid
    simp only [Leaf.words, List.getD_cons_zero, decode_field0 NOTE_HASH_TAG_lt hvalid] at htag
    exact absurd htag.symm TAGS_ne
  | transfer t a b v =>
    rw [hleaf] at haddr hspec hvalid hl
    simp only [Leaf.words, List.getD_cons_zero, List.getD_cons_succ,
      decode_field0 TRANSFER_TAG_lt hvalid.1] at haddr hspec ⊢
    have hb : b = addressOf (burnDigest h E.chain (RE.pk h w) w.salt) := by
      have := hspec.address
      exact (cast_inj (hvalid.2.2.2.2.1.trans address_lt_r) ((address_lt _).trans address_lt_r)).mp
        (by simpa [Env.chain, RE.pk] using this)
    subst hb
    have hcalls := hc.calls
    simp only [Action.calls, RE.calls] at hcalls
    have hop : Opens R s req.index w.akh (nullifyingKey h w.sk) :=
      ⟨hcalls (by simp), Or.inr ⟨t, a, v, w.salt, hl, hc.openings (by simp [Action.openings, RE.pk])⟩⟩
    refine ⟨t, a, v, hl, rfl, rfl, rfl, ⟨hidxL, hop, by simp [leafValueAt, hl],
      fun t' ht' => by simp [leafValueAt, hl, Ne.symm ht']⟩, ?_⟩
    have := hspec.nf; simp only at this; rw [this]; rfl

theorem Inv.rageExit (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {req : Verifier.RageReq} {w : RE.Wit} (hc : StepCtx R s (.rageExit req w))
    (hs : Verifier.rageExit h E req w s = some s') : Inv R s' := by
  obtain ⟨-, -, hcommits, hlen, hchain, htag, htok, haddr, hspec, hnf, s2, h2, rfl⟩ :=
    rageExit_spec hs
  obtain ⟨t, a, v, hl, ht, ha, hv, hop, hnfeq⟩ :=
    hI.rage_deposit hyp hpre hc hcommits hlen hchain htag haddr hspec
  rw [ht, ha, hv] at h2
  rw [ht] at htok
  have hp := payOut_paid h2
  have hfr := hp.1
  have f_spent : (Verifier.recordSpent [req.index] s2).ghost.spent = s.ghost.spent ++ [req.index] := by
    simp [Verifier.recordSpent, hfr.ghost, State.spendAll]
  have hsl : s2.ledger = s.ledger := by rw [hfr.ledger]; rfl
  have hsg : s2.ghost = s.ghost := by rw [hfr.ghost]; rfl
  have hsu : s2.verifier.used = s.verifier.used ∪ {req.nf} := by
    rw [hfr.used]; simp [State.spendAll]
  have h0t : (s.spendAll [req.nf]).tokens = s.tokens := rfl
  have he : Extends s (Verifier.recordSpent [req.index] s2) [] :=
    Extends.refl _ (by simp [Verifier.recordSpent, hsl]) (by simp [Verifier.recordSpent, hsg])
  have hfresh : req.index ∉ s.ghost.spent := hI.fresh hyp hop.opens (by rw [← hnfeq]; exact hnf)
  apply hI.extend he
  · intro t' ht'
    exact hI.registered t' (by rw [← h0t]; exact (hp.tokens_iff t').mp ht')
  · intro t' ht'
    exact (hp.tokens_iff t').mpr (by rw [h0t]; exact ht')
  · simp [Verifier.recordSpent, hsl, hI.head]
  · simp [Verifier.recordSpent, hsl, hI.cap]
  · simp [Verifier.recordSpent, hsl]
  · simp
  · intro j t' nh hj hl'
    simp [Verifier.recordSpent, hsl] at hl'
    exact absurd (List.getElem?_eq_some_iff.mp hl').1 (by omega)
  · exact f_spent
  · intro x hx; simp [Verifier.recordSpent, hsu, hx]
  · rw [List.nodup_append]
    exact ⟨hI.nodup, List.nodup_singleton _, fun j hj j' hj' hjj => by
      simp at hj'; subst hj' hjj; exact hfresh hj⟩
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst hj
    refine ⟨by rw [he.leaves]; simpa using hop.lt, _, _, (he.opens hop.lt).mpr hop.opens, ?_⟩
    simp [Verifier.recordSpent, hsu, ← hnfeq]
  · apply books_step (s' := Verifier.recordSpent [req.index] s2) hI hp h0t rfl (c := 0) (u := v)
    · omega
    · intro t'; rw [he.created]; simp
    · intro t'
      rw [he.consumed t' f_spent (fun j hj => (hI.spent j hj).1)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [he.leafValueAt hop.lt]
      split_ifs with htt
      · rw [htt, hop.value]
      · rw [hop.other t' htt]
    · intro t' a'
      rw [he.deposits]; simp [deposits]

end rageInv

/-! ## Steps that keep the leaves -/

section keeping

variable {s s' : State}

/-- A step that keeps the leaves, the ghost and the tokens, and leaves the checkpoints, proved roots
and root state canonical, keeps the invariant. -/
theorem Inv.keeping (hI : Inv R s) (hl : s'.ledger.leaves = s.ledger.leaves)
    (hh : s'.ledger.head = s.ledger.head) (hg : s'.ghost.notes = s.ghost.notes)
    (hsp : s'.ghost.spent = s.ghost.spent) (hu : s.verifier.used ⊆ s'.verifier.used)
    (ht : ∀ t, s.tokens t ≠ none → s'.tokens t = s.tokens t)
    (hnew : ∀ t, s'.tokens t ≠ s.tokens t → s.tokens t = none ∧ s'.tokens t = some TokenSt.empty ∧
      t ≠ 0 ∧ t < TOKEN_BOUND)
    (hcp : ∀ i, s'.ledger.checkpoints i ≠ 0 →
      i ≤ s.ledger.leaves.length ∧ s'.ledger.checkpoints i = chainOf h (s.ledger.leaves.take i))
    (hpr : ∀ i ρ, s'.ledger.provedIn i ρ ≠ 0 →
      i ≤ s.ledger.leaves.length ∧ ρ = treeRoot h (hashes h (s.ledger.leaves.take i)))
    (hrs : s'.ledger.rootState.index ≤ s.ledger.leaves.length ∧
      s'.ledger.rootState.chain = chainOf h (s.ledger.leaves.take s'.ledger.rootState.index) ∧
      s'.ledger.rootState.root = treeRoot h (hashes h (s.ledger.leaves.take s'.ledger.rootState.index))) :
    Inv R s' := by
  have he : Extends s s' [] := Extends.refl _ hl hg
  have hcr : ∀ t, created s' t = created s t := fun t => by rw [he.created]; simp
  have hco : ∀ t, consumed s' t = consumed s t := fun t => by
    rw [he.consumed t (hsp.trans (List.append_nil _).symm) (fun j hj => (hI.spent j hj).1)]; simp
  have hde : ∀ t a, deposits s' t a = deposits s t a := fun t a => by unfold deposits; rw [hl]
  -- A token that is new has no leaves, so nothing created, consumed or deposited.
  have hfresh : ∀ t, s.tokens t = none → created s t = 0 ∧ ∀ a, deposits s t a = 0 := by
    intro t ht0
    have hnot : ∀ l ∈ s.ledger.leaves, l.token ≠ t := fun l hl' heq =>
      (hI.valid l hl').2 (heq ▸ ht0)
    refine ⟨?_, fun a => ?_⟩
    · apply List.sum_eq_zero
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      unfold noteValueAt
      cases hlj : s.ledger.leaves[j]? with
      | none => rfl
      | some l =>
        cases l with
        | transfer _ _ _ _ => rfl
        | note t' nh =>
          have := hnot _ (List.mem_of_getElem? hlj)
          cases s.ghost.notes j <;> simp_all [Leaf.token]
    · apply List.sum_eq_zero
      intro x hx
      obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hx
      have := hnot l hl'
      cases l <;> simp_all [Leaf.token]
  refine ⟨fun t ht' => ?_, by rw [hh, hI.head, hl], by rw [hl]; exact hI.cap,
    fun i hi => by rw [hl]; exact hcp i hi, fun i ρ hi => by rw [hl]; exact hpr i ρ hi,
    by rw [hl]; exact hrs, fun l hl' => ?_, fun j t nh hj => ?_, by rw [hsp]; exact hI.nodup,
    fun j hj => ?_, fun t tk htk => ?_⟩
  · by_cases hc : s'.tokens t = s.tokens t
    · exact hI.registered t (hc ▸ ht')
    · exact (hnew t hc).2.2
  · rw [hl] at hl'
    obtain ⟨hv, htk⟩ := hI.valid l hl'
    exact ⟨hv, by rw [ht _ htk]; exact htk⟩
  · rw [hl] at hj
    obtain ⟨o, ho, rest⟩ := hI.notes j t nh hj
    exact ⟨o, by rw [hg, ho], rest⟩
  · rw [hsp] at hj
    obtain ⟨hlt, akh, nk, hop, hnf⟩ := hI.spent j hj
    exact ⟨by rw [hl]; exact hlt, akh, nk, (he.opens hlt).mpr hop, hu hnf⟩
  · rw [hcr, hco]
    simp only [hde]
    by_cases hc : s'.tokens t = s.tokens t
    · exact hI.books t tk (hc ▸ htk)
    · obtain ⟨h0, hempty, -⟩ := hnew t hc
      rw [hempty] at htk; cases htk
      obtain ⟨hcr0, hde0⟩ := hfresh t h0
      refine ⟨⟨rfl, rfl⟩, by simp [hcr0, TokenSt.empty], fun a _ => by simp [hde0 a, TokenSt.empty]⟩

end keeping

/-! ## Token operations -/

section tokenOps

variable {s s' : State}

/-- What appending `new` adds to the deposits of token `t` at `x`. -/
def newDeposits (new : List Leaf) (t : ℕ) (x : Addr) : ℕ :=
  (new.map fun l => match l with
    | .transfer t' _ b v => if t' = t ∧ b = x then v else 0
    | .note .. => 0).sum

/-- A step that moves one token's books, appending at most one transfer of it, keeps the invariant
when the supply grows no faster than the underlying and the burn addresses' balances grow at least
by what they are paid. -/
theorem Inv.token_step (hI : Inv R s) {t : ℕ} {tk tk' : TokenSt} (htk : s.tokens t = some tk)
    {new : List Leaf}
    (hnew : new = [] ∨ ∃ a b v, new = [Leaf.transfer t a b v] ∧ (Leaf.transfer t a b v).Valid)
    (hcap : s.ledger.leaves.length + new.length ≤ TREE_SIZE)
    (hT : s'.tokens = Function.update s.tokens t (some tk'))
    (hL : s'.ledger.leaves = s.ledger.leaves ++ new)
    (hH : s'.ledger.head = new.foldl (fun c l => h.hc c l.words) s.ledger.head)
    (hM : s'.ledger.checkpoints = s.ledger.checkpoints ∧ s'.ledger.provedIn = s.ledger.provedIn ∧
      s'.ledger.rootState = s.ledger.rootState)
    (hG : s'.ghost = s.ghost) (hU : s'.verifier.used = s.verifier.used)
    (hbooks : tk.Books → tk'.Books)
    (hacc : tk'.supply + tk.underlying ≤ tk.supply + tk'.underlying)
    (hbal : ∀ x ∈ R.burnAddrs, tk.bal x + newDeposits new t x ≤ tk'.bal x) :
    Inv R s' := by
  have he : Extends s s' new := ⟨hL, fun j _ => by rw [hG]⟩
  have hnotes : ∀ k < new.length, noteValueAt s' t (s.ledger.leaves.length + k) = 0 := by
    intro k hk
    rcases hnew with rfl | ⟨a, b, v, rfl, -⟩
    · simp at hk
    · unfold noteValueAt
      rw [hL, List.getElem?_append_right (by omega)]
      simp at hk; subst hk; simp
  have hcr : ∀ t', created s' t' = created s t' := fun t' => by
    rw [he.created]
    simp only [add_eq_left]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    rcases hnew with rfl | ⟨a, b, v, rfl, -⟩
    · simp at hk
    · unfold noteValueAt
      rw [hL, List.getElem?_append_right (by omega)]
      simp at hk; subst hk; simp
  have hco : ∀ t', consumed s' t' = consumed s t' := fun t' => by
    rw [he.consumed (js := []) t' (by rw [hG]; simp) (fun j hj => (hI.spent j hj).1)]; simp
  have hde : ∀ t' x, deposits s' t' x = deposits s t' x + newDeposits new t' x := fun t' x => by
    rw [he.deposits]; rfl
  have hreg := hI.registered t (by simp [htk])
  apply hI.extend (js := []) he
  · intro t' ht'
    rw [hT, Function.update_apply] at ht'
    split_ifs at ht' with htt
    · subst htt; exact hreg
    · exact hI.registered t' ht'
  · intro t' ht'
    rw [hT, Function.update_apply]; split_ifs <;> simp_all
  · rw [hH, hL, hI.head, chainOf_eq_foldl, chainOf_eq_foldl, List.map_append, List.foldl_append,
      List.foldl_map, List.foldl_map]
  · rw [hL, List.length_append]; exact hcap
  · exact hM
  · intro l hl
    rcases hnew with rfl | ⟨a, b, v, rfl, hv⟩
    · simp at hl
    · simp only [List.mem_singleton] at hl; subst hl
      exact ⟨hv, by rw [hT]; simp [Leaf.token]⟩
  · intro j t' nh hj hl
    rw [hL] at hl
    rcases hnew with rfl | ⟨a, b, v, rfl, -⟩
    · simp at hl; exact absurd (List.getElem?_eq_some_iff.mp hl).1 (by omega)
    · rw [List.getElem?_append_right hj] at hl
      have : j - s.ledger.leaves.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hl).1; simp at this; omega
      rw [this] at hl; simp at hl
  · rw [hG]; simp
  · rw [hU]
  · simpa using hI.nodup
  · simp
  · intro t' tk2 ht2
    rw [hcr, hco]
    rw [hT, Function.update_apply] at ht2
    split_ifs at ht2 with htt
    · subst htt; cases ht2
      obtain ⟨hb, hbook, hdep⟩ := hI.books _ tk htk
      refine ⟨hbooks hb, by omega, fun x hx => ?_⟩
      rw [hde]; exact (Nat.add_le_add_right (hdep x hx) _).trans (hbal x hx)
    · obtain ⟨hb, hbook, hdep⟩ := hI.books _ tk2 ht2
      refine ⟨hb, hbook, fun x hx => ?_⟩
      rw [hde]
      have : newDeposits new t' x = 0 := by
        rcases hnew with rfl | ⟨a, b, v, rfl, -⟩
        · rfl
        · simp [newDeposits, Ne.symm htt]
      rw [this, add_zero]; exact hdep x hx

end tokenOps

section tokenActions

variable {S : Set (List F)} {O : Set (F × F × F)} {s s' : State}

theorem TokenSt.move_bal (tk : TokenSt) (src dst : Addr) (v x : ℕ) :
    (tk.move src dst v).bal x =
      (if src ≠ 0 ∧ x = src then tk.bal x - v else tk.bal x) + (if dst ≠ 0 ∧ x = dst then v else 0) := by
  unfold TokenSt.move
  by_cases hs : src = 0 <;> by_cases hd : dst = 0 <;>
    simp [hs, hd, Finsupp.update_apply] <;> split_ifs <;> simp_all

theorem TokenSt.move_supply (tk : TokenSt) (src dst : Addr) (v : ℕ) :
    (tk.move src dst v).supply = (if src = 0 then tk.supply + v else tk.supply) - (if dst = 0 then v else 0) := by
  unfold TokenSt.move
  by_cases hs : src = 0 <;> by_cases hd : dst = 0 <;> simp [hs, hd]

theorem TokenSt.move_underlying (tk : TokenSt) (src dst : Addr) (v : ℕ) :
    (tk.move src dst v).underlying = tk.underlying := by
  unfold TokenSt.move
  by_cases hs : src = 0 <;> by_cases hd : dst = 0 <;> simp [hs, hd]

/-- `_update` where it succeeds, field by field. -/
theorem update_post {t : ℕ} {src dst : Addr} {v : ℕ} (hs : ZERC20.update h E t src dst v s = some s') :
    ∃ tk, s.tokens t = some tk ∧ tk.canMove src v ∧ v < AMOUNT_BOUND ∧ src < ADDRESS_BOUND ∧
      dst < ADDRESS_BOUND ∧ s'.tokens = Function.update s.tokens t (some (tk.move src dst v)) ∧
      s'.ghost = s.ghost ∧ s'.verifier = s.verifier ∧ s'.blocked = s.blocked ∧
      s'.ledger.checkpoints = s.ledger.checkpoints ∧ s'.ledger.provedIn = s.ledger.provedIn ∧
      s'.ledger.rootState = s.ledger.rootState ∧ s'.ledger.bound = s.ledger.bound ∧
      s'.ledger.era = s.ledger.era ∧ s'.ledger.eraEnd = s.ledger.eraEnd ∧
      let new := if src = 0 ∨ dst = 0 ∨ v = 0 then [] else [Leaf.transfer t src dst v]
      s'.ledger.leaves = s.ledger.leaves ++ new ∧
        s'.ledger.head = new.foldl (fun c l => h.hc c l.words) s.ledger.head ∧
        (new ≠ [] → s.ledger.leaves.length < TREE_SIZE) := by
  obtain ⟨tk, htk, a1, a2, -, h2, -, -, h5, hs⟩ := update_eq.mp hs
  refine ⟨tk, htk, h5, h2, a1, a2, ?_⟩
  split_ifs at hs ⊢ with hl
  · subst hs; simp [State.setToken]
  · obtain ⟨hcap, rfl⟩ := hs
    simp [State.setToken, State.append, hcap]

/-- A transfer between two accounts, the sender not a burn address. -/
theorem Inv.transferStep (hI : Inv R s) {t : ℕ} {src dst : Addr} {v : ℕ}
    (hsrc : src ≠ 0) (hdst : dst ≠ 0) (hfz : src ∉ R.burnAddrs)
    (hs : ZERC20.update h E t src dst v s = some s') : Inv R s' := by
  obtain ⟨tk, htk, hm, hv, hsl, hdl, hT, hG, hV, -, hcp, hpr, hrs, -, -, -, hL, hH, hcap⟩ :=
    update_post hs
  refine hI.token_step htk ?_ ?_ hT hL hH ⟨hcp, hpr, hrs⟩ hG (by rw [hV])
    (fun hb => TokenSt.move_books hb hm) ?_ ?_
  · split_ifs with hl
    · exact Or.inl rfl
    · simp only [not_or] at hl
      have hreg := hI.registered t (by simp [htk])
      exact Or.inr ⟨src, dst, v, rfl, hreg.2, hl.1, hsl, hl.2.1, hdl, hl.2.2, hv⟩
  · split_ifs with hl
    · simpa using hI.cap
    · have := hcap (by rw [if_neg hl]; simp); simpa using this
  · rw [TokenSt.move_supply, TokenSt.move_underlying]; simp [hsrc, hdst]
  · intro x hx
    have hxs : x ≠ src := fun h => hfz (h ▸ hx)
    rw [TokenSt.move_bal]
    simp only [hxs, and_false, if_false, newDeposits]
    split_ifs with hl hd <;> simp_all [eq_comm]

theorem Inv.donate (hI : Inv R s) {t v : ℕ} (hs : donate t v s = some s') : Inv R s' := by
  simp only [Zerc20.donate, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hs
  obtain ⟨tk, htk, rfl⟩ := hs
  exact hI.token_step (new := []) htk (Or.inl rfl) (by simpa using hI.cap) rfl (by simp [State.setToken])
    rfl ⟨rfl, rfl, rfl⟩ rfl rfl id (by simp) (fun x _ => by simp [newDeposits])

theorem TokenSt.books_underlying {tk : TokenSt} {u : ℕ} (hb : tk.Books) :
    ({ tk with underlying := u } : TokenSt).Books := hb

theorem Inv.unwrap (hI : Inv R s) {t : ℕ} {caller receiver : Addr} {v : ℕ}
    (hfz : caller ∉ R.burnAddrs) (hs : ZERC20.unwrap h E t caller receiver v s = some s') :
    Inv R s' := by
  simp only [ZERC20.unwrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const] at hs
  obtain ⟨⟨hc, -, hv0⟩, -, s1, h1, h2⟩ := hs
  obtain ⟨tk, htk, hm, hv, -, -, hT1, hG1, hV1, -, hcp, hpr, hrs, -, -, -, hL1, hH1, -⟩ := update_post h1
  simp only [ZERC20.release, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq] at h2
  obtain ⟨tk1, htk1, hvu, rfl⟩ := h2
  rw [hT1, Function.update_self, Option.some.injEq] at htk1
  subst htk1
  simp only [true_or, or_true, if_true] at hL1 hH1
  obtain ⟨hb, -, -⟩ := hI.books t tk htk
  have hsup : v ≤ tk.supply := by
    rw [hb.1]
    exact (by simpa [TokenSt.canMove, hc] using hm : v ≤ tk.bal caller).trans (TokenSt.bal_le_total _ _)
  refine hI.token_step (new := [])
    (tk' := { tk.move caller 0 v with underlying := (tk.move caller 0 v).underlying - v }) htk
    (Or.inl rfl) (by simpa using hI.cap)
    (by simp [State.setToken, hT1]) (by simpa [State.setToken] using hL1)
    (by simpa [State.setToken] using hH1) ⟨hcp, hpr, hrs⟩ (by simpa [State.setToken] using hG1)
    (by simp [State.setToken, hV1]) (fun hb => TokenSt.books_underlying (TokenSt.move_books hb hm))
    ?_ ?_
  · simp only [TokenSt.move_supply, TokenSt.move_underlying, hc, if_false, if_true] at hvu ⊢
    omega
  · intro x hx
    have hxc : x ≠ caller := fun h => hfz (h ▸ hx)
    simp [TokenSt.move_bal, hxc, newDeposits]

theorem Inv.wrap (hI : Inv R s) {t : ℕ} {caller receiver : Addr} {v : ℕ}
    (hs : ZERC20.wrap h E t caller receiver v s = some s') : Inv R s' := by
  simp only [ZERC20.wrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const] at hs
  obtain ⟨⟨hc, hr, hv0⟩, tk, htk, s1, h1, h2⟩ := hs
  obtain ⟨tk0, htk0, hm0, hv, -, hcl, hT1, hG1, hV1, -, hcp1, hpr1, hrs1, -, -, -, hL1, hH1, -⟩ :=
    update_post h1
  simp only [State.setToken, Function.update_self, Option.some.injEq] at htk0
  subst htk0
  simp only [true_or, if_true, List.append_nil, List.foldl_nil] at hL1 hH1
  simp only [State.setToken] at hT1 hG1 hV1 hcp1 hpr1 hrs1 hL1 hH1
  rw [Function.update_idem] at hT1
  obtain ⟨hb, -, -⟩ := hI.books t tk htk
  set tk1 := ({ tk with underlying := tk.underlying + v } : TokenSt).move 0 caller v with htk1
  have hb1 : tk1.Books := TokenSt.move_books (TokenSt.books_underlying hb) hm0
  have hsup1 : tk1.supply = tk.supply + v := by simp [htk1, TokenSt.move_supply, hc]
  have hund1 : tk1.underlying = tk.underlying + v := by simp [htk1, TokenSt.move_underlying]
  have hbal1 : ∀ x, tk1.bal x = tk.bal x + if x = caller then v else 0 := by
    intro x; simp [htk1, TokenSt.move_bal, hc]
  split_ifs at h2 with hrc
  · obtain ⟨tk2, htk2, hm2, -, -, hrl, hT2, hG2, hV2, -, hcp2, hpr2, hrs2, -, -, -, hL2, hH2, hcap2⟩ :=
      update_post h2
    rw [hT1, Function.update_self, Option.some.injEq] at htk2
    subst htk2
    simp only [hc, hr, hv0, or_self, if_false] at hL2 hH2 hcap2
    have hreg := hI.registered t (by simp [htk])
    refine hI.token_step htk (Or.inr ⟨caller, receiver, v, rfl, hreg.2, hc, hcl, hr, hrl, hv0, hv⟩)
      (by have := hcap2 (by simp); rw [hL1] at this; simpa using this)
      (by rw [hT2, hT1, Function.update_idem]) (by rw [hL2, hL1])
      (by rw [hH2, hH1]) ⟨hcp2.trans hcp1, hpr2.trans hpr1, hrs2.trans hrs1⟩
      (hG2.trans hG1) (by rw [hV2, hV1]) (fun _ => TokenSt.move_books hb1 hm2) ?_ ?_
    · rw [TokenSt.move_supply, TokenSt.move_underlying, hsup1, hund1]; simp [hc, hr]; omega
    · intro x _
      rw [TokenSt.move_bal, hbal1]
      by_cases hxc : x = caller
      · subst hxc; simp [hc, hr, hrc, newDeposits]
      · by_cases hxr : x = receiver
        · subst hxr; simp [hc, hr, hxc, newDeposits]
        · simp [hxc, hxr, newDeposits, Ne.symm hxr]
  · cases h2
    exact hI.token_step (new := []) htk (Or.inl rfl) (by simpa using hI.cap) hT1 (by simpa using hL1)
      (by simpa using hH1) ⟨hcp1, hpr1, hrs1⟩ hG1 (by rw [hV1]) (fun _ => hb1)
      (by rw [hsup1, hund1]; omega) (fun x _ => by rw [hbal1]; simp [newDeposits])

theorem Inv.claimFees (hI : Inv R s) {t : ℕ} {rcpt : Addr} (hfz : E.verifier ∉ R.burnAddrs)
    (hs : Verifier.claimFees h E t rcpt s = some s') : Inv R s' := by
  by_cases hv : s.verifier.accrued t rcpt = 0
  · simp only [Verifier.claimFees, hv, if_true, Option.some.injEq] at hs
    subst hs; exact hI
  · simp only [Verifier.claimFees, hv, if_false, ZERC20.transfer, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const] at hs
    obtain ⟨⟨hs0, hr0⟩, hs⟩ := hs
    refine Inv.transferStep (s := { s with verifier := { s.verifier with
      accrued := Function.update s.verifier.accrued t
        (Function.update (s.verifier.accrued t) rcpt 0) } }) ?_ hs0 hr0 hfz hs
    exact hI.keeping rfl rfl rfl rfl (fun _ hx => hx) (fun _ _ => rfl) (fun _ h => absurd rfl h)
      hI.checkpoints hI.proved hI.rootState

end tokenActions

/-! ## The ledger's checkpoints and roots, and admin -/

section ledgerActions

variable {S : Set (List F)} {O : Set (F × F × F)} {s s' : State}

theorem Inv.reserveHashChain (hI : Inv R s) (hs : CommitmentLedger.reserveHashChain s = some s') :
    Inv R s' := by
  unfold CommitmentLedger.reserveHashChain at hs
  by_cases h0 : s.ledger.leaves.length = 0
  · simp only [h0, if_true, Option.some.injEq] at hs; subst hs; exact hI
  simp only [h0, if_false, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq] at hs
  obtain ⟨-, rfl⟩ := hs
  refine hI.keeping rfl rfl rfl rfl (fun _ hx => hx) (fun _ _ => rfl) (fun _ h => absurd rfl h)
    (fun i hi => ?_) hI.proved hI.rootState
  simp only [Function.update_apply] at hi ⊢
  split_ifs at hi ⊢ with hil
  · subst hil; exact ⟨le_rfl, by rw [hI.head, List.take_length]⟩
  · exact hI.checkpoints i hi

theorem Inv.checkpointBefore (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {e prev : ℕ} {commits : List (List ℕ)} (hc : StepCtx R s (.checkpointBefore e prev commits))
    (hs : CommitmentLedger.checkpointBefore h e prev commits s = some s') : Inv R s' := by
  simp only [CommitmentLedger.checkpointBefore, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
    exists_const, Option.pure_def, Option.some.injEq, verifySegment_eq] at hs
  obtain ⟨start, ⟨hne, hlen, hch, rfl⟩, hprev, rfl⟩ := hs
  obtain ⟨hend, hc0⟩ := hI.hashChainAt hch
  have hseg := segment_binds h s.ledger.leaves R.shaCalls hyp.sha
    ((canonCalls_mono hpre).trans (fun p hp => Or.inr hp)) hend
    (fun p hp => hc.sha (by simpa [Action.shaCalls] using hp)) hlen hc0
  refine hI.keeping rfl rfl rfl rfl (fun _ hx => hx) (fun _ _ => rfl) (fun _ h => absurd rfl h)
    (fun i hi => ?_) hI.proved hI.rootState
  simp only [Function.update_apply] at hi ⊢
  split_ifs at hi ⊢ with hil
  · subst hil; exact ⟨by omega, hseg.1⟩
  · exact hI.checkpoints i hi

theorem Inv.proveRoot (hI : Inv R s) (hyp : RunHyp R S O) (hpre : s.ledger.leaves <+: R.leaves)
    {new : RootSt} {ws : List Root.Wit} (hc : StepCtx R s (.proveRoot new ws))
    (hs : CommitmentLedger.proveRootTransition h new ws s = some s') : Inv R s' := by
  simp only [CommitmentLedger.proveRootTransition, bind, Option.bind_eq_some_iff,
    guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
  obtain ⟨⟨hcap, -⟩, -, hlt, c, hch, rfl, ⟨hlen, hchain⟩, rfl⟩ := hs
  obtain ⟨hni, hc0⟩ := hI.hashChainAt hch
  obtain ⟨hoi, hoc, hor⟩ := hI.rootState
  have hcalls := hc.calls
  have hsha := hc.sha
  simp only [Action.calls, Action.shaCalls, hoc, hor] at hcalls hsha
  rw [hoc, hor, hc0] at hchain
  have hroot := root_chain hyp hpre hlt.le hlen hni hcap hcalls hsha hchain
  refine hI.keeping rfl rfl rfl rfl (fun _ hx => hx) (fun _ _ => rfl) (fun _ h => absurd rfl h)
    hI.checkpoints (fun i ρ hi => ?_) ⟨hni, hc0, hroot⟩
  simp only at hi
  split_ifs at hi with hiρ
  · obtain ⟨rfl, rfl⟩ := hiρ; exact ⟨hni, hroot⟩
  · exact hI.proved i ρ hi

/-- What an admin step does to the ledger: at most it lowers the bound, or recovers a proved root. -/
theorem admin_ledger {op : AdminOp} (hs : op.exec s = some s') :
    s'.ledger.head = s.ledger.head ∧ s'.ledger.checkpoints = s.ledger.checkpoints ∧
      s'.ledger.provedIn = s.ledger.provedIn ∧
      (s'.ledger.rootState = s.ledger.rootState ∨
        ∃ i ρ c, s.inEra i ρ ∧ s.hashChainAt i = some c ∧ s'.ledger.rootState = ⟨i, c, ρ⟩) := by
  cases op <;>
    simp only [AdminOp.exec, CommitmentLedger.enterEmergency, CommitmentLedger.recover, bind,
      Option.bind_eq_some_iff, guard_eq_some_unit, exists_const, Option.pure_def,
      Option.some.injEq] at hs
  case recover i ρ =>
    obtain ⟨-, -, hin, c, hc, rfl⟩ := hs
    exact ⟨rfl, rfl, rfl, Or.inr ⟨i, ρ, c, hin, hc, rfl⟩⟩
  case enterEmergency b =>
    subst hs; split_ifs <;> simp
  all_goals first
    | (obtain ⟨-, rfl⟩ := hs; simp)
    | (obtain ⟨-, c, -, -, rfl⟩ := hs; simp)

theorem admin_tokens {op : AdminOp} (hs : op.exec s = some s') (t : ℕ) (ht : s'.tokens t ≠ s.tokens t) :
    s.tokens t = none ∧ s'.tokens t = some TokenSt.empty ∧ t ≠ 0 ∧ t < TOKEN_BOUND := by
  cases op <;>
    simp only [AdminOp.exec, CommitmentLedger.enterEmergency, CommitmentLedger.recover, bind,
      Option.bind_eq_some_iff, guard_eq_some_unit, exists_const, Option.pure_def,
      Option.some.injEq] at hs
  case createToken t' =>
    obtain ⟨⟨h1, h2, h3⟩, rfl⟩ := hs
    simp only [Function.update_apply] at ht ⊢
    split_ifs at ht ⊢ with htt
    · subst htt; exact ⟨h1, rfl, h2, h3⟩
    · exact absurd rfl ht
  case enterEmergency b =>
    subst hs; split_ifs at ht <;> exact absurd rfl ht
  case recover i ρ =>
    obtain ⟨-, -, -, c, -, rfl⟩ := hs; exact absurd rfl ht
  all_goals first
    | (obtain ⟨-, rfl⟩ := hs; exact absurd rfl ht)
    | (obtain ⟨-, c, -, -, rfl⟩ := hs; exact absurd rfl ht)

theorem Inv.admin (hI : Inv R s) {op : AdminOp} (hs : op.exec s = some s') : Inv R s' := by
  obtain ⟨hl, hg, hu, ht⟩ := admin_frame hs
  obtain ⟨hh, hcp, hpr, hrs⟩ := admin_ledger hs
  refine hI.keeping hl hh (by rw [hg]) (by rw [hg]) (by rw [hu]) ht (admin_tokens hs)
    (by rw [hcp]; exact hI.checkpoints) (by rw [hpr]; exact hI.proved) ?_
  rcases hrs with hrs | ⟨i, ρ, c, hin, hc, hrs⟩
  · rw [hrs]; exact hI.rootState
  · rw [hrs]
    obtain ⟨hi, hρ⟩ := hI.proved i ρ hin.1
    exact ⟨hi, (hI.hashChainAt hc).2, hρ⟩

end ledgerActions

/-! ## Every step -/

theorem Inv.step (hI : Inv R s) {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O)
    {a : Action} {s' : State} (hpre : s.ledger.leaves <+: R.leaves) (hc : StepCtx R s a)
    (hs : exec h E A a s = some s') : Inv R s' := by
  cases a with
  | wrap t c rc v => exact hI.wrap hs
  | unwrap t c rc v => exact hI.unwrap (hc.frozen c (by simp [Action.debits])) hs
  | transfer t a b v =>
    simp only [exec, ZERC20.transfer, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    exact hI.transferStep hs.1.1 hs.1.2 (hc.frozen a (by simp [Action.debits])) hs.2
  | donate t v => exact hI.donate hs
  | reserveHashChain => exact hI.reserveHashChain hs
  | checkpointBefore e p cs => exact hI.checkpointBefore hyp hpre hc hs
  | proveRoot new ws => exact hI.proveRoot hyp hpre hc hs
  | transact req w => exact hI.transact hyp hpre hc hs
  | merge req ws => exact hI.merge hyp hpre hc hs
  | rageExit req w => exact hI.rageExit hyp hpre hc hs
  | publishAspRoot c a =>
    simp only [exec, Verifier.publishAspRoot, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs
    exact hI.keeping rfl rfl rfl rfl (fun _ hx => hx) (fun _ _ => rfl) (fun _ h => absurd rfl h)
      hI.checkpoints hI.proved hI.rootState
  | claimFees t rc => exact hI.claimFees (hc.frozen _ (by simp [Action.debits])) hs
  | sign m =>
    simp only [exec, Option.some.injEq] at hs
    subst hs
    exact hI.keeping rfl rfl rfl rfl (fun _ hx => hx) (fun _ _ => rfl) (fun _ h => absurd rfl h)
      hI.checkpoints hI.proved hI.rootState
  | admin op => exact hI.admin hs

/-- Every state of a run satisfies the invariant. -/
theorem RunHyp.inv {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O) :
    ∀ i ≤ R.n, Inv R (R.s i) := by
  intro i hi
  induction i with
  | zero => rw [R.init]; exact Inv.init R _
  | succ i ih =>
    exact (ih (by omega)).step hyp (R.prefix i (by omega)) (hyp.ctx (by omega)) (R.step i (by omega))

end

end Zerc20
