import Zerc20.Preserve
import Mathlib.Order.Interval.Finset.Nat

/-!
# No theft

An honest owner's notes and burn deposits are spent only by a proof that holds the owner's private
key, or by a merge whose message the owner signed, and each at most once; spending conserves value;
and a token's underlying covers its supply and the notes committed, less what spends consumed.

Each theorem holds for every run that meets no collision among the hashes it evaluates, no forged
signature under the owner's key, and no key for a burn address it opens (`RunHyp`, `OwnerHyp`),
whatever the relayers, the attesters, the ASP, root provers and other users do.
-/

namespace Zerc20

open scoped Classical

noncomputable section

variable {h : Hashes} {E : Env} {A : Attest} {R : Run h E A}

/-- The ledger positions an action spends. -/
def Action.spends : Action → List ℕ
  | .transact _ w => transactSpent w
  | .merge _ ws => ws.map fun w => w.idx.val
  | .rageExit req _ => [req.index]
  | _ => []

/-- The owner owns position `j`: a note to its public key, or a deposit to one of its burn
addresses. -/
def Owner.owns (h : Hashes) (E : Env) (U : Owner) (s : State) (j : ℕ) : Prop :=
  (∃ t nh o, s.ledger.leaves[j]? = some (.note t nh) ∧ s.ghost.notes j = some o ∧ o.pk = U.pk h) ∨
    (∃ t a v salt, salt ∈ U.salts ∧ s.ledger.leaves[j]? = some (.transfer t a (U.burnAddr h E salt) v))

/-- Who may spend the owner's position `j` in an action: the owner's private key in a JoinSplit or
rage exit proof, or the owner's signature on a merge, whose message fixes the merged note's owner
and salt, the fee and its recipient. -/
def Action.AuthorizedBy (h : Hashes) (E : Env) (U : Owner) (s : State) (j : ℕ) : Action → Prop
  | .transact _ w => (j = w.idx0.val ∧ w.sk0 = U.sk) ∨
      (w.in1IsDummy = false ∧ j = w.idx1.val ∧ w.sk1 = U.sk)
  | .rageExit req w => j = req.index ∧ w.sk = U.sk
  | .merge req ws => ∃ w ∈ ws, j = w.idx.val ∧ w.ak = U.ak ∧
      mergeMessage h (Verifier.nullifierChain h req.nullifiers) w.outPk w.outSalt req.fee
        req.feeRecipient ∈ s.ghost.signed ∧
      req.noteHash = noteHash h E.chain w.outPk ((ws.map Merge.value).sum - req.fee)
        (req.token : F) w.outSalt
  | _ => False

theorem mergeOpening_value {req : Verifier.MergeReq} {ws : List Merge.Wit} (hne : ws ≠ []) :
    (Verifier.mergeOpening req ws).value = (ws.map Merge.value).sum - req.fee := by
  unfold Verifier.mergeOpening
  rw [List.getLast?_eq_some_getLast hne]

section owner

variable {U : Owner} {s : State}

/-- A key that opens a position the owner owns is the owner's. -/
theorem OwnerHyp.owner_key (hyp : OwnerHyp R U) {j : ℕ} {akh nk : F} (hown : U.owns h E s j)
    (hop : Opens R s j akh nk) : akh = U.akh h ∧ nk = U.nk h := by
  have pk_eq : publicKey h akh nk = U.pk h → akh = U.akh h ∧ nk = U.nk h := fun he => by
    have := hyp.inj _ (Or.inl hop.1) _ (Or.inr (by simp [Owner.calls, Owner.pk])) he
    simp only [List.cons.injEq] at this
    exact ⟨this.2.1, this.2.2.1⟩
  obtain ⟨-, ⟨t, nh, o, hl, ho, hpk⟩ | ⟨t, a, v, salt, hl, hopen⟩⟩ := hop <;>
    obtain ⟨t', nh', o', hl', ho', hpk'⟩ | ⟨t', a', v', salt', hsalt, hl'⟩ := hown
  · rw [ho] at ho'; cases ho'
    exact pk_eq (hpk.symm.trans hpk')
  · rw [hl] at hl'; cases hl'
  · rw [hl] at hl'; cases hl'
  · rw [hl] at hl'
    simp only [Option.some.injEq, Leaf.transfer.injEq] at hl'
    have hU : (E.chain, U.pk h, salt') ∈ U.openings h E := ⟨salt', hsalt, rfl⟩
    have hd := hyp.burnAddr _ (Or.inl hopen) _ (Or.inr hU) hl'.2.2.1
    have := hyp.inj _ (Or.inl (R.openings_calls hopen)) _
      (Or.inr (Or.inl (Or.inr ⟨salt', hsalt, rfl⟩))) hd
    simp only [List.cons.injEq] at this
    exact pk_eq this.2.2.1

/-- A private key whose nullifying key is the owner's is the owner's. -/
theorem OwnerHyp.sk_eq (hyp : OwnerHyp R U) {sk : F} (hsk : [DOMAIN_NULLIFYING_KEY, sk] ∈ R.calls)
    (hnk : nullifyingKey h sk = U.nk h) : sk = U.sk := by
  have := hyp.inj _ (Or.inl hsk) _ (Or.inr (by simp [Owner.calls])) hnk
  simp only [List.cons.injEq] at this
  exact this.2.1

/-- A signing key whose hash is the owner's is the owner's. -/
theorem OwnerHyp.ak_eq (hyp : OwnerHyp R U) {ak : F × F}
    (hak : [DOMAIN_AUTH_KEY, ak.1, ak.2] ∈ R.calls) (he : authKeyHash h ak = U.akh h) : ak = U.ak := by
  have := hyp.inj _ (Or.inl hak) _ (Or.inr (by simp [Owner.calls])) he
  simp only [List.cons.injEq] at this
  exact Prod.ext this.2.1 this.2.2.1

end owner

/-- **No theft.** Every position of an honest owner a step spends, the step spends with the
owner's private key, or as a merge the owner signed before it. -/
theorem no_theft {U : Owner} (hyp : OwnerHyp R U) {i : ℕ} (hi : i < R.n) {j : ℕ}
    (hj : j ∈ (R.a i).spends) (hown : U.owns h E (R.s i) j) :
    (R.a i).AuthorizedBy h E U (R.s i) j := by
  have hI := hyp.toRunHyp.inv i hi.le
  have hpre := R.prefix i hi.le
  have hc := hyp.toRunHyp.ctx hi
  have hstep := R.step i hi
  generalize ha : R.a i = a at hj hc hstep ⊢
  cases a with
  | transact req w =>
    obtain ⟨hok, -⟩ := transact_spec hstep
    have hcalls := hc.calls
    simp only [Action.calls] at hcalls
    simp only [Action.spends, transactSpent, List.mem_cons] at hj
    rcases hj with rfl | hj
    · left
      obtain ⟨-, hnk⟩ := hyp.owner_key hown (hI.transact_in0 hyp.toRunHyp hpre hc hok).opens
      exact ⟨rfl, hyp.sk_eq (hcalls (by simp [JS.calls])) hnk⟩
    · right
      cases hd : w.in1IsDummy
      · simp only [hd, Bool.false_eq_true, if_false, List.mem_singleton] at hj
        subst hj
        obtain ⟨-, hnk⟩ := hyp.owner_key hown (hI.transact_in1 hyp.toRunHyp hpre hc hok hd).opens
        exact ⟨rfl, rfl, hyp.sk_eq (hcalls (by simp [JS.calls])) hnk⟩
      · simp [hd] at hj
  | rageExit req w =>
    obtain ⟨-, -, hcommits, hlen, hchain, htag, -, haddr, hspec, -⟩ := rageExit_spec hstep
    obtain ⟨t, a, v, -, -, -, -, hop, -⟩ :=
      hI.rage_deposit hyp.toRunHyp hpre hc hcommits hlen hchain htag haddr hspec
    simp only [Action.spends, List.mem_singleton] at hj
    subst hj
    obtain ⟨-, hnk⟩ := hyp.owner_key hown hop.opens
    have hcalls := hc.calls
    simp only [Action.calls, RE.calls] at hcalls
    exact ⟨rfl, hyp.sk_eq (hcalls (by simp)) hnk⟩
  | merge req ws =>
    obtain ⟨hok, hnd, -⟩ := merge_spec hstep
    simp only [Action.spends, List.mem_map] at hj
    obtain ⟨w, hw, rfl⟩ := hj
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    obtain ⟨hakh, -⟩ := hyp.owner_key hown (hI.merge_in hyp.toRunHyp hpre hc hok hk).opens
    have hcalls := hc.calls
    simp only [Action.calls] at hcalls
    have hak := hyp.ak_eq ((Merge.callsAlong_mem hk).trans hcalls (by simp [Merge.calls])) hakh
    obtain ⟨hnh, -, -, -, hsame⟩ := merge_output hyp.toRunHyp hok hnd hc.calls
    obtain ⟨hpk, hsalt⟩ := hsame _ hw
    refine ⟨ws[k], hw, rfl, hak, hyp.signed i hi req ws ha _ hw hak, ?_⟩
    rw [hnh, hpk, hsalt, mergeOpening_value (List.ne_nil_of_mem hw)]
  | _ => simp [Action.spends] at hj

/-! ## At most once -/

theorem exec_spent {s s' : State} {a : Action} (hs : exec h E A a s = some s') :
    s'.ghost.spent = s.ghost.spent ++ a.spends := by
  cases a with
  | transact req w =>
    obtain ⟨-, -, s4, hp, rfl⟩ := transact_spec hs
    simp [Verifier.recordSpent, Verifier.recordNote, hp.1.ghost, State.append, State.spendAll,
      Action.spends, transactSpent]
  | merge req ws =>
    obtain ⟨-, -, -, s3, hp, rfl⟩ := merge_spec hs
    simp [Verifier.recordSpent, Verifier.recordNote, hp.1.ghost, State.append, State.spendAll,
      Action.spends]
  | rageExit req w =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, s2, h2, rfl⟩ := rageExit_spec hs
    simp [Verifier.recordSpent, (payOut_paid h2).1.ghost, State.spendAll, Action.spends]
  | admin op => simp [Action.spends, (admin_frame hs).2.1]
  | sign m => simp only [exec, Option.some.injEq] at hs; subst hs; simp [Action.spends]
  | wrap t c rc v =>
    simp only [exec, ZERC20.wrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, tk, -, s1, h1, h2⟩ := hs
    obtain ⟨-, -, -, -, -, -, -, hG1, -⟩ := update_post h1
    split_ifs at h2
    · obtain ⟨-, -, -, -, -, -, -, hG2, -⟩ := update_post h2
      simp [Action.spends, hG2, hG1, State.setToken]
    · cases h2; simp [Action.spends, hG1, State.setToken]
  | unwrap t c rc v =>
    simp only [exec, ZERC20.unwrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, -, s1, h1, h2⟩ := hs
    obtain ⟨-, -, -, -, -, -, -, hG1, -⟩ := update_post h1
    simp [Action.spends, (release_paid h2).1.ghost, hG1]
  | transfer t a b v =>
    simp only [exec, ZERC20.transfer, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, -, -, -, -, -, -, hG, -⟩ := update_post hs.2
    simp [Action.spends, hG]
  | donate t v =>
    simp only [exec, Zerc20.donate, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hs
    obtain ⟨tk, -, rfl⟩ := hs; simp [Action.spends, State.setToken]
  | reserveHashChain =>
    simp only [exec, CommitmentLedger.reserveHashChain] at hs
    split_ifs at hs
    · cases hs; simp [Action.spends]
    · simp only [bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
        Option.pure_def, Option.some.injEq] at hs
      obtain ⟨-, rfl⟩ := hs; simp [Action.spends]
  | checkpointBefore e p cs =>
    simp only [exec, CommitmentLedger.checkpointBefore, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, rfl⟩ := hs; simp [Action.spends]
  | proveRoot new ws =>
    simp only [exec, CommitmentLedger.proveRootTransition, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs; simp [Action.spends]
  | publishAspRoot c a =>
    simp only [exec, Verifier.publishAspRoot, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs; simp [Action.spends]
  | claimFees t rc =>
    by_cases hv : (s.verifier.accrued t rc) = 0
    · simp only [exec, Verifier.claimFees, hv, if_true, Option.some.injEq] at hs
      subst hs; simp [Action.spends]
    · simp only [exec, Verifier.claimFees, hv, if_false, ZERC20.transfer, bind,
        Option.bind_eq_some_iff, guard_eq_some_unit, exists_const] at hs
      obtain ⟨-, -, -, -, -, -, -, hG, -⟩ := update_post hs.2
      simp [Action.spends, hG]

/-- The positions a run has spent: every action's, in order. -/
theorem Run.spent (R : Run h E A) : ∀ i ≤ R.n,
    (R.s i).ghost.spent = ((List.range i).map fun k => (R.a k).spends).flatten := by
  intro i hi
  induction i with
  | zero => simp [R.init, State.init]
  | succ i ih =>
    rw [exec_spent (R.step i (by omega)), ih (by omega), List.range_succ, List.map_append,
      List.flatten_append]
    simp

/-- **At most once.** No ledger position is spent twice in a run. -/
theorem at_most_once {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O) :
    ((List.range R.n).map fun k => (R.a k).spends).flatten.Nodup := by
  rw [← R.spent R.n le_rfl]
  exact (hyp.inv R.n le_rfl).nodup

/-! ## Conservation and solvency -/

/-- The value of the notes of `t` not spent yet. -/
def unspentNotes (s : State) (t : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range s.ledger.leaves.length).filter (· ∉ s.ghost.spent), noteValueAt s t j

/-- The deposit of `t` at position `j`, if it pays an address in `B`. -/
def depositAt (B : Set Addr) (s : State) (t j : ℕ) : ℕ :=
  match s.ledger.leaves[j]? with
  | some (.transfer t' _ b v) => if t' = t ∧ b ∈ B then v else 0
  | _ => 0

/-- The deposits of `t` to burn addresses already spent. -/
def spentDeposits (B : Set Addr) (s : State) (t : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range s.ledger.leaves.length).filter (· ∈ s.ghost.spent), depositAt B s t j

/-- The deposits of `t` to burn addresses not spent yet. -/
def unspentDeposits (B : Set Addr) (s : State) (t : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range s.ledger.leaves.length).filter (· ∉ s.ghost.spent), depositAt B s t j

theorem leafValue_split {B : Set Addr} {s : State} {t j : ℕ} (hB : ∀ t' a b v,
    s.ledger.leaves[j]? = some (.transfer t' a b v) → b ∈ B) :
    leafValueAt s t j = noteValueAt s t j + depositAt B s t j := by
  unfold leafValueAt depositAt noteValueAt
  cases hl : s.ledger.leaves[j]? with
  | none => simp
  | some l =>
    cases l with
    | note t' nh => simp
    | transfer t' a b v => simp [hB t' a b v hl]

/-- **Conservation.** The underlying covers the supply and the unspent notes, less the burn
deposits already spent (which still count in the supply, at the burn addresses). -/
theorem conservation {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O) {i : ℕ}
    (hi : i ≤ R.n) {t : ℕ} {tk : TokenSt} (htk : (R.s i).tokens t = some tk) :
    tk.supply + unspentNotes (R.s i) t ≤ tk.underlying + spentDeposits R.burnAddrs (R.s i) t := by
  have hI := hyp.inv i hi
  set s := R.s i
  obtain ⟨-, hbook, -⟩ := hI.books t tk htk
  have hsub : ∀ j ∈ s.ghost.spent, j < s.ledger.leaves.length := fun j hj => (hI.spent j hj).1
  -- Every spent transfer pays a burn address the run opens.
  have hB : ∀ j ∈ s.ghost.spent, ∀ t' a b v, s.ledger.leaves[j]? = some (.transfer t' a b v) →
      b ∈ R.burnAddrs := by
    intro j hj t' a b v hl
    obtain ⟨-, akh, nk, ⟨-, ⟨_, _, _, hl', -, -⟩ | ⟨_, _, _, salt, hl', hop⟩⟩, -⟩ := hI.spent j hj
    · rw [hl] at hl'; cases hl'
    · rw [hl] at hl'; cases hl'; exact ⟨_, hop, rfl⟩
  have hfin : s.ghost.spent.toFinset = (Finset.range s.ledger.leaves.length).filter (· ∈ s.ghost.spent) := by
    ext j; simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hsub j h, h⟩, fun h => h.2⟩
  have hcon : consumed s t = ∑ j ∈ (Finset.range s.ledger.leaves.length).filter (· ∈ s.ghost.spent),
      (noteValueAt s t j + depositAt R.burnAddrs s t j) := by
    unfold consumed
    rw [← List.sum_toFinset _ hI.nodup, hfin]
    apply Finset.sum_congr rfl
    intro j hj
    exact leafValue_split (hB j (Finset.mem_filter.mp hj).2)
  have hcre : created s t = unspentNotes s t +
      ∑ j ∈ (Finset.range s.ledger.leaves.length).filter (· ∈ s.ghost.spent), noteValueAt s t j := by
    unfold created unspentNotes
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      ← Finset.sum_filter_add_sum_filter_not _ (· ∈ s.ghost.spent), add_comm]
  rw [hcon, Finset.sum_add_distrib] at hbook
  rw [hcre] at hbook
  unfold spentDeposits
  omega

/-- A list's sum, indexed by position. -/
theorem sum_map_eq_range {α : Type} (f : α → ℕ) (l : List α) :
    (l.map f).sum = ∑ j ∈ Finset.range l.length, (l[j]?.map f).getD 0 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [List.map_append, List.sum_append, ih, List.length_append, List.length_singleton,
      Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [List.getElem?_append_left (Finset.mem_range.mp hj)]
    · simp

/-- The burn addresses `t`'s ledger pays, among `B`. -/
def paidAddrs (B : Set Addr) (s : State) (t : ℕ) : Finset Addr :=
  (Finset.range s.ledger.leaves.length).biUnion fun j => match s.ledger.leaves[j]? with
    | some (.transfer t' _ b _) => if t' = t ∧ b ∈ B then {b} else ∅
    | _ => ∅

theorem deposits_sum (B : Set Addr) (s : State) (t : ℕ) :
    ∑ a ∈ paidAddrs B s t, deposits s t a =
      ∑ j ∈ Finset.range s.ledger.leaves.length, depositAt B s t j := by
  unfold deposits
  simp only [sum_map_eq_range]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  unfold depositAt
  cases hl : s.ledger.leaves[j]? with
  | none => simp
  | some l =>
    cases l with
    | note t' nh => simp
    | transfer t' a b v =>
      simp only [Option.map_some, Option.getD_some]
      by_cases hc : t' = t ∧ b ∈ B
      · have hb : b ∈ paidAddrs B s t := Finset.mem_biUnion.mpr ⟨j, hj, by simp [hl, hc]⟩
        rw [if_pos hc, Finset.sum_eq_single_of_mem b hb (fun a _ hab => by simp [Ne.symm hab])]
        simp [hc.1]
      · rw [if_neg hc]
        apply Finset.sum_eq_zero
        intro a ha
        obtain ⟨j', -, hj'⟩ := Finset.mem_biUnion.mp ha
        split_ifs with h1
        · obtain ⟨rfl, rfl⟩ := h1
          exfalso
          cases hl' : s.ledger.leaves[j']? with
          | none => simp [hl'] at hj'
          | some l' =>
            cases l' with
            | note _ _ => simp [hl'] at hj'
            | transfer t'' a'' b'' v'' =>
              simp only [hl'] at hj'
              split_ifs at hj' with h2
              · simp at hj'; subst hj'; exact hc ⟨rfl, h2.2⟩
              · simp at hj'
        · rfl

/-- **Solvency.** A token's underlying covers every balance outside the run's burn addresses, every
unspent note, and every unspent burn deposit: everything its holders can redeem. -/
theorem solvent {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O) {i : ℕ}
    (hi : i ≤ R.n) {t : ℕ} {tk : TokenSt} (htk : (R.s i).tokens t = some tk) :
    (∑ a ∈ tk.bal.support.filter (· ∉ R.burnAddrs), tk.bal a) + unspentNotes (R.s i) t +
      unspentDeposits R.burnAddrs (R.s i) t ≤ tk.underlying := by
  have hI := hyp.inv i hi
  have hcon := conservation hyp hi htk
  set s := R.s i
  obtain ⟨⟨hsup, -⟩, -, hdep⟩ := hI.books t tk htk
  -- The supply splits into the burn addresses' balances and the rest.
  have hsplit : tk.supply = (∑ a ∈ tk.bal.support.filter (· ∉ R.burnAddrs), tk.bal a) +
      ∑ a ∈ tk.bal.support.filter (· ∈ R.burnAddrs), tk.bal a := by
    rw [hsup, TokenSt.total, Finsupp.sum, add_comm,
      Finset.sum_filter_add_sum_filter_not tk.bal.support (· ∈ R.burnAddrs)]
  -- The burn addresses hold at least every deposit paid to them.
  have hburn : spentDeposits R.burnAddrs s t + unspentDeposits R.burnAddrs s t ≤
      ∑ a ∈ tk.bal.support.filter (· ∈ R.burnAddrs), tk.bal a := by
    unfold spentDeposits unspentDeposits
    rw [Finset.sum_filter_add_sum_filter_not, ← deposits_sum]
    calc ∑ a ∈ paidAddrs R.burnAddrs s t, deposits s t a
        ≤ ∑ a ∈ paidAddrs R.burnAddrs s t, tk.bal a := by
          apply Finset.sum_le_sum
          intro a ha
          obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp ha
          apply hdep
          cases hl : s.ledger.leaves[j]? with
          | none => simp [hl] at hj
          | some l =>
            cases l with
            | note _ _ => simp [hl] at hj
            | transfer t' a' b v =>
              simp only [hl] at hj
              split_ifs at hj with h2
              · simp at hj; subst hj; exact h2.2
              · simp at hj
      _ ≤ ∑ a ∈ tk.bal.support.filter (· ∈ R.burnAddrs), tk.bal a := by
          rw [← Finset.sum_filter_ne_zero]
          apply Finset.sum_le_sum_of_subset
          intro a ha
          simp only [Finset.mem_filter, Finsupp.mem_support_iff] at ha ⊢
          refine ⟨ha.2, ?_⟩
          obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp ha.1
          cases hl : s.ledger.leaves[j]? with
          | none => simp [hl] at hj
          | some l =>
            cases l with
            | note _ _ => simp [hl] at hj
            | transfer t' a' b v =>
              simp only [hl] at hj
              split_ifs at hj with h2
              · simp at hj; subst hj; exact h2.2
              · simp at hj
  omega

end

end Zerc20
