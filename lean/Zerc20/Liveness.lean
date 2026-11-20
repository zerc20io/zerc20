import Zerc20.Safety

/-!
# Exit

An owner can always get its value out, under conditions stated where the exit runs:

* a burn deposit not spent yet comes back through `rageExit`, which needs no ASP, attester, proved
  root or indexer, only that the Verifier and the token are not paused and the sender not blocked;
* a note comes out through a `transact` withdrawal, which also needs an accepted root that holds it,
  an accepted ASP root, an attester's answer, a fresh dummy nullifier and room in the tree.

What makes an exit possible stays so: no action of another party spends the owner's position
(`no_theft`), and only admin steps withdraw a root, drop the ASP roots or stop the token.
-/

namespace Zerc20

open scoped Classical

noncomputable section

variable {h : Hashes} {E : Env} {A : Attest}

/-! ## The contract steps succeed -/

section succeed

variable {s : State}

theorem spend_ok {nfs : List F} (hnd : nfs.Nodup) (hu : ∀ nf ∈ nfs, nf ∉ s.verifier.used) :
    Verifier.spend nfs s = some (s.spendAll nfs) :=
  spend_eq.mpr ⟨⟨hnd, hu⟩, rfl⟩

/-- Minting `v` to a real account succeeds while the token runs, the recipient is not blocked and
the supply does not overflow. -/
theorem mint_ok {t : ℕ} {tk : TokenSt} (htk : s.tokens t = some tk) {rcpt : Addr} {v : ℕ}
    (hrl : rcpt < ADDRESS_BOUND) (hstop : ¬ s.stopped t) (hv : v < AMOUNT_BOUND)
    (hb : s.notBlocked E rcpt) (hsup : tk.supply + v < UINT256) :
    ZERC20.update h E t 0 rcpt v s = some (s.setToken t (tk.move 0 rcpt v)) := by
  rw [update_eq]
  refine ⟨tk, htk, by unfold ADDRESS_BOUND; positivity, hrl, hstop, hv, Or.inl rfl, hb,
    by simp [TokenSt.canMove, hsup], ?_⟩
  simp

theorem payOut_mint_ok {t : ℕ} {tk : TokenSt} (htk : s.tokens t = some tk) {rcpt : Addr} {v : ℕ}
    (hr : rcpt ≠ 0) (hrl : rcpt < ADDRESS_BOUND) (hv0 : v ≠ 0) (hstop : ¬ s.stopped t)
    (hv : v < AMOUNT_BOUND) (hb : s.notBlocked E rcpt) (hsup : tk.supply + v < UINT256) :
    ZERC20.payOut h E t rcpt v false s = some (s.setToken t (tk.move 0 rcpt v)) :=
  payOut_eq.mpr ⟨hr, hv0, by simpa using mint_ok htk hrl hstop hv hb hsup⟩

end succeed

/-! ## Rage exit -/

section rage

variable {R : Run h E A} {U : Owner}

/-- The rage exit of the deposit at `j`: the segment from it to the live head, and the owner's key. -/
def rageReq (h : Hashes) (E : Env) (U : Owner) (s : State) (j : ℕ) : Verifier.RageReq where
  checkpointIndex := s.ledger.leaves.length
  prev := chainOf h (s.ledger.leaves.take j)
  commits := (s.ledger.leaves.drop j).map Leaf.words
  nf := nullifier h E.chain j (U.nk h)

def rageWit (h : Hashes) (U : Owner) (salt : F) : RE.Wit := ⟨U.sk, U.akh h, salt⟩

theorem r_le_uint256 : r < UINT256 := by unfold r UINT256; norm_num

/-- **Rage exit.** The owner's unspent burn deposit at `j` comes back, as zERC20, to the account
that paid it, while the Verifier and the token run, that account is not blocked, and the supply
does not overflow. -/
theorem rageExit_now {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O) {i : ℕ}
    (hi : i ≤ R.n) {j t : ℕ} {a : Addr} {v : ℕ} {salt : F}
    (hdep : (R.s i).ledger.leaves[j]? = some (.transfer t a (U.burnAddr h E salt) v))
    (hpow : (burnDigest h E.chain (U.pk h) salt).val < POW_BOUND)
    (hnf : nullifier h E.chain j (U.nk h) ∉ (R.s i).verifier.used)
    (hpaused : (R.s i).verifier.paused = false) (htp : (R.s i).verifier.tokenPaused t = false)
    (hblocked : (R.s i).notBlocked E a) {tk : TokenSt} (htk : (R.s i).tokens t = some tk)
    (hsup : tk.supply + v < UINT256) :
    ∃ s', exec h E A (.rageExit (rageReq h E U (R.s i) j) (rageWit h U salt)) (R.s i) = some s' ∧
      ∃ tk', s'.tokens t = some tk' ∧ tk'.bal a = tk.bal a + v := by
  have hI := hyp.inv i hi
  set s := R.s i
  have hjL : j < s.ledger.leaves.length := (List.getElem?_eq_some_iff.mp hdep).1
  have hlj : s.ledger.leaves[j] = .transfer t a (U.burnAddr h E salt) v :=
    (List.getElem?_eq_some_iff.mp hdep).2
  have hvalid := (hI.valid _ (List.getElem_mem hjL)).1
  rw [hlj] at hvalid
  obtain ⟨ht, ha0, hal, hb0, hbl, hv0, hvl⟩ := hvalid
  have hjT : j < 2 ^ DEPTH := lt_of_lt_of_le hjL hI.cap
  have hjr : j < r := hjT.trans (two_pow_le_r (by unfold DEPTH; norm_num))
  have hcommits : (rageReq h E U s j).commits ≠ [] := by
    simp [rageReq, List.drop_eq_nil_iff, hjL]
  have hlen : (rageReq h E U s j).commits.length = s.ledger.leaves.length - j := by
    simp [rageReq]
  have hidx : (rageReq h E U s j).index = j := by
    simp only [Verifier.RageReq.index, hlen]; simp [rageReq]; omega
  have hhead : (rageReq h E U s j).commits.headD [] = [field0 TRANSFER_TAG t, a,
      U.burnAddr h E salt, v] := by
    simp [rageReq, List.headD_eq_head?_getD, List.head?_drop, hdep, Leaf.words]
  have hfold : (rageReq h E U s j).commits.foldl h.hc (rageReq h E U s j).prev =
      s.ledger.head := by
    have hsplit : chainOf h s.ledger.leaves = ((s.ledger.leaves.drop j).map Leaf.words).foldl h.hc
        (chainOf h (s.ledger.leaves.take j)) := by
      conv_lhs => rw [← List.take_append_drop j s.ledger.leaves]
      rw [chainOf_eq_foldl, chainOf_eq_foldl, List.map_append, List.foldl_append]
    simp only [rageReq]
    rw [hI.head, hsplit]
  have hspec : RE.Spec h ⟨(rageReq h E U s j).nf, E.chainId, (rageReq h E U s j).index,
      (rageReq h E U s j).commits.headD [] |>.getD 2 0⟩ (rageWit h U salt) := by
    rw [hidx, hhead]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [val_cast (E.chainId_lt.trans (two_pow_le_r (by norm_num)))]; exact E.chainId_lt
    · rw [val_cast hjr]; exact hjT
    · exact hpow
    · rfl
    · rfl
  -- Every step of `rageExit` succeeds.
  have hwf : ∀ c ∈ (rageReq h E U s j).commits, c.length = 4 ∧ ∀ x ∈ c, x < UINT256 := by
    intro c hc
    simp only [rageReq, List.mem_map] at hc
    obtain ⟨l, hl, rfl⟩ := hc
    have hlv := (hI.valid l (List.mem_of_mem_drop hl)).1
    cases l with
    | transfer t' a' b' v' =>
      obtain ⟨ht', -, ha', -, hb', -, hv'⟩ := hlv
      refine ⟨rfl, fun x hx => ?_⟩
      simp only [Leaf.words, List.mem_cons, List.not_mem_nil, or_false] at hx
      have hr := r_le_uint256
      rcases hx with rfl | rfl | rfl | rfl
      · exact (field0_lt_r TRANSFER_TAG_lt ht').trans hr
      · exact (ha'.trans address_lt_r).trans hr
      · exact (hb'.trans address_lt_r).trans hr
      · exact (hv'.trans amount_lt_r).trans hr
    | note t' nh =>
      refine ⟨rfl, fun x hx => ?_⟩
      simp only [Leaf.words, List.mem_cons, List.not_mem_nil, or_false] at hx
      have hr := r_le_uint256
      rcases hx with rfl | rfl | rfl | rfl
      · exact (field0_lt_r NOTE_HASH_TAG_lt hlv).trans hr
      · exact (ZMod.val_lt nh).trans hr
      · exact lt_of_le_of_lt (Nat.zero_le _) hr
      · exact lt_of_le_of_lt (Nat.zero_le _) hr
  have hdec : Verifier.decode (field0 TRANSFER_TAG t) = (TRANSFER_TAG, t) :=
    decode_field0 TRANSFER_TAG_lt ht
  have htokn : s.tokens t ≠ none := by simp [htk]
  have hstop : ¬ s.stopped t := by simp [State.stopped, hpaused, htp]
  have hpay := payOut_mint_ok (h := h) (s := s.spendAll [(rageReq h E U s j).nf]) htk ha0 hal hv0
    (by simpa [State.stopped, State.spendAll] using hstop) hvl
    (by simpa [State.notBlocked, State.spendAll] using hblocked) hsup
  refine ⟨Verifier.recordSpent [(rageReq h E U s j).index]
      ((s.spendAll [(rageReq h E U s j).nf]).setToken t (tk.move 0 a v)), ?_, tk.move 0 a v,
    by simp [Verifier.recordSpent, State.setToken, State.spendAll],
    by simp [TokenSt.move, ha0]⟩
  simp only [exec, Verifier.rageExit, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
    exists_const, Option.pure_def, Option.some.injEq, verifySegment_eq]
  refine ⟨⟨hpaused, hwf⟩, _, ⟨hcommits, by rw [hlen]; simp [rageReq],
    by rw [hashChainAt_eq]; exact ⟨le_rfl, by
      rw [if_pos (show (rageReq h E U s j).checkpointIndex = s.ledger.leaves.length from rfl)]
      exact hfold⟩, rfl⟩, ?_⟩
  rw [show (rageReq h E U s j).checkpointIndex - (rageReq h E U s j).commits.length =
    (rageReq h E U s j).index from rfl, hhead]
  simp only [List.getD_cons_zero, List.getD_cons_succ, hdec]
  refine ⟨⟨trivial, ⟨ht, htokn, htp⟩, (address_lt _).trans address_lt_r,
      by rw [hhead] at hspec; simpa using hspec⟩,
    _, spend_ok (List.nodup_singleton _) (by simpa [rageReq] using hnf), _, ?_, rfl⟩
  rw [Nat.mod_eq_of_lt hal]
  exact hpay

end rage

/-! ## Fees stay at most 3% -/

section fees

/-- Every fee schedule charges at most 300 basis points. -/
def FeesOK (s : State) : Prop := ∀ t, ∀ tier ∈ (s.verifier.fees t).tiers, tier.2 ≤ 300

theorem validFees_le {fs : FeeSch} {ch : Bool} (hv : Verifier.validFees fs = some ch) :
    ∀ tier ∈ fs.tiers, tier.2 ≤ 300 := by
  simp only [Verifier.validFees, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
    exists_const] at hv
  exact fun tier ht => (hv.2.2.2.1 tier ht).2

/-- The fee on a withdrawal is at most 3% of it. -/
theorem quote_le {fs : FeeSch} (hfs : ∀ tier ∈ fs.tiers, tier.2 ≤ 300) (v : ℕ) :
    Verifier.quote fs v * 10000 ≤ v * 300 := by
  unfold Verifier.quote
  have hb : ((fs.tiers.takeWhile fun tier => tier.1 ≤ v).getLast?.map Prod.snd |>.getD 0) ≤ 300 := by
    cases hl : (fs.tiers.takeWhile fun tier => tier.1 ≤ v).getLast? with
    | none => simp
    | some tier =>
      simp only [Option.map_some, Option.getD_some]
      exact hfs tier (List.takeWhile_subset _ (List.mem_of_getLast? hl))
  calc v * _ / 10000 * 10000 ≤ v * _ := Nat.div_mul_le_self _ _
    _ ≤ v * 300 := Nat.mul_le_mul_left _ hb

set_option linter.unusedTactic false in
theorem exec_fees {s s' : State} {a : Action} (hok : FeesOK s) (hs : exec h E A a s = some s') :
    FeesOK s' := by
  have same : s'.verifier.fees = s.verifier.fees → FeesOK s' := fun he t => by rw [he]; exact hok t
  cases a with
  | transact req w =>
    obtain ⟨-, -, s4, hp, rfl⟩ := transact_spec hs
    exact same (by simp [Verifier.recordSpent, Verifier.recordNote, hp.1.fees, State.append,
      State.spendAll])
  | merge req ws =>
    obtain ⟨-, -, -, s3, hp, rfl⟩ := merge_spec hs
    exact same (by simp [Verifier.recordSpent, Verifier.recordNote, hp.1.fees, State.append,
      State.spendAll])
  | rageExit req w =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, s2, h2, rfl⟩ := rageExit_spec hs
    exact same (by simp [Verifier.recordSpent, (payOut_paid h2).1.fees, State.spendAll])
  | wrap t c rc v =>
    simp only [exec, ZERC20.wrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, tk, -, s1, h1, h2⟩ := hs
    obtain ⟨-, -, -, -, -, -, -, -, hV1, -⟩ := update_post h1
    split_ifs at h2
    · obtain ⟨-, -, -, -, -, -, -, -, hV2, -⟩ := update_post h2
      exact same (by rw [hV2, hV1]; rfl)
    · cases h2; exact same (by rw [hV1]; rfl)
  | unwrap t c rc v =>
    simp only [exec, ZERC20.unwrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, -, s1, h1, h2⟩ := hs
    obtain ⟨-, -, -, -, -, -, -, -, hV1, -⟩ := update_post h1
    exact same (by rw [(release_paid h2).1.fees, hV1])
  | transfer t a b v =>
    simp only [exec, ZERC20.transfer, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, -, -, -, -, -, -, -, hV, -⟩ := update_post hs.2
    exact same (by rw [hV])
  | donate t v =>
    simp only [exec, Zerc20.donate, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hs
    obtain ⟨tk, -, rfl⟩ := hs; exact hok
  | reserveHashChain =>
    simp only [exec, CommitmentLedger.reserveHashChain] at hs
    split_ifs at hs
    · cases hs; exact hok
    · simp only [bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
        Option.pure_def, Option.some.injEq] at hs
      obtain ⟨-, rfl⟩ := hs; exact hok
  | checkpointBefore e p cs =>
    simp only [exec, CommitmentLedger.checkpointBefore, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, rfl⟩ := hs; exact hok
  | proveRoot new ws =>
    simp only [exec, CommitmentLedger.proveRootTransition, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs; exact hok
  | publishAspRoot c a =>
    simp only [exec, Verifier.publishAspRoot, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs; exact hok
  | claimFees t rc =>
    by_cases hv : (s.verifier.accrued t rc) = 0
    · simp only [exec, Verifier.claimFees, hv, if_true, Option.some.injEq] at hs
      subst hs; exact hok
    · simp only [exec, Verifier.claimFees, hv, if_false, ZERC20.transfer, bind,
        Option.bind_eq_some_iff, guard_eq_some_unit, exists_const] at hs
      obtain ⟨-, -, -, -, -, -, -, -, hV, -⟩ := update_post hs.2
      exact same (by rw [hV])
  | sign m => simp only [exec, Option.some.injEq] at hs; subst hs; exact hok
  | admin op =>
    cases op <;>
      simp only [exec, AdminOp.exec, CommitmentLedger.enterEmergency, CommitmentLedger.recover, bind,
        Option.bind_eq_some_iff, guard_eq_some_unit, exists_const, Option.pure_def,
        Option.some.injEq] at hs
    case setFee t fs =>
      obtain ⟨-, ch, hv, -, rfl⟩ := hs
      intro t' tier ht'
      simp only [Function.update_apply] at ht'
      split_ifs at ht' with htt
      · exact validFees_le hv tier ht'
      · exact hok t' tier ht'
    case enterEmergency b => subst hs; split_ifs <;> exact hok
    all_goals first
      | (obtain ⟨-, rfl⟩ := hs; exact hok)
      | (obtain ⟨-, -, -, c, -, rfl⟩ := hs; exact hok)

theorem Run.feesOK (R : Run h E A) : ∀ i ≤ R.n, FeesOK (R.s i) := by
  intro i hi
  induction i with
  | zero => rw [R.init]; intro t tier ht; simp [State.init, FeeSch.none] at ht
  | succ i ih => exact exec_fees (ih (by omega)) (R.step i (by omega))

end fees

/-! ## Withdrawing a note -/

section withdraw

variable {s : State}

/-- `transact` succeeds once its checks hold, the tree has room for both notes, and the
withdrawal settles. -/
theorem transact_of {req : Verifier.TransactReq} {w : JS.Wit}
    (hok : Verifier.TransactOK h E A req w s) (hcap : s.ledger.leaves.length + 2 ≤ TREE_SIZE)
    {s4 : State}
    (hset : Verifier.settleWithdraw h E req.pub.token.val req.pub.recipient.val req.pub.amount.val
      (req.pub.intent.val = E.unwrapIntent)
      (((s.spendAll [req.pub.nf0, req.pub.nf1]).append h (.note req.pub.token.val req.pub.nh1)).append
        h (.note req.pub.token.val req.pub.nh2)) = some s4) :
    Verifier.transact h E A req w s = some (Verifier.recordSpent
      (w.idx0.val :: if w.in1IsDummy then [] else [w.idx1.val])
      (Verifier.recordNote (s.ledger.leaves.length + 1) w.out2
        (Verifier.recordNote s.ledger.leaves.length w.out1 s4))) := by
  simp only [Verifier.transact, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq, spend_eq, ZERC20.commitNote, commit_eq]
  refine ⟨hok, _, ⟨⟨by simp [hok.nfs.1], by simp [hok.nfs.2.1, hok.nfs.2.2]⟩, rfl⟩, _,
    ⟨by simp [State.spendAll]; omega, rfl⟩, _, ⟨by simp [State.spendAll, State.append]; omega, rfl⟩,
    s4, hset, ?_⟩
  simp [State.spendAll]

/-- A withdrawal of `g` settles while the token runs, the recipient is not blocked and the supply
does not overflow; the recipient gets at least the amount less the fee. -/
theorem settle_ok {t : ℕ} {tk : TokenSt} (htk : s.tokens t = some tk) {rc : Addr} {g : ℕ}
    (hg : g ≠ 0) (hfees : FeesOK s) (hrc0 : rc ≠ 0) (hrcl : rc < ADDRESS_BOUND)
    (hstop : ¬ s.stopped t) (hgl : g < AMOUNT_BOUND) (hb : s.notBlocked E rc)
    (hsup : tk.supply + g < UINT256) :
    ∃ s', Verifier.settleWithdraw h E t rc g false s = some s' ∧ s'.ledger = s.ledger ∧
      s'.ghost = s.ghost ∧ s'.verifier.used = s.verifier.used ∧
      ∃ tk', s'.tokens t = some tk' ∧ tk.bal rc + (g - Verifier.withdrawFee s t g) ≤ tk'.bal rc := by
  set fee := Verifier.withdrawFee s t g with hfee
  have hfle := quote_le (hfees t) g
  rw [← Verifier.withdrawFee] at hfle
  have hfg : fee < g := by
    rw [hfee]; have := Nat.pos_of_ne_zero hg; omega
  -- The fee is minted to the Verifier first, which takes nothing from the recipient.
  obtain ⟨s1, tk1, h1, hl1, hg1, hu1, htk1, hbal1, hsup1, hstop1, hb1⟩ :
      ∃ s1 tk1, Verifier.payFee h E t fee s = some s1 ∧ s1.ledger = s.ledger ∧
        s1.ghost = s.ghost ∧ s1.verifier.used = s.verifier.used ∧ s1.tokens t = some tk1 ∧
        tk.bal rc ≤ tk1.bal rc ∧ tk1.supply = tk.supply + fee ∧ ¬ s1.stopped t ∧
        s1.notBlocked E rc := by
    unfold Verifier.payFee
    by_cases hf0 : fee = 0
    · rw [if_pos hf0]
      exact ⟨s, tk, rfl, rfl, rfl, rfl, htk, le_rfl, by omega, hstop, hb⟩
    · rw [if_neg hf0, payOut_mint_ok (h := h) (E := E) htk E.verifier_ne E.verifier_lt hf0 hstop
        (by omega) (Or.inr (Or.inl rfl)) (by omega)]
      refine ⟨_, tk.move 0 E.verifier fee, rfl, rfl, rfl, rfl, by simp [State.setToken],
        by simp [TokenSt.move_bal], by simp [TokenSt.move_supply, E.verifier_ne],
        hstop, hb⟩
  have h2 := payOut_mint_ok (h := h) (E := E) htk1 hrc0 hrcl (by omega : g - fee ≠ 0) hstop1
    (by omega) hb1 (by rw [hsup1]; omega)
  simp only [Verifier.settleWithdraw, hg, if_false]
  simp only [← hfee, h1, Option.bind_some]
  rw [if_neg (by omega : ¬ g = fee), h2]
  exact ⟨_, rfl, hl1, hg1, hu1, tk1.move 0 rc (g - fee), by simp [State.setToken],
    by simpa [TokenSt.move_bal, hrc0] using hbal1⟩

end withdraw

section withdrawNote

variable {R : Run h E A} {U : Owner}

/-- The public signals of withdrawing the owner's note `o` at `j`, of token `t`, to `rc`, with a
dummy second input and two empty change notes to the owner. -/
def withdrawPub (h : Hashes) (E : Env) (U : Owner) (t j : ℕ) (o : JS.Opening) (ρ : F) (asp : ℕ)
    (e : F) (rc : Addr) (salt1 salt2 : F) : JS.Pub where
  nf0 := nullifier h E.chain j (U.nk h)
  nf1 := dummyNullifier h E.chain e
  recipient := rc
  amount := o.value
  intent := 0
  nh1 := noteHash h E.chain (U.pk h) 0 t salt1
  nh2 := noteHash h E.chain (U.pk h) 0 t salt2
  token := t
  chain := E.chain
  root := ρ
  asp := asp

def withdrawWit (h : Hashes) (U : Owner) (j : ℕ) (o : JS.Opening) (sib : Fin DEPTH → F) (e : F)
    (salt1 salt2 : F) : JS.Wit where
  in0IsBurn := false
  in1IsDummy := true
  entropy := e
  note0 := o
  note1 := JS.Opening.zero
  burnPk := 0
  burnSalt := 0
  burnFrom := 0
  burnValue := 0
  out1 := ⟨U.pk h, 0, salt1⟩
  out2 := ⟨U.pk h, 0, salt2⟩
  sk0 := U.sk
  sk1 := 0
  akh0 := U.akh h
  akh1 := 0
  idx0 := j
  idx1 := 0
  sib0 := sib
  sib1 := 0
  aspSib := 0

/-- **Withdrawal.** The owner's unspent note comes out to any account the owner names, less a fee
of at most 3%, given an accepted root that holds the note, an accepted ASP root, an attester's
answer, a fresh dummy nullifier, room in the tree for the two change notes, a running Verifier and
token, an unblocked recipient, and a supply that does not overflow. -/
theorem withdraw_now {S : Set (List F)} {O : Set (F × F × F)} (hyp : RunHyp R S O) {i : ℕ}
    (hi : i ≤ R.n) {j t : ℕ} {nh : F} {o : JS.Opening}
    (hnote : (R.s i).ledger.leaves[j]? = some (.note t nh)) (hopen : (R.s i).ghost.notes j = some o)
    (hown : o.pk = U.pk h) (hval : o.value ≠ 0)
    {ri : ℕ} {ρ : F} (hroot : (R.s i).provedRoots ri ρ) (hjr : j < ri)
    {asp : ℕ} (hasp : (R.s i).aspAccepted asp) (haspr : asp < r)
    {e : F} (hnf0 : nullifier h E.chain j (U.nk h) ∉ (R.s i).verifier.used)
    (hnf1 : dummyNullifier h E.chain e ∉ (R.s i).verifier.used)
    (hne : nullifier h E.chain j (U.nk h) ≠ dummyNullifier h E.chain e)
    (hroom : (R.s i).ledger.leaves.length + 2 ≤ TREE_SIZE)
    (hpaused : (R.s i).verifier.paused = false) (htp : (R.s i).verifier.tokenPaused t = false)
    {rc : Addr} (hrc0 : rc ≠ 0) (hrcl : rc < ADDRESS_BOUND) (hblocked : (R.s i).notBlocked E rc)
    {tk : TokenSt} (htk : (R.s i).tokens t = some tk) (hsup : tk.supply + o.value.val < UINT256)
    (salt1 salt2 : F) {att : Addr}
    (hatt : att ∈ (R.s i).verifier.attesters ∧
      A.transact att (withdrawPub h E U t j o ρ asp e rc salt1 salt2)) :
    ∃ s', exec h E A (.transact ⟨ri, withdrawPub h E U t j o ρ asp e rc salt1 salt2, att⟩
        (withdrawWit h U j o (siblings h (hashes h ((R.s i).ledger.leaves.take ri)) j) e salt1 salt2))
        (R.s i) = some s' ∧
      ∃ tk', s'.tokens t = some tk' ∧
        tk.bal rc + (o.value.val - Verifier.withdrawFee (R.s i) t o.value.val) ≤ tk'.bal rc ∧
        Verifier.withdrawFee (R.s i) t o.value.val * 10000 ≤ o.value.val * 300 := by
  have hI := hyp.inv i hi
  have hfees := R.feesOK i hi
  set s := R.s i
  have hjL : j < s.ledger.leaves.length := (List.getElem?_eq_some_iff.mp hnote).1
  have hvalid := (hI.valid _ (List.mem_of_getElem? hnote))
  have ht : t < TOKEN_BOUND := hvalid.1
  obtain ⟨o', ho', hnh, hvl, -⟩ := hI.notes j t nh hnote
  rw [hopen, Option.some.injEq] at ho'
  subst ho'
  obtain ⟨hri, rfl⟩ := hI.provedRoots hroot
  have hjT : j < 2 ^ DEPTH := lt_of_lt_of_le hjL hI.cap
  have hjr' : j < r := hjT.trans (two_pow_le_r (by unfold DEPTH; norm_num))
  have htr : t < r := ht.trans (two_pow_le_r (by norm_num))
  have hchain : (E.chain).val = E.chainId := val_cast (E.chainId_lt.trans (two_pow_le_r (by norm_num)))
  set x := withdrawPub h E U t j o (treeRoot h (hashes h (s.ledger.leaves.take ri))) asp e rc salt1 salt2
  set w := withdrawWit h U j o (siblings h (hashes h (s.ledger.leaves.take ri)) j) e salt1 salt2
  -- The note's leaf, at its slot of the proved root.
  have hleaf : JS.leaf0 h x w = node h (hashes h (s.ledger.leaves.take ri)) 0 j := by
    simp only [JS.leaf0, x, w, withdrawPub, withdrawWit, Bool.false_eq_true, if_false, node,
      hashes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, if_pos hjr, hnote,
      Option.map_some, Option.getD_some, Leaf.hash, Leaf.words, val_cast htr, ZMod.natCast_zmod_val,
      List.map_cons, List.map_nil, Nat.cast_zero, hnh]
  have hspec : JS.Spec h x w := by
    refine ⟨by simp [x, withdrawPub, val_cast htr, ht], by simp [x, withdrawPub, hchain, E.chainId_lt],
      by simp [x, withdrawPub, hvl], by simp [w, withdrawWit, AMOUNT_BOUND],
      by simp [w, withdrawWit, hvl], by simp [w, withdrawWit, JS.Opening.zero, AMOUNT_BOUND],
      by simp [w, withdrawWit, AMOUNT_BOUND], by simp [w, withdrawWit, AMOUNT_BOUND],
      by simp [x, withdrawPub, val_cast (hrcl.trans address_lt_r), hrcl],
      by simp [w, withdrawWit, ADDRESS_BOUND], by simp [w, withdrawWit, val_cast hjr', hjT],
      by simp [w, withdrawWit], fun _ => ?_, fun h => by simp [w, withdrawWit] at h, ?_,
      ?_, fun h => by simp [w, withdrawWit] at h, fun _ => ?_, by simpa [x, withdrawPub] using hne,
      rfl, rfl, ?_, fun h => absurd h hval⟩
    · refine ⟨?_, rfl, rfl, rfl, rfl⟩
      simp [w, withdrawWit, JS.pk0, JS.nk0, hown, Owner.pk, Owner.nk]
    · rw [hleaf, show (w.idx0).val = j from val_cast hjr']
      exact merkleRoot_canonical h _ j hjT
    · simp [x, w, withdrawPub, withdrawWit, JS.nk0, Owner.nk]
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · simp [x, w, withdrawPub, withdrawWit, JS.value0, JS.value1]
  have hok : Verifier.TransactOK h E A ⟨ri, x, att⟩ w s := by
    refine ⟨hpaused, ⟨by simpa [x, withdrawPub, val_cast htr] using ht, ?_, ?_⟩, by simp [x, withdrawPub, hchain],
      hroot, ⟨by simp [x, withdrawPub, hvl], by simp [x, withdrawPub, val_cast (hrcl.trans address_lt_r), hrcl]⟩,
      by simpa [x, withdrawPub, val_cast haspr] using hasp, ⟨by simpa [x, withdrawPub] using hne,
        by simpa [x, withdrawPub] using hnf0, by simpa [x, withdrawPub] using hnf1⟩, ?_, hatt, hspec⟩
    · simpa [x, withdrawPub, val_cast htr] using hvalid.2
    · simpa [x, withdrawPub, val_cast htr] using htp
    · have hrcF : (rc : F) ≠ 0 := by
        intro he
        have := congrArg ZMod.val he
        rw [val_cast (hrcl.trans address_lt_r), ZMod.val_zero] at this
        exact hrc0 this
      simp [x, withdrawPub, hval, hrcF]
  have hval' : o.value.val ≠ 0 := (ZMod.val_ne_zero _).mpr hval
  -- The withdrawal settles on the state with both change notes committed.
  set s3 := ((s.spendAll [x.nf0, x.nf1]).append h (.note x.token.val x.nh1)).append h
    (.note x.token.val x.nh2)
  have htk3 : s3.tokens t = some tk := by simpa [s3, State.append, State.spendAll] using htk
  obtain ⟨s4, hset, -, -, -, tk', htk', hbal⟩ := settle_ok (h := h) (E := E) htk3 hval'
    (fun t' => by simpa [s3, State.append, State.spendAll] using hfees t') hrc0 hrcl
    (by simp [s3, State.append, State.spendAll, State.stopped, hpaused, htp])
    hvl (by simpa [s3, State.append, State.spendAll, State.notBlocked] using hblocked) hsup
  have hx : x.token.val = t ∧ x.recipient.val = rc ∧ x.amount.val = o.value.val ∧
      decide (x.intent.val = E.unwrapIntent) = false := by
    refine ⟨by simp [x, withdrawPub, val_cast htr], by simp [x, withdrawPub,
      val_cast (hrcl.trans address_lt_r)], rfl, ?_⟩
    simp [x, withdrawPub, Ne.symm E.unwrapIntent_ne]
  rw [← hx.1, ← hx.2.1, ← hx.2.2.1, ← hx.2.2.2] at hset
  rw [← hx.1] at htk'
  refine ⟨_, transact_of hok (by simpa using hroom) hset, tk', ?_, hbal, ?_⟩
  · simpa [Verifier.recordSpent, Verifier.recordNote, hx.1] using htk'
  · exact quote_le (hfees t) _

end withdrawNote

/-! ## What keeps an exit possible -/

section stays

/-- The nullifiers an action spends. -/
def Action.nullifiers : Action → List F
  | .transact req _ => [req.pub.nf0, req.pub.nf1]
  | .merge req _ => req.nullifiers
  | .rageExit req _ => [req.nf]
  | _ => []

/-- What a step other than an admin's leaves alone, and what it only adds to. -/
structure NonAdminStep (s s' : State) (nfs : List F) : Prop where
  leaves : s.ledger.leaves <+: s'.ledger.leaves
  notes : ∀ j < s.ledger.leaves.length, s'.ghost.notes j = s.ghost.notes j
  used : s'.verifier.used = s.verifier.used ∪ {nf | nf ∈ nfs}
  era : s'.ledger.era = s.ledger.era
  provedRoots : ∀ i ρ, 0 < s.ledger.era → s.provedRoots i ρ → s'.provedRoots i ρ
  aspAccepted : ∀ a, s.aspAccepted a → s'.aspAccepted a
  paused : s'.verifier.paused = s.verifier.paused
  tokenPaused : s'.verifier.tokenPaused = s.verifier.tokenPaused
  blocked : s'.blocked = s.blocked
  attesters : s'.verifier.attesters = s.verifier.attesters
  tokens : ∀ t, s.tokens t ≠ none → s'.tokens t ≠ none

theorem NonAdminStep.trans {s1 s2 s3 : State} {n1 n2 : List F} (h12 : NonAdminStep s1 s2 n1)
    (h23 : NonAdminStep s2 s3 n2) : NonAdminStep s1 s3 (n1 ++ n2) where
  leaves := h12.leaves.trans h23.leaves
  notes j hj := by
    rw [h23.notes j (lt_of_lt_of_le hj h12.leaves.length_le), h12.notes j hj]
  used := by rw [h23.used, h12.used]; ext; simp [or_assoc]
  era := h23.era.trans h12.era
  provedRoots i ρ he hp := h23.provedRoots i ρ (by rw [h12.era]; exact he) (h12.provedRoots i ρ he hp)
  aspAccepted a ha := h23.aspAccepted a (h12.aspAccepted a ha)
  paused := h23.paused.trans h12.paused
  tokenPaused := h23.tokenPaused.trans h12.tokenPaused
  blocked := h23.blocked.trans h12.blocked
  attesters := h23.attesters.trans h12.attesters
  tokens t ht := h23.tokens t (h12.tokens t ht)

/-- A step that keeps the ledger, the ghost's openings, the blocklist and the Verifier but its fee
debts and spent nullifiers. -/
theorem NonAdminStep.of_frame {s s' : State} {nfs : List F} (hl : s'.ledger = s.ledger)
    (hn : s'.ghost.notes = s.ghost.notes) (hv : s'.verifier.noAccrued =
      ({ s.verifier with used := s.verifier.used ∪ {nf | nf ∈ nfs} } : VerifierSt).noAccrued)
    (hb : s'.blocked = s.blocked) (ht : ∀ t, s.tokens t ≠ none → s'.tokens t ≠ none) :
    NonAdminStep s s' nfs := by
  have f := fun {α : Type} (g : VerifierSt → α) => (congrArg g hv : _)
  refine ⟨by rw [hl], fun j _ => by rw [hn], ?_, by rw [hl], fun i ρ _ hp => ?_, fun a ha => ?_,
    ?_, ?_, hb, ?_, ht⟩
  · have := f VerifierSt.used; exact this
  · unfold State.provedRoots State.inEra at *; rw [hl]; exact hp
  · unfold State.aspAccepted at *
    have h1 := f VerifierSt.aspRootEpoch; have h2 := f VerifierSt.aspEpoch
    simp only [VerifierSt.noAccrued] at h1 h2
    rw [h1, h2]; exact ha
  · have := f VerifierSt.paused; exact this
  · have := f VerifierSt.tokenPaused; exact this
  · have := f VerifierSt.attesters; exact this

/-- A step that keeps the proved roots' bookkeeping, the blocklist and the Verifier but its fee
debts and spent nullifiers, and only appends leaves and opens new positions. -/
theorem NonAdminStep.mk' {s s' : State} {nfs : List F} (hl : s.ledger.leaves <+: s'.ledger.leaves)
    (hn : ∀ j < s.ledger.leaves.length, s'.ghost.notes j = s.ghost.notes j)
    (hp : s'.ledger.provedIn = s.ledger.provedIn) (hbd : s'.ledger.bound = s.ledger.bound)
    (he : s'.ledger.era = s.ledger.era) (hee : s'.ledger.eraEnd = s.ledger.eraEnd)
    (hv : s'.verifier.noAccrued =
      ({ s.verifier with used := s.verifier.used ∪ {nf | nf ∈ nfs} } : VerifierSt).noAccrued)
    (hb : s'.blocked = s.blocked) (ht : ∀ t, s.tokens t ≠ none → s'.tokens t ≠ none) :
    NonAdminStep s s' nfs := by
  have f := fun {α : Type} (g : VerifierSt → α) => (congrArg g hv : _)
  refine ⟨hl, hn, ?_, he, fun i ρ _ hpr => ?_, fun a ha => ?_, ?_, ?_, hb, ?_, ht⟩
  · have := f VerifierSt.used; exact this
  · unfold State.provedRoots State.inEra at *; rw [hp, hbd, he, hee]; exact hpr
  · unfold State.aspAccepted at *
    have h1 := f VerifierSt.aspRootEpoch; have h2 := f VerifierSt.aspEpoch
    simp only [VerifierSt.noAccrued] at h1 h2
    rw [h1, h2]; exact ha
  · have := f VerifierSt.paused; exact this
  · have := f VerifierSt.tokenPaused; exact this
  · have := f VerifierSt.attesters; exact this

theorem NonAdminStep.ofFrame {s s' : State} (f : Frame s s')
    (ht : ∀ t, s.tokens t ≠ none → s'.tokens t ≠ none) : NonAdminStep s s' [] :=
  NonAdminStep.mk' (by rw [f.ledger]) (fun _ _ => by rw [f.ghost]) (by rw [f.ledger])
    (by rw [f.ledger]) (by rw [f.ledger]) (by rw [f.ledger]) (by rw [f.verifier]; simp [VerifierSt.noAccrued])
    f.blocked ht

theorem NonAdminStep.update {s s' : State} {t : ℕ} {a b : Addr} {v : ℕ}
    (hs : ZERC20.update h E t a b v s = some s') : NonAdminStep s s' [] := by
  obtain ⟨tk, htk, -, -, -, -, hT, hG, hV, hB, -, hpr, -, hbd, he, hee, hL, -⟩ := update_post hs
  refine NonAdminStep.mk' (by rw [hL]; exact List.prefix_append _ _) (fun _ _ => by rw [hG]) hpr hbd
    he hee (by rw [hV]; simp [VerifierSt.noAccrued]) hB (fun t' ht' => ?_)
  rw [hT, Function.update_apply]; split_ifs <;> simp_all

theorem exec_nonAdmin {s s' : State} {a : Action} (hs : exec h E A a s = some s')
    (ha : ∀ op, a ≠ .admin op) : NonAdminStep s s' a.nullifiers := by
  cases a with
  | transact req w =>
    obtain ⟨hok, -, s4, hp, rfl⟩ := transact_spec hs
    have hf := hp.1
    refine NonAdminStep.mk' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [Verifier.recordSpent, Verifier.recordNote, hf.ledger]
      simp [State.append, State.spendAll]
    · intro j hj
      simp only [Verifier.recordSpent, Verifier.recordNote, Function.update_apply, hf.ghost]
      rw [if_neg (by omega), if_neg (by omega)]; simp [State.append, State.spendAll]
    all_goals first
      | (simp [Verifier.recordSpent, Verifier.recordNote, hf.ledger, State.append, State.spendAll];
         done)
      | skip
    · simp only [Verifier.recordSpent, Verifier.recordNote, hf.verifier]
      simp [VerifierSt.noAccrued, State.append, State.spendAll, Action.nullifiers]
    · simp only [Verifier.recordSpent, Verifier.recordNote]
      rw [hf.blocked]; simp [State.append, State.spendAll]
    · intro t ht
      simp only [Verifier.recordSpent, Verifier.recordNote]
      exact (hp.tokens_iff t).mpr (by simpa [State.append, State.spendAll] using ht)
  | merge req ws =>
    obtain ⟨hok, -, -, s3, hp, rfl⟩ := merge_spec hs
    have hf := hp.1
    refine NonAdminStep.mk' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [Verifier.recordSpent, Verifier.recordNote, hf.ledger]
      simp [State.append, State.spendAll]
    · intro j hj
      simp only [Verifier.recordSpent, Verifier.recordNote, Function.update_apply, hf.ghost]
      rw [if_neg (by omega)]; simp [State.append, State.spendAll]
    all_goals first
      | (simp [Verifier.recordSpent, Verifier.recordNote, hf.ledger, State.append, State.spendAll];
         done)
      | skip
    · simp only [Verifier.recordSpent, Verifier.recordNote, hf.verifier]
      simp [VerifierSt.noAccrued, State.append, State.spendAll, Action.nullifiers]
    · simp only [Verifier.recordSpent, Verifier.recordNote]
      rw [hf.blocked]; simp [State.append, State.spendAll]
    · intro t ht
      simp only [Verifier.recordSpent, Verifier.recordNote]
      exact (hp.tokens_iff t).mpr (by simpa [State.append, State.spendAll] using ht)
  | rageExit req w =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, s2, h2, rfl⟩ := rageExit_spec hs
    have hp := payOut_paid h2
    have hf := hp.1
    refine NonAdminStep.mk' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (simp [Verifier.recordSpent, hf.ledger, State.spendAll]; done)
      | skip
    · intro j hj; simp [Verifier.recordSpent, hf.ghost, State.spendAll]
    · simp only [Verifier.recordSpent, hf.verifier]
      simp [VerifierSt.noAccrued, State.spendAll, Action.nullifiers]
    · simp only [Verifier.recordSpent]; rw [hf.blocked]; rfl
    · intro t ht
      exact (hp.tokens_iff t).mpr (by simpa [State.spendAll] using ht)
  | wrap t c rc v =>
    simp only [exec, ZERC20.wrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, tk, htk, s1, h1, h2⟩ := hs
    have n0 : NonAdminStep s (s.setToken t { tk with underlying := tk.underlying + v }) [] :=
      NonAdminStep.mk' (by simp [State.setToken]) (fun _ _ => rfl) rfl rfl rfl rfl
        (by simp [State.setToken, VerifierSt.noAccrued]) rfl
        (fun t' _ => by simp [State.setToken, Function.update_apply]; split_ifs <;> simp_all)
    have n1 := n0.trans (NonAdminStep.update h1)
    split_ifs at h2
    · simpa [Action.nullifiers] using n1.trans (NonAdminStep.update h2)
    · cases h2; simpa [Action.nullifiers] using n1
  | unwrap t c rc v =>
    simp only [exec, ZERC20.unwrap, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    obtain ⟨-, -, s1, h1, h2⟩ := hs
    have hp := release_paid h2
    simpa [Action.nullifiers] using (NonAdminStep.update h1).trans
      (NonAdminStep.ofFrame hp.1 fun t' => (hp.tokens_iff t').mpr)
  | transfer t a b v =>
    simp only [exec, ZERC20.transfer, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
      exists_const] at hs
    simpa [Action.nullifiers] using NonAdminStep.update hs.2
  | donate t v =>
    simp only [exec, Zerc20.donate, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hs
    obtain ⟨tk, htk, rfl⟩ := hs
    exact NonAdminStep.mk' (by simp [State.setToken]) (fun _ _ => rfl) rfl rfl rfl rfl
      (by simp [State.setToken, VerifierSt.noAccrued, Action.nullifiers]) rfl
      (fun t' _ => by simp [State.setToken, Function.update_apply]; split_ifs <;> simp_all)
  | reserveHashChain =>
    simp only [exec, CommitmentLedger.reserveHashChain] at hs
    split_ifs at hs
    · cases hs
      exact NonAdminStep.mk' (List.prefix_refl _) (fun _ _ => rfl) rfl rfl rfl rfl
        (by simp [VerifierSt.noAccrued, Action.nullifiers]) rfl (fun _ h => h)
    · simp only [bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
        Option.pure_def, Option.some.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      exact NonAdminStep.mk' (List.prefix_refl _) (fun _ _ => rfl) rfl rfl rfl rfl
        (by simp [VerifierSt.noAccrued, Action.nullifiers]) rfl (fun _ h => h)
  | checkpointBefore e p cs =>
    simp only [exec, CommitmentLedger.checkpointBefore, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, rfl⟩ := hs
    exact NonAdminStep.mk' (List.prefix_refl _) (fun _ _ => rfl) rfl rfl rfl rfl
      (by simp [VerifierSt.noAccrued, Action.nullifiers]) rfl (fun _ h => h)
  | proveRoot new ws =>
    simp only [exec, CommitmentLedger.proveRootTransition, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hs
    refine ⟨List.prefix_refl _, fun _ _ => rfl, by simp [Action.nullifiers], rfl,
      fun i ρ he hp => ?_, fun _ h => h, rfl, rfl, rfl, rfl, fun _ h => h⟩
    unfold State.provedRoots State.inEra at *
    simp only
    split_ifs with hiρ
    · exact ⟨hp.1, Nat.pos_iff_ne_zero.mp he, Or.inl rfl⟩
    · exact hp
  | publishAspRoot c a =>
    simp only [exec, Verifier.publishAspRoot, bind, Option.bind_eq_some_iff,
      guard_eq_some_unit, exists_const, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs
    refine ⟨List.prefix_refl _, fun _ _ => rfl, by simp [Action.nullifiers], rfl,
      fun _ _ _ h => h, fun a' ha => ?_, rfl, rfl, rfl, rfl, fun _ h => h⟩
    unfold State.aspAccepted at *
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | claimFees t rc =>
    by_cases hv : (s.verifier.accrued t rc) = 0
    · simp only [exec, Verifier.claimFees, hv, if_true, Option.some.injEq] at hs
      subst hs
      exact NonAdminStep.mk' (List.prefix_refl _) (fun _ _ => rfl) rfl rfl rfl rfl
        (by simp [VerifierSt.noAccrued, Action.nullifiers]) rfl (fun _ h => h)
    · simp only [exec, Verifier.claimFees, hv, if_false, ZERC20.transfer, bind,
        Option.bind_eq_some_iff, guard_eq_some_unit, exists_const] at hs
      have n0 : NonAdminStep s { s with verifier := { s.verifier with
          accrued := Function.update s.verifier.accrued t
            (Function.update (s.verifier.accrued t) rc 0) } } [] :=
        NonAdminStep.mk' (List.prefix_refl _) (fun _ _ => rfl) rfl rfl rfl rfl
          (by simp [VerifierSt.noAccrued]) rfl (fun _ h => h)
      simpa [Action.nullifiers] using n0.trans (NonAdminStep.update hs.2)
  | sign m =>
    simp only [exec, Option.some.injEq] at hs
    subst hs
    exact NonAdminStep.mk' (List.prefix_refl _) (fun _ _ => rfl) rfl rfl rfl rfl
      (by simp [VerifierSt.noAccrued, Action.nullifiers]) rfl (fun _ h => h)
  | admin op => exact absurd rfl (ha op)

end stays

section staysRun

variable {R : Run h E A} {U : Owner}

theorem Run.era_pos (R : Run h E A) : ∀ i ≤ R.n, 0 < (R.s i).ledger.era := by
  intro i hi
  induction i with
  | zero => rw [R.init]; simp [State.init]
  | succ i ih =>
    have hs := R.step i (by omega)
    have he := ih (by omega)
    cases ha : R.a i with
    | admin op =>
      rw [ha] at hs
      cases op <;>
        simp only [exec, AdminOp.exec, CommitmentLedger.enterEmergency, CommitmentLedger.recover,
          bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const, Option.pure_def,
          Option.some.injEq] at hs
      case recover i' ρ =>
        obtain ⟨-, -, -, c, -, hs⟩ := hs; rw [← hs]; simp
      case enterEmergency b => rw [← hs]; split_ifs <;> simpa
      all_goals first
        | (obtain ⟨-, hs⟩ := hs; rw [← hs]; exact he)
        | (rw [← hs]; exact he)
        | (obtain ⟨-, -, -, -, hs⟩ := hs; rw [← hs]; exact he)
    | _ =>
      rw [ha] at hs
      rw [(exec_nonAdmin hs (by simp)).era]; exact he

/-- A step that does not spend the owner's position `j` does not spend its nullifier: every
nullifier a step spends is a position's under the key that opens it, or a dummy one, and no
collision equates either with the owner's. -/
theorem OwnerHyp.nullifier_kept (hyp : OwnerHyp R U) {i : ℕ} (hi : i < R.n) {j : ℕ}
    (hj : j < 2 ^ DEPTH) (hns : j ∉ (R.a i).spends) :
    nullifier h E.chain j (U.nk h) ∉ (R.a i).nullifiers := by
  have hc := hyp.toRunHyp.ctx hi
  have hstep := R.step i hi
  have hU : [DOMAIN_NULLIFIER, E.chain, (j : F), U.nk h, 0] ∈ R.calls ∪ U.calls h E :=
    Or.inr (Or.inr ⟨j, hj, rfl⟩)
  have hjr : j < r := hj.trans (two_pow_le_r (by unfold DEPTH; norm_num))
  -- A position's nullifier equal to the owner's is the owner's position.
  have hpos : ∀ (c idx nk : F), c = E.chain →
      [DOMAIN_NULLIFIER, c, idx, nk, 0] ∈ R.calls → nullifier h c idx nk = nullifier h E.chain j (U.nk h) →
      idx.val = j := by
    intro c idx nk hcE hx he
    have := hyp.inj _ (Or.inl hx) _ hU he
    simp only [List.cons.injEq] at this
    rw [this.2.2.1, val_cast hjr]
  have hdummy : ∀ (c e : F), [DOMAIN_DUMMY_NULLIFIER, c, e + 1] ∈ R.calls →
      dummyNullifier h c e ≠ nullifier h E.chain j (U.nk h) := by
    intro c e hx he
    have := hyp.inj _ (Or.inl hx) _ hU he
    simp at this
  generalize ha : R.a i = a at hns hc hstep ⊢
  cases a with
  | transact req w =>
    obtain ⟨hok, -⟩ := transact_spec hstep
    have hsp := hok.proof
    have hcalls := hc.calls
    simp only [Action.calls] at hcalls
    have hchain : req.pub.chain = E.chain := by rw [Env.chain, ← hok.chain, ZMod.natCast_zmod_val]
    simp only [Action.nullifiers, List.mem_cons, List.not_mem_nil, or_false]
    rintro (he | he)
    · rw [hsp.nf0] at he
      exact hns (by simp [Action.spends, transactSpent,
        ← hpos _ _ _ hchain (hcalls (by simp [JS.calls])) he.symm])
    · cases hd : w.in1IsDummy
      · rw [(hsp.real1 hd).2.2] at he
        exact hns (by simp [Action.spends, transactSpent, hd,
          ← hpos _ _ _ hchain (hcalls (by simp [JS.calls])) he.symm])
      · rw [(hsp.dummy1 hd).1] at he
        exact hdummy _ _ (hcalls (by simp [JS.calls])) he.symm
  | merge req ws =>
    obtain ⟨hok, -⟩ := merge_spec hstep
    have hcalls := hc.calls
    simp only [Action.calls] at hcalls
    simp only [Action.nullifiers]
    intro hmem
    rw [← merge_nfs hyp.toRunHyp hok hc.sha] at hmem
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem hmem
    rw [mergeNfs_length] at hk
    rw [mergeNfs_getElem _ _ hk, Merge.nf] at he
    have fk := (mergeAlong_fixed (h := h) (req.z0 h E) ws k).2.1
    have hidx := hpos _ _ _ fk ((Merge.callsAlong_mem hk).trans hcalls (by simp [Merge.calls])) he
    exact hns (by simp only [Action.spends, List.mem_map]; exact ⟨ws[k], List.getElem_mem hk, hidx⟩)
  | rageExit req w =>
    obtain ⟨-, -, -, -, hch, -, -, -, hspec, -⟩ := rageExit_spec hstep
    have hcalls := hc.calls
    simp only [Action.calls, RE.calls] at hcalls
    simp only [Action.nullifiers, List.mem_singleton]
    intro he
    have hnf := hspec.nf
    simp only at hnf
    rw [hnf] at he
    have := hpos E.chain (req.index : F) (nullifyingKey h w.sk) rfl (hcalls (by simp [Env.chain])) he.symm
    have hir : req.index < r := by
      have hI := hyp.toRunHyp.inv i hi.le

      have := (hI.hashChainAt hch).1
      have hcap := hI.cap
      unfold Verifier.RageReq.index TREE_SIZE DEPTH at *
      have := two_pow_le_r (n := 32) (by norm_num)
      omega
    rw [val_cast hir] at this
    exact hns (by simp [Action.spends, this])
  | _ => simp [Action.nullifiers]

end staysRun

end

end Zerc20
