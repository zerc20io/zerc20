import Zerc20.Model

/-!
# What each contract function changes

Closed forms of the model's functions where they succeed, so the invariant proofs never unfold a
`do` block.
-/

namespace Zerc20

open scoped Classical

@[simp] theorem guard_bind_eq_some {α : Type} (p : Prop) [Decidable p] (f : Unit → Option α)
    (x : α) : (guard p : Option Unit).bind f = some x ↔ p ∧ f () = some x := by
  by_cases hp : p <;> simp [guard, hp]

@[simp] theorem guard_eq_some_unit (p : Prop) [Decidable p] (u : Unit) :
    (guard p : Option Unit) = some u ↔ p := by
  by_cases hp : p <;> simp [guard, hp]

variable (h : Hashes) (E : Env)

section ledger

variable {h}

theorem commit_eq {l : Leaf} {s s' : State} :
    CommitmentLedger.commit h l s = some s' ↔
      s.ledger.leaves.length < TREE_SIZE ∧ s' = s.append h l := by
  simp only [CommitmentLedger.commit, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
    exists_const, Option.pure_def, Option.some.injEq]
  exact and_congr_right fun _ => eq_comm

theorem hashChainAt_eq {s : State} {i c : ℕ} : s.hashChainAt i = some c ↔
    i ≤ s.ledger.leaves.length ∧
      (if i = s.ledger.leaves.length then c = s.ledger.head
        else if i = 0 then c = 0 else s.ledger.checkpoints i ≠ 0 ∧ c = s.ledger.checkpoints i) := by
  unfold State.hashChainAt
  by_cases h1 : s.ledger.leaves.length < i
  · simp [h1]
  · simp only [h1, if_false, not_lt.mp h1, true_and]
    split_ifs <;> simp_all [eq_comm]

theorem verifySegment_eq {end_ prev : ℕ} {commits : List (List ℕ)} {s : State} {start : ℕ} :
    CommitmentLedger.verifySegment h end_ prev commits s = some start ↔
      commits ≠ [] ∧ commits.length ≤ end_ ∧ s.hashChainAt end_ = some (commits.foldl h.hc prev) ∧
        start = end_ - commits.length := by
  simp only [CommitmentLedger.verifySegment, bind, Option.bind_eq_some_iff, guard_eq_some_unit,
    exists_const, Option.pure_def, Option.some.injEq]
  constructor
  · rintro ⟨h1, h2, c, hc, h3, rfl⟩
    exact ⟨h1, h2, h3 ▸ hc, rfl⟩
  · rintro ⟨h1, h2, hc, rfl⟩
    exact ⟨h1, h2, _, hc, rfl, rfl⟩

end ledger

section token

variable {h E}

theorem update_eq {t : ℕ} {src dst : Addr} {v : ℕ} {s s' : State} :
    ZERC20.update h E t src dst v s = some s' ↔
      ∃ tk, s.tokens t = some tk ∧ src < ADDRESS_BOUND ∧ dst < ADDRESS_BOUND ∧
        ¬ s.stopped t ∧ v < AMOUNT_BOUND ∧ s.notBlocked E src ∧
        s.notBlocked E dst ∧ tk.canMove src v ∧
        if src = 0 ∨ dst = 0 ∨ v = 0 then s' = s.setToken t (tk.move src dst v)
        else s.ledger.leaves.length < TREE_SIZE ∧
          s' = (s.setToken t (tk.move src dst v)).append h (Leaf.transfer t src dst v) := by
  simp only [ZERC20.update, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def]
  constructor
  · rintro ⟨tk, htk, ⟨a1, a2⟩, ⟨h1, h2, h3, h4, h5⟩, hs⟩
    refine ⟨tk, htk, a1, a2, h1, h2, h3, h4, h5, ?_⟩
    split_ifs at hs ⊢ with hl
    · simpa [eq_comm] using hs
    · simpa [commit_eq, State.setToken] using hs
  · rintro ⟨tk, htk, a1, a2, h1, h2, h3, h4, h5, hs⟩
    refine ⟨tk, htk, ⟨a1, a2⟩, ⟨h1, h2, h3, h4, h5⟩, ?_⟩
    split_ifs at hs ⊢ with hl
    · simp [hs]
    · simpa [commit_eq, State.setToken] using hs

end token

/-! ## Token books -/

namespace TokenSt

/-- The sum of all balances. -/
def total (tk : TokenSt) : ℕ := tk.bal.sum fun _ v => v

/-- OpenZeppelin's ERC-20 books: the supply is the sum of the balances, and the zero address holds
nothing. -/
def Books (tk : TokenSt) : Prop := tk.supply = tk.total ∧ tk.bal 0 = 0

theorem total_update (tk : TokenSt) (i a : ℕ) :
    (tk.bal.update i a).sum (fun _ v => v) + tk.bal i = tk.total + a :=
  Finsupp.sum_update_add _ _ _ _ (fun _ => rfl) fun _ _ _ => rfl

theorem bal_le_total (tk : TokenSt) (i : ℕ) : tk.bal i ≤ tk.total := by
  by_cases hi : i ∈ tk.bal.support
  · exact Finset.single_le_sum (f := fun j => tk.bal j) (fun _ _ => Nat.zero_le _) hi
  · simp [Finsupp.notMem_support_iff.mp hi]

theorem move_books {tk : TokenSt} {src dst : Addr} {v : ℕ} (hb : tk.Books)
    (hm : tk.canMove src v) : (tk.move src dst v).Books := by
  obtain ⟨hs, h0⟩ := hb
  have hle := bal_le_total tk src
  have hu := total_update
  unfold move canMove Books total at *
  by_cases hsrc : src = 0 <;> by_cases hdst : dst = 0 <;>
    simp only [hsrc, hdst, if_true, if_false] at hm ⊢
  · exact ⟨by omega, h0⟩
  · have := hu tk dst (tk.bal dst + v)
    refine ⟨by omega, ?_⟩
    rw [Finsupp.update_apply, if_neg (Ne.symm hdst), h0]
  · have := hu tk src (tk.bal src - v)
    refine ⟨by omega, ?_⟩
    rw [Finsupp.update_apply, if_neg (Ne.symm hsrc), h0]
  · have h1 := hu tk src (tk.bal src - v)
    have h2 := hu { tk with bal := tk.bal.update src (tk.bal src - v) } dst
      (Function.update tk.bal src (tk.bal src - v) dst + v)
    simp only [Finsupp.coe_update] at h1 h2 hle ⊢
    refine ⟨by omega, ?_⟩
    simp [Function.update_apply, Ne.symm hsrc, Ne.symm hdst, h0]

end TokenSt

/-- A Verifier's state, its fee debts aside. -/
def VerifierSt.noAccrued (v : VerifierSt) : VerifierSt := { v with accrued := fun _ _ => 0 }

/-- Parts of the state a payout leaves alone. -/
structure Frame (s s' : State) : Prop where
  ledger : s'.ledger = s.ledger
  ghost : s'.ghost = s.ghost
  verifier : s'.verifier.noAccrued = s.verifier.noAccrued
  blocked : s'.blocked = s.blocked

theorem Frame.used {s s' : State} (f : Frame s s') : s'.verifier.used = s.verifier.used :=
  by have := congrArg VerifierSt.used f.verifier; exact this

theorem Frame.fees {s s' : State} (f : Frame s s') : s'.verifier.fees = s.verifier.fees :=
  by have := congrArg VerifierSt.fees f.verifier; exact this

theorem Frame.trans {s1 s2 s3 : State} (f1 : Frame s1 s2) (f2 : Frame s2 s3) : Frame s1 s3 :=
  ⟨f2.ledger.trans f1.ledger, f2.ghost.trans f1.ghost, f2.verifier.trans f1.verifier,
    f2.blocked.trans f1.blocked⟩

/-- A token's books after paying out `d`: as much minted or released, and no balance lower. -/
structure Payout (tk tk' : TokenSt) (d : ℕ) : Prop where
  books : tk'.supply + tk.underlying = tk.supply + d + tk'.underlying
  grows : ∀ a, tk.bal a ≤ tk'.bal a
  erc20 : tk.Books → tk'.Books

/-- A step that only pays out `d` of token `t`. -/
def PaidOut (t d : ℕ) (s s' : State) : Prop :=
  Frame s s' ∧ (∀ t', t' ≠ t → s'.tokens t' = s.tokens t') ∧
    ∃ tk tk', s.tokens t = some tk ∧ s'.tokens t = some tk' ∧ Payout tk tk' d

theorem PaidOut.refl {t : ℕ} {s : State} (ht : s.tokens t ≠ none) : PaidOut t 0 s s := by
  obtain ⟨tk, htk⟩ := Option.ne_none_iff_exists'.mp ht
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, tk, tk, htk, htk, ⟨by omega, fun _ => le_rfl, id⟩⟩

theorem PaidOut.trans {t a b : ℕ} {s1 s2 s3 : State} (h12 : PaidOut t a s1 s2)
    (h23 : PaidOut t b s2 s3) : PaidOut t (a + b) s1 s3 := by
  obtain ⟨f1, o1, tk1, tk2, e1, e2, p1⟩ := h12
  obtain ⟨f2, o2, tk2', tk3, e2', e3, p2⟩ := h23
  rw [e2] at e2'
  cases e2'
  refine ⟨f1.trans f2,
    fun t' ht => (o2 t' ht).trans (o1 t' ht), tk1, tk3, e1, e3, ⟨?_, fun x => (p1.grows x).trans
    (p2.grows x), p2.erc20 ∘ p1.erc20⟩⟩
  have := p1.books; have := p2.books; omega

theorem PaidOut.tokens_ne_none {t d : ℕ} {s s' : State} (hp : PaidOut t d s s') :
    s.tokens t ≠ none := by
  obtain ⟨-, -, tk, -, htk, -⟩ := hp
  simp [htk]

theorem setToken_tokens {s : State} {t t' : ℕ} {tk : TokenSt} :
    (s.setToken t tk).tokens t' = if t' = t then some tk else s.tokens t' := by
  simp [State.setToken, Function.update_apply]

section payout

variable {h E}

/-- Minting `v` to a real account. -/
theorem mint_paid {t : ℕ} {rcpt : Addr} {v : ℕ} {s s' : State} (hr : rcpt ≠ 0)
    (hs : ZERC20.update h E t 0 rcpt v s = some s') : PaidOut t v s s' := by
  obtain ⟨tk, htk, -, -, -, -, -, -, hm, hs⟩ := update_eq.mp hs
  simp only [true_or, if_true] at hs
  subst hs
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, fun t' ht => by simp [setToken_tokens, ht], tk, tk.move 0 rcpt v, htk,
    by simp [setToken_tokens], ⟨?_, fun a => ?_, fun hb => TokenSt.move_books hb hm⟩⟩
  · simp only [TokenSt.move, if_true, hr, if_false]
  · simp only [TokenSt.move, if_true, hr, if_false, Finsupp.update_apply]
    split_ifs with ha
    · subst ha; omega
    · exact le_rfl

theorem release_paid {t v : ℕ} {s s' : State} (hs : ZERC20.release t v s = some s') :
    PaidOut t v s s' := by
  simp only [ZERC20.release, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq] at hs
  obtain ⟨tk, htk, hv, rfl⟩ := hs
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, fun t' ht => by simp [setToken_tokens, ht], tk,
    { tk with underlying := tk.underlying - v }, htk, by simp [setToken_tokens],
    ⟨by simp; omega, fun _ => le_rfl, fun hb => hb⟩⟩

theorem payOut_eq {t : ℕ} {rcpt : Addr} {v : ℕ} {u : Bool} {s s' : State} :
    ZERC20.payOut h E t rcpt v u s = some s' ↔ rcpt ≠ 0 ∧ v ≠ 0 ∧
      if u then ¬ s.stopped t ∧ s.notBlocked E rcpt ∧ ZERC20.release t v s = some s'
      else ZERC20.update h E t 0 rcpt v s = some s' := by
  simp only [ZERC20.payOut, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const]
  cases u <;> simp [and_assoc]

theorem payOut_paid {t : ℕ} {rcpt : Addr} {v : ℕ} {u : Bool} {s s' : State}
    (hs : ZERC20.payOut h E t rcpt v u s = some s') : PaidOut t v s s' := by
  obtain ⟨hr, -, hs⟩ := payOut_eq.mp hs
  cases u
  · exact mint_paid hr (by simpa using hs)
  · exact release_paid (by simp at hs; exact hs.2.2)

theorem payFee_paid {t fee : ℕ} {s s' : State} (ht : s.tokens t ≠ none)
    (hs : Verifier.payFee h E t fee s = some s') : PaidOut t fee s s' := by
  unfold Verifier.payFee at hs
  by_cases hf : fee = 0
  · simp only [hf, if_true, Option.some.injEq] at hs
    subst hs hf; exact PaidOut.refl ht
  · simp only [hf, if_false, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hs
    obtain ⟨s1, h1, rfl⟩ := hs
    have p := payOut_paid h1
    exact ⟨p.1.trans ⟨rfl, rfl, rfl, rfl⟩, p.2.1, p.2.2⟩

theorem settleWithdraw_paid {t : ℕ} {rcpt : Addr} {g : ℕ} {u : Bool} {s s' : State}
    (ht : s.tokens t ≠ none) (hs : Verifier.settleWithdraw h E t rcpt g u s = some s') :
    PaidOut t g s s' := by
  unfold Verifier.settleWithdraw at hs
  by_cases hg : g = 0
  · simp only [hg, if_true, Option.some.injEq] at hs
    subst hs hg; exact PaidOut.refl ht
  simp only [hg, if_false, Option.bind_eq_some_iff] at hs
  obtain ⟨s1, h1, h2⟩ := hs
  set fee := Verifier.withdrawFee s t g
  have p1 := payFee_paid ht h1
  -- The net payout is non-zero whenever it is made, so the fee never exceeds the gross amount.
  have p2 : PaidOut t (g - fee) s1 s' ∧ fee ≤ g := by
    by_cases hgf : g = fee
    · simp only [hgf, if_true, Option.some.injEq] at h2
      subst h2
      obtain ⟨-, -, -, tk', -, htk', -⟩ := p1
      exact ⟨by rw [hgf, Nat.sub_self]; exact PaidOut.refl (by simp [htk']), hgf.ge⟩
    · simp only [hgf, if_false] at h2
      exact ⟨payOut_paid h2, by have := (payOut_eq.mp h2).2.1; omega⟩
  have p := p1.trans p2.1
  rwa [Nat.add_sub_cancel' p2.2] at p

end payout

/-! ## Spends -/

/-- The state with `nfs` spent. -/
def State.spendAll (s : State) (nfs : List F) : State :=
  { s with verifier := { s.verifier with used := s.verifier.used ∪ {nf | nf ∈ nfs} } }

theorem spend_eq {nfs : List F} {s s' : State} :
    Verifier.spend nfs s = some s' ↔
      (nfs.Nodup ∧ ∀ nf ∈ nfs, nf ∉ s.verifier.used) ∧ s' = s.spendAll nfs := by
  simp only [Verifier.spend, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq, State.spendAll]
  exact and_congr_right fun _ => eq_comm

section actions

variable {h E} {A : Attest}

/-- `transact` where it succeeds: its checks hold, two notes are appended, the withdrawal is paid
out, and the ghost records the outputs' openings and the positions spent. -/
theorem transact_spec {req : Verifier.TransactReq} {w : JS.Wit} {s s' : State}
    (hs : Verifier.transact h E A req w s = some s') :
    Verifier.TransactOK h E A req w s ∧ s.ledger.leaves.length + 2 ≤ TREE_SIZE ∧
      ∃ s4, PaidOut req.pub.token.val req.pub.amount.val
          (((s.spendAll [req.pub.nf0, req.pub.nf1]).append h (.note req.pub.token.val req.pub.nh1)).append
            h (.note req.pub.token.val req.pub.nh2)) s4 ∧
        s' = Verifier.recordSpent (w.idx0.val :: if w.in1IsDummy then [] else [w.idx1.val])
          (Verifier.recordNote (s.ledger.leaves.length + 1) w.out2
            (Verifier.recordNote s.ledger.leaves.length w.out1 s4)) := by
  simp only [Verifier.transact, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq, spend_eq, ZERC20.commitNote, commit_eq] at hs
  obtain ⟨hok, s1, ⟨-, rfl⟩, s2, ⟨hc1, rfl⟩, s3, ⟨hc2, rfl⟩, s4, h4, rfl⟩ := hs
  refine ⟨hok, ?_, s4, settleWithdraw_paid ?_ h4, rfl⟩
  · simp [State.append, State.spendAll] at hc2; omega
  · simpa [State.append, State.spendAll] using hok.token.2.1

/-- `merge` where it succeeds: its checks hold, the nullifiers are distinct, the merged note is
appended, the fee is paid out, and the ghost records the note's opening and the positions spent. -/
theorem merge_spec {req : Verifier.MergeReq} {ws : List Merge.Wit} {s s' : State}
    (hs : Verifier.merge h E A req ws s = some s') :
    Verifier.MergeOK h E A req ws s ∧ req.nullifiers.Nodup ∧
      s.ledger.leaves.length + 1 ≤ TREE_SIZE ∧
      ∃ s3, PaidOut req.token req.fee
          ((s.spendAll req.nullifiers).append h (.note req.token req.noteHash)) s3 ∧
        s' = Verifier.recordSpent (ws.map fun w => w.idx.val)
          (Verifier.recordNote s.ledger.leaves.length (Verifier.mergeOpening req ws) s3) := by
  simp only [Verifier.merge, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq, spend_eq, ZERC20.commitNote, commit_eq] at hs
  obtain ⟨hok, s1, ⟨⟨hnd, -⟩, rfl⟩, s2, ⟨hc1, rfl⟩, s3, h3, rfl⟩ := hs
  refine ⟨hok, hnd, ?_, s3, settleWithdraw_paid ?_ h3, rfl⟩
  · simp [State.spendAll] at hc1; omega
  · simpa [State.append, State.spendAll] using hok.token.2.1

/-- `rageExit` where it succeeds: the segment reaches the chain at the checkpoint, the first
commitment is a transfer of a live token whose burn address the proof opens, the nullifier is
fresh, and the deposit is minted back to its sender. -/
theorem rageExit_spec {req : Verifier.RageReq} {w : RE.Wit} {s s' : State}
    (hs : Verifier.rageExit h E req w s = some s') :
    s.verifier.paused = false ∧ (∀ c ∈ req.commits, c.length = 4 ∧ ∀ v ∈ c, v < UINT256) ∧
      req.commits ≠ [] ∧ req.commits.length ≤ req.checkpointIndex ∧
      s.hashChainAt req.checkpointIndex = some (req.commits.foldl h.hc req.prev) ∧
      (Verifier.decode ((req.commits.headD []).getD 0 0)).1 = TRANSFER_TAG ∧
      Verifier.token (Verifier.decode ((req.commits.headD []).getD 0 0)).2 s ∧
      (req.commits.headD []).getD 2 0 < r ∧
      RE.Spec h ⟨req.nf, E.chainId, req.index, (req.commits.headD []).getD 2 0⟩ w ∧
      req.nf ∉ s.verifier.used ∧
      ∃ s2, ZERC20.payOut h E (Verifier.decode ((req.commits.headD []).getD 0 0)).2
          ((req.commits.headD []).getD 1 0 % ADDRESS_BOUND) ((req.commits.headD []).getD 3 0) false
          (s.spendAll [req.nf]) = some s2 ∧
        s' = Verifier.recordSpent [req.index] s2 := by
  simp only [Verifier.rageExit, bind, Option.bind_eq_some_iff, guard_eq_some_unit, exists_const,
    Option.pure_def, Option.some.injEq, spend_eq, verifySegment_eq] at hs
  obtain ⟨⟨h1, h2⟩, idx, ⟨h3, h4, h5, rfl⟩, ⟨h6, h7, h8, h9⟩, s1, ⟨⟨-, h10⟩, rfl⟩, s2, h11, rfl⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by simpa using h10, s2, h11, rfl⟩

end actions

end Zerc20
