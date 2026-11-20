import Zerc20.Liveness
import Zerc20.Circom
import Zerc20.Steps

/-!
# The deployed circuits

The protocol theorems hold for any hashes; here they meet the deployed ones. Poseidon is circomlib's
in the circom circuits and arkworks' sponge in the step circuits, which compute one permutation; the
hash chain is SHA-256; a signature is the Schnorr check over Baby-JubJub. With these:

* each verifier's acceptance condition in the model — a witness meeting the circuit's `Spec` — is
  exactly that the circuit's constraints are satisfiable: what an ideal Groth16 verifier accepts,
  and what an accepted call to a Nova decider gives (`decider_sound`);
* the ledger's initial root is the contract's `EMPTY_ROOT`.
-/

namespace Zerc20

open Zkp

/-! ## The constraints, and what the model's verifiers accept -/

theorem joinSplit_accepts (x : JS.Pub) :
    (∃ w, JS.Spec Zkp.hashes x w) ↔ ∃ a, Circom.JoinSplit.Rel Circom.circomlibPoseidon x a :=
  ⟨fun ⟨_, hs⟩ => (Circom.JoinSplit.main_complete rfl hs).imp fun _ h => h.1,
    fun ⟨_, ha⟩ => ⟨_, Circom.JoinSplit.main_sound rfl ha⟩⟩

theorem rageExit_accepts (x : RE.Pub) :
    (∃ w, RE.Spec Zkp.hashes x w) ↔ ∃ a, Circom.RageExit.Rel Circom.circomlibPoseidon x a :=
  ⟨fun ⟨_, hs⟩ => (Circom.RageExit.main_complete rfl hs).imp fun _ h => h.1,
    fun ⟨_, ha⟩ => ⟨_, Circom.RageExit.main_sound rfl ha⟩⟩

section chains

variable {Z W V : Type} {S : Z → W → Z → Prop} {T : Z → V → Prop} {next : Z → V → Z}
  {proj : V → W}

/-- A circuit's step chain: each step's constraints hold, and the next state is what they output. -/
def CircuitChain (T : Z → V → Prop) (next : Z → V → Z) : Z → List V → Z → Prop :=
  Chain fun z v z' => T z v ∧ z' = next z v

theorem chain_of_circuit (hs : ∀ z v, T z v → S z (proj v) (next z v)) :
    ∀ {z vs z'}, CircuitChain T next z vs z' → Chain S z (vs.map proj) z' := by
  intro z vs z' hc
  induction hc with
  | nil z => exact Chain.nil z
  | cons hstep _ ih =>
    obtain ⟨hT, rfl⟩ := hstep
    exact Chain.cons (hs _ _ hT) ih

theorem circuit_of_chain (hc : ∀ z w z', S z w z' → ∃ v, proj v = w ∧ T z v ∧ next z v = z') :
    ∀ {z ws z'}, Chain S z ws z' → ∃ vs, vs.map proj = ws ∧ CircuitChain T next z vs z' := by
  intro z ws z' hch
  induction hch with
  | nil z => exact ⟨[], rfl, Chain.nil z⟩
  | cons hstep _ ih =>
    obtain ⟨v, rfl, hT, hn⟩ := hc _ _ _ hstep
    obtain ⟨vs, rfl, hvs⟩ := ih
    exact ⟨v :: vs, rfl, Chain.cons ⟨hT, hn.symm⟩ hvs⟩

end chains

theorem root_accepts (n : ℕ) (z z' : Root.Z) :
    (∃ ws, ws.length = n ∧ Chain (Root.Spec Zkp.hashes) z ws z') ↔
      ∃ vs : List (root.RootCircuit.synthesize_step.StepWit poseidon.hash_var), vs.length = n ∧
        CircuitChain root.RootCircuit.synthesize_step.Rel root.RootCircuit.synthesize_step.next z vs z' := by
  constructor
  · rintro ⟨ws, rfl, hc⟩
    obtain ⟨vs, rfl, hvs⟩ := circuit_of_chain
      (fun z w z' hs => root.RootCircuit.synthesize_step.complete_poseidon Zkp.hashes rfl rfl hs) hc
    exact ⟨vs, by simp, hvs⟩
  · rintro ⟨vs, hn, hvs⟩
    refine ⟨_, ?_, chain_of_circuit (S := Root.Spec Zkp.hashes)
      (proj := root.RootCircuit.synthesize_step.StepWit.spec)
      (fun z v hR => root.RootCircuit.synthesize_step.sound_poseidon Zkp.hashes rfl rfl hR) hvs⟩
    simpa using hn

theorem merge_accepts (n : ℕ) (z z' : Merge.Z) :
    (∃ ws, ws.length = n ∧ Chain (Merge.Spec Zkp.hashes) z ws z') ↔
      ∃ vs : List (merge.MergeCircuit.synthesize_step.StepWit poseidon.hash_var), vs.length = n ∧
        CircuitChain merge.MergeCircuit.synthesize_step.Rel merge.MergeCircuit.synthesize_step.next z vs
          z' := by
  constructor
  · rintro ⟨ws, rfl, hc⟩
    obtain ⟨vs, rfl, hvs⟩ := circuit_of_chain
      (fun z w z' hs => merge.MergeCircuit.synthesize_step.complete_poseidon Zkp.hashes rfl rfl rfl hs) hc
    exact ⟨vs, by simp, hvs⟩
  · rintro ⟨vs, hn, hvs⟩
    refine ⟨_, ?_, chain_of_circuit (S := Merge.Spec Zkp.hashes)
      (proj := merge.MergeCircuit.synthesize_step.StepWit.spec)
      (fun z v hR => merge.MergeCircuit.synthesize_step.sound_poseidon Zkp.hashes rfl rfl rfl hR) hvs⟩
    simpa using hn

/-! ## The empty tree -/

/-- `Protocol.EMPTY_ROOT`. -/
def EMPTY_ROOT : F := 21443572485391568159800782191812935835534334817699172242223315142338162256601

/-- The empty subtree's root at each height, over ℕ. -/
def zeroN : ℕ → ℕ
  | 0 => 0
  | k + 1 => (Poseidon.Check.permN 3 PoseidonConstants.T3.partialRounds PoseidonConstants.T3.ark
      PoseidonConstants.T3.mds [0, zeroN k, zeroN k]).getD 0 0

theorem hash_pair (a b : ℕ) : Zkp.hashes.H [(a : F), (b : F)] =
    ((Poseidon.Check.permN 3 PoseidonConstants.T3.partialRounds PoseidonConstants.T3.ark
      PoseidonConstants.T3.mds [0, a, b]).getD 0 0 : ℕ) := by
  have hs : (Matrix.vecCons (0 : F) [(a : F), (b : F)].get : Fin 3 → F) = Poseidon.castVec [0, a, b] := by
    funext i; fin_cases i <;> rfl
  change Poseidon.perm 3 (Matrix.vecCons (0 : F) [(a : F), (b : F)].get) 0 = _
  rw [hs]
  show (Poseidon.ofLists PoseidonConstants.T3.partialRounds PoseidonConstants.T3.ark
    PoseidonConstants.T3.mds : Poseidon.Params 3).perm (Poseidon.castVec [0, a, b]) 0 = _
  rw [← Poseidon.Check.castVec_permN]
  simp only [Poseidon.castVec, Fin.val_zero]

theorem node_empty (k j : ℕ) : node Zkp.hashes [] k j = (zeroN k : F) := by
  induction k generalizing j with
  | zero => simp [node, zeroN]
  | succ k ih => rw [node, ih, ih, zeroN, hash_pair]

/-- The initial root, the ledger's empty tree, is the contract's `EMPTY_ROOT`. -/
theorem treeRoot_empty : treeRoot Zkp.hashes [] = EMPTY_ROOT := by
  have h : zeroN DEPTH =
      21443572485391568159800782191812935835534334817699172242223315142338162256601 := by
    decide +kernel
  rw [treeRoot, node_empty, h]
  rfl

/-! ## Nothing but Lean's own axioms

Every headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound`: no
`sorry`, no added axiom, and no `native_decide`. -/

/-- info: 'Zerc20.no_theft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_theft

/-- info: 'Zerc20.at_most_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms at_most_once

/-- info: 'Zerc20.conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conservation

/-- info: 'Zerc20.solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms solvent

/-- info: 'Zerc20.rageExit_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rageExit_now

/-- info: 'Zerc20.withdraw_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms withdraw_now

/-- info: 'Zerc20.OwnerHyp.nullifier_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwnerHyp.nullifier_kept

/-- info: 'Zerc20.exec_nonAdmin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exec_nonAdmin

/-- info: 'Zerc20.Run.feesOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Run.feesOK

/-- info: 'Zerc20.joinSplit_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms joinSplit_accepts

/-- info: 'Zerc20.rageExit_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rageExit_accepts

/-- info: 'Zerc20.root_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms root_accepts

/-- info: 'Zerc20.merge_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms merge_accepts

/-- info: 'Zerc20.treeRoot_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms treeRoot_empty

/-- info: 'Zerc20.Circomlib.PoseidonEx.opt_eq_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Circomlib.PoseidonEx.opt_eq_std

end Zerc20
