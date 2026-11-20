import Zerc20.Main
import Sonobe.Deployment

/-!
# The Nova deciders

The root and the merge chains are proved with Nova, and a decider contract checks each proof on
chain. sonobe proves, down to its circuits' constraints, what an accepted call to such a decider
means: `Sonobe.Deployment.evm_decider_sound_deployed` gives a chain of the step circuit's
constraints from the call's initial state to its final one, from the witnesses extracted from the
run. Here the step circuit is zERC20's root or merge step, and `root_accepts` and `merge_accepts`
turn that chain into the chain of the spec that `CommitmentLedger.proveRootTransition` and
`Verifier.merge` check.

The IVC carries a state as a vector of field elements, in the order of the step circuit's
`StateVar`, which is also the order the decider's calldata lists `z₀` and `zᵢ` in.
-/

namespace Zerc20

open Zkp

/-- An IVC step circuit of zERC20: the state vector the IVC carries, the step circuit's constraints
on it, and the spec those constraints state. -/
structure IvcStep where
  /-- The length of the state vector. -/
  sN : ℕ
  /-- The spec's state. -/
  Z : Type
  /-- The spec's step witness. -/
  W : Type
  /-- The step circuit's wires. -/
  V : Type
  spec : Z → W → Z → Prop
  ofVec : (Fin sN → F) → Z
  /-- The step circuit's constraints on state vectors. -/
  rel : (Fin sN → F) → V → (Fin sN → F) → Prop
  /-- A chain of the constraints is a chain of the spec, of the same length. -/
  sound : ∀ n z z', (∃ vs : List V, vs.length = n ∧ Sonobe.IVC.Chain rel z vs z') →
    ∃ ws : List W, ws.length = n ∧ Chain spec (ofVec z) ws (ofVec z')

section chains

variable {sN : ℕ} {Z V : Type} {T : Z → V → Prop} {next : Z → V → Z}

/-- A chain of the step circuit's constraints on state vectors is one on the states they encode. -/
theorem circuitChain_of_ivc (ofVec : (Fin sN → F) → Z) (vec : Z → Fin sN → F)
    (h : ∀ z, ofVec (vec z) = z) {z : Fin sN → F} {vs : List V} {z' : Fin sN → F}
    (hc : Sonobe.IVC.Chain (fun z v z' => T (ofVec z) v ∧ z' = vec (next (ofVec z) v)) z vs z') :
    CircuitChain T next (ofVec z) vs (ofVec z') := by
  induction hc with
  | nil z => exact Chain.nil _
  | cons hstep _ ih =>
    obtain ⟨hT, rfl⟩ := hstep
    rw [h] at ih
    exact Chain.cons ⟨hT, rfl⟩ ih

end chains

namespace Root

/-- `[index, hash_chain, root]`. -/
def Z.vec (z : Z) : Fin 3 → F := ![z.index, z.chain, z.root]

def Z.ofVec (v : Fin 3 → F) : Z := ⟨v 0, v 1, v 2⟩

/-- The root step. -/
def ivc : IvcStep where
  sN := 3
  Z := Z
  W := Wit
  V := root.RootCircuit.synthesize_step.StepWit poseidon.hash_var
  spec := Spec Zkp.hashes
  ofVec := Z.ofVec
  rel z v z' := root.RootCircuit.synthesize_step.Rel (Z.ofVec z) v ∧
    z' = (root.RootCircuit.synthesize_step.next (Z.ofVec z) v).vec
  sound := by
    rintro n z z' ⟨vs, rfl, hc⟩
    exact (root_accepts _ _ _).mpr ⟨vs, rfl, circuitChain_of_ivc _ Z.vec (fun _ => rfl) hc⟩

end Root

namespace Merge

/-- `[token_id, chain_id, commitment_root, asp_root, nullifier_chain, signed_chain, note_hash,
remaining, fee, fee_recipient]`. -/
def Z.vec (z : Z) : Fin 10 → F :=
  ![z.token, z.chain, z.root, z.asp, z.nfChain, z.signedChain, z.noteHash, z.remaining, z.fee,
    z.feeRecipient]

def Z.ofVec (v : Fin 10 → F) : Z := ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9⟩

/-- The merge step. -/
def ivc : IvcStep where
  sN := 10
  Z := Z
  W := Wit
  V := merge.MergeCircuit.synthesize_step.StepWit poseidon.hash_var
  spec := Spec Zkp.hashes
  ofVec := Z.ofVec
  rel z v z' := merge.MergeCircuit.synthesize_step.Rel (Z.ofVec z) v ∧
    z' = (merge.MergeCircuit.synthesize_step.next (Z.ofVec z) v).vec
  sound := by
    rintro n z z' ⟨vs, rfl, hc⟩
    exact (merge_accepts _ _ _).mpr ⟨vs, rfl, circuitChain_of_ivc _ Z.vec (fun _ => rfl) hc⟩

end Merge

section decider

open Sonobe Sonobe.IVC Sonobe.Nova Sonobe.Gadget Sonobe.EVM
open Sonobe.Deployment (q bn254 grumpkin g1 g2 sponge dS dT rm1 emu)

/-- sonobe's copy of `r`, so that its instances on `ZMod` apply as they are. -/
local notation "rS" => Sonobe.Deployment.r

/-- sonobe builds the curve groups with classical equality on `ZMod`, so the points here have the
same group structure as in its statements. -/
noncomputable local instance decEqZModNova {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable [Module (ZMod rS) bn254.toAffine.Point] [Module (ZMod q) grumpkin.toAffine.Point]

/-- **An accepted call to a decider contract is a chain of the spec.** If the decider of `C`'s
Nova proofs accepts the call `cd`, and the run meets sonobe's hypotheses, then the spec takes the
call's initial state to its final one in `cd.i` steps. The hypotheses are those of
`Sonobe.Deployment.evm_decider_sound_deployed` with `C`'s step circuit: the deployed circuits'
synthesis, the curve groups' prime order, and the run's (the CP-SNARK's extractor outputs a valid
witness on the call; every fold's rewinding is accepting, breaks no binding and meets no state hash
collision). -/
theorem decider_sound (C : IvcStep)
    {PWd G₂ G_T : Type*} [AddCommGroup G₂] [Module (ZMod rS) G₂] [AddCommGroup G_T] [Module (ZMod rS) G_T]
    (T : Setup (ZMod rS) bn254.toAffine.Point (ZMod q) grumpkin.toAffine.Point (Fin C.sN → ZMod rS)
      (ZMod q × ZMod q) 7)
    (hco : T.coords = coordsOf bn254) (hhs : T.hs = hsC grumpkin sponge dS)
    (hch : T.ch1n = ch1nC sponge dT) (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (circA : Circuit (ZMod rS) 1 T.nw1 (AugVars rS C.sN))
    (hsatA : ∀ x w, T.k1.r1cs.Sat x w → circA.rel x (circA.decode w))
    (hrelA : ∀ x ω, circA.rel x ω → AugRel grumpkin emu sponge dS dT rm1 g2 C.rel ω (x 0))
    (circC : Circuit (ZMod q) 7 T.nw2 (CFWit (ZMod q))) (hcompC : circC.Compiles T.k2.r1cs)
    (hrelC : ∀ x ω, circC.rel x ω ↔ CFRel bn254 128 g1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) ω)
    (PEc PWc : PedConst rS) (pph : ZMod rS) (hpph : T.pph = pph)
    (hkE : T.k2.ckE = PedersenKey.mk (F := ZMod q) (fun i : Fin T.m2 => (PEc.g i).pt grumpkin)
      (PEc.h.pt grumpkin))
    (hkW : T.k2.ckW = PedersenKey.mk (F := ZMod q) (fun i : Fin T.nw2 => (PWc.g i).pt grumpkin)
      (PWc.h.pt grumpkin))
    (hgE : ∀ i < T.m2, (PEc.g i).OnCurve grumpkin.a₄ grumpkin.a₆)
    (hhE : PEc.h.OnCurve grumpkin.a₄ grumpkin.a₆)
    (hgW : ∀ i < T.nw2, (PWc.g i).OnCurve grumpkin.a₄ grumpkin.a₆)
    (hhW : PWc.h.OnCurve grumpkin.a₄ grumpkin.a₆)
    {mD nwD : ℕ}
    (circD : Circuit (ZMod rS) (2 * C.sN + 26) nwD (DecWit rS C.sN T.m1 T.nw1 T.m2 T.nw2))
    (RD : R1CS (ZMod rS) mD (2 * C.sN + 26) nwD)
    (hsatD : ∀ x w, RD.Sat x w → circD.rel x (circD.decode w))
    (hrelD : ∀ (p : DecPub rS C.sN) ω, circD.rel (vecOfList p.toList (2 * C.sN + 26)) ω →
      DecRel grumpkin T.k1.r1cs T.k2.r1cs sponge dS dT rm1 g2 PEc PWc pph ω p)
    (e : bn254.toAffine.Point →ₗ[ZMod rS] G₂ →ₗ[ZMod rS] G_T)
    (vk : LegoGroth16.VK bn254.toAffine.Point G₂ (2 * C.sN + 26) 2)
    (decodeProof : PWd → Option (LegoGroth16.Proof bn254.toAffine.Point G₂))
    (hord1 : ∀ P : bn254.toAffine.Point, P ≠ 0 → addOrderOf P = rS)
    (hord2 : ∀ P : grumpkin.toAffine.Point, P ≠ 0 → addOrderOf P = q)
    (cd : Calldata C.sN PWd) (hacc : DeciderAccepts bn254 e vk decodeProof cd)
    (wD : Fin nwD → ZMod rS) (o : Fin 2 → ZMod rS)
    (hcp : ∀ cG π, (∀ j, decodeG1 bn254 (![ceOf bn254 cd, cwOf bn254 cd] j) = some (cG j)) →
      decodeProof cd.proof = some π →
      LegoGroth16.ExtractsAt e vk RD (fun w => ((circD.decode w).we, (circD.decode w).ww))
        T.k1.ckE T.k1.ckW (xOf bn254 cd (2 * C.sN + 26)) cG π wD o)
    (E : T.Extraction)
    (hE : T.ExtractionOK (fun w => augOutOf grumpkin (circA.decode w)) cd.i
      (fun k => (cd.z0 k : ZMod rS)) (fun k => (cd.zi k : ZMod rS))
      (decOutOf bn254 grumpkin T cd (circD.decode wD) o) E) :
    ∃ ws : List C.W, ws.length = cd.i ∧
      Zerc20.Chain C.spec (C.ofVec fun k => (cd.z0 k : ZMod rS)) ws
        (C.ofVec fun k => (cd.zi k : ZMod rS)) :=
  C.sound _ _ _ (Sonobe.Deployment.evm_decider_sound_deployed C.rel T hco hhs hch hcfx circA hsatA
    hrelA circC hcompC hrelC PEc PWc pph hpph hkE hkW hgE hhE hgW hhW circD RD hsatD hrelD e vk
    decodeProof hord1 hord2 cd hacc wD o hcp E hE)

end decider

/-- info: 'Zerc20.decider_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decider_sound

/-- info: 'Zerc20.Root.ivc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Root.ivc

/-- info: 'Zerc20.Merge.ivc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Merge.ivc

end Zerc20
