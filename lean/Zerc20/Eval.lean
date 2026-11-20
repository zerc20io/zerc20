import Zerc20.Steps

/-!
# Evaluating the spec

`Poseidon.hash` keeps the permutation's state as a function, which compiled code cannot evaluate
quickly. `fastH` runs the same permutation on a list of naturals mod `r`, and `fastHashes` is
`Zkp.hashes` with `fastH` as its Poseidon. `fastHashes_eq` proves the two equal, so a spec function
evaluated on `fastHashes` is that spec function on the deployed hashes.
-/

namespace Zerc20.Eval

open Poseidon.Check PoseidonConstants

/-- `Poseidon.hash` of `xs` over `ℕ`: lane 0 of `permN` of `[0, x₁, …, xₙ]` with circomlib's
constants for `t = n + 1`. Lengths without constants have no rounds, so lane 0 stays 0. -/
def fastH (xs : List ℕ) : ℕ :=
  match xs.length with
  | 2 => (permN 3 T3.partialRounds T3.ark T3.mds (0 :: xs)).getD 0 0
  | 3 => (permN 4 T4.partialRounds T4.ark T4.mds (0 :: xs)).getD 0 0
  | 4 => (permN 5 T5.partialRounds T5.ark T5.mds (0 :: xs)).getD 0 0
  | 5 => (permN 6 T6.partialRounds T6.ark T6.mds (0 :: xs)).getD 0 0
  | 6 => (permN 7 T7.partialRounds T7.ark T7.mds (0 :: xs)).getD 0 0
  | _ => 0

theorem hash_map_cast (xs : List ℕ) :
    Poseidon.hash (xs.map (↑)) = Poseidon.perm (xs.length + 1) (Poseidon.castVec (0 :: xs)) 0 := by
  rw [Poseidon.hash_eq (xs.map (↑)) (fun i : Fin xs.length => (xs.get i : F)) (by simp)
    (by simp)]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Poseidon.castVec]

theorem lane0_permN {t : ℕ} [NeZero t] (RP : ℕ) (ark : List ℕ) (mds : List (List ℕ))
    (s : List ℕ) :
    ((permN t RP ark mds s).getD 0 0 : F) =
      (Poseidon.ofLists RP ark mds : Poseidon.Params t).perm (Poseidon.castVec s) 0 := by
  rw [← castVec_permN]
  simp [Poseidon.castVec]

theorem fastH_eq (xs : List ℕ) : (fastH xs : F) = Poseidon.hash (xs.map (↑)) := by
  rw [hash_map_cast, fastH]
  generalize xs.length = n
  match n with
  | 0 | 1 => rfl
  | 2 => exact lane0_permN _ _ _ _
  | 3 => exact lane0_permN _ _ _ _
  | 4 => exact lane0_permN _ _ _ _
  | 5 => exact lane0_permN _ _ _ _
  | 6 => exact lane0_permN _ _ _ _
  | _ + 7 => rfl

/-- `Zkp.hashes` with its Poseidon evaluated by `fastH`. -/
def fastHashes : Hashes := { Zkp.hashes with H := fun xs => (fastH (xs.map ZMod.val) : F) }

theorem fastHashes_eq : fastHashes = Zkp.hashes := by
  have hH : (fun xs : List F => (fastH (xs.map ZMod.val) : F)) = Zkp.hashes.H := by
    funext xs
    rw [fastH_eq, List.map_map]
    show _ = Poseidon.hash xs
    congr 1
    conv_rhs => rw [← List.map_id xs]
    exact List.map_congr_left fun x _ => ZMod.natCast_zmod_val x
  simp only [fastHashes, hH]

/-- A node of the empty tree at height `k`. Both its children are the same node, so each level
hashes once, where `node` would recurse into both. -/
def emptyNode : ℕ → F
  | 0 => 0
  | k + 1 => let z := emptyNode k; fastHashes.H [z, z]

theorem node_nil (k j : ℕ) : node fastHashes [] k j = emptyNode k := by
  induction k generalizing j with
  | zero => simp [node, emptyNode]
  | succ k ih => simp [node, emptyNode, ih]

theorem treeRoot_nil : treeRoot Zkp.hashes [] = emptyNode DEPTH := by
  rw [← fastHashes_eq]
  exact node_nil DEPTH 0

end Zerc20.Eval
