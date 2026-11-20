import Zerc20.Spec

/-!
# The commitment tree

A Merkle path to the root of a tree reaches it exactly along the tree's own nodes, so a path that
hashes to the root with no collision among the hashes involved opens the slot's real content.
Appending a leaf changes the tree only along that leaf's path.
-/

namespace Zerc20

variable (h : Hashes)

/-- Poseidon is injective on `S`. -/
def Injective (S : Set (List F)) : Prop := ∀ x ∈ S, ∀ y ∈ S, h.H x = h.H y → x = y

theorem pathRoot_succ (leaf : F) (idx : ℕ) (sib : Fin DEPTH → F) (k : ℕ) (hk : k < DEPTH) :
    pathRoot h leaf idx sib (k + 1) = h.H (pathPair h leaf idx sib ⟨k, hk⟩) := by
  simp only [pathRoot, hk, dite_true, pathPair]
  split_ifs <;> rfl

theorem node_succ (ls : List F) (k j : ℕ) :
    node h ls (k + 1) j = h.H [node h ls k (2 * j), node h ls k (2 * j + 1)] := rfl

theorem div_two_pow_succ (i k : ℕ) : i / 2 ^ (k + 1) = i / 2 ^ k / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- The canonical pair at level `k` above slot `i`, in path order. -/
theorem pathPair_canonical (ls : List F) (i : ℕ) (k : ℕ) (hk : k < DEPTH)
    (hpath : pathRoot h (node h ls 0 i) i (siblings h ls i) k = node h ls k (i / 2 ^ k)) :
    pathPair h (node h ls 0 i) i (siblings h ls i) ⟨k, hk⟩ =
      [node h ls k (2 * (i / 2 ^ (k + 1))), node h ls k (2 * (i / 2 ^ (k + 1)) + 1)] := by
  simp only [pathPair, siblings, sibIndex, hpath, div_two_pow_succ]
  set m := i / 2 ^ k
  split_ifs with hm
  · have : m - 1 = 2 * (m / 2) := by omega
    have h2 : m = 2 * (m / 2) + 1 := by omega
    rw [this, ← h2]
  · have : m + 1 = 2 * (m / 2) + 1 := by omega
    have h2 : m = 2 * (m / 2) := by omega
    rw [this, ← h2]

/-- A slot's own path climbs the tree's nodes. -/
theorem path_canonical (ls : List F) (i : ℕ) :
    ∀ k ≤ DEPTH, pathRoot h (node h ls 0 i) i (siblings h ls i) k = node h ls k (i / 2 ^ k)
  | 0, _ => by simp [pathRoot]
  | k + 1, hk => by
    have hk' : k < DEPTH := by omega
    rw [pathRoot_succ h _ _ _ k hk', pathPair_canonical h ls i k hk' (path_canonical ls i k hk'.le),
      div_two_pow_succ, ← node_succ]

theorem merkleRoot_canonical (ls : List F) (i : ℕ) (hi : i < 2 ^ DEPTH) :
    merkleRoot h (node h ls 0 i) i (siblings h ls i) = treeRoot h ls := by
  rw [merkleRoot, path_canonical h ls i DEPTH le_rfl, Nat.div_eq_of_lt hi, treeRoot]

/-- A path that reaches the root of `ls`, with Poseidon injective on the tree's and the path's
hashes, runs along the tree's nodes: its leaf is the slot's content and its siblings the tree's. -/
theorem binding (ls : List F) (leaf : F) (i : ℕ) (sib : Fin DEPTH → F) (hi : i < 2 ^ DEPTH)
    (hinj : Injective h (treeCalls h ls ∪ pathCalls h leaf i sib))
    (hroot : merkleRoot h leaf i sib = treeRoot h ls) :
    leaf = node h ls 0 i ∧ sib = siblings h ls i := by
  -- Downward: the path value at height `DEPTH - d` is the tree's node there.
  have down : ∀ d ≤ DEPTH, pathRoot h leaf i sib (DEPTH - d) = node h ls (DEPTH - d) (i / 2 ^ (DEPTH - d))
      ∧ ∀ k : Fin DEPTH, DEPTH - d ≤ k.val → sib k = siblings h ls i k := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨?_, fun k hk => absurd k.isLt (by omega)⟩
      simpa [Nat.div_eq_of_lt hi] using hroot
    | succ d ih =>
      intro hd
      obtain ⟨hp, hs⟩ := ih (by omega)
      set k := DEPTH - (d + 1) with hk
      have hk' : k < DEPTH := by omega
      have hk1 : DEPTH - d = k + 1 := by omega
      rw [hk1, pathRoot_succ h _ _ _ k hk', div_two_pow_succ, node_succ] at hp
      set m := i / 2 ^ k
      have hpair := hinj _ (Or.inr ⟨⟨k, hk'⟩, rfl⟩) _ (Or.inl ⟨k, hk', m / 2, rfl⟩) hp
      simp only [pathPair] at hpair
      have hsib : sib ⟨k, hk'⟩ = siblings h ls i ⟨k, hk'⟩ := by
        simp only [siblings, sibIndex]
        split_ifs at hpair ⊢ with hm
        · have : m - 1 = 2 * (m / 2) := by omega
          rw [this]; exact (List.cons.inj hpair).1
        · have : m + 1 = 2 * (m / 2) + 1 := by omega
          rw [this]; simp at hpair; exact hpair.2
      have hpk : pathRoot h leaf i sib k = node h ls k m := by
        split_ifs at hpair with hm
        · have h2 : m = 2 * (m / 2) + 1 := by omega
          rw [h2]; simp at hpair; exact hpair.2
        · have h2 : m = 2 * (m / 2) := by omega
          rw [h2]; exact (List.cons.inj hpair).1
      refine ⟨hpk, fun k' hk'' => ?_⟩
      rcases Nat.lt_or_ge k'.val (k + 1) with hlt | hge
      · have : k' = ⟨k, hk'⟩ := Fin.ext (by show k'.val = k; omega)
        rw [this]; exact hsib
      · exact hs k' (by omega)
  obtain ⟨h0, hs⟩ := down DEPTH le_rfl
  simp only [Nat.sub_self, pow_zero, Nat.div_one, pathRoot] at h0
  exact ⟨h0, funext fun k => hs k (by omega)⟩

/-! ## Appending a leaf -/

/-- A node depends only on the slots below it. -/
theorem node_congr (ls ls' : List F) :
    ∀ k j, (∀ m, j * 2 ^ k ≤ m → m < (j + 1) * 2 ^ k → ls.getD m 0 = ls'.getD m 0) →
      node h ls k j = node h ls' k j
  | 0, j, hs => by simpa [node] using hs j (by simp) (by simp)
  | k + 1, j, hs => by
    rw [node_succ, node_succ, node_congr ls ls' k (2 * j) fun m h1 h2 => hs m ?_ ?_,
      node_congr ls ls' k (2 * j + 1) fun m h1 h2 => hs m ?_ ?_]
    all_goals rw [pow_succ] at *; nlinarith

/-- Appending a leaf leaves the siblings of its slot unchanged. -/
theorem siblings_append (ls : List F) (x : F) :
    siblings h (ls ++ [x]) ls.length = siblings h ls ls.length := by
  funext k
  simp only [siblings]
  apply node_congr
  intro m h1 h2
  have hne : m ≠ ls.length := by
    intro hm
    subst hm
    have hpos : 0 < 2 ^ k.val := by positivity
    have hs := Nat.div_eq_of_lt_le h1 h2
    simp only [sibIndex] at hs
    split_ifs at hs <;> omega
  rcases Nat.lt_or_ge m ls.length with hm | hm
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hm,
      List.getElem?_eq_none (by omega : ls.length ≤ m),
      show m - ls.length ≠ 0 by omega]

/-- The root after appending `x`: the path of `x` with the old tree's siblings. -/
theorem treeRoot_append (ls : List F) (x : F) (hi : ls.length < 2 ^ DEPTH) :
    merkleRoot h x ls.length (siblings h ls ls.length) = treeRoot h (ls ++ [x]) := by
  rw [← siblings_append h ls x, ← merkleRoot_canonical h (ls ++ [x]) _ (by simpa using hi)]
  simp [node]

/-- The slot after the last leaf is empty. -/
theorem merkleRoot_empty (ls : List F) (hi : ls.length < 2 ^ DEPTH) :
    merkleRoot h 0 ls.length (siblings h ls ls.length) = treeRoot h ls := by
  rw [← merkleRoot_canonical h ls _ hi]
  simp [node]

end Zerc20
