import Zerc20.Eval

/-!
# The circuit test vectors

`lake test` runs this driver from `lean/`. It reads `zkp/test-vectors/circuit-vectors.json`, which
`gen_circuit_vectors.mjs` derives with circomlibjs from the circom circuits' conventions, and
evaluates the Lean spec on every vector. The spec runs on `Eval.fastHashes`, which
`Eval.fastHashes_eq` proves equal to `Zkp.hashes`, so a passing run shows that the spec itself, not
a copy of it, derives keys, nullifiers, notes, burns, leaves, tree nodes, hash chains, domain tags
and signatures as the circuits do, with circomlib's Poseidon constants.

Wallet derivations outside the spec are not checked: spend secrets come from SHA-256 with a counter
and auth secrets from SHA-512, outside every circuit, and the transact message has no Lean
counterpart.
-/

open Lean Zerc20 Zerc20.Eval

/-- A vector's checks, each named, with whether it holds. -/
abbrev Checks := Except String (List (String × Bool))

def natOf (s : String) : Except String ℕ :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"not a decimal number: {s}"

/-- Field `k` of `j`, a decimal string. -/
def nat (j : Json) (k : String) : Except String ℕ := do
  natOf (← j.getObjValAs? String k)

/-- Field `k` of `j`, an array of decimal strings. -/
def nats (j : Json) (k : String) : Except String (List ℕ) := do
  (← j.getObjValAs? (Array String) k).toList.mapM natOf

/-- Field `k` of `j`, a point's two coordinates. -/
def pair (j : Json) (k : String) : Except String (ℕ × ℕ) := do
  match ← nats j k with
  | [x, y] => pure (x, y)
  | _ => throw s!"{k}: not a pair"

/-- Whether a field element is the canonical value `n`. -/
def is (x : F) (n : ℕ) : Bool := x.val == n

/-- The checks of every vector in the array `rows`, each named with the vector's position. -/
def eachRow (rows : Except String Json) (f : Json → Checks) : Checks := do
  let rows ← (← rows).getArr?
  if rows.isEmpty then throw "no vectors"
  let checks ← rows.toList.mapIdxM fun i v => do
    return (← f v).map fun (name, ok) => (s!"[{i}] {name}", ok)
  return checks.flatten

/-! ## Baby-JubJub over `ℕ`

`BabyJubJub.smulN` runs double-and-add in projective coordinates, and `BabyJubJub.smulN_rep` proves
it represents the scalar multiple. -/

/-- `n • G`, for `n < 2^251`. -/
def smulG (n : ℕ) : ℕ × ℕ × ℕ := BabyJubJub.smulN 251 n BabyJubJub.Gp (0, 1, 1)

/-- Whether two projective points, both with `Z ≠ 0`, are the same point. -/
def same (p q : ℕ × ℕ × ℕ) : Bool :=
  p.1 * q.2.2 % r == q.1 * p.2.2 % r && p.2.1 * q.2.2 % r == q.2.1 * p.2.2 % r

/-- The point `(x, y)`, if it is on the curve. -/
def point (x y : ℕ) : Except String BabyJubJub.Point :=
  if h : (x : F) ^ 2 + (y : F) ^ 2 = 1 + BabyJubJub.d * (x : F) ^ 2 * (y : F) ^ 2 then
    pure ⟨x, y, h⟩
  else throw s!"({x}, {y}) is not on the curve"

/-! ## The vectors -/

namespace Check

/-- The spec's constants: the field, the bounds, and the leaf tags. -/
def constants (root : Json) : Checks := do
  let ranges ← root.getObjVal? "ranges"
  let bits (k : String) : Except String ℕ := ranges.getObjValAs? ℕ k
  let tags ← root.getObjVal? "field0_tags"
  return [
    ("modulus", r == (← nat (← root.getObjVal? "field") "modulus")),
    ("FIELD_BIT_LENGTH", r.log2 + 1 == (← bits "FIELD_BIT_LENGTH")),
    ("MERKLE_DEPTH", DEPTH == (← bits "MERKLE_DEPTH")),
    ("AMOUNT_BITS", AMOUNT_BOUND == 2 ^ (← bits "AMOUNT_BITS")),
    ("ADDRESS_BITS", ADDRESS_BOUND == 2 ^ (← bits "ADDRESS_BITS")),
    ("TOKEN_ID_BITS", TOKEN_BOUND == 2 ^ (← bits "TOKEN_ID_BITS")),
    ("CHAIN_ID_BITS", CHAIN_BOUND == 2 ^ (← bits "CHAIN_ID_BITS")),
    ("BURN_POW_BITS", POW_BOUND == 2 ^ ((← bits "FIELD_BIT_LENGTH") - (← bits "BURN_POW_BITS"))),
    ("FIELD0_TAG_SHIFT", field0 1 0 == 2 ^ (← nat tags "FIELD0_TAG_SHIFT")),
    ("TRANSFER_FIELD0_BASE", field0 TRANSFER_TAG 0 == (← nat tags "TRANSFER_FIELD0_BASE")),
    ("NOTE_FIELD0_BASE", field0 NOTE_HASH_TAG 0 == (← nat tags "NOTE_FIELD0_BASE"))]

/-- The spec's domain tags, under the names the vectors give them. -/
def specTags : List (String × F) :=
  [("NOTE", DOMAIN_NOTE), ("PUBLIC_KEY", DOMAIN_PUBLIC_KEY),
    ("NULLIFYING_KEY", DOMAIN_NULLIFYING_KEY), ("NULLIFIER", DOMAIN_NULLIFIER),
    ("DUMMY_NULLIFIER", DOMAIN_DUMMY_NULLIFIER), ("BURN", DOMAIN_BURN), ("ASP_LEAF", DOMAIN_ASP_LEAF),
    ("AUTH_KEY", DOMAIN_AUTH_KEY), ("MERGE_AUTH", DOMAIN_MERGE_AUTH),
    ("SPEND_AUTH", Zkp.auth.DOMAIN_SPEND_AUTH)]

/-- Every tag is `sha256(label) mod r` of its UTF-8 label, and each of the spec's tags is the one the
vectors give. -/
def domainTags (root : Json) : Checks := do
  let tags ← root.getObjVal? "domain_tags"
  let labels ← (← (← root.getObjVal? "domain_tag_provenance").getObjVal? "labels").getObj?
  let derived ← labels.toList.mapM fun (name, label) => do
    let label ← label.getStr?
    let digest := Sha256.ofBytesBE (Sha256.hash label.toUTF8.toList)
    return (s!"{name} = sha256(\"{label}\") mod r", digest % r == (← nat tags name))
  let spec ← specTags.mapM fun (name, tag) => do
    return (s!"DOMAIN_{name}", is tag (← nat tags name))
  return derived ++ spec

def keys (v : Json) : Checks := do
  let (x, y) ← pair v "auth_key"
  let akh ← nat v "auth_key_hash"
  let nk ← nat v "nullifying_key"
  return [
    ("nullifying_key", is (nullifyingKey fastHashes (← nat v "private_key")) nk),
    ("auth_key", same (smulG (← nat v "auth_secret")) (x, y, 1)),
    ("auth_key_hash", is (authKeyHash fastHashes (x, y)) akh),
    ("public_key", is (publicKey fastHashes akh nk) (← nat v "public_key"))]

/-- Only the nullifying key: the spend secret and its auth key derive outside the spec. -/
def spendSecrets (v : Json) : Checks := do
  return [("nullifying_key",
    is (nullifyingKey fastHashes (← nat v "spend_secret")) (← nat v "nullifying_key"))]

def noteHashes (v : Json) : Checks := do
  return [("note_hash",
    is (noteHash fastHashes (← nat v "chain_id") (← nat v "public_key") (← nat v "value")
      (← nat v "token_id") (← nat v "note_salt")) (← nat v "note_hash"))]

def nullifiers (v : Json) : Checks := do
  return [("nullifier",
    is (nullifier fastHashes (← nat v "chain_id") (← nat v "commitment_index")
      (← nat v "nullifying_key")) (← nat v "nullifier"))]

/-- `dummyNullifier` is the one JoinSplit's slot 1 publishes, which adds 1 to the entropy; slot `i`
adds `i`, so its nullifier is `dummyNullifier` of `entropy + i - 1`. -/
def dummyNullifiers (v : Json) : Checks := do
  let e ← nat v "entropy"
  let i ← nat v "dummy_index"
  return [
    ("indexed_entropy", is (e + i : F) (← nat v "indexed_entropy")),
    ("dummy_nullifier",
      is (dummyNullifier fastHashes (← nat v "chain_id") (e + i - 1 : F)) (← nat v "dummy_nullifier"))]

def burns (v : Json) : Checks := do
  let d := burnDigest fastHashes (← nat v "chain_id") (← nat v "public_key") (← nat v "burn_salt")
  return [
    ("burn_digest", is d (← nat v "burn_digest")),
    ("burn_address", addressOf d == (← nat v "burn_address")),
    ("burn_pow_ok", decide (d.val < POW_BOUND) == (← v.getObjValAs? Bool "burn_pow_ok"))]

def noteLeaves (v : Json) : Checks := do
  let t ← nat v "token_id"
  return [
    ("field0", field0 NOTE_HASH_TAG t == (← nat v "field0")),
    ("note_leaf", is ((Leaf.note t (← nat v "note_hash")).hash fastHashes) (← nat v "note_leaf"))]

def transferLeaves (v : Json) : Checks := do
  let t ← nat v "token_id"
  let leaf := Leaf.transfer t (← nat v "from") (← nat v "to") (← nat v "value")
  return [
    ("field0", field0 TRANSFER_TAG t == (← nat v "field0")),
    ("transfer_leaf", is (leaf.hash fastHashes) (← nat v "transfer_leaf"))]

/-- A node hashes its children left to right, so a one-level path from either child reaches it. -/
def merkleNodes (v : Json) : Checks := do
  let a ← nat v "left"
  let b ← nat v "right"
  let node ← nat v "hash"
  return [
    ("from the left child", is (pathRoot fastHashes a 0 (fun _ => b) 1) node),
    ("from the right child", is (pathRoot fastHashes b 1 (fun _ => a) 1) node)]

def aspLeaves (v : Json) : Checks := do
  return [("leaf", is (aspLeaf fastHashes (← nat v "commitment_index")) (← nat v "leaf"))]

/-- A burn deposit's transfer pays the burn address, and a small ASP tree approves the deposit's
index and another one: `pathRoot` at the tree's depth is its root. -/
def burnIntake (v : Json) : Checks := do
  let depth ← v.getObjValAs? ℕ "tree_depth"
  let sibs ← nats v "asp_siblings"
  let sib : Fin DEPTH → F := fun k => (sibs.getD k 0 : F)
  let approval (idx leaf root : String) : Checks := do
    let i ← nat v idx
    return [
      (leaf, is (aspLeaf fastHashes i) (← nat v leaf)),
      (root, is (pathRoot fastHashes (aspLeaf fastHashes i) i sib depth) (← nat v root))]
  let address ← nat v "burn_address"
  let transfer := Leaf.transfer (← nat v "token_id") (← nat v "transfer_from") address
    (← nat v "transfer_value")
  return [
      ("tree_depth", sibs.length == depth),
      ("burn_address", addressOf (burnDigest fastHashes (← nat v "chain_id")
        (← nat v "burn_public_key") (← nat v "burn_salt")) == address),
      ("transfer_leaf", is (transfer.hash fastHashes) (← nat v "transfer_leaf"))] ++
    (← approval "commitment_index" "deposit_asp_leaf" "deposit_asp_root") ++
    (← approval "other_commitment_index" "other_deposit_asp_leaf" "other_deposit_asp_root")

def hashChains (v : Json) : Checks := do
  return [("hash_chain",
    fastHashes.hc (← nat v "prev") (← nats v "values") == (← nat v "hash_chain"))]

/-- `Eval.treeRoot_nil` proves `emptyNode DEPTH` is the spec's empty tree. -/
def emptyTree (v : Json) : Checks := do
  return [
    ("depth", DEPTH == (← v.getObjValAs? ℕ "depth")),
    ("root", is (emptyNode DEPTH) (← nat v "root"))]

def mergeMessages (v : Json) : Checks := do
  return [("message",
    is (mergeMessage fastHashes (← nat v "nullifier_chain") (← nat v "out_public_key")
      (← nat v "out_salt") (← nat v "fee") (← nat v "fee_recipient")) (← nat v "message"))]

/-- `verify_var`'s check: `s < 2^251` and `s·G = c·A + R`, with `c` the spec's `challenge` under the
signer's auth key `A`, which the vectors' `keys` give. -/
def signatures (keys : Array Json) (v : Json) : Checks := do
  let sk ← v.getObjValAs? String "private_key"
  let some key := keys.find? fun k => (k.getObjValAs? String "private_key").toOption == some sk
    | throw s!"no key {sk}"
  let (ax, ay) ← pair key "auth_key"
  let (rx, ry) ← pair v "r"
  let s ← nat v "s"
  let c := Zkp.auth.challenge fastHashes.H (← point rx ry) (authKeyHash fastHashes (ax, ay))
    (← nat v "message")
  let cA := BabyJubJub.smulN 254 c (ax, ay, 1) (0, 1, 1)
  return [
    ("s < 2^251", s < 2 ^ 251),
    ("s·G = c·A + R", same (smulG s) (BabyJubJub.paddN cA (rx, ry, 1)))]

end Check

def main : IO UInt32 := do
  let root ← IO.ofExcept <| Json.parse
    (← IO.FS.readFile "../zkp/test-vectors/circuit-vectors.json")
  let vec (k : String) : Except String Json := do (← root.getObjVal? "vectors").getObjVal? k
  let groups : List (String × Checks) := [
    ("constants", Check.constants root),
    ("domain_tags", Check.domainTags root),
    ("keys", eachRow (vec "keys") Check.keys),
    ("spend_secrets", eachRow (vec "spend_secrets") Check.spendSecrets),
    ("note_hashes", eachRow (vec "note_hashes") Check.noteHashes),
    ("nullifiers", eachRow (vec "nullifiers") Check.nullifiers),
    ("dummy_nullifiers", eachRow (vec "dummy_nullifiers") Check.dummyNullifiers),
    ("burns", eachRow (vec "burns") Check.burns),
    ("note_leaves", eachRow (vec "note_leaves") Check.noteLeaves),
    ("transfer_leaves", eachRow (vec "transfer_leaves") Check.transferLeaves),
    ("merkle_nodes", eachRow (vec "merkle_nodes") Check.merkleNodes),
    ("asp_leaves", eachRow (vec "asp_leaves") Check.aspLeaves),
    ("burn_intake_bindings", eachRow (vec "burn_intake_bindings") Check.burnIntake),
    ("hash_chains", eachRow (vec "hash_chains") Check.hashChains),
    ("empty_tree", do Check.emptyTree (← vec "empty_tree")),
    ("auth_messages.merge",
      eachRow (do (← vec "auth_messages").getObjVal? "merge") Check.mergeMessages),
    ("signatures", do eachRow (vec "signatures") (Check.signatures (← (← vec "keys").getArr?)))]
  let mut failures := 0
  for (group, checks) in groups do
    match checks with
    | .error e =>
      IO.eprintln s!"FAIL {group}: {e}"
      failures := failures + 1
    | .ok checks =>
      let failed := checks.filter (!·.2)
      for (name, _) in failed do
        IO.eprintln s!"FAIL {group} {name}"
      failures := failures + failed.length
      IO.println s!"{group}: {checks.length - failed.length}/{checks.length}"
  return if failures = 0 then 0 else 1
