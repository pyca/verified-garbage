module

public import VerifiedGarbage.Spec.SlhDsa
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# SLH-DSA: the values the internal functions compute

Untrusted: the contracts of the functions only verified code calls are
stated in these terms (`Proof/SlhDsa/X86_64/Contracts.lean`), and the
proofs relate them to `Spec/SlhDsa.lean` (`Proof/SlhDsa/Lemmas.lean`).

A tree's address is its layer and tree addresses, the 16 bytes `a16`, the
rest zero (`treeAdrs`): every algorithm of the specification sets the other
fields before it uses them (`xmssNode_congr`). The nodes of a height of a
tree, from those of the height below, are `upNodes`: node `j` of height
`z + 1` is `H` of nodes `2j` and `2j + 1` of height `z`, with the address of
the type `ty` (`TREE` or `FORS_TREE`), the key pair `kp`, the height `z + 1`
and the tree index `⌊base / 2^(z+1)⌋ + j`, for the index `base` of the first
leaf below them in the sequence of leaves the specification numbers them by.
-/

@[expose] public section

namespace VG.Proof.SlhDsa

open VG.Spec.SlhDsa

variable (p : Params)

/-- A tree's address: its layer and tree addresses `a16`, the rest zero. -/
def treeAdrs (a16 : List Byte) : Adrs := a16 ++ toByte 0 16

/-- The layer and tree addresses of layer `l` and tree `t`
(`setTreeAddress(setLayerAddress(ADRS, l), t)`). -/
def layerTree (l t : Nat) : List Byte := toByte l 4 ++ toByte t 12

/-- The address of the WOTS⁺ key pair `kp` of the tree `a16`. -/
def wotsAdrs (a16 : List Byte) (kp : Nat) : Adrs :=
  setKeyPairAddress (setTypeAndClear (treeAdrs a16) WOTS_HASH) kp

/-- Chain `i` of the WOTS⁺ key pair `kp` of the tree `a16`, after `d` steps:
`chain(sk_i, 0, d)` for its private key value `sk_i` (Algorithms 6 and 7). -/
def wotsChainAt (skSeed pkSeed a16 : List Byte) (kp i d : Nat) : List Byte :=
  chain p (prf p pkSeed skSeed (setChainAddress (wotsSkAdrs (wotsAdrs a16 kp)) i)) 0 d pkSeed
    (setChainAddress (wotsAdrs a16 kp) i)

/-- The address of node `j` of height `z` of a tree `a16`, of the type `ty`
and the key pair `kp`. -/
def nodeAdrs (a16 : List Byte) (ty kp z j : Nat) : Adrs :=
  setTreeIndex (setTreeHeight (setKeyPairAddress (setTypeAndClear (treeAdrs a16) ty) kp) z) j

/-- The nodes of height `z + r` above the nodes `L` of height `z` (`r`
heights up), the first leaf below them `base`. -/
def upNodes (pkSeed a16 : List Byte) (ty kp base : Nat) : (z : Nat) → (L : List (List Byte)) → (r : Nat) →
    List (List Byte)
  | _, L, 0 => L
  | z, L, r + 1 =>
    upNodes pkSeed a16 ty kp base (z + 1)
      ((List.range (L.length / 2)).map fun j =>
        H p pkSeed (nodeAdrs a16 ty kp (z + 1) (base / 2 ^ (z + 1) + j)) (L.getD (2 * j) [] ++ L.getD (2 * j + 1) []))
      r

/-- The node of an authentication path at height `z`, if it is among the
nodes `L` of height `z` whose first one has the index `first` in its tree:
the node `⌊idx / 2^z⌋ ⊕ 1`, or `n` zero bytes if it is not among them. -/
def pick (n : Nat) (L : List (List Byte)) (first idx z : Nat) : List Byte :=
  let sib := idx / 2 ^ z ^^^ 1
  if first ≤ sib ∧ sib < first + L.length then L.getD (sib - first) [] else toByte 0 n

/-- The bytewise XOR of two strings of the same length. -/
def xorB (a b : List Byte) : List Byte := List.zipWith (· ^^^ ·) a b

/-- The WOTS⁺ digits as the bytes `xmssTree` stores them. -/
def digitBytes (M : List Byte) : List Byte := (wotsDigits p M).map fun d => BitVec.ofNat 8 d

/-- The FORS address of the signing key pair `kp` of the tree `a16`, as
`slh_sign_internal` sets it (Algorithm 19, lines 11–13). -/
def forsAdrs (a16 : List Byte) (kp : Nat) : Adrs :=
  setKeyPairAddress (setTypeAndClear (treeAdrs a16) FORS_TREE) kp

end VG.Proof.SlhDsa
