module

public import VerifiedGarbage.Proof.SlhDsa.Internal
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCTBase
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsV
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the specification as the code computes it

Untrusted: everything here is checked by Lean. The six SHAKE parameter sets
(`S6`) and the facts of them the proofs use (`VPar`); the hypertree's
verification as a loop over its `d` layers from layer 0, each layer's tree
address and leaf index those of the layer below shifted (`htFold`,
`htVerify_eq`); the addresses of the layers in the lanes' terms
(`treeAdrs (layerTree j t)`); the indices of `splitDigest` as the
big-endian words the code reads (`os2ip_take`); and `verifyInternal` in
these terms (`verifyInternal_eq`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.Spec.SlhDsa
open VG.Proof.SlhDsa (treeAdrs layerTree forsAdrs)

/-- The six SHAKE parameter sets. -/
def S6 (p : Params) : Prop :=
  p = shake_128s ∨ p = shake_128f ∨ p = shake_192s ∨ p = shake_192f ∨ p = shake_256s ∨ p = shake_256f

/-- What the proofs need of a parameter set. -/
structure VPar (p : Params) : Prop where
  n : p.n = 16 ∨ p.n = 24 ∨ p.n = 32
  fam : p.family = .shake
  w4 : p.lgw = 4
  p6 : ForsCT.P6 p
  fpar : FPar p
  hp1 : 0 < p.hp
  hp9 : p.hp ≤ 9
  d1 : 1 ≤ p.d
  d22 : p.d ≤ 22
  hd : p.h / p.d = p.hp
  tb : p.h - p.hp ≤ 64
  tb' : p.h - p.h / p.d = p.h - p.hp
  ti : p.treeIdxLen = (p.h - p.hp + 7) / 8
  ti8 : p.treeIdxLen ≤ 8
  ti7 : 7 ≤ p.treeIdxLen
  li : p.leafIdxLen = 1 ∨ p.leafIdxLen = 2
  li8 : p.hp ≤ 8 * p.leafIdxLen
  m : p.m = p.mdLen + p.treeIdxLen + p.leafIdxLen
  m64 : p.m ≤ 64
  rd : p.mdLen + p.treeIdxLen + 8 ≤ 64
  trd : 8 ≤ p.treeIdxLen + p.leafIdxLen
  len : p.len = 2 * p.n + 3
  sigLen : p.sigLen = p.n + p.forsSigLen + p.d * p.xmssSigLen
  sigLt : p.sigLen < 2 ^ 31
  xsl : p.xmssSigLen < 2 ^ 31
  fsl : p.n + p.forsSigLen < 2 ^ 31
  pk : p.pkLen = 2 * p.n
  hgt : p.hp < p.h
  fpos : 0 < p.forsSigLen
  xpos : 0 < p.xmssSigLen

theorem S6.par {p : Params} (h : S6 p) : VPar p := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, rfl, rfl, by unfold ForsCT.P6; decide, ⟨by decide, rfl, by decide, by decide, by decide, by decide,
      by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Addresses -/

theorem length_toByte (x n : Nat) : (toByte x n).length = n := by simp [toByte]

theorem adrsZero_eq : adrsZero = toByte 0 4 ++ toByte 0 12 ++ toByte 0 16 := by decide

/-- The address of layer 0's tree `t`. -/
theorem setTreeAddress_zero (t : Nat) : setTreeAddress adrsZero t = treeAdrs (layerTree 0 t) := by
  simp only [setTreeAddress, setBytes, adrsZero_eq, treeAdrs, layerTree, length_toByte, List.append_assoc]
  rw [List.take_append_of_le_length (by simp [length_toByte]), List.take_of_length_le (by simp [length_toByte]),
    show 4 + 12 = (toByte 0 4).length + (toByte 0 12).length by simp [length_toByte], List.drop_length_add_append,
    List.drop_left]

/-- The address of layer `j`'s tree `t`, from any tree's. -/
theorem setTreeAddress_layer (j₀ t₀ j t : Nat) :
    setTreeAddress (setLayerAddress (treeAdrs (layerTree j₀ t₀)) j) t = treeAdrs (layerTree j t) := by
  simp only [setTreeAddress, setLayerAddress, setBytes, treeAdrs, layerTree, length_toByte, List.append_assoc,
    List.take_zero, List.nil_append, Nat.zero_add]
  rw [List.drop_left' (length_toByte _ _)]
  rw [List.take_append_of_le_length (by simp [length_toByte]), List.take_of_length_le (by simp [length_toByte]),
    show 4 + 12 = (toByte j 4).length + (toByte t₀ 12).length by simp [length_toByte], List.drop_length_add_append,
    List.drop_left]

/-! ## The hypertree, layer by layer -/

variable (p : Params)

/-- Layer `j` of the hypertree as the code runs it, from its message (the
root below), tree address and leaf index: the root its XMSS signature
gives, and the next layer's tree address and leaf index. -/
def htStep (sigHt pkSeed : List Byte) (st : List Byte × Nat × Nat) (j : Nat) : List Byte × Nat × Nat :=
  (xmssPkFromSig p st.2.2 (chunk sigHt p.xmssSigLen j) st.1 pkSeed (treeAdrs (layerTree j st.2.1)),
    st.2.1 >>> p.hp, st.2.1 % 2 ^ p.hp)

/-- The first `k` layers. -/
def htFold (M sigHt pkSeed : List Byte) (idxTree idxLeaf k : Nat) : List Byte × Nat × Nat :=
  (List.range k).foldl (htStep p sigHt pkSeed) (M, idxTree, idxLeaf)

theorem htFold_succ (M sigHt pkSeed : List Byte) (idxTree idxLeaf k : Nat) :
    htFold p M sigHt pkSeed idxTree idxLeaf (k + 1) = htStep p sigHt pkSeed (htFold p M sigHt pkSeed idxTree idxLeaf k) k := by
  simp only [htFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem htFold_zero (M sigHt pkSeed : List Byte) (idxTree idxLeaf : Nat) :
    htFold p M sigHt pkSeed idxTree idxLeaf 0 = (M, idxTree, idxLeaf) := rfl

/-- The specification's layers `1` to `d - 1`, from the state after layer 0. -/
theorem ht_rest (sigHt pkSeed : List Byte) : ∀ (l : List Nat) (node : List Byte) (T : Nat) (adrs : Adrs),
    (∃ j t, adrs = treeAdrs (layerTree j t)) →
    (l.foldl (fun (st : List Byte × Nat × Adrs) j' =>
      let (node, idxTree, adrs) := st
      let j := j' + 1
      let idxLeaf := idxTree % 2 ^ p.hp
      let idxTree := idxTree >>> p.hp
      let adrs := setTreeAddress (setLayerAddress adrs j) idxTree
      let sigTmp := chunk sigHt p.xmssSigLen j
      (xmssPkFromSig p idxLeaf sigTmp node pkSeed adrs, idxTree, adrs)) (node, T, adrs)).1 =
    (l.foldl (fun st j' => htStep p sigHt pkSeed st (1 + j')) (node, T >>> p.hp, T % 2 ^ p.hp)).1
  | [], _, _, _, _ => rfl
  | j' :: l, node, T, adrs, ⟨j₀, t₀, ha⟩ => by
    simp only [List.foldl_cons]
    subst ha
    rw [setTreeAddress_layer]
    have e := ht_rest sigHt pkSeed l
      (xmssPkFromSig p (T % 2 ^ p.hp) (chunk sigHt p.xmssSigLen (j' + 1)) node pkSeed
        (treeAdrs (layerTree (j' + 1) (T >>> p.hp)))) (T >>> p.hp) (treeAdrs (layerTree (j' + 1) (T >>> p.hp)))
      ⟨_, _, rfl⟩
    rw [e]
    simp only [htStep, Nat.add_comm 1 j']

theorem htVerify_eq (hd : 1 ≤ p.d) (M sigHt pkSeed : List Byte) (idxTree idxLeaf : Nat) (pkRoot : List Byte) :
    htVerify p M sigHt pkSeed idxTree idxLeaf pkRoot =
      ((htFold p M sigHt pkSeed idxTree idxLeaf p.d).1 == pkRoot) := by
  obtain ⟨d', hd'⟩ : ∃ d', p.d = 1 + d' := ⟨p.d - 1, by omega⟩
  simp only [htVerify, htFold, hd', Nat.add_sub_cancel_left, List.range_add, List.foldl_append, List.foldl_map]
  rw [setTreeAddress_zero]
  rw [ht_rest p sigHt pkSeed _ _ idxTree _ ⟨0, idxTree, rfl⟩]
  rfl

/-! ## The indices -/

theorem foldl_os (B : List Byte) : ∀ a : Nat, B.foldl (fun x b => 256 * x + b.toNat) a =
    a * 256 ^ B.length + B.foldl (fun x b => 256 * x + b.toNat) 0 := by
  induction B with
  | nil => intro a; simp
  | cons b B ih =>
    intro a
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (256 * a + b.toNat), ih (256 * 0 + b.toNat), Nat.pow_succ, Nat.mul_zero, Nat.zero_add, Nat.add_mul,
      Nat.mul_comm 256 a, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ B.length), Nat.add_assoc]

theorem os2ip_append (A B : List Byte) : Spec.Rsa.os2ip (A ++ B) = Spec.Rsa.os2ip A * 256 ^ B.length + Spec.Rsa.os2ip B := by
  simp only [Spec.Rsa.os2ip, List.foldl_append]
  exact foldl_os B _

theorem os2ip_lt : ∀ B : List Byte, Spec.Rsa.os2ip B < 256 ^ B.length
  | [] => by simp [Spec.Rsa.os2ip]
  | b :: B => by
    have e := os2ip_append [b] B
    simp only [List.cons_append, List.nil_append] at e
    rw [e, List.length_cons, Nat.pow_succ]
    have hb := b.isLt
    have ih := os2ip_lt B
    have h1 : Spec.Rsa.os2ip [b] = b.toNat := by simp [Spec.Rsa.os2ip]
    rw [h1]
    have : (b.toNat + 1) * 256 ^ B.length ≤ 256 * 256 ^ B.length := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- The first `L` bytes of `X`, big-endian: the big-endian `X` shifted right. -/
theorem os2ip_take (X : List Byte) (L : Nat) :
    Spec.Rsa.os2ip X / 256 ^ (X.length - L) = Spec.Rsa.os2ip (X.take L) := by
  have e := os2ip_append (X.take L) (X.drop L)
  rw [List.take_append_drop] at e
  rw [e, List.length_drop]
  have := os2ip_lt (X.drop L)
  rw [List.length_drop] at this
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt this, Nat.zero_add]

theorem toInt_eq (X : List Byte) (n : Nat) : toInt X n = Spec.Rsa.os2ip (X.take n) := rfl

/-! ## `verify_internal` -/

/-- `slh_verify_internal` for a signature of the right length, in the terms
of the code: the digest; FORS's public key from the digest's `md`; the
hypertree from it. -/
theorem verifyInternal_eq {p : Params} (hp : VPar p) (M sig pk : List Byte) (hl : sig.length = p.sigLen) :
    verifyInternal p M sig pk =
      let pkSeed := chunk pk p.n 0
      let pkRoot := chunk pk p.n 1
      let digest := Spec.Sha3.shake256 (sig.take p.n ++ pkSeed ++ pkRoot ++ M) p.m
      let sd := splitDigest p digest
      ((htFold p (forsPkFromSig p ((sig.drop p.n).take p.forsSigLen) sd.1 pkSeed (forsAdrs (layerTree 0 sd.2.1) sd.2.2))
        (sig.drop (p.n + p.forsSigLen)) pkSeed sd.2.1 sd.2.2 p.d).1 == pkRoot) := by
  simp only [verifyInternal, hl, ne_eq, not_true_eq_false, ite_false, hMsg, hp.fam]
  rw [htVerify_eq p hp.d1]
  rfl

end VG.Proof.SlhDsa.X86_64.VerifyTop
