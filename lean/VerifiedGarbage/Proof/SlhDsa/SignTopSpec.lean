module

-- separate module: the spec of signing in loop form, which every target's proofs of `sign` read, apart from their code

public import VerifiedGarbage.Proof.SlhDsa.VerifyTopSpec
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE), `sign`: the specification as the code computes it

Untrusted: everything here is checked by Lean. The hypertree's signature
as a loop over its `d` layers from layer 0, each layer signing the root of
the one below with the tree of the layer's tree address and leaf index,
those of the layer below shifted (`hsFold`, `hsSig`, `htSign_eq`), the
root of each tree being what its signature gives
(`xmssPkFromSig_xmssSign`); `signInternal` in these terms
(`signInternal_eq`); and the indices of `splitDigest` as the shifts and
masks of the big-endian words the code reads (`idxTree_code`,
`idxLeaf_code`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.Spec.SlhDsa
open VG.Proof.SlhDsa (treeAdrs layerTree forsAdrs)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar setTreeAddress_zero setTreeAddress_layer os2ip_take toInt_eq)

variable (p : Params)

/-! ## The hypertree, layer by layer -/

/-- Layer `j` of the hypertree's signature as the code runs it, from its
message (the root below), tree address and leaf index: the root of its
tree, and the next layer's tree address and leaf index. -/
def hsStep (skSeed pkSeed : List Byte) (st : List Byte × Nat × Nat) (j : Nat) : List Byte × Nat × Nat :=
  (xmssNode p skSeed 0 p.hp pkSeed (treeAdrs (layerTree j st.2.1)), st.2.1 >>> p.hp, st.2.1 % 2 ^ p.hp)

/-- The first `k` layers. -/
def hsFold (M skSeed pkSeed : List Byte) (idxTree idxLeaf k : Nat) : List Byte × Nat × Nat :=
  (List.range k).foldl (hsStep p skSeed pkSeed) (M, idxTree, idxLeaf)

/-- The XMSS signature of layer `j`. -/
def hsSig (M skSeed pkSeed : List Byte) (idxTree idxLeaf j : Nat) : List Byte :=
  xmssSign p (hsFold p M skSeed pkSeed idxTree idxLeaf j).1 skSeed (hsFold p M skSeed pkSeed idxTree idxLeaf j).2.2
    pkSeed (treeAdrs (layerTree j (hsFold p M skSeed pkSeed idxTree idxLeaf j).2.1))

theorem hsFold_succ (M skSeed pkSeed : List Byte) (idxTree idxLeaf k : Nat) :
    hsFold p M skSeed pkSeed idxTree idxLeaf (k + 1) =
      hsStep p skSeed pkSeed (hsFold p M skSeed pkSeed idxTree idxLeaf k) k := by
  simp only [hsFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hsFold_zero (M skSeed pkSeed : List Byte) (idxTree idxLeaf : Nat) :
    hsFold p M skSeed pkSeed idxTree idxLeaf 0 = (M, idxTree, idxLeaf) := rfl

theorem hsFold_leaf {M skSeed pkSeed : List Byte} {idxTree idxLeaf : Nat} (h : idxLeaf < 2 ^ p.hp) :
    ∀ k, (hsFold p M skSeed pkSeed idxTree idxLeaf k).2.2 < 2 ^ p.hp
  | 0 => h
  | k + 1 => by rw [hsFold_succ]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem treeAdrs_length (j t : Nat) : (treeAdrs (layerTree j t)).length = 32 := by
  simp [treeAdrs, layerTree, toByte]

/-- The state of `htSign`'s loop after `m` of its `d - 1` steps. -/
theorem ht_inv (hn : p.n ≤ 32) (hhp : p.hp ≤ 32) {M skSeed pkSeed : List Byte} {T I : Nat} (hI : I < 2 ^ p.hp) :
    ∀ m, m ≤ p.d - 1 →
      let st := (List.range m).foldl
        (fun (st : List Byte × List Byte × Nat × Adrs) j' =>
          let (sigHt, root, idxTree, adrs) := st
          let j := j' + 1
          let idxLeaf := idxTree % 2 ^ p.hp
          let idxTree := idxTree >>> p.hp
          let adrs := setTreeAddress (setLayerAddress adrs j) idxTree
          let sigTmp := xmssSign p root skSeed idxLeaf pkSeed adrs
          let sigHt := sigHt ++ sigTmp
          let root := if j < p.d - 1 then xmssPkFromSig p idxLeaf sigTmp root pkSeed adrs else root
          (sigHt, root, idxTree, adrs))
        (xmssSign p M skSeed I pkSeed (setTreeAddress adrsZero T),
          xmssPkFromSig p I (xmssSign p M skSeed I pkSeed (setTreeAddress adrsZero T)) M pkSeed
            (setTreeAddress adrsZero T), T, setTreeAddress adrsZero T)
      st.1 = (List.range (m + 1)).flatMap (hsSig p M skSeed pkSeed T I) ∧
        st.2.2.1 = (hsFold p M skSeed pkSeed T I m).2.1 ∧
        st.2.2.2 = treeAdrs (layerTree m (hsFold p M skSeed pkSeed T I m).2.1) ∧
        (m < p.d - 1 → st.2.1 = (hsFold p M skSeed pkSeed T I (m + 1)).1)
  | 0, _ => by
    simp only [List.range_zero, List.foldl_nil, Nat.zero_add, List.range_one, List.flatMap_singleton]
    rw [setTreeAddress_zero]
    refine ⟨rfl, rfl, rfl, fun _ => ?_⟩
    rw [xmssPkFromSig_xmssSign hn M skSeed hI (Nat.lt_of_lt_of_le hI (Nat.pow_le_pow_right (by decide) hhp)) pkSeed
      (treeAdrs_length 0 T), hsFold_succ]
    rfl
  | m + 1, hm => by
    obtain ⟨h1, h2, h3, h4⟩ := ht_inv hn hhp hI m (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h1 h2 h3 h4 ⊢
    generalize (List.range m).foldl _ _ = st at h1 h2 h3 h4 ⊢
    obtain ⟨sigHt, root, idxTree, adrs⟩ := st
    simp only at h1 h2 h3 h4 ⊢
    have hr := h4 (by omega)
    subst h1 h2 h3 hr
    have hL : (hsFold p M skSeed pkSeed T I m).2.1 % 2 ^ p.hp = (hsFold p M skSeed pkSeed T I (m + 1)).2.2 := by
      rw [hsFold_succ]; rfl
    have hT : (hsFold p M skSeed pkSeed T I m).2.1 >>> p.hp = (hsFold p M skSeed pkSeed T I (m + 1)).2.1 := by
      rw [hsFold_succ]; rfl
    rw [hL, hT, setTreeAddress_layer]
    have hsig : xmssSign p (hsFold p M skSeed pkSeed T I (m + 1)).1 skSeed (hsFold p M skSeed pkSeed T I (m + 1)).2.2
        pkSeed (treeAdrs (layerTree (m + 1) (hsFold p M skSeed pkSeed T I (m + 1)).2.1)) =
        hsSig p M skSeed pkSeed T I (m + 1) := rfl
    rw [hsig]
    refine ⟨by simp only [List.flatMap_append, List.flatMap_singleton], rfl, rfl, fun hm' => ?_⟩
    rw [ite_eq_left hm', ← hsig, xmssPkFromSig_xmssSign hn _ skSeed (hsFold_leaf p hI _)
      (Nat.lt_of_lt_of_le (hsFold_leaf p hI _) (Nat.pow_le_pow_right (by decide) hhp)) pkSeed (treeAdrs_length _ _),
      hsFold_succ (k := m + 1)]
    rfl

/-- `ht_sign` (Algorithm 12) as the code runs it: the `d` signatures of
`hsSig`. -/
theorem htSign_eq (hn : p.n ≤ 32) (hhp : p.hp ≤ 32) (hd : 1 ≤ p.d) {M skSeed pkSeed : List Byte} {T I : Nat}
    (hI : I < 2 ^ p.hp) :
    htSign p M skSeed pkSeed T I = (List.range p.d).flatMap (hsSig p M skSeed pkSeed T I) := by
  have h := (ht_inv p hn hhp (M := M) (skSeed := skSeed) (pkSeed := pkSeed) (T := T) hI (p.d - 1) (Nat.le_refl _)).1
  rw [Nat.sub_add_cancel hd] at h
  rw [← h]
  dsimp only [htSign]

/-! ## `slh_sign_internal` -/

/-- The signature of `slh_sign_internal` in the terms of the code: `R`, the
digest, the FORS signature of its `md`, the hypertree's signatures from
FORS's public key. -/
theorem signInternal_eq {p : Params} (hp : VPar p) (M sk rnd : List Byte) :
    signInternal p M sk rnd =
      let R := Spec.Sha3.shake256 (chunk sk p.n 1 ++ rnd ++ M) p.n
      let sd := splitDigest p (Spec.Sha3.shake256 (R ++ chunk sk p.n 2 ++ chunk sk p.n 3 ++ M) p.m)
      let sigF := forsSign p sd.1 (chunk sk p.n 0) (chunk sk p.n 2) (forsAdrs (layerTree 0 sd.2.1) sd.2.2)
      R ++ sigF ++ (List.range p.d).flatMap (hsSig p
        (forsPkFromSig p sigF sd.1 (chunk sk p.n 2) (forsAdrs (layerTree 0 sd.2.1) sd.2.2))
        (chunk sk p.n 0) (chunk sk p.n 2) sd.2.1 sd.2.2) := by
  have hn : p.n ≤ 32 := by have := hp.n; omega
  have hI : ∀ D : List Byte, (splitDigest p D).2.2 < 2 ^ p.hp := fun D => by
    simp only [splitDigest, hp.hd]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  simp only [signInternal, prfMsg, hMsg, hp.fam]
  rw [htSign_eq p hn (by have := hp.hp9; omega) hp.d1 (hI _)]
  simp only [forsAdrs, setTreeAddress_zero]

/-! ## The indices -/

theorem toNat_append8 {w : Nat} (x : BitVec w) (b : Byte) : (x ++ b).toNat = x.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

/-- Eight bytes, big-endian. -/
theorem toNat_bytes8 (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64).toNat =
      Spec.Rsa.os2ip [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [toNat_append8, Spec.Rsa.os2ip, List.foldl_cons, List.foldl_nil]
  omega

/-- The first `L` of eight bytes, from the word they make shifted right. -/
theorem os2ip_shift (W : List Byte) (hW : W.length = 8) {L : Nat} (hL : L ≤ 8) :
    Spec.Rsa.os2ip W / 2 ^ (64 - 8 * L) = Spec.Rsa.os2ip (W.take L) := by
  rw [← os2ip_take, hW, show 2 ^ (64 - 8 * L) = 256 ^ (8 - L) by
    rw [show 64 - 8 * L = 8 * (8 - L) by omega, Nat.pow_mul]]

/-- `idx_tree` of `splitDigest`, from the eight bytes `W` after `md`. -/
theorem idxTree_code {p : Params} (hp : VPar p) {D W : List Byte} (hW : W.length = 8)
    (hWD : W.take p.treeIdxLen = (D.drop p.mdLen).take p.treeIdxLen) :
    (splitDigest p D).2.1 = Spec.Rsa.os2ip W / 2 ^ (64 - 8 * p.treeIdxLen) % 2 ^ (p.h - p.hp) := by
  simp only [splitDigest, toInt_eq, hp.tb', List.take_take, Nat.min_self]
  rw [os2ip_shift W hW hp.ti8, hWD]

/-- `idx_leaf` of `splitDigest`, from the eight bytes `W` after `md` and `idx_tree`'s bytes. -/
theorem idxLeaf_code {p : Params} (hp : VPar p) {D W : List Byte} (hW : W.length = 8)
    (hWD : W.take p.leafIdxLen = (D.drop (p.mdLen + p.treeIdxLen)).take p.leafIdxLen) :
    (splitDigest p D).2.2 = Spec.Rsa.os2ip W / 2 ^ (64 - 8 * p.leafIdxLen) % 2 ^ p.hp := by
  simp only [splitDigest, toInt_eq, hp.hd, List.take_take, Nat.min_self]
  rw [os2ip_shift W hW (by rcases hp.li with h | h <;> omega), hWD]

end VG.Proof.SlhDsa.X86_64.SignTop
