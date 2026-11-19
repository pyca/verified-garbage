module

public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64
public import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
public import VerifiedGarbage.Impl.Ed448.AArch64.SignCached
public import VerifiedGarbage.Impl.Ed448.AArch64.Verify
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed448.WholeLocal

/-!
# Ed448 on AArch64, without secret residue

The postconditions of `vg_ed448_public_key` and `vg_ed448_sign_cached` read
the memory on return only within their outputs, and that of
`vg_ed448_verify` not at all (`ScrubAll.ScrubAllOk`, from
`Proof.Ed448.WholeLocal`): each implementation, generic over the Keccak
permutation it calls, returns with every register it may leave secret
cleared and its whole stack zeroed (`ScrubAll.scrubAllOf`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem publicKeyOk : ScrubAllOk
    (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352)
    352 (Spec.Ed448.publicKeySig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed448.publicKeySig)
    (c₀ := (Impl.X448.AArch64.Base.combSym, Impl.X448.AArch64.Base.combWords)) (cs := []) (W := 352)
    (by decide) (by decide) (Nat.le_refl _) (WholeLocal.publicKeyPostOut_local _)

theorem signCachedOk : ScrubAllOk
    (Spec.Ed448.signCachedContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352)
    352 (Spec.Ed448.signCachedSig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed448.signCachedSig)
    (c₀ := (Impl.X448.AArch64.Base.combSym, Impl.X448.AArch64.Base.combWords)) (cs := []) (W := 352)
    (by decide) (by decide) (Nat.le_refl _) (WholeLocal.signCachedPostOut_local _)

theorem verifyOk : ScrubAllOk
    (Spec.Ed448.verifyContract (AArch64.abi.withConsts Impl.Ed448.AArch64.Sparse.baseConsts) 352)
    352 (Spec.Ed448.verifySig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed448.verifySig)
    (c₀ := (Impl.Ed448.AArch64.Sparse.baseSym, Impl.Ed448.AArch64.Sparse.baseWords)) (cs := []) (W := 352)
    (by decide) (by decide) (Nat.le_refl _) (WholeLocal.verifyPostOut_local _)

/-- The registers the three functions write themselves: their tails clear
them with those their permutation writes (`Permutation.clear`). -/
def own : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
    .v27, .v28, .v29, .v30, .v31],
   [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩

/-- What `scrubAllOf` needs of `Impl.Ed448.AArch64.PublicKey.publicKeyWith` with each permutation: evaluated
here. -/
theorem publicKeySide (v : Proof.Sha3.AArch64.Permutation) (hv : v ∈ Proof.Variants.Keccak.AArch64.variants) :
    scrubSide (Impl.Ed448.AArch64.PublicKey.publicKeyWith v.callee) 352 (Spec.Ed448.publicKeySig.retBits AArch64.abi.ptrBits)
      (clearUnion own v.clear) [] = true := by
  have e : (Proof.Variants.Keccak.AArch64.variants.all fun v =>
      scrubSide (Impl.Ed448.AArch64.PublicKey.publicKeyWith v.callee) 352 (Spec.Ed448.publicKeySig.retBits AArch64.abi.ptrBits)
        (clearUnion own v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- What `scrubAllOf` needs of `Impl.Ed448.AArch64.SignCached.signCachedWith` with each permutation: evaluated
here. -/
theorem signCachedSide (v : Proof.Sha3.AArch64.Permutation) (hv : v ∈ Proof.Variants.Keccak.AArch64.variants) :
    scrubSide (Impl.Ed448.AArch64.SignCached.signCachedWith v.callee) 352 (Spec.Ed448.signCachedSig.retBits AArch64.abi.ptrBits)
      (clearUnion own v.clear) [] = true := by
  have e : (Proof.Variants.Keccak.AArch64.variants.all fun v =>
      scrubSide (Impl.Ed448.AArch64.SignCached.signCachedWith v.callee) 352 (Spec.Ed448.signCachedSig.retBits AArch64.abi.ptrBits)
        (clearUnion own v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- What `scrubAllOf` needs of `Impl.Ed448.AArch64.Verify.verifyWith` with each permutation: evaluated
here. -/
theorem verifySide (v : Proof.Sha3.AArch64.Permutation) (hv : v ∈ Proof.Variants.Keccak.AArch64.variants) :
    scrubSide (Impl.Ed448.AArch64.Verify.verifyWith v.callee) 352 (Spec.Ed448.verifySig.retBits AArch64.abi.ptrBits)
      (clearUnion own v.clear) [] = true := by
  have e : (Proof.Variants.Keccak.AArch64.variants.all fun v =>
      scrubSide (Impl.Ed448.AArch64.Verify.verifyWith v.callee) 352 (Spec.Ed448.verifySig.retBits AArch64.abi.ptrBits)
        (clearUnion own v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.Ed448.AArch64.Scrub
