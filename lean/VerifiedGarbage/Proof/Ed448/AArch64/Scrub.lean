module

public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Ed448.WholeLocal

/-!
# Ed448 on AArch64, without secret residue

The postconditions of `vg_ed448_public_key` and `vg_ed448_sign_cached` read
the memory on return only within their outputs, and that of
`vg_ed448_verify` not at all (`ScrubAll.ScrubAllOk`, from
`Proof.Ed448.WholeLocal`): each implementation, generic over the Keccak
permutation it calls, returns with every register it may leave secret
cleared and its whole stack zeroed (`ScrubAll.withScrubAll`).
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

end VG.Proof.Ed448.AArch64.Scrub
