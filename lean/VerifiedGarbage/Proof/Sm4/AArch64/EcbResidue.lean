module

public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public meta import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public meta import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Key
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public meta import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit

/-!
# SM4-ECB on AArch64 returns without secret residue

`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` run in a frame of 3264 bytes
whose scratch words they zero (`withStackScratchWiped`). The analysis of the
window's bytes (`rtaintG`) finds that only six of its 204 granules may differ
between the two runs on return: the five lowest and the highest. They clear
their registers, then zero those six granules (`withScrubG 3264 [0, 1, 2, 3,
4, 203]`); their postcondition reads the memory on return only within the
data (`Proof.Sm4.ecbPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.EcbResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintG

/-- `vg_sm4_ecb_encrypt`, before its granules [0, 1, 2, 3, 4, 203] are zeroed. -/
abbrev ecbEncryptBase : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30] none
    (Impl.Sm4.AArch64.ecbFew .encrypt Proof.Sm4.AArch64.ecbAnyFramed)

theorem ecbEncryptBase_verified : Verified AArch64.target ecbEncryptBase (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.encrypt 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.ecbFew_verified .encrypt) (by decide)

theorem ecbEncryptScrubOk : RTaintF.ScrubOk (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.encrypt 3264) 3264 :=
  RTaintF.scrubOk_regs (sig := Spec.Sm4.ecbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Sm4.ecbPostOut_local _ .encrypt)

/-- `vg_sm4_ecb_encrypt`. -/
abbrev ecbEncryptCode : Prog isa := withScrubG 3264 [0, 1, 2, 3, 4, 203] ecbEncryptBase

theorem ecbEncryptCode_verified : Verified AArch64.target ecbEncryptCode (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.encrypt 3264) :=
  RTaintG.Verified.withScrubG ecbEncryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) ecbEncryptScrubOk

theorem ecbEncryptCode_noResidue : NoResidue ecbEncryptCode (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.encrypt 3264) 0 :=
  noResidue_withScrubG (P₀ := 0) ecbEncryptBase_verified ⟨by decide, by decide, by decide⟩ ecbEncryptScrubOk.sp
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ecb_decrypt`, before its granules [0, 1, 2, 3, 4, 203] are zeroed. -/
abbrev ecbDecryptBase : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30] none
    (Impl.Sm4.AArch64.ecbFew .decrypt Proof.Sm4.AArch64.ecbAnyFramed)

theorem ecbDecryptBase_verified : Verified AArch64.target ecbDecryptBase (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.decrypt 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.ecbFew_verified .decrypt) (by decide)

theorem ecbDecryptScrubOk : RTaintF.ScrubOk (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.decrypt 3264) 3264 :=
  RTaintF.scrubOk_regs (sig := Spec.Sm4.ecbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Sm4.ecbPostOut_local _ .decrypt)

/-- `vg_sm4_ecb_decrypt`. -/
abbrev ecbDecryptCode : Prog isa := withScrubG 3264 [0, 1, 2, 3, 4, 203] ecbDecryptBase

theorem ecbDecryptCode_verified : Verified AArch64.target ecbDecryptCode (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.decrypt 3264) :=
  RTaintG.Verified.withScrubG ecbDecryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) ecbDecryptScrubOk

theorem ecbDecryptCode_noResidue : NoResidue ecbDecryptCode (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.decrypt 3264) 0 :=
  noResidue_withScrubG (P₀ := 0) ecbDecryptBase_verified ⟨by decide, by decide, by decide⟩ ecbDecryptScrubOk.sp
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

end VG.Proof.Sm4.AArch64.EcbResidue
