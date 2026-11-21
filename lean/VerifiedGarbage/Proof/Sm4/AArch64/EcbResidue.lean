module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public meta import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSel
public meta import VerifiedGarbage.Proof.Framework.AArch64.ScrubSel
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
their registers, then zero those six granules (`scrubSel 3264 [0, 1, 2, 3,
4, 203]`); their postcondition reads the memory on return only within the
data (`Proof.Sm4.ecbPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.EcbResidue

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintG

/-- `vg_sm4_ecb_encrypt`, before its granules [0, 1, 2, 3, 4, 203] are zeroed. -/
abbrev ecbEncryptBase : Prog isa := Impl.Sm4.AArch64.Fn.ecbEncryptBase

theorem ecbEncryptBase_verified : Verified AArch64.target ecbEncryptBase (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.encrypt 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.ecbFew_verified .encrypt) (by decide)

theorem ecbEncryptScrubOk : RTaintF.ScrubOk (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.encrypt 3264) 3264 :=
  RTaintF.scrubOk_regs (sig := Spec.Sm4.ecbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Sm4.ecbPostOut_local _ .encrypt)

/-- `vg_sm4_ecb_encrypt`. -/
abbrev ecbEncryptCode : Prog isa := Impl.Sm4.AArch64.Fn.ecbEncrypt

/-- `vg_sm4_ecb_decrypt`, before its granules [0, 1, 2, 3, 4, 203] are zeroed. -/
abbrev ecbDecryptBase : Prog isa := Impl.Sm4.AArch64.Fn.ecbDecryptBase

theorem ecbDecryptBase_verified : Verified AArch64.target ecbDecryptBase (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.decrypt 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.ecbFew_verified .decrypt) (by decide)

theorem ecbDecryptScrubOk : RTaintF.ScrubOk (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.decrypt 3264) 3264 :=
  RTaintF.scrubOk_regs (sig := Spec.Sm4.ecbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Sm4.ecbPostOut_local _ .decrypt)

/-- `vg_sm4_ecb_decrypt`. -/
abbrev ecbDecryptCode : Prog isa := Impl.Sm4.AArch64.Fn.ecbDecrypt

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.ecbEncrypt
      (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.encrypt 3264) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) ecbEncryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) ecbEncryptScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.ecbDecrypt
      (Spec.Sm4.ecbContract AArch64.abi Spec.Sm4.Direction.decrypt 3264) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) ecbDecryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) ecbDecryptScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

end VG.Proof.Sm4.AArch64.EcbResidue
