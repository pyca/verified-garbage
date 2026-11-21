module

public import VerifiedGarbage.Impl.Seed.AArch64.Fn
public meta import VerifiedGarbage.Impl.Seed.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public meta import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public import VerifiedGarbage.Proof.Seed.AArch64.Frame
public meta import VerifiedGarbage.Proof.Seed.AArch64.Frame
public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public meta import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SEED-ECB on AArch64 returns without secret residue

`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` run in a frame of 1456 bytes
whose scratch words they zero (`withStackScratchWiped`), and call a block
function whose own frame lies below it. The analysis of the window's bytes
(`rtaintG`) finds that only the lowest 16-byte granule of the 1472-byte window
may differ between the two runs on return. They clear their registers, then
zero that granule (`scrubSel 1472 [0]`); their postcondition reads the
memory on return only within the data (`Proof.Seed.ecbPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64.EcbResidue

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintG

/-- `vg_seed_ecb_encrypt`, before its granules [0] are zeroed. -/
abbrev ecbEncryptBase : Prog isa := Impl.Seed.AArch64.Fn.ecbEncryptBase

theorem ecbEncryptBase_verified : Verified AArch64.target ecbEncryptBase (Spec.Seed.ecbContract AArch64.abi Spec.Seed.Direction.encrypt 1472) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.ecbFew_framed .encrypt) (by decide))

theorem ecbEncryptScrubOk : RTaintF.ScrubOk (Spec.Seed.ecbContract AArch64.abi Spec.Seed.Direction.encrypt 1472) 1472 :=
  RTaintF.scrubOk_regs (sig := Spec.Seed.ecbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Seed.ecbPostOut_local _ .encrypt)

/-- `vg_seed_ecb_encrypt`. -/
abbrev ecbEncryptCode : Prog isa := Impl.Seed.AArch64.Fn.ecbEncrypt

/-- `vg_seed_ecb_decrypt`, before its granules [0] are zeroed. -/
abbrev ecbDecryptBase : Prog isa := Impl.Seed.AArch64.Fn.ecbDecryptBase

theorem ecbDecryptBase_verified : Verified AArch64.target ecbDecryptBase (Spec.Seed.ecbContract AArch64.abi Spec.Seed.Direction.decrypt 1472) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.ecbFew_framed .decrypt) (by decide))

theorem ecbDecryptScrubOk : RTaintF.ScrubOk (Spec.Seed.ecbContract AArch64.abi Spec.Seed.Direction.decrypt 1472) 1472 :=
  RTaintF.scrubOk_regs (sig := Spec.Seed.ecbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Seed.ecbPostOut_local _ .decrypt)

/-- `vg_seed_ecb_decrypt`. -/
abbrev ecbDecryptCode : Prog isa := Impl.Seed.AArch64.Fn.ecbDecrypt

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Seed.AArch64.EcbResidue.ecbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Seed.AArch64.Fn.ecbEncrypt
      (Spec.Seed.ecbContract AArch64.abi Spec.Seed.Direction.encrypt 1472) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) ecbEncryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) ecbEncryptScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Seed.AArch64.EcbResidue.ecbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Seed.AArch64.Fn.ecbDecrypt
      (Spec.Seed.ecbContract AArch64.abi Spec.Seed.Direction.decrypt 1472) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) ecbDecryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) ecbDecryptScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.AArch64.EcbResidue
