module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.PolyvalCT
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch
meta import VerifiedGarbage.Proof.AesGcmSiv.AArch64.PolyvalCT
meta import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the code the taint analysis checks

Untrusted: everything here is checked by Lean. The batches of `polyData`,
`crypt` and `openData`, with the arguments in `x19`–`x26` public, and the
instructions that set up the data past them.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Proof.AesGcmSiv.AArch64 (pubRegs)
open VG.Impl.Gcm.AArch64.Stitch (byRounds)

theorem polyB_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (ifBatch (.seq (.block (tblBuild ++ batches ++ ghSetup)) (.seq ghLoop (.block ghFinish)))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ctrB_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (ifBatch (.seq (.block (ctrSetup ++ batches)) (.seq (byRounds ctrLoop) (.block ctrFinish)))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem openB_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (ifBatch (.seq (.block (tblBuild ++ ctrSetup ++ batches ++ ghSetup))
      (.seq (byRounds openLoop) (.block (ctrFinish ++ ghFinish))))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem rest_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block rest) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restC_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.block (rest ++ ([.lsr .x .x9 .x28 4] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.AesGcmSiv.AArch64.Stitch
