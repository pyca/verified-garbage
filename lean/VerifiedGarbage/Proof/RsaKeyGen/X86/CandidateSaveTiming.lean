module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSave
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWordTiming

/-! # Saving and restoring the candidate have fixed public loop bounds -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateSave
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.CandidateSave

theorem copy_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (VG.Impl.Rsa.X86.Div.copyWords n src dst)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (VG.Impl.Rsa.X86.Div.copyWords n src dst)
    (VG.Impl.Rsa.X86.Div.copyWords 1 0 0) (VG.Taint.hintOf taint (τr [.esp, .edi]) (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0)))
    rfl rfl rfl (by decide +kernel)

theorem save_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (save n src dst)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (copy_trace n src dst) (LowWord.decrement_trace dst)

theorem restore_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (restore n src dst)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (copy_trace n src dst) (LowWord.increment_trace dst)

theorem restore_workspace_trace (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)) (restore n src dst)
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)) := by
  unfold restore
  apply RelCT.seq (R := VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false))
  · exact erased_relCT (VG.Impl.Rsa.X86.Div.copyWords n src dst)
      (VG.Impl.Rsa.X86.Div.copyWords 1 0 0)
      (VG.Taint.hintOf taint (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)
        (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0))) rfl rfl rfl (by decide +kernel)
  · exact erased_relCT (.block (VG.Impl.RsaKeyGen.X86.LowWord.increment dst))
      (.block (VG.Impl.RsaKeyGen.X86.LowWord.increment 0)) (.block []) rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.CandidateSave
