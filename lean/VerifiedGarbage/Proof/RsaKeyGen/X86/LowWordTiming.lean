module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowWord
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Low-word updates have no secret-dependent addresses or branches -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowWord
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.LowWord

theorem decrement_trace (out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (decrement out))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (decrement out)) (.block (decrement 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

theorem increment_trace (out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (increment out))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (increment out)) (.block (increment 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.LowWord
