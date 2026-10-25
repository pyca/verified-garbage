module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateBits
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Candidate-bit forcing uses fixed public workspace addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateBits
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.CandidateBits

theorem code_trace (w out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (code w out))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (code w out)) (.block (code 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.CandidateBits
