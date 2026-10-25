module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Difference
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Absolute difference executes the same public native-word loops for every input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Difference
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Difference

theorem code_trace (n out tmp a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (code n out tmp a b)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (code n out tmp a b) (code 0 0 0 0 0)
    (VG.Taint.hintOf taint (τr [.esp, .edi]) (code 0 0 0 0 0))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.Difference
