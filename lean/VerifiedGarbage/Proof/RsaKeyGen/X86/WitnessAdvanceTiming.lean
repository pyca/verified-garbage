module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAdvance
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAvailable
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Entropy cursor arithmetic uses only fixed header addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem WitnessAdvance.codeAt_trace (D : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessAdvance.codeAt D)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block (VG.Impl.RsaKeyGen.X86.WitnessAdvance.codeAt 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem WitnessAvailable.codeAt_trace (D : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.codeAt D)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.codeAt 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.RsaKeyGen.X86
