module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Initializing the witness policy has a width-only trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessChecks
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem codeOf_trace (checks : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf checks)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem code_trace (w : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.code w)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeOf_trace _

end VG.Proof.RsaKeyGen.X86.WitnessChecks
