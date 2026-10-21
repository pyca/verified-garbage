module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Masked witness-count status does not reveal the test or sampling result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStatus
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block VG.Impl.RsaKeyGen.X86.WitnessStatus.code) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

end VG.Proof.RsaKeyGen.X86.WitnessStatus
