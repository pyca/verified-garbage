module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessCount
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStatus
/-! # Counting uniform samples and choosing status use no secret branch -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessStatusTiming.lean`, which only this module imported.
section

/-! # Masked witness-count status does not reveal the test or sampling result -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessStatus
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block VG.Impl.RsaKeyGen.X86.WitnessStatus.code) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

end VG.Proof.RsaKeyGen.X86.WitnessStatus
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.WitnessCount

theorem next_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block next) (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl

theorem store_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block [.store (VG.Impl.Mont.X86.sc statusOffset) .ecx]) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) code
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq next_trace (RelCT.seq WitnessStatus.code_trace store_trace)

end VG.Proof.RsaKeyGen.X86.WitnessCount
