module

import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStep
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext

/-! # One divisor's trace has no candidate-dependent memory address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Sieve

theorem step_trace {g : Geometry} (v : g.Valid) {c d i q : Nat} (index : i < 1024) :
    RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (step stackSlots) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (loadPrime_trace v index) (RelCT.seq (divisor_trace v) (checkedBlockInvariant rfl rfl))

end VG.Proof.RsaKeyGen.X86.Sieve
