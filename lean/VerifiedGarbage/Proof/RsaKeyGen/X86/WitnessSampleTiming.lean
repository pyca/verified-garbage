module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessUniformTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFallbackTiming

/-! # Complete witness sampling has a secret-independent trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessSample
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessSample

theorem codeAt_trace (k w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (codeAt k w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (WitnessUniform.code_trace w src modulus) (WitnessFallback.codeAt_trace k src)

theorem code_trace (w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeAt_trace (2 * w) w src modulus

end VG.Proof.RsaKeyGen.X86.WitnessSample
