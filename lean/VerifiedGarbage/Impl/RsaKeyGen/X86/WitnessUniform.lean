module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessOdd
public import VerifiedGarbage.Impl.Dsa.X86.Checks

/-! # Classify a witness as uniform using two complete native scans -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessUniform
open VG VG.X86

def code (w src modulus : Nat) : Prog isa :=
  .seq (WitnessLower.code (2 * w) src) (.seq (.block (WitnessOdd.mark src))
    (.seq (VG.Impl.Dsa.X86.lessThan w src modulus)
      (.seq (.block (WitnessOdd.restore src)) (.block [.alu .and .eax (.reg .ebx)]))))

end VG.Impl.RsaKeyGen.X86.WitnessUniform
