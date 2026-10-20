module

public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerInstance
import VerifiedGarbage.Proof.Ffdh.Arm.SampleCallTailCT
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw

/-! The selected public scalar width uses the existing shared exponentiator. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SampleKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm

def tail (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.KeyGenerate.tail (power b)

theorem tailLaw (b : MontBackend) : SampleTailLaw (tail b) :=
  sampleCallTail_law (powerLaw b)

end VG.Proof.Ffdh.Arm.SampleKeyGenerate
