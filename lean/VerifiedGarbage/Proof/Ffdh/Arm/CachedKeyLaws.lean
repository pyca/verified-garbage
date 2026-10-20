module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyPrograms
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleInstance
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerInstance
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentCallTailCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw

/-! One arithmetic backend supplies the cached attempt's preparation, sampling and power laws. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm

theorem prepareLaw : EnvironmentPrepareLaw cachedGenerationEnvironment prepare := cachedPrepareLaw

theorem sampleLaw : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample := CachedSample.law

theorem tailLaw (backend : MontBackend) :
    EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted (tail backend) :=
  environmentCallTail_law (CachedPower.powerLaw backend)

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
