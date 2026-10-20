module

import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleInstance
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleCT
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound

/-! Cached sampling uses only canonical public header words and the shared byte cutter. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm

theorem boundLaw : EnvironmentBoundLaw cachedGenerationEnvironment ScalarLayout.vetted
    VG.Impl.Ffdh.Arm.CachedSample.bound where
  correct := by
    intro s p slots h environment _normalized _odd _stable special h52 _h24 _h28 _h32 _h60
    exact bound_ok s h environment h52 special (bits_positive environment) (bits_bound p)
  ct := by
    intro p slots _stable _special _normalized _odd h52 _h24 _h28 _h32 _h60
    exact (bound_ct h52).mono (fun _ _ h => ⟨h.1, h.2.1, h.2.2.2⟩) (fun _ _ h => h)

theorem law : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted
    VG.Impl.Ffdh.Arm.CachedSample.code :=
  environmentSample_law cachedGenerationEnvironment ScalarLayout.vetted _ boundLaw

end VG.Proof.Ffdh.Arm.CachedSample
