module

public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSample
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentScalarCT

/-! The existing byte cutter consumes one verified public-context bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem environmentSample_law (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (bound : Prog isa) (law : EnvironmentBoundLaw env layout bound) :
    EnvironmentSampleLaw env layout (VG.Impl.Ffdh.Arm.SampleScalar.code bound) where
  correct := environmentSample_ok env layout bound law
  ct := by
    intro p slots rb1 rb2 stable special normalized odd h52 _h0 h24 h28 h32 h40 h48 h60 size1 size2 separate
    exact environmentScalar_ct env bound layout law stable special normalized odd h52 h24 h28 h32 h40 h48 h60 size1 size2 separate

end VG.Proof.Ffdh.Arm
