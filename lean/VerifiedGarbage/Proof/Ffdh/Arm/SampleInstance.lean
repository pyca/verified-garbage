module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleBoundLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
import VerifiedGarbage.Proof.Ffdh.Arm.SampleSample
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarCT

/-! A verified public width selection supplies the complete sampling law. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem sampleLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : SampleBoundLaw env layout bound) : SampleLaw env layout (VG.Impl.Ffdh.Arm.SampleScalar.code bound) :=
  { correct := sampleSample_ok env layout bound law
    ct := by
      intro p slots rb1 rb2 stable special normalized odd _h0 h24 h28 h32 h40 h48 h60 size1 size2 separate
      exact sampleScalar_ct env bound layout law stable special normalized odd h24 h28 h32 h40 h48 h60 size1 size2 separate }

end VG.Proof.Ffdh.Arm
