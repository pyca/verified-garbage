module

public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Umaal4SquareReduce

/-! Shared Montgomery arithmetic uses UMAAL with a four-word square-reduction row. -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal

def variant := Umaal4SquareReduce.variant

end VG.Proof.Variants.RsaMont.Arm.Umaal
