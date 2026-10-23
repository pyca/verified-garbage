module

public import VerifiedGarbage.Proof.Bignum.Arm.MontCallFios2
public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Round
public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.CT
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelinePairCT

/-! One two-row UMAAL kernel supplies every caller of the shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal
open VG VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : MontBackend := montCallFios2_backend
  (MontPipeline.PairLaw.loop Fios2.round_law)
  (MontPipeline.PairCTLaw.loop Fios2.round_law fun _ hi => Fios2.round_ct hi)

end VG.Proof.Variants.RsaMont.Arm.Umaal
