module

public import VerifiedGarbage.Proof.Bignum.Arm.MontCallFios
public import VerifiedGarbage.Proof.Bignum.Arm.FiosFastRound
public import VerifiedGarbage.Proof.Bignum.Arm.FiosFastCT

/-! One pipelined UMAAL kernel supplies every caller of the shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal
open VG VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : MontBackend := montCallFios_backend FiosFast.round_law (by
  intro base size tmp a b mod acc n i _ hi
  exact FiosFast.round_ct hi)

end VG.Proof.Variants.RsaMont.Arm.Umaal
