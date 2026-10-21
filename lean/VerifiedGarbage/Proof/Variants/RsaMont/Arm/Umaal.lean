module

public import VerifiedGarbage.Proof.Bignum.Arm.MontCallFios
public import VerifiedGarbage.Proof.Bignum.Arm.FiosRound
public import VerifiedGarbage.Proof.Bignum.Arm.FiosCT

/-! One pipelined UMAAL kernel supplies every caller of the shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal
open VG VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : MontBackend := montCallFios_backend Fios.round_law (by
  intro base size tmp a b mod acc n i _ hi
  exact Fios.round_ct hi)

end VG.Proof.Variants.RsaMont.Arm.Umaal
