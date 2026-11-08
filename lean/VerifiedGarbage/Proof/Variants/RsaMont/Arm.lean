module

public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Base
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Umaal

/-! # The implementations of `RsaMont` on 32-bit ARM -/

@[expose] public section

namespace VG.Proof.Variants.RsaMont.Arm

def base : Proof.Bignum.Arm.MontBackend := Proof.Variants.RsaMont.Arm.Base.variant

def umaal : Proof.Bignum.Arm.MontBackend := Proof.Variants.RsaMont.Arm.Umaal.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [umaal, base]

end VG.Proof.Variants.RsaMont.Arm
