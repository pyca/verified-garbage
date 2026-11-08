module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86.Base

/-! # The implementations of `RsaPrivateCrt` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.X86

def base : Proof.Rsa.X86.PrivChecked.CrtImpl := Proof.Variants.RsaPrivateCrt.X86.Base.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [base]

end VG.Proof.Variants.RsaPrivateCrt.X86
