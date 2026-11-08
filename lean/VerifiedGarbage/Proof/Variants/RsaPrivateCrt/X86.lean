module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86.Base

/-! # The implementations of `RsaPrivateCrt` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.X86

def base : Proof.Rsa.X86.PrivChecked.CrtImpl := Proof.Variants.RsaPrivateCrt.X86.Base.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [base]

end VG.Proof.Variants.RsaPrivateCrt.X86
