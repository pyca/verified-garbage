module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86.Base

/-! # Baseline i686 RSA private CRT variant -/

@[expose] public section
namespace VG.Variants.RsaPrivateCrt.X86.Base

def variant : Proof.Rsa.X86.PrivChecked.CrtImpl := Proof.Variants.RsaPrivateCrt.X86.Base.variant

end VG.Variants.RsaPrivateCrt.X86.Base
