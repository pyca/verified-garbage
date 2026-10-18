module

public import VerifiedGarbage.Proof.Rsa.X86.PrivInstances

/-! # Baseline i686 RSA private CRT and its public verification callees -/

@[expose] public section
namespace VG.Proof.Variants.RsaPrivateCrt.X86.Base

def variant : Proof.Rsa.X86.PrivChecked.CrtImpl := Proof.Rsa.X86.PrivChecked.baseline

end VG.Proof.Variants.RsaPrivateCrt.X86.Base
