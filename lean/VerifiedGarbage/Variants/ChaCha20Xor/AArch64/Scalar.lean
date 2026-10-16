module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorBackends

@[expose] public section

namespace VG.Variants.ChaCha20Xor.AArch64.Scalar

def variant : Proof.ChaCha20.AArch64.XorImpl := .scalar

end VG.Variants.ChaCha20Xor.AArch64.Scalar
