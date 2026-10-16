module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorBackends

@[expose] public section

namespace VG.Variants.ChaCha20Xor.AArch64.Sve2

def variant : Proof.ChaCha20.AArch64.XorImpl := .sve2

end VG.Variants.ChaCha20Xor.AArch64.Sve2
