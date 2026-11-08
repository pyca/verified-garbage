module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorBackends

/-! # The implementations of `ChaCha20Xor` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.ChaCha20Xor.AArch64

def neon : Proof.ChaCha20.AArch64.XorImpl := .neon

def scalar : Proof.ChaCha20.AArch64.XorImpl := .scalar

def sve2 : Proof.ChaCha20.AArch64.XorImpl := .sve2

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [neon, scalar, sve2]

end VG.Proof.Variants.ChaCha20Xor.AArch64
