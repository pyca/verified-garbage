module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorBackends

/-! # The implementations of `ChaCha20Xor` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.ChaCha20Xor.AArch64

def neon : Proof.ChaCha20.AArch64.XorImpl := .neon

def scalar : Proof.ChaCha20.AArch64.XorImpl := .scalar

def sve2 : Proof.ChaCha20.AArch64.XorImpl := .sve2

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [sve2, neon, scalar]

end VG.Proof.Variants.ChaCha20Xor.AArch64
