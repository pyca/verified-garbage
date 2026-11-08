module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-! # The implementations of `ChaCha20Xor` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.ChaCha20Xor.X86_64

def avx2 : Proof.ChaCha20.X86_64.XorImpl := .avx2

def avx512 : Proof.ChaCha20.X86_64.XorImpl := .avx512

def avx512Vl : Proof.ChaCha20.X86_64.XorImpl := .avx512vl

def ifma : Proof.ChaCha20.X86_64.XorImpl := .ifma

def scalar : Proof.ChaCha20.X86_64.XorImpl := .scalar

def ssse3 : Proof.ChaCha20.X86_64.XorImpl := .ssse3

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [ifma, avx512Vl, avx512, avx2, ssse3, scalar]

end VG.Proof.Variants.ChaCha20Xor.X86_64
