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

/-- The implementations of the XOR of the keystream alone, best first: those
of `variants` but `ifma`, which differs from `avx512` only in its
`vg_poly1305_blocks`, for the functions that do not call that (whose
instances for `ifma` would be `avx512`'s). -/
def xorVariants := [avx512Vl, avx512, avx2, ssse3, scalar]

end VG.Proof.Variants.ChaCha20Xor.X86_64
