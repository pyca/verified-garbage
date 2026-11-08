module

public import VerifiedGarbage.Proof.Aes.X86_64.Variant

/-! # The implementations of `AesCtr32` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.AesCtr32.X86_64

def aesNi : Proof.Aes.X86_64.Ctr32Impl := .aesni

def scalar : Proof.Aes.X86_64.Ctr32Impl := .scalar

def vaes : Proof.Aes.X86_64.Ctr32Impl := .vaes

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [vaes, aesNi, scalar]

end VG.Proof.Variants.AesCtr32.X86_64
