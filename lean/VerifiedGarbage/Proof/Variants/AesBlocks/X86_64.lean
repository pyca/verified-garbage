module

public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant

/-! # The implementations of `AesBlocks` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.AesBlocks.X86_64

def aesNi : Proof.Aes.X86_64.BlocksImpl := .aesni

def scalar : Proof.Aes.X86_64.BlocksImpl := .scalar

def vaes : Proof.Aes.X86_64.BlocksImpl := .vaes

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [vaes, aesNi, scalar]

end VG.Proof.Variants.AesBlocks.X86_64
