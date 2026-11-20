module

public import VerifiedGarbage.Proof.AesCfb.AArch64.Caller
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # The implementations of AES-CFB128 on AArch64

Each implementation of the block functions with the code that decrypts whole
blocks with it: the Cryptographic Extension's and AdvSIMD's each have their
own, and the scalar one calls its block function. -/

@[expose] public section

namespace VG.Proof.Variants.AesCfb.AArch64

open VG.Proof.AesCfb.AArch64 (CfbImpl)

def aes : CfbImpl := .aes Proof.Variants.AesBlocks.AArch64.aes

def neon : CfbImpl := .neon Proof.Variants.AesBlocks.AArch64.neon

def scalar : CfbImpl := .ofBlocks Proof.Variants.AesBlocks.AArch64.scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aes, neon, scalar]

end VG.Proof.Variants.AesCfb.AArch64
