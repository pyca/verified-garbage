module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Wiped
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # The implementations of AES-CBC that wipe `scratch`, on AArch64

Those whose blocks functions write in `scratch`. The implementation with the
AES instructions writes nothing there, and its functions are registered by
name (`Artifacts/AesCbc/AArch64.lean`). -/

@[expose] public section

namespace VG.Proof.Variants.AesCbc.AArch64

open VG.Proof.AesCbc.AArch64.Wiped (CbcImpl)

def neon : CbcImpl := .neon Proof.Variants.AesBlocks.AArch64.neon (by decide) rfl

def scalar : CbcImpl := .blocks Proof.Variants.AesBlocks.AArch64.scalar (by decide)

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [neon, scalar]

end VG.Proof.Variants.AesCbc.AArch64
