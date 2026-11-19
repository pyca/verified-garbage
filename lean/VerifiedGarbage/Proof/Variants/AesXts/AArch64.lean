module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64.Neon

/-! # The implementations of `AesXts` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesXts.AArch64

def aes : Proof.AesXts.AArch64.XtsImpl := .aes

def neon : Proof.AesXts.AArch64.XtsImpl := .blocks Proof.Variants.AesBlocks.AArch64.neon
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

def scalar : Proof.AesXts.AArch64.XtsImpl := .blocks .scalar
  ⟨[.x1, .x2, .x3, .x4, .x6, .x9, .x10, .x11, .x12, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩
  ⟨[.x1, .x2, .x3, .x4, .x6, .x9, .x10, .x11, .x12, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30],
   []⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aes, neon, scalar]

end VG.Proof.Variants.AesXts.AArch64
