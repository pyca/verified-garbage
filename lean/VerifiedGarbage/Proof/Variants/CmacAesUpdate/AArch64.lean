module

public import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
public import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64.Neon

/-! # The implementations of `CmacAesUpdate` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.CmacAesUpdate.AArch64

def aese : Proof.CmacAes.AArch64.UpdateImpl := .aese

def neon : Proof.CmacAes.AArch64.UpdateImpl := .ctr32 Proof.Variants.AesCtr32.AArch64.neon
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

def scalar : Proof.CmacAes.AArch64.UpdateImpl := .ctr32 .scalar
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x9, .x10, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aese, neon, scalar]

end VG.Proof.Variants.CmacAesUpdate.AArch64
