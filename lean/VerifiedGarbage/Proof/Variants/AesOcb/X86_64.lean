module

public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64

/-! # The implementations of `AesOcb` on x86-64 -/

@[expose] public section

namespace VG.Proof.AesOcb.X86_64

/-- An implementation of `vg_aes_ocb_seal` and `vg_aes_ocb_open`. -/
inductive OcbImpl where
  /-- The one-pass functions with AES-NI. -/
  | onePass
  /-- The functions over the AES block functions `v`. -/
  | blocks (v : Proof.Aes.X86_64.BlocksImpl)

end VG.Proof.AesOcb.X86_64

namespace VG.Proof.Variants.AesOcb.X86_64

/-- Every implementation, best first: the dispatchers of `seal` and `open`
try them in this order. -/
def variants : List Proof.AesOcb.X86_64.OcbImpl := [.onePass, .blocks AesBlocks.X86_64.scalar]

end VG.Proof.Variants.AesOcb.X86_64
