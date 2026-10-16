module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Verified

/-!
# The instance of `seal` that `seal_gather` calls

`sealFn`: the code of `seal` for a variant, with its proof and stack depth,
for `Generic/ChaCha20Xor/AArch64/ChaCha20Poly1305.lean`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

/-- The instance of `vg_chacha20_poly1305_seal` calling the backend `v`. -/
def sealFn (v : Proof.ChaCha20.AArch64.XorImpl) : Proof.ChaCha20Poly1305.AArch64.Gather.SealFn where
  name := Spec.ChaCha20Poly1305.sealApi.name ++ v.callee.suffix
  code := Impl.StackScratch.AArch64.withStackScratchWiped 768 .x7 95
    (Impl.ChaCha20Poly1305.AArch64.sealCode v.callee v.stitched)
  verified := Proof.ChaCha20Poly1305.AArch64.seal_framed v
  depth := Proof.ChaCha20Poly1305.AArch64.Gather.seal_depth v

end VG.Proof.ChaCha20Poly1305.AArch64
