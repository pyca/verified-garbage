module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64

A generic caller (see `TCB/Emit.lean`), emitted for every ChaCha20 stream
backend. With 64 to 256 bytes of data (1 to 256 with SVE2), one pass of the five-block kernel (four
blocks in NEON lanes and one in the integer registers) computes the one-time
Poly1305 key and the data's keystream together
(`Impl/ChaCha20Poly1305/AArch64/Short.lean`); otherwise the one-time key uses
the scalar block function. The code
uses no stack: its calls (`bl`) keep the return address in `x30`, which it
saves in its working space. Each function keeps its working space (1280
bytes, `work`) in a frame of 1280 bytes on the stack
(`withStackScratchWiped`), whose first 760 bytes are zeroed after the code,
as they hold the one-time Poly1305 key and keystream; the code for 257 to 511
bytes zeroes the keystream it keeps in the rest itself. Every backend's `open`
(the scalar one's too) decrypts 449 to 511 bytes with one chunk of the
eight-block NEON kernel, whose integer units absorb the first 448 bytes into
Poly1305 while it computes the keystream (`OpenPad.openMain`,
`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`). With the eight-block stream
(`XorImpl.stitched`), the same kernel computes the keystream of the data's
whole chunks of 512 bytes while the integer units absorb them, and `seal`
also absorbs the last chunk while it computes the keystream of the four
blocks after it. `seal_gather` gathers its
slices to its output and calls this `seal` on them there.
-/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
      (Impl.ChaCha20Poly1305.AArch64.sealCode v.callee v.stitched)
    stack := 1280
    verified := Proof.ChaCha20Poly1305.AArch64.seal_framed v },
  Spec.ChaCha20Poly1305.openApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
      (Impl.ChaCha20Poly1305.AArch64.openCode v.callee v.stitched)
    stack := 1280
    verified := Proof.ChaCha20Poly1305.AArch64.open_framed v },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather (Proof.ChaCha20Poly1305.AArch64.sealFn v).name (Proof.ChaCha20Poly1305.AArch64.sealFn v).code
    stack := 1296
    verified := Proof.ChaCha20Poly1305.AArch64.Gather.sealGather_verified (Proof.ChaCha20Poly1305.AArch64.sealFn v) }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305
