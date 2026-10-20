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
saves in its working space. Each function keeps its working space (760
bytes, `work`) in a frame of 768 bytes on the stack
(`withStackScratchWiped`), zeroed after the code, as it holds the one-time
Poly1305 key and keystream. With the eight-block stream
(`XorImpl.stitched`), the integer units absorb the data's whole chunks of 512
bytes into Poly1305 while the stream computes their keystream
(`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`), and `seal` also absorbs
the last chunk while it computes the keystream of the four blocks after it. `seal_gather` gathers its
slices to its output and calls this `seal` on them there.
-/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305

/-- Notes on the implementation. -/
def notes (v : Proof.ChaCha20.AArch64.XorImpl) : List String :=
  ["With " ++ (if v.callee.sve then "1" else "64") ++ " to 256 bytes of data, computes the one-time " ++
    "Poly1305 key and the data's keystream in one pass of four NEON blocks and one integer block."] ++
  if v.stitched then ["Absorbs each 512 bytes into Poly1305 with integer instructions while " ++
    "computing the keystream of the next with the eight-block ChaCha20 kernel."] else []

/-- `seal`'s notes: also the rest after the chunks
(`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`, `Tail`). -/
def sealNotes (v : Proof.ChaCha20.AArch64.XorImpl) : List String :=
  notes v ++ if v.stitched then ["Computes the keystream of the four blocks after " ++
    "the chunks while absorbing the last chunk, and encrypts up to 256 bytes of the rest with it."]
  else []

/-- What `vg_chacha20_poly1305_seal_gather` does: it calls `vg_chacha20_poly1305_seal`. -/
def gatherNote (fn : String) : String :=
  "This implementation copies the slices one after the other to `dst`, 16 bytes at a time and then \
    the last bytes of each eight, four and one at a time, and encrypts them there in place with `" ++
    fn ++ "`."

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := sealNotes v
    code := Impl.StackScratch.AArch64.withStackScratchWiped 768 .x7 95
      (Impl.ChaCha20Poly1305.AArch64.sealCode v.callee v.stitched)
    stack := 768
    verified := Proof.ChaCha20Poly1305.AArch64.seal_framed v },
  Spec.ChaCha20Poly1305.openApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes v
    code := Impl.StackScratch.AArch64.withStackScratchWiped 768 .x7 95
      (Impl.ChaCha20Poly1305.AArch64.openCode v.callee v.stitched)
    stack := 768
    verified := Proof.ChaCha20Poly1305.AArch64.open_framed v },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := [gatherNote (Proof.ChaCha20Poly1305.AArch64.sealFn v).name]
    code := Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather (Proof.ChaCha20Poly1305.AArch64.sealFn v).name (Proof.ChaCha20Poly1305.AArch64.sealFn v).code
    stack := 784
    verified := Proof.ChaCha20Poly1305.AArch64.Gather.sealGather_verified (Proof.ChaCha20Poly1305.AArch64.sealFn v) }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305
