module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_chacha20_xor`, are emitted once for each
implementation (`Variants/ChaCha20Xor/X86_64/`), named with its suffix (e.g.
`vg_chacha20_poly1305_seal_avx2`), and need its CPU features and those of the
implementation of `vg_poly1305_blocks` it comes with (`XorImpl.poly`).
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there. The emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks against
the contract.

Each function keeps its working space (1696 bytes, `work`) in a frame of
1728 bytes on the stack, which also holds a copy of `tag` and the address of
`work` (`withStackArgScratchWipedX`), and 8 bytes it leaves unused at its top:
`work` is then at `rsp + 8` modulo 16 on entry (`rsp - 1728 + 24`), 16-byte
aligned, where with a frame of 1720 bytes it was not, and its keystream's
16- and 32-byte stores and loads split cache lines (2.6-4.4% of `seal` and
`open` at 64-448 bytes on an Intel Xeon 8573C with the AVX2 code, 0.5-2.3%
on Zen 4 with the AVX-512 code). The first 672 bytes of `work`, which hold
the key, the one-time Poly1305 key and the keystream of the call of
`vg_chacha20_xor`, are zeroed after the code, 16 bytes at a time with SSE2;
the code zeroes the keystream it
keeps after them itself. The code below the frame uses 24 bytes of stack for
every implementation: the return address of the call of `vg_chacha20_xor`,
and up to 16 bytes for its own calls; 1752 bytes in all. `seal_split`, emitted only with the
AVX-512 implementations of `vg_poly1305_blocks` (whose `seal_gather` alone
calls it), keeps its working space as `seal` does, in a frame of 1736 bytes (which also holds
copies of `dst`, `len` and `tag`), and runs `seal`'s code in a frame of 40
bytes laid out as `seal`'s entry, whose calls use 24 bytes below it: 1800
bytes in all. `seal_gather` gathers its slices to its output and calls the
instance of `seal` on them there, with the six argument registers pushed in
a frame of 48 bytes and `tag` pushed for the call (1816 bytes); or, with the
AVX-512 implementations for more than 960 bytes, gathers its slices but the
first, after the first's length, and calls the instance of `seal_split` with
the first slice as `src`, with `dst`, `len` and `tag` pushed for the call:
1880 bytes in all.
-/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305

open VG.Proof.ChaCha20Poly1305.X86_64

/-- The CPU features an instance requires: those of both implementations. -/
def features (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  (v.features ++ v.poly.features).eraseDups

/-- The CPU features `open` requires: with the IFMA implementation of
`vg_poly1305_blocks`, those of `vg_chacha20_xor_avx512vl` too, which its
window calls. -/
def openFeatures (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  match v.poly with
  | .ifma => (features v ++ Proof.ChaCha20.X86_64.XorImpl.avx512vl.features).eraseDups
  | _ => features v

def artifacts (v : Proof.ChaCha20.X86_64.XorImpl) : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42
      (Impl.ChaCha20Poly1305.X86_64.Stitch.sealFor v.callee v.poly)
    stack := 1752
    verified := Stitch.sealFor_framed v
    spSafe := X86_64.withStackArgScratchWipedX_spSafe (Stitch.sealFor_spSafe v)
    features := features v },
  Spec.ChaCha20Poly1305.openApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42
      (Impl.ChaCha20Poly1305.X86_64.Stitch.openFor v.callee v.poly)
    stack := 1752
    verified := Stitch.openFor_framed v
    spSafe := X86_64.withStackArgScratchWipedX_spSafe (Stitch.openFor_spSafe v)
    features := openFeatures v },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact X86_64.target {
    suffix := v.suffix
    code := Gather.gatherCode v
    stack := 1880
    verified := Gather.gather_verified v
    spSafe := Gather.gather_spSafe v
    features := features v }] ++
  -- Only the AVX-512 implementations' `seal_gather` calls `seal_split`.
  match v.poly with
  | .avx512 | .ifma => [
    Spec.ChaCha20Poly1305.sealSplitApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratchWipedX 1736 3 42
        (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)
      stack := 1800
      verified := Split.sealSplit_framed v
      spSafe := X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v)
      features := features v }]
  | _ => []

end VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305
