module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchPad

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_chacha20_xor`, are emitted once for each
implementation (`Variants/ChaCha20Xor/X86_64/`), named with its suffix (e.g.
`vg_chacha20_poly1305_seal_avx2`), and need its CPU features and those of
the implementation of `vg_poly1305_blocks` it comes with (`XorImpl.poly`). **Review
note**: `sig` and `doc` are trusted, as they tie the Rust caller to the
contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there, and this file adds only notes on the implementation. The emitter
adds the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract.

Each function keeps its working space (1696 bytes, `work`) in a frame of
1720 bytes on the stack, which also holds a copy of `tag` and the address of
`work` (`withStackArgScratchWipedX`). The first 672 bytes of `work`, which hold
the key, the one-time Poly1305 key and the keystream of the call of
`vg_chacha20_xor`, are zeroed after the code, 16 bytes at a time with SSE2;
the code zeroes the keystream it
keeps after them itself. The code below the frame uses 24 bytes of stack for
every implementation: the return address of the call of `vg_chacha20_xor`,
and up to 16 bytes for its own calls; 1744 bytes in all. `seal_split`, emitted only with the
AVX-512 implementations of `vg_poly1305_blocks` (whose `seal_gather` alone
calls it), keeps its working space as `seal` does, in a frame of 1736 bytes (which also holds
copies of `dst`, `len` and `tag`), and runs `seal`'s code in a frame of 40
bytes laid out as `seal`'s entry, whose calls use 24 bytes below it: 1800
bytes in all. `seal_gather` gathers its slices to its output and calls the
instance of `seal` on them there, with the six argument registers pushed in
a frame of 48 bytes and `tag` pushed for the call (1808 bytes); or, with the
AVX-512 implementations for more than 960 bytes, gathers its slices but the
first, after the first's length, and calls the instance of `seal_split` with
the first slice as `src`, with `dst`, `len` and `tag` pushed for the call:
1880 bytes in all.
-/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305

open VG.Proof.ChaCha20Poly1305.X86_64

/-- Which implementations of `vg_chacha20_xor` and `vg_poly1305_blocks` an
instance calls. -/
def xorNote (v : Proof.ChaCha20.X86_64.XorImpl) : String :=
  "This implementation encrypts with `" ++ v.callee.name ++ "` and authenticates with `" ++
    v.poly.name ++ "`."

/-- What `vg_chacha20_poly1305_seal_gather` does: it copies the slices, as
many bytes at a time as the instance's CPUs allow, and calls
`vg_chacha20_poly1305_seal`; with the AVX-512 implementations of
`vg_poly1305_blocks`, for more than 960 bytes of data, it copies the slices
but the first and calls `vg_chacha20_poly1305_seal_split` with the first. -/
def gatherNote (v : Proof.ChaCha20.X86_64.XorImpl) : String :=
  let how := match Gather.width v with
    | .x16 => "16 bytes at a time"
    | .y32 => "32 bytes at a time with AVX"
    | .z64 => "64 bytes at a time with AVX-512"
  let whole := "copies the slices, " ++ how ++ ", one after the other to `dst`, and encrypts them there in \
    place with `" ++ (Gather.Whole.sealFn v).name ++ "`"
  match v.poly with
  | .avx512 | .ifma => "For at most 960 bytes of data, this implementation " ++ whole ++ ". For more, it \
      copies the slices but the first to `dst` after the first slice's length, and encrypts the data there, \
      its first slice read from where it is, with `" ++ (Gather.sealSplitFn v).name ++ "`."
  | _ => "This implementation " ++ whole ++ "."

/-- What `vg_chacha20_poly1305_seal_split` does (it is emitted only with the
AVX-512 implementations of `vg_poly1305_blocks`, whose `seal_gather` calls
it): it copies only the bytes of `src` the first pass of the keystream covers
and reads the rest from `src` as it encrypts. -/
def splitNote : String :=
  "This implementation copies to `dst` the bytes of `src` that the first keystream it \
    computes covers (all of them for at most 960 bytes of data, else at most 960, as many as the data has \
    past its last multiple of 1024 bytes, rounded up to 64), and reads the rest of `src` as it encrypts, \
    with `vg_chacha20_xor_avx512`'s code, inline, loading those blocks from `src`."

/-- What `vg_chacha20_poly1305_seal` does for short data with the AVX-512
implementation of `vg_poly1305_blocks` (without IFMA): the AVX2 code, whose
CPUs (Skylake-SP, Cascade Lake) run slower while they run 512-bit
instructions (`Stitch.sealSmall`). -/
def sealNotes (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  match v.poly with
  | .avx512 => [xorNote v, "For fewer than " ++ toString (Impl.ChaCha20Poly1305.X86_64.Stitch.smallLim v.callee.vl) ++
      " bytes of data, it runs the code of `vg_chacha20_poly1305_seal_avx2` instead, with no 512-bit \
      instruction: the CPUs with AVX-512 but not IFMA (Skylake-SP, Cascade Lake) lower their clock while \
      they run 512-bit instructions, which costs short data more than the wider keystream saves."]
  | _ => [xorNote v]

/-- The CPU features an instance requires: those of both implementations. -/
def features (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  (v.features ++ v.poly.features).eraseDups

/-- What `vg_chacha20_poly1305_open` does in a window of lengths with the IFMA
implementation of `vg_poly1305_blocks` (`Stitch.openWin`). -/
def openNotes (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  match v.poly with
  | .ifma => [xorNote v, "From " ++ toString Impl.ChaCha20Poly1305.X86_64.Stitch.ifmaLo ++ " to " ++
      toString (Impl.ChaCha20Poly1305.X86_64.Stitch.ifmaHi - 1) ++ " bytes of data, it runs the code \
      `vg_chacha20_poly1305_open_avx512vl` runs for short data instead: `vg_chacha20_xor_avx512vl`'s \
      rounds with `vg_poly1305_blocks_avx2`'s Poly1305 inside them, rather than a pass of twelve blocks \
      and then `vg_poly1305_blocks_ifma`."]
  | _ => [xorNote v]

/-- The CPU features `open` requires: with the IFMA implementation of
`vg_poly1305_blocks`, those of `vg_chacha20_xor_avx512vl` too, which its
window calls (`openNotes`). -/
def openFeatures (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  match v.poly with
  | .ifma => (features v ++ Proof.ChaCha20.X86_64.XorImpl.avx512vl.features).eraseDups
  | _ => features v

def artifacts (v : Proof.ChaCha20.X86_64.XorImpl) : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact X86_64.target {
    suffix := v.suffix
    notes := sealNotes v
    code := Impl.StackScratch.X86_64.withStackArgScratchWipedXP 1728 1 8 42
      (Impl.ChaCha20Poly1305.X86_64.Stitch.sealFor v.callee v.poly)
    stack := 1752
    verified := Stitch.sealFor_framed v
    spSafe := X86_64.Pad.withStackArgScratchWipedXP_spSafe (Stitch.sealFor_spSafe v)
    features := features v },
  Spec.ChaCha20Poly1305.openApi.artifact X86_64.target {
    suffix := v.suffix
    notes := openNotes v
    code := Impl.StackScratch.X86_64.withStackArgScratchWipedXP 1728 1 8 42
      (Impl.ChaCha20Poly1305.X86_64.Stitch.openFor v.callee v.poly)
    stack := 1752
    verified := Stitch.openFor_framed v
    spSafe := X86_64.Pad.withStackArgScratchWipedXP_spSafe (Stitch.openFor_spSafe v)
    features := openFeatures v },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [gatherNote v]
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
      notes := [xorNote v, splitNote]
      code := Impl.StackScratch.X86_64.withStackArgScratchWipedX 1736 3 42
        (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)
      stack := 1800
      verified := Split.sealSplit_framed v
      spSafe := X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v)
      features := features v }]
  | _ => []

end VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305
