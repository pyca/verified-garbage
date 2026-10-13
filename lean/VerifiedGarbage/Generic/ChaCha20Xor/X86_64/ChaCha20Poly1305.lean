module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified

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
and up to 16 bytes for its own calls; 1744 bytes in all. `seal_split` keeps
its working space as `seal` does, in a frame of 1736 bytes (which also holds
copies of `dst`, `len` and `tag`), and runs `seal`'s code in a frame of 40
bytes laid out as `seal`'s entry, whose calls use 24 bytes below it: 1800
bytes in all. `seal_gather` gathers its slices but the first to its output,
after the first's length, and calls the instance of `seal_split` on them
there with the first slice as `src`, with the six argument registers pushed
in a frame of 48 bytes and `dst`, `len` and `tag` pushed for the call: 1880
bytes in all.
-/

@[expose] public section

namespace VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305

open VG.Proof.ChaCha20Poly1305.X86_64

/-- Which implementations of `vg_chacha20_xor` and `vg_poly1305_blocks` an
instance calls. -/
def xorNote (v : Proof.ChaCha20.X86_64.XorImpl) : String :=
  "This implementation encrypts with `" ++ v.callee.name ++ "` and authenticates with `" ++
    v.poly.name ++ "`."

/-- What `vg_chacha20_poly1305_seal_gather` does: it copies the slices but
the first, as many bytes at a time as `w` says, and calls
`vg_chacha20_poly1305_seal_split` with the first. -/
def gatherNote (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (fn : String) : String :=
  let how := match w with
    | .x16 => "16 bytes at a time"
    | .y32 => "32 bytes at a time with AVX"
    | .z64 => "64 bytes at a time with AVX-512"
  "This implementation copies the slices but the first, " ++ how ++ ", one after the other to `dst` \
    after the first slice's length, and encrypts the data there, its first slice read from where it is, \
    with `" ++ fn ++ "`."

/-- What `vg_chacha20_poly1305_seal_split` does: with the AVX-512
implementations of `vg_poly1305_blocks`, it copies only the bytes of `src`
the first pass of the keystream covers and reads the rest from `src` as it
encrypts; otherwise it copies all of `src`. -/
def splitNote (v : Proof.ChaCha20.X86_64.XorImpl) : String :=
  match v.poly with
  | .avx512 | .ifma => "This implementation copies to `dst` the bytes of `src` that the first keystream it \
      computes covers (all of them for at most 960 bytes of data, else at most 960, as many as the data has \
      past its last multiple of 1024 bytes, rounded up to 64), and reads the rest of `src` as it encrypts, \
      in the code of `vg_chacha20_xor_split_avx512`."
  | _ => "This implementation copies `src` to `dst` and encrypts it there in place, as \
      `vg_chacha20_poly1305_seal` does."

/-- The CPU features an instance requires: those of both implementations. -/
def features (v : Proof.ChaCha20.X86_64.XorImpl) : List String :=
  (v.features ++ v.poly.features).eraseDups

def artifacts (v : Proof.ChaCha20.X86_64.XorImpl) : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc (notes := [xorNote v])
    code := Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42
      (Impl.ChaCha20Poly1305.X86_64.Stitch.sealFor v.callee v.poly)
    contract := Spec.ChaCha20Poly1305.sealContract X86_64.abi 1744
    stack := 1744
    verified := Stitch.sealFor_framed v
    spSafe := X86_64.withStackArgScratchWipedX_spSafe (Stitch.sealFor_spSafe v)
    features := features v },
  { Spec.ChaCha20Poly1305.openApi with
    name := Spec.ChaCha20Poly1305.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.openApi.doc (notes := [xorNote v])
    code := Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42
      (Impl.ChaCha20Poly1305.X86_64.Stitch.openFor v.callee v.poly)
    contract := Spec.ChaCha20Poly1305.openContract X86_64.abi 1744
    stack := 1744
    verified := Stitch.openFor_framed v
    spSafe := X86_64.withStackArgScratchWipedX_spSafe (Stitch.openFor_spSafe v)
    features := features v },
  { Spec.ChaCha20Poly1305.sealSplitApi with
    name := Spec.ChaCha20Poly1305.sealSplitApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.sealSplitApi.doc (notes := [xorNote v, splitNote v])
    code := Impl.StackScratch.X86_64.withStackArgScratchWipedX 1736 3 42
      (Impl.ChaCha20Poly1305.X86_64.SealSplit.sealSplitFor v.callee v.poly)
    contract := Spec.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800
    stack := 1800
    verified := Split.sealSplit_framed v
    spSafe := X86_64.withStackArgScratchWipedX_spSafe (Split.sealSplitFor_spSafe v)
    features := features v },
  { Spec.ChaCha20Poly1305.sealGatherApi with
    name := Spec.ChaCha20Poly1305.sealGatherApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.sealGatherApi.doc
      (notes := [gatherNote (Gather.width v) (Gather.sealSplitFn v).name])
    code := Impl.ChaCha20Poly1305.X86_64.SealGather.sealGather (Gather.width v) (Gather.sealSplitFn v).name
      (Gather.sealSplitFn v).code
    contract := Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880
    stack := 1880
    verified := Gather.sealGather_verified (Gather.width v) (Gather.sealSplitFn v)
    spSafe := Gather.sealGather_spSafe v
    features := features v }]

end VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305
