import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.OpenCT

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
and up to 16 bytes for its own calls; 1744 bytes in all. `seal_gather`
gathers its slices to its output and calls the instance of `seal` on them
there, with the six argument registers pushed in a frame of 48 bytes and
`tag` pushed for the call: 1808 bytes in all.
-/

namespace VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305

open VG.Proof.ChaCha20Poly1305.X86_64

/-- Which implementations of `vg_chacha20_xor` and `vg_poly1305_blocks` an
instance calls. -/
def xorNote (v : Proof.ChaCha20.X86_64.XorImpl) : String :=
  "This implementation encrypts with `" ++ v.callee.name ++ "` and authenticates with `" ++
    v.poly.name ++ "`."

/-- What `vg_chacha20_poly1305_seal_gather` does: it copies the slices, as
many bytes at a time as `w` says, and calls `vg_chacha20_poly1305_seal`. -/
def gatherNote (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (fn : String) : String :=
  let how := match w with
    | .x16 => "16 bytes at a time"
    | .y32 => "32 bytes at a time with AVX"
    | .z64 => "64 bytes at a time with AVX-512"
  "This implementation copies the slices, " ++ how ++ ", one after the other to `dst`, and \
    encrypts them there in place with `" ++ fn ++ "`."

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
  { Spec.ChaCha20Poly1305.sealGatherApi with
    name := Spec.ChaCha20Poly1305.sealGatherApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.sealGatherApi.doc
      (notes := [gatherNote (Gather.width v) (Gather.sealFn v).name])
    code := Impl.ChaCha20Poly1305.X86_64.SealGather.sealGather (Gather.width v) (Gather.sealFn v).name
      (Gather.sealFn v).code
    contract := Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1808
    stack := 1808
    verified := Gather.sealGather_verified (Gather.width v) (Gather.sealFn v)
    spSafe := Gather.sealGather_spSafe v
    features := features v }]

end VG.Generic.ChaCha20Xor.X86_64.ChaCha20Poly1305
