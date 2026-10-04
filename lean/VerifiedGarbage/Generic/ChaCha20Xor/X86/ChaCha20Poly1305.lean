import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Verified

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_chacha20_xor`, are emitted once for each
implementation (`Variants/ChaCha20Xor/X86/`), named with its suffix (e.g.
`vg_chacha20_poly1305_seal_ssse3`), and need its CPU features. **Review
note**: `sig` and `doc` are trusted, as they tie the Rust caller to the
contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there, and this file adds only notes on the implementation. The emitter
adds the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract.

The code uses 32 bytes of stack for every implementation. Each function
keeps its working space (704 bytes, `work`) in a frame of 740 bytes on the
stack (`withStackScratchWiped`, with a copy of the seven other arguments),
zeroed after the code, as it holds the one-time Poly1305 key and keystream:
772 bytes in all.
-/

namespace VG.Generic.ChaCha20Xor.X86.ChaCha20Poly1305

/-- Which implementation of `vg_chacha20_xor` an instance calls. -/
def xorNote (v : Proof.ChaCha20.X86.XorImpl) : String :=
  "This implementation encrypts with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.ChaCha20.X86.XorImpl) : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix
    target := X86.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc (notes := [xorNote v])
    code := Impl.StackScratch.X86.withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» v.callee)
    contract := Spec.ChaCha20Poly1305.sealContract X86.abi 772
    stack := 772
    verified := Proof.ChaCha20Poly1305.X86.seal_framed v
    spSafe := Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe (by decide +kernel)
      (Proof.ChaCha20Poly1305.X86.seal_spSafe v)
    features := v.features },
  { Spec.ChaCha20Poly1305.openApi with
    name := Spec.ChaCha20Poly1305.openApi.name ++ v.suffix
    target := X86.target
    doc := Spec.ChaCha20Poly1305.openApi.doc (notes := [xorNote v])
    code := Impl.StackScratch.X86.withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» v.callee)
    contract := Spec.ChaCha20Poly1305.openContract X86.abi 772
    stack := 772
    verified := Proof.ChaCha20Poly1305.X86.open_framed v
    spSafe := Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe (by decide +kernel)
      (Proof.ChaCha20Poly1305.X86.open_spSafe v)
    features := v.features }]

end VG.Generic.ChaCha20Xor.X86.ChaCha20Poly1305
