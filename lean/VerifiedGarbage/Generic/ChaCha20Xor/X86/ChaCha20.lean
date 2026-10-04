import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT

/-!
# Streaming ChaCha20 (RFC 8439) on x86: `vg_chacha20_apply`

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_chacha20_xor` for the whole blocks, are emitted
once for each implementation (`Variants/ChaCha20Xor/X86/`), named with its
suffix (e.g. `vg_chacha20_apply_ssse3`), and need its CPU features. **Review
note**: `sig` and `doc` are trusted, as they tie the Rust caller to the
contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there, and this file adds only notes on the implementation. The emitter
adds the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract.

The stack is 32 bytes for every implementation: the arguments and return
address of the call of `vg_chacha20_xor`, and the 12 bytes below them that
it uses.
-/

namespace VG.Generic.ChaCha20Xor.X86.ChaCha20

def artifacts (v : Proof.ChaCha20.X86.XorImpl) : List Artifact := [
  { Spec.ChaCha20.applyApi with
    name := Spec.ChaCha20.applyApi.name ++ v.suffix
    target := X86.target
    doc := Spec.ChaCha20.applyApi.doc (notes := ["This implementation XORs the whole blocks with `" ++
      v.callee.name ++ "`."])
    code := Impl.ChaCha20.X86.Stream.apply v.callee
    contract := Spec.ChaCha20.applyContract X86.abi 32
    stack := 32
    verified := Proof.ChaCha20.X86.Stream.apply_verified v
    spSafe := Proof.ChaCha20.X86.Stream.apply_spSafe v
    features := v.features }]

end VG.Generic.ChaCha20Xor.X86.ChaCha20
