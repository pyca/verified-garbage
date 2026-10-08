import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesCtr.AArch64.Verified

/-!
# AES-CTR (NIST SP 800-38A §6.5) on AArch64

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_ctr32`, is emitted once for each
implementation (`Variants/AesCtr32/AArch64/`), named with its suffix (e.g.
`vg_aes_ctr_aes`), and needs its CPU features.

No stack is used: the calls keep the return address in `x30`, which the
function saves in the scratch buffer.
-/

namespace VG.Generic.AesCtr32.AArch64.AesCtr

open VG.Proof.AesCtr.AArch64

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  { Spec.Ctr.aesApi with
    name := Spec.Ctr.aesApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Ctr.aesApi.doc (notes := ["This implementation enciphers the counter blocks with `" ++
      v.callee.name ++ "`, as many at once as its 32-bit counter allows."])
    code := Impl.AesCtr.AArch64.crypt v.callee
    contract := Spec.Ctr.aesContract AArch64.abi
    verified := crypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.AesCtr
