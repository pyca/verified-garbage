import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesCcm.X86_64.Verified

/-!
# AES-CCM (NIST SP 800-38C) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32` (through `vg_cmac_aes_update` made with
it, for the CBC-MAC, and directly for counter mode), are emitted once for
each implementation (`Variants/AesCtr32/X86_64/`), named with its suffix
(e.g. `vg_aes_ccm_seal_aesni`), and need its CPU features.

The stack is 16 bytes for each: the return addresses of the call of
`vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of its call of
`vg_aes_ctr32`; both also read their arguments after the sixth, from the
data to the tag's length, from the stack above their return address.
-/

namespace VG.Generic.AesCtr32.X86_64.AesCcm

open VG.Proof.AesCcm.X86_64

/-- Which functions an instance of `seal` or `open` calls. -/
def callNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation computes the CBC-MAC with `" ++ Spec.Cmac.aesUpdateApi.name ++ v.suffix ++
    "`, and encrypts with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  { Spec.Ccm.sealApi with
    name := Spec.Ccm.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ccm.sealApi.doc (notes := [callNote v])
    code := Impl.AesCcm.X86_64.seal v.callee v.suffix
    contract := Spec.Ccm.sealContract X86_64.abi 16
    stack := 16
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.Ccm.openApi with
    name := Spec.Ccm.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ccm.openApi.doc (notes := [callNote v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesCcm.X86_64.open v.callee v.suffix
    contract := Spec.Ccm.openContract X86_64.abi 16
    stack := 16
    verified := open_verified v
    spSafe := open_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.AesCcm
