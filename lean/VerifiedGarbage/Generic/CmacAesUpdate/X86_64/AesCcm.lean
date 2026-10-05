import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesCcm.X86_64.Frame

/-!
# AES-CCM (NIST SP 800-38C) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_cmac_aes_update` for the CBC-MAC, and the
implementation of `vg_aes_ctr32` that goes with it (`v.ctr`) for counter
mode, are emitted once for each implementation
(`Variants/CmacAesUpdate/X86_64/`), named with its suffix (e.g.
`vg_aes_ccm_seal_aesni_cbc`), and need the CPU features of both.

The code of each uses at most 16 bytes of stack: the return addresses of
the call of `vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of its call of
`vg_aes_ctr32`, if it makes one; both also read their arguments after the
sixth, from the data to the tag's length, from the stack above their return
address. Each keeps its working space, its last argument, in a frame of
2608 bytes on the stack that also holds a copy of its four other stack
arguments (`Verified.stackArgScratch`).
-/

namespace VG.Generic.CmacAesUpdate.X86_64.AesCcm

open VG.Proof.AesCcm.X86_64

/-- Which functions an instance of `seal` or `open` calls. -/
def callNote (v : Proof.CmacAes.X86_64.UpdateImpl) : String :=
  "This implementation computes the CBC-MAC with `" ++ v.callee.name ++ "`, and encrypts with `" ++
    v.ctr.callee.name ++ "`."

def artifacts (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  { Spec.Ccm.sealApi with
    name := Spec.Ccm.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ccm.sealApi.doc (notes := [callNote v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesCcm.X86_64.seal v.callee v.ctr.callee)
    contract := Spec.Ccm.sealContract X86_64.abi 2624
    stack := 2624
    verified := seal_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v)
    features := v.ctr.features },
  { Spec.Ccm.openApi with
    name := Spec.Ccm.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ccm.openApi.doc (notes := [callNote v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesCcm.X86_64.open v.callee v.ctr.callee)
    contract := Spec.Ccm.openContract X86_64.abi 2624
    stack := 2624
    verified := open_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v)
    features := v.ctr.features }]

end VG.Generic.CmacAesUpdate.X86_64.AesCcm
