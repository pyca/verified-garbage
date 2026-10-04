import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesCcm.X86.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame

/-!
# AES-CCM (NIST SP 800-38C) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32` (through `vg_cmac_aes_update` made with
it, for the CBC-MAC, and directly for counter mode), are emitted once for
each implementation (`Variants/AesCtr32/X86/`), named with its suffix
(e.g. `vg_aes_ccm_seal_aesni`), and need its CPU features.

Each runs in a frame of 2608 bytes holding its working space and a copy of
its ten stack arguments (`Proof/AesCcm/X86/Frame.lean`), below which it uses
56 bytes: a call of `vg_cmac_aes_update` (its six arguments and return
address) and its own calls of `vg_aes_ctr32`; 2664 bytes in all.
-/

namespace VG.Generic.AesCtr32.X86.AesCcm

open VG.Proof.AesCcm.X86

/-- Which functions an instance of `seal` or `open` calls. -/
def callNote (v : Proof.Aes.X86.Ctr32Impl) : String :=
  "This implementation computes the CBC-MAC with `" ++ Spec.Cmac.aesUpdateApi.name ++ v.suffix ++
    "`, and encrypts with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  { Spec.Ccm.sealApi with
    name := Spec.Ccm.sealApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Ccm.sealApi.doc (notes := [callNote v])
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesCcm.X86.seal v.callee v.suffix)
    contract := Spec.Ccm.sealContract X86.abi 2664
    stack := 2664
    verified := seal_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (by decide) (seal_spSafe v)
    features := v.features },
  { Spec.Ccm.openApi with
    name := Spec.Ccm.openApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Ccm.openApi.doc (notes := [callNote v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesCcm.X86.open v.callee v.suffix)
    contract := Spec.Ccm.openContract X86.abi 2664
    stack := 2664
    verified := open_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (by decide) (open_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86.AesCcm
