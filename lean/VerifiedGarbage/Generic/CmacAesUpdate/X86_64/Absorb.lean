import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame

/-!
# Streaming AES-CMAC's `absorb` on x86-64

A generic file (see `TCB/Emit.lean`): `vg_cmac_aes_absorb`, calling an
implementation `v` of `vg_cmac_aes_update`, is emitted once for each
implementation (`Variants/CmacAesUpdate/X86_64/`), named with its suffix
(e.g. `vg_cmac_aes_absorb_aesni_cbc`), and needs its CPU features. Its
buffering proof depends on the update's contract, not on how it chains.

It keeps its working space in a frame of its own on the stack
(`Proof/CmacAes/Stream/X86_64/Frame.lean`), below which its calls use at
most 16 bytes: the return addresses of the call of `vg_cmac_aes_update` and
of its call of `vg_aes_ctr32`.
-/

namespace VG.Generic.CmacAesUpdate.X86_64.Absorb

def artifacts (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  { Spec.Cmac.aesAbsorbApi with
    name := Spec.Cmac.aesAbsorbApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Cmac.aesAbsorbApi.doc (notes := [
      "This implementation chains blocks with `" ++ v.callee.name ++ "`."])
    code := Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (Impl.CmacAes.Stream.X86_64.absorb v.callee)
    contract := Spec.Cmac.aesAbsorbContract X86_64.abi 2328
    stack := 2328
    verified := Proof.CmacAes.Stream.X86_64.absorb_framed v
    spSafe := X86_64.withStackScratch_spSafe (by decide) (Proof.CmacAes.Stream.X86_64.absorb_spSafe v)
    features := v.features }]

end VG.Generic.CmacAesUpdate.X86_64.Absorb
