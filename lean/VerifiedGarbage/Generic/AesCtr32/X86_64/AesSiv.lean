import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesSiv.X86_64.Frame

/-!
# AES-SIV (RFC 5297) key setup on x86-64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_init`, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC subkeys made with it)
and the implementation of `vg_aes_expand_key_scratch` that goes with it, is
emitted once for each implementation (`Variants/AesCtr32/X86_64/`), named
with its suffix (e.g. `vg_aes_siv_init_aesni`), and needs its CPU features.
`vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, which also call
`vg_cmac_aes_update`, follow its implementations instead
(`Generic/CmacAesUpdate/X86_64/AesSiv.lean`).

`init` keeps its working space in a frame of its own
(`Proof/AesSiv/X86_64/Frame.lean`) of 2568 bytes, below which its calls use
16 bytes: the return addresses of the call of `vg_cmac_aes_subkeys` (or of
`vg_aes_expand_key_scratch`) and of its call of `vg_aes_ctr32` (2584 bytes
of stack in all).
-/

namespace VG.Generic.AesCtr32.X86_64.AesSiv

open VG.Proof.AesSiv.X86_64

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  { Spec.Siv.initApi with
    name := Spec.Siv.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.initApi.doc (notes := [
      "This implementation expands the keys with `" ++ v.expand.name ++ "` and computes the CMAC subkeys \
      with `" ++ Spec.Cmac.aesSubkeysApi.name ++ v.suffix ++ "`."])
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx
      (Impl.AesSiv.X86_64.init v.expand v.callee v.suffix)
    contract := Spec.Siv.initContract X86_64.abi 2584
    stack := 2584
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe (by decide) (init_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.AesSiv
