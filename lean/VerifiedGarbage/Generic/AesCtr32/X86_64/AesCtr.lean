module

public import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CTR (NIST SP 800-38A §6.5) on x86-64

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_ctr32`, is emitted once for each
implementation (`Variants/AesCtr32/X86_64/`), named with its suffix (e.g.
`vg_aes_ctr_aesni`), and needs its CPU features.

The stack is 8 bytes: the return address of the call of `vg_aes_ctr32`,
which uses no stack.
-/

@[expose] public section

namespace VG.Generic.AesCtr32.X86_64.AesCtr

open VG.Proof.AesCtr.X86_64

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  Spec.Ctr.aesApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCtr.X86_64.crypt v.callee
    stack := 8
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.AesCtr
