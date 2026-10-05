import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesSiv.X86_64.Frame

/-!
# AES-SIV (RFC 5297) encryption and decryption on x86-64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, calling an implementation `v` of `vg_cmac_aes_update`,
and the CMAC functions and `vg_aes_ctr32` made with the implementation of
AES that goes with it (`v.ctr`), are emitted once for each implementation
of the update (`Variants/CmacAesUpdate/X86_64/`), named with its suffix
(e.g. `vg_aes_siv_encrypt_aesni_cbc`), and need the CPU features of both.

Each function keeps its working space in a frame of its own
(`Proof/AesSiv/X86_64/Frame.lean`) of 2600 bytes, which also holds a copy of
`siv`, its seventh argument, passed on the stack; below it its calls use at
most 16 bytes: the return addresses of the call of a CMAC function (or of
`vg_aes_ctr32`) and of its call of `vg_aes_ctr32` (2616 bytes of stack in
all).
-/

namespace VG.Generic.CmacAesUpdate.X86_64.AesSiv

open VG.Proof.AesSiv.X86_64

/-- Which functions an instance of `encrypt` or `decrypt` calls. -/
def cryptNote (v : Proof.CmacAes.X86_64.UpdateImpl) : String :=
  "This implementation chains the blocks of CMAC with `" ++ v.callee.name ++ "`, calls the other CMAC \
    functions made with `" ++ v.ctr.callee.name ++ "` (e.g. `" ++ Spec.Cmac.aesFinalizeApi.name ++
    v.ctr.suffix ++ "`), and encrypts with `" ++ v.ctr.callee.name ++ "`."

def artifacts (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  { Spec.Siv.encryptApi with
    name := Spec.Siv.encryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.encryptApi.doc (notes := [cryptNote v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (Impl.AesSiv.X86_64.encrypt v.callee v.ctr.callee v.ctr.suffix)
    contract := Spec.Siv.encryptContract X86_64.abi 2616
    stack := 2616
    verified := encrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (encrypt_spSafe v)
    features := v.ctr.features },
  { Spec.Siv.decryptApi with
    name := Spec.Siv.decryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.decryptApi.doc (notes := [cryptNote v,
      "It compares the IVs and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 1
      (Impl.AesSiv.X86_64.decrypt v.callee v.ctr.callee v.ctr.suffix)
    contract := Spec.Siv.decryptContract X86_64.abi 2616
    stack := 2616
    verified := decrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (decrypt_spSafe v)
    features := v.ctr.features }]

end VG.Generic.CmacAesUpdate.X86_64.AesSiv
