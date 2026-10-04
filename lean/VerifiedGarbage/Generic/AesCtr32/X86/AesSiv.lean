import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesSiv.X86.Verified
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame

/-!
# AES-SIV (RFC 5297) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC functions made with
it, and directly for CTR), are emitted once for each implementation
(`Variants/AesCtr32/X86/`), named with its suffix (e.g.
`vg_aes_siv_encrypt_aesni`), and need its CPU features.

`encrypt` and `decrypt` use 56 bytes of stack: a call of a CMAC function
(its six arguments and return address) and its own calls of `vg_aes_ctr32`.
`init` keeps its working space in a frame of 2580 bytes holding a copy of
its three stack arguments (`Proof/AesSiv/X86/Verified.lean`), below which
its calls use 48 bytes; 2628 bytes in all.
-/

namespace VG.Generic.AesCtr32.X86.AesSiv

open VG.Proof.AesSiv.X86

/-- Which functions an instance of `encrypt` or `decrypt` calls. -/
def cryptNote (v : Proof.Aes.X86.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`), and encrypts with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  { Spec.Siv.initApi with
    name := Spec.Siv.initApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Siv.initApi.doc (notes := [
      "This implementation expands the keys with `" ++ v.expand.name ++ "` and computes the CMAC subkeys \
      with `" ++ Spec.Cmac.aesSubkeysApi.name ++ v.suffix ++ "`."])
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesSiv.X86.initCore v.expand v.callee v.suffix)
    contract := Spec.Siv.initContract X86.abi 2628
    stack := 2628
    verified := init_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (by decide) (init_spSafe v)
    features := v.features },
  { Spec.Siv.encryptApi with
    name := Spec.Siv.encryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Siv.encryptApi.doc (notes := [cryptNote v])
    code := Impl.AesSiv.X86.encrypt v.callee v.suffix
    contract := Spec.Siv.encryptContract X86.abi 56
    stack := 56
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  { Spec.Siv.decryptApi with
    name := Spec.Siv.decryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Siv.decryptApi.doc (notes := [cryptNote v,
      "It compares the IVs and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesSiv.X86.decrypt v.callee v.suffix
    contract := Spec.Siv.decryptContract X86.abi 56
    stack := 56
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86.AesSiv
