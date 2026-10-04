import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified

/-!
# AES-SIV (RFC 5297) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC functions made with
it, and directly for CTR), are emitted once for each implementation
(`Variants/AesCtr32/X86_64/`), named with its suffix (e.g.
`vg_aes_siv_encrypt_aesni`), and need its CPU features.

The stack is 16 bytes for each: the return addresses of the call of a CMAC
function (or of `vg_aes_ctr32`) and of its call of `vg_aes_ctr32`; `encrypt`
and `decrypt` also read their seventh argument, the working space's address,
from the stack above their return address.
-/

namespace VG.Generic.AesCtr32.X86_64.AesSiv

open VG.Proof.AesSiv.X86_64

/-- Which functions an instance of `encrypt` or `decrypt` calls. -/
def cryptNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`), and encrypts with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  { Spec.Siv.initApi with
    name := Spec.Siv.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.initApi.doc (notes := [
      "This implementation expands the keys with `" ++ v.expand.name ++ "` and computes the CMAC subkeys \
      with `" ++ Spec.Cmac.aesSubkeysApi.name ++ v.suffix ++ "`."])
    code := Impl.AesSiv.X86_64.init v.expand v.callee v.suffix
    contract := Spec.Siv.initContract X86_64.abi 16
    stack := 16
    verified := init_verified v
    spSafe := init_spSafe v
    features := v.features },
  { Spec.Siv.encryptApi with
    name := Spec.Siv.encryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.encryptApi.doc (notes := [cryptNote v])
    code := Impl.AesSiv.X86_64.encrypt v.callee v.suffix
    contract := Spec.Siv.encryptContract X86_64.abi 16
    stack := 16
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  { Spec.Siv.decryptApi with
    name := Spec.Siv.decryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Siv.decryptApi.doc (notes := [cryptNote v,
      "It compares the IVs and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesSiv.X86_64.decrypt v.callee v.suffix
    contract := Spec.Siv.decryptContract X86_64.abi 16
    stack := 16
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.AesSiv
