import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp

/-!
# RSAES-OAEP encryption on x86-64

A generic file of two interfaces (see `TCB/Emit.lean`), both `MdHash`:
`vg_rsa_oaep_<H>_mgf1_<G>_encrypt` calls the streaming functions of `H`,
made with the compression function of its variant `v` (for `lHash`), and of
`G`, made with that of its variant `v2` (for MGF1), and
`vg_rsa_public_checked`. It is emitted for the pairs `Inst.emitted` says,
named by `Emit.qualifiedName` (`Inst.parts`), and needs both's CPU features.

Its stack is its frame, a return address and what the hash functions'
calls and `vg_rsa_public_checked` use.
-/

namespace VG.Generic.MdHash.MdHash.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (encStack enc_verified enc_spSafe enc_sat)
open VG.Proof.RsaOaep.X86_64.Inst (emitted parts features)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked)

def artifacts (v v2 : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if emitted v v2 then [
    { Spec.RsaOaep.encryptApi v.mgf.G v2.mgf.G with
      name := Emit.qualifiedName (Spec.RsaOaep.encryptApi v.mgf.G v2.mgf.G).name (parts v v2)
      target := X86_64.target
      doc := (Spec.RsaOaep.encryptApi v.mgf.G v2.mgf.G).doc
        (notes := ["This implementation hashes the label with `" ++ v.H.stream.updN ++ "`, masks `DB` \
          and the seed with MGF1 calling `" ++ v2.H.stream.updN ++ "`, and calls `" ++ pubChecked.name ++
          "`. The message's length is public; its bytes, the label's and the seed's are only copied, \
          hashed and masked."])
      code := Impl.RsaOaep.X86_64.encrypt v.H.stream v2.H.stream pubChecked.name pubChecked.code
      contract := Spec.RsaOaep.encryptContract v.mgf.G v2.mgf.G X86_64.abi encStack
      stack := encStack
      verified := enc_verified v.ok v.K v2.ok v2.K v.mgf v2.mgf (enc_sat v.mgf.G v2.mgf.G v.mgf.mem)
      spSafe := enc_spSafe v.ok v.K v2.ok v2.K
      features := features v v2 }]
  else []

end VG.Generic.MdHash.MdHash.X86_64.RsaOaep
