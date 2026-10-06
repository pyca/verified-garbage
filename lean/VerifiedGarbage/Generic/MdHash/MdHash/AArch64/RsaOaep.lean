import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst

/-!
# RSAES-OAEP encryption on AArch64

A generic file of two interfaces (see `TCB/Emit.lean`), both `MdHash`:
`vg_rsa_oaep_<H>_mgf1_<G>_encrypt` calls the streaming functions of `H`,
made with the compression function of its variant `v` (for `lHash`), and of
`G`, made with that of its variant `v2` (for MGF1), and
`vg_rsa_public_checked`. It is emitted for the pairs `Inst.emitted` says,
named by `Emit.qualifiedName` (`Inst.parts`), and needs both's CPU features.

Its stack is its frames, 288 bytes, and 16 bytes below them for the calls,
whose callees use no stack of their own.
-/

namespace VG.Generic.MdHash.MdHash.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (mgf_valid enc_sat)
open VG.Proof.RsaOaep.AArch64.Inst (emitted parts features)
open VG.Proof.RsaOaep.AArch64.Enc (encStack enc_verified)
open VG.Proof.RsaPkcs1Enc.AArch64 (pubImpl)

def artifacts (v v2 : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if emitted v v2 then [
    { Spec.RsaOaep.encryptApi v.mgf.G v2.mgf.G with
      name := Emit.qualifiedName (Spec.RsaOaep.encryptApi v.mgf.G v2.mgf.G).name (parts v v2)
      target := AArch64.target
      doc := (Spec.RsaOaep.encryptApi v.mgf.G v2.mgf.G).doc
        (notes := ["This implementation hashes the label with `" ++ v.H.stream.updN ++ "`, masks `DB` \
          and the seed with MGF1 calling `" ++ v2.H.stream.updN ++ "`, and calls `" ++ pubImpl.name ++
          "`. The message's length is public; its bytes, the label's and the seed's are only copied, \
          hashed and masked."])
      code := Impl.RsaOaep.AArch64.encrypt v.H v2.H pubImpl.name pubImpl.code
      contract := Spec.RsaOaep.encryptContract v.mgf.G v2.mgf.G AArch64.abi (encStack pubImpl)
      stack := encStack pubImpl
      verified := enc_verified v.ok.stream v2.ok.stream v.mgf.hash v.mgf.len (mgf_valid v.mgf) v2.mgf.hash
        v2.mgf.len (mgf_valid v2.mgf) pubImpl (enc_sat v2.mgf.G v.mgf.mem)
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := features v v2 }]
  else []

end VG.Generic.MdHash.MdHash.AArch64.RsaOaep
