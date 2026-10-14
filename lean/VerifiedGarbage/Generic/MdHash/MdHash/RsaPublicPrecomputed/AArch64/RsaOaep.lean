module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# RSAES-OAEP encryption with a precomputed public key on AArch64

A generic file of three interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` calls the streaming functions
of `H`, made with the compression function of its `MdHash` variant `v` (for
`lHash`), and of `G`, made with that of its variant `v2` (for MGF1), and an
implementation `c` of `vg_rsa_public_precomputed_checked`
(`Variants/RsaPublicPrecomputed/AArch64/`). It is emitted for the pairs of
hash functions `Inst.emitted` says, with each `c`, named by
`Emit.qualifiedName` (`Inst.parts`, then `rsa`), and needs all three's CPU
features.

Its stack is its frames, 288 bytes, and 16 bytes below them for the calls,
whose callees use no more.
-/

@[expose] public section

namespace VG.Generic.MdHash.MdHash.RsaPublicPrecomputed.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (mgf_valid enc_sat)
open VG.Proof.RsaOaep.AArch64.Inst (emitted parts features)
open VG.Proof.RsaOaep.AArch64.Enc (encStack enc_verified)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)

def artifacts (v v2 : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact :=
  if emitted v v2 then [
    { Spec.RsaOaep.encryptPrecomputedApi v.mgf.G v2.mgf.G with
      name := Emit.qualifiedName (Spec.RsaOaep.encryptPrecomputedApi v.mgf.G v2.mgf.G).name
        (parts v v2 ++ [("rsa", c.suffix)])
      target := AArch64.target
      doc := (Spec.RsaOaep.encryptPrecomputedApi v.mgf.G v2.mgf.G).doc
        (notes := ["This implementation hashes the label with `" ++ v.H.stream.updN ++ "`, masks `DB` \
          and the seed with MGF1 calling `" ++ v2.H.stream.updN ++ "`, and calls `" ++ c.name ++
          "` with the cached modulus values. The message's length is public; its bytes, the label's \
          and the seed's are only copied, hashed and masked."])
      code := Impl.RsaOaep.AArch64.Precomputed.encrypt v.H v2.H (pdOf c).name (pdOf c).code
      contract := Spec.RsaOaep.encryptPrecomputedContract v.mgf.G v2.mgf.G AArch64.abi (encStack (pdOf c))
      stack := encStack (pdOf c)
      verified := enc_verified v.ok.stream v2.ok.stream v.mgf.hash v.mgf.len (mgf_valid v.mgf) v2.mgf.hash
        v2.mgf.len (mgf_valid v2.mgf) (pdOf c) (enc_sat v2.mgf.G v.mgf.mem c)
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := features v v2 ++ c.features.filter (!(features v v2).contains ·) }]
  else []

end VG.Generic.MdHash.MdHash.RsaPublicPrecomputed.AArch64.RsaOaep
