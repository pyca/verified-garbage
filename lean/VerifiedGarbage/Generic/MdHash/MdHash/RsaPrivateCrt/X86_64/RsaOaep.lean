import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees

/-!
# RSAES-OAEP decryption on x86-64

A generic file of three interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_<H>_mgf1_<G>_decrypt` calls the streaming functions of `H`,
made with the compression function of its `MdHash` variant `v` (for
`lHash`), and of `G`, made with that of its variant `v2` (for MGF1), and
`vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86_64/`). It is emitted for
the pairs of hash functions `Inst.emitted` says, with each `c`, named by
`Emit.qualifiedName` (`Inst.parts`, then `crt`), and needs all three's CPU
features.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3248 bytes, which are more than the hash functions use.
-/

namespace VG.Generic.MdHash.MdHash.RsaPrivateCrt.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (decStack dec_verified dec_spSafe)
open VG.Proof.RsaOaep.X86_64.Inst (emitted parts features)
open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)

def artifacts (v v2 : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  if emitted v v2 then [
    { Spec.RsaOaep.decryptApi v.mgf.G v2.mgf.G with
      name := Emit.qualifiedName (Spec.RsaOaep.decryptApi v.mgf.G v2.mgf.G).name
        (parts v v2 ++ [("crt", c.suffix)])
      target := X86_64.target
      doc := (Spec.RsaOaep.decryptApi v.mgf.G v2.mgf.G).doc
        (notes := ["This implementation calls `" ++ (privOf c).name ++ "`, hashes the label with `" ++
          v.H.stream.updN ++ "` and unmasks the seed and `DB` with MGF1 calling `" ++ v2.H.stream.updN ++
          "`. The checks of `Y`, `lHash'` and the separator, the scan for it and the shift of the \
          message to the start of `out` are masks computed without branches, reading every byte of \
          `EM` whatever the outcome."])
      code := Impl.RsaOaep.X86_64.decrypt v.H.stream v2.H.stream (privOf c).name (privOf c).code
      contract := Spec.RsaOaep.decryptContract v.mgf.G v2.mgf.G X86_64.abi decStack
      stack := decStack
      verified := dec_verified v.ok v.K v2.ok v2.K v.mgf v2.mgf (privOf c)
      spSafe := dec_spSafe v.ok v.K v2.ok v2.K (privOf c)
      features := features v v2 ++ c.features.filter (!(features v v2).contains ·) }]
  else []

end VG.Generic.MdHash.MdHash.RsaPrivateCrt.X86_64.RsaOaep
