module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase

/-! # RSAES-PKCS1-v1_5 decryption with implicit rejection on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPkcs1Enc

open VG.Proof.RsaPkcs1Enc.AArch64 (privOf dec_sat)
open VG.Proof.RsaPkcs1Enc.AArch64.Dec (HH decStack dec_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact :=
  match v.sha256 with
  | none => []
  | some h => [
    Spec.RsaPkcs1Enc.decryptApi.artifact AArch64.target {
      suffix := Emit.qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      code := Impl.RsaPkcs1Enc.AArch64.Decrypt.code (HH h) (privOf c).name (privOf c).code
      stack := decStack (privOf c)
      verified := dec_verified h (privOf c) (dec_sat c)
      features := h.features ++ c.features.filter (!h.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPkcs1Enc
