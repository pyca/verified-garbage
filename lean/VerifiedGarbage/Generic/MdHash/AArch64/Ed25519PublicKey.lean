module

public import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Verified
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Ed25519PublicKey

def artifacts (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
  { Spec.Ed25519.publicKeyApi with
    name := Spec.Ed25519.publicKeyApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Ed25519.publicKeyApi.doc
    code := Impl.Ed25519.AArch64.PublicKey.code v.code v.suffix
    consts := Impl.Ed25519.AArch64.combConsts
    contract := Spec.Ed25519.publicKeyContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts) 352
    stack := 352
    verified := Proof.Ed25519.AArch64.PublicKey.publicKey_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MdHash.AArch64.Ed25519PublicKey
