module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified

/-! # Checked private RSA for every ARMv7 CRT variant

The wrapper uses 3440 stack bytes, including the largest nested callee frame.
-/

@[expose] public section
namespace VG.Generic.RsaPrivateCrt.Arm.Rsa
open VG.Proof.Rsa.Arm

def artifacts (v : CrtImpl) : List Artifact := [
  { Spec.Rsa.privateCheckedApi with
    name := privName v
    target := Arm.target
    doc := Spec.Rsa.privateCheckedApi.doc (notes := ["Computes the private CRT result with `" ++ v.name ++
      "` in a private stack buffer, then checks it with `" ++ v.pcName ++ "` and `" ++ v.pdName ++
      "`. The comparison, status selection, masked release, and clearing of the temporary run without secret-dependent branches."])
    code := privCode v
    contract := Spec.Rsa.privateCheckedContract Arm.abi stackBytes
    stack := stackBytes
    verified := code_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]
end VG.Generic.RsaPrivateCrt.Arm.Rsa
