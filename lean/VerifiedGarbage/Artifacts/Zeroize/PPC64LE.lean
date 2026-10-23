module

public import VerifiedGarbage.Proof.Zeroize.PPC64LE

@[expose] public section

namespace VG.Artifacts.Zeroize.PPC64LE
open VG.PPC64LE

def artifacts : List Artifact := [
  { Spec.Zeroize.zeroizeApi with
    target := target
    doc := Spec.Zeroize.zeroizeApi.doc
    code := Impl.Zeroize.PPC64LE.zeroize
    contract := Spec.Zeroize.zeroizeContract abi
    verified := Proof.Zeroize.PPC64LE.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]
end VG.Artifacts.Zeroize.PPC64LE
