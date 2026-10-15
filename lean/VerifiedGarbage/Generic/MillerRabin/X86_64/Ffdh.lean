module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Backend

/-! # Emit FFDH domain operations for every shared arithmetic backend -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.Ffdh

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  { Spec.Ffdh.checkPublicApi with
    name := Spec.Ffdh.checkPublicApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ffdh.checkPublicApi.doc
      (notes := ["The verified range and optional subgroup checks use fixed four-bit windows \
        with the selected Montgomery backend. Domain bytes and the public key are public \
        under the shared contract."])
    code := Proof.Ffdh.X86_64.CheckPublic.publicCode v
    contract := Spec.Ffdh.checkPublicContract X86_64.abi
    verified := by exact Proof.Ffdh.X86_64.CheckPublic.publicCode_verified v
    spSafe := by exact Proof.Ffdh.X86_64.CheckPublic.publicCode_sp v
    features := v.features },
  { Spec.Ffdh.exchangeApi with
    name := Spec.Ffdh.exchangeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ffdh.exchangeApi.doc
      (notes := ["The selected Montgomery backend and fixed four-bit windows process every \
        supplied scalar byte. The result is masked to zero for a degenerate shared value."])
    code := Proof.Ffdh.X86_64.Exchange.exchangeCode v
    contract := Spec.Ffdh.exchangeContract X86_64.abi
    verified := by exact Proof.Ffdh.X86_64.Exchange.exchangeCode_verified v
    spSafe := by exact Proof.Ffdh.X86_64.Exchange.exchangeCode_sp v
    features := v.features },
  { Spec.Ffdh.checkPrivateApi with
    name := Spec.Ffdh.checkPrivateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ffdh.checkPrivateApi.doc
      (notes := ["The scalar bound and the public-value equality are checked in verified code. \
        Powers of a checked generator remain in its q subgroup, so the generated power \
        needs only its range check. Fixed four-bit windows use the selected Montgomery backend."])
    code := Proof.Ffdh.X86_64.CheckPrivate.privateCode v
    contract := Spec.Ffdh.checkPrivateContract X86_64.abi
    verified := by exact Proof.Ffdh.X86_64.CheckPrivate.privateCode_verified v
    spSafe := by exact Proof.Ffdh.X86_64.CheckPrivate.privateCode_sp v
    features := v.features },
  { Spec.Ffdh.generateKeyApi with
    name := Spec.Ffdh.generateKeyApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Ffdh.generateKeyApi.doc
      (notes := ["Scalar masking, scalar-range rejection, generator exponentiation, and \
        degenerate-public-value rejection run in verified code. Fixed four-bit windows \
        use the public bound's significant byte width and the selected Montgomery backend."])
    code := Proof.Ffdh.X86_64.GenerateKey.generateCode v
    contract := Spec.Ffdh.generateKeyContract X86_64.abi
    verified := by exact Proof.Ffdh.X86_64.GenerateKey.generateCode_verified v
    spSafe := by exact Proof.Ffdh.X86_64.GenerateKey.generateCode_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.Ffdh
