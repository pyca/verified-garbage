module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit

/-! # Raw RC4 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc4.PPC64LE

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact PPC64LE.target {
    notes := ["The table is visited as 32 doublewords at fixed addresses: a \
      secret-indexed read keeps, with masks, the doubleword and then the byte that hold \
      it, and a write stores every doubleword back XORed with a masked difference, so no \
      address or branch depends on the key, the table or `j`."]
    code := Impl.Rc4.PPC64LE.init
    verified := Proof.Rc4.PPC64LE.init_verified },
  Spec.Rc4.applyApi.artifact PPC64LE.target {
    notes := ["The table is visited as 32 doublewords at fixed addresses: a \
      secret-indexed read keeps, with masks, the doubleword and then the byte that hold \
      it, and a write stores every doubleword back XORed with a masked difference, so no \
      address or branch depends on the table, `j` or the data."]
    code := Impl.Rc4.PPC64LE.apply
    verified := Proof.Rc4.PPC64LE.apply_verified }]

end VG.Artifacts.Rc4.PPC64LE
