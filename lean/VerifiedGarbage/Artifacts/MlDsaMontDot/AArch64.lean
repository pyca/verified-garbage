import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVerified

namespace VG.Artifacts.MlDsaMontDot.AArch64

def one (n : Nat) (h : n=4∨n=5∨n=7) : Artifact :=
  { Spec.MlDsa.montDotApi n with
    target := AArch64.target
    doc := (Spec.MlDsa.montDotApi n).doc
    code := Impl.MlDsa.AArch64.Optimized.MontDot.dot n
    contract := Spec.MlDsa.montDotContract AArch64.abi n
    verified := Proof.MlDsa.AArch64.Optimized.MontDot.verified h
    spSafe := Code.all_of_forall (fun _=>rfl) _ }

def artifacts : List Artifact := [one 4 (by omega),one 5 (by omega),one 7 (by omega)]

end VG.Artifacts.MlDsaMontDot.AArch64
