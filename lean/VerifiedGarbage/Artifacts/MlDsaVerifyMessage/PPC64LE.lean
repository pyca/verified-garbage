module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: verifying messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessage.PPC64LE

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r22`–`r30` it uses and its return address in the last 1 KiB \
    of `scratch`, and pushes nothing of its own; the functions it calls use the 96 bytes of stack \
    below the stack pointer. It computes the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, and calls the \
    verification function on it, which uses the rest of `scratch`."]

def artifacts : List Artifact := [
  Spec.MlDsa.verifyMessage44Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Message.verifyMessage Spec.MlDsa.verify44Api.name
      Impl.MlDsa.PPC64LE.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessage44_verified },
  Spec.MlDsa.verifyMessage65Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Message.verifyMessage Spec.MlDsa.verify65Api.name
      Impl.MlDsa.PPC64LE.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessage65_verified },
  Spec.MlDsa.verifyMessage87Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Message.verifyMessage Spec.MlDsa.verify87Api.name
      Impl.MlDsa.PPC64LE.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessage87_verified }]

end VG.Artifacts.MlDsaVerifyMessage.PPC64LE
