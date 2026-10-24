module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: signing messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.PPC64LE

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r22`–`r30` it uses and its return address in the last 1 KiB \
    of `scratch`, and pushes nothing of its own; the functions it calls use the 96 bytes of stack \
    below the stack pointer. It computes the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, and calls the \
    signing function on it, which uses the rest of `scratch`."]

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign44Api.name
      Impl.MlDsa.PPC64LE.Sign.sign44 Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign65Api.name
      Impl.MlDsa.PPC64LE.Sign.sign65 Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact PPC64LE.target {
    notes := notes
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign87Api.name
      Impl.MlDsa.PPC64LE.Sign.sign87 Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.signMessage87_verified }]

end VG.Artifacts.MlDsaSignMessage.PPC64LE
