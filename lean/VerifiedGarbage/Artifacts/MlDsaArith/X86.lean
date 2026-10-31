module

public import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-DSA (FIPS 204) on x86: the arithmetic of polynomials

The functions call no other one, and save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaArith.X86

def artifacts : List Artifact := [
  Spec.MlDsa.nttApi.artifact X86.target {
    code := Impl.MlDsa.X86.Arith.ntt
    stack := 16
    verified := Proof.MlDsa.X86.Arith.NttFwd.verified },
  Spec.MlDsa.nttInvApi.artifact X86.target {
    code := Impl.MlDsa.X86.Arith.nttInv
    stack := 16
    verified := Proof.MlDsa.X86.Arith.NttInvP.verified },
  Spec.MlDsa.mulApi.artifact X86.target {
    code := Impl.MlDsa.X86.Arith.mul
    stack := 16
    verified := Proof.MlDsa.X86.Arith.mul_verified },
  Spec.MlDsa.mulAddApi.artifact X86.target {
    code := Impl.MlDsa.X86.Arith.mulAdd
    stack := 16
    verified := Proof.MlDsa.X86.Arith.mulAdd_verified },
  Spec.MlDsa.addApi.artifact X86.target {
    code := Impl.MlDsa.X86.Arith.add
    stack := 16
    verified := Proof.MlDsa.X86.Arith.add_verified },
  Spec.MlDsa.subApi.artifact X86.target {
    code := Impl.MlDsa.X86.Arith.sub
    stack := 16
    verified := Proof.MlDsa.X86.Arith.sub_verified }]

end VG.Artifacts.MlDsaArith.X86
