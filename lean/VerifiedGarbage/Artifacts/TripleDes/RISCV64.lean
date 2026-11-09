module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit

/-! # Triple DES on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDes.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Key.expandKey
    verified := Proof.TripleDes.RISCV64.Key.verified },
  Spec.TripleDes.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Bitslice.encrypt
    stack := 1056
    verified := Proof.TripleDes.RISCV64.Bitsliced.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Bitslice.decrypt
    stack := 1056
    verified := Proof.TripleDes.RISCV64.Bitsliced.decrypt_verified }]

end VG.Artifacts.TripleDes.RISCV64
