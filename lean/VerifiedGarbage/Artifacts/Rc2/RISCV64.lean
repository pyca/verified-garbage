module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Block
public import VerifiedGarbage.Proof.Rc2.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit

/-! # RC2 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rc2.RISCV64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.init
    stack := 608
    verified := Proof.Rc2.RISCV64.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.encryptUpdate
    stack := 608
    verified := Proof.Rc2.RISCV64.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.decryptUpdate
    stack := 608
    verified := Proof.Rc2.RISCV64.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.RISCV64.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.RISCV64.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.expandKey
    stack := 0
    verified := Proof.Rc2.RISCV64.key_verified },
  Spec.Rc2.encryptBlockApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.encryptBlock
    stack := 0
    verified := Proof.Rc2.RISCV64.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.decryptBlock
    stack := 0
    verified := Proof.Rc2.RISCV64.decrypt_verified }]

end VG.Artifacts.Rc2.RISCV64
