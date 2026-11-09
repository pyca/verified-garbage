module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Block
public import VerifiedGarbage.Proof.Rc2.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit

/-! # RC2 on RISC-V -/

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
  Spec.Rc2.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt
    stack := 512
    verified := Proof.Rc2.RISCV64.Cbc.encryptChained_framed },
  Spec.Rc2.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt
    stack := 512
    verified := Proof.Rc2.RISCV64.Cbc.decryptChained_framed }]

end VG.Artifacts.Rc2.RISCV64
