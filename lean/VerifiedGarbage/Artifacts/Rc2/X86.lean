module

public import VerifiedGarbage.Proof.Rc2.X86.Key
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.X86.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit

/-! # RC2 on x86 -/

@[expose] public section

namespace VG.Artifacts.Rc2.X86

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.init
    stack := 632
    verified := Proof.Rc2.X86.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.encryptUpdate
    stack := 648
    verified := Proof.Rc2.X86.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.decryptUpdate
    stack := 648
    verified := Proof.Rc2.X86.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 544 4 128 Impl.Rc2.X86.Cbc.encrypt
    stack := 560
    verified := Proof.Rc2.X86.Cbc.encryptChained_framed },
  Spec.Rc2.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 544 4 128 Impl.Rc2.X86.Cbc.decrypt
    stack := 560
    verified := Proof.Rc2.X86.Cbc.decryptChained_framed }]

end VG.Artifacts.Rc2.X86
