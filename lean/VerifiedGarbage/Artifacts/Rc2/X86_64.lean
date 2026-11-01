module

public import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.X86_64.Key
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit

/-! # RC2 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rc2.X86_64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.init
    stack := 600
    verified := Proof.Rc2.X86_64.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.encryptUpdate
    stack := 608
    verified := Proof.Rc2.X86_64.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.decryptUpdate
    stack := 608
    verified := Proof.Rc2.X86_64.Stream.decryptUpdate_framed }]

end VG.Artifacts.Rc2.X86_64
