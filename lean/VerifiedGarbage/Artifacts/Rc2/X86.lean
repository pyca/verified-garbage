module

public import VerifiedGarbage.Proof.Rc2.X86.Key
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.X86.Stream.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit

/-! # RC2 artifacts on baseline x86 -/

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
    verified := Proof.Rc2.X86.Stream.decryptUpdate_framed }]

end VG.Artifacts.Rc2.X86
