module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RC2 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc2.PPC64LE

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.init
    stack := 608
    verified := Proof.Rc2.PPC64LE.Stream.init_framed },
  Spec.Rc2.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.encrypt
    stack := 544
    verified := Proof.Rc2.PPC64LE.Cbc.encryptChained_framed },
  Spec.Rc2.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.decrypt
    stack := 544
    verified := Proof.Rc2.PPC64LE.Cbc.decryptChained_framed }]

end VG.Artifacts.Rc2.PPC64LE
