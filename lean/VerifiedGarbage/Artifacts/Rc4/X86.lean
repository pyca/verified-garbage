module

public import VerifiedGarbage.Proof.Rc4.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.X86.Lit

/-! # Raw RC4 on baseline x86 -/

@[expose] public section

namespace VG.Artifacts.Rc4.X86

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact X86.target {
    notes := [
      "Secret-indexed table operations visit every doubleword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`. Our caller's `ebx`, \
       `esi`, `edi` and `ebp` are saved in a 64-byte working space on the stack, which is \
       zeroed before returning."]
    code := Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.init
    stack := 84
    verified := Proof.Rc4.X86.init_framed },
  Spec.Rc4.applyApi.artifact X86.target {
    notes := [
      "Secret-indexed table operations visit every doubleword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`. Our caller's `ebx`, \
       `esi`, `edi` and `ebp` are saved in a 64-byte working space on the stack, and `j` is \
       kept there during each keystream lookup. The working space is zeroed before returning."]
    code := Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.apply
    stack := 84
    verified := Proof.Rc4.X86.apply_framed }]

end VG.Artifacts.Rc4.X86
