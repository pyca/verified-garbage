import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rc4.X86.Frame

/-! # Raw RC4 on baseline x86 -/
namespace VG.Artifacts.Rc4.X86

def artifacts : List Artifact := [
  { Spec.Rc4.initApi with
    target := X86.target
    doc := Spec.Rc4.initApi.doc (notes := [
      "Secret-indexed table operations visit every doubleword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`. Our caller's `ebx`, \
       `esi`, `edi` and `ebp` are saved in a 64-byte working space on the stack, which is \
       zeroed before returning."])
    code := Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.init
    contract := Spec.Rc4.initContract X86.abi 84
    stack := 84
    verified := Proof.Rc4.X86.init_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc4.applyApi with
    target := X86.target
    doc := Spec.Rc4.applyApi.doc (notes := [
      "Secret-indexed table operations visit every doubleword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`. Our caller's `ebx`, \
       `esi`, `edi` and `ebp` are saved in a 64-byte working space on the stack, and `j` is \
       kept there during each keystream lookup. The working space is zeroed before returning."])
    code := Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.apply
    contract := Spec.Rc4.applyContract X86.abi 84
    stack := 84
    verified := Proof.Rc4.X86.apply_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Rc4.X86
