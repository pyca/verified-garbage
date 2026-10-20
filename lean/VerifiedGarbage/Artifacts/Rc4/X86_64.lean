module

public import VerifiedGarbage.Proof.Rc4.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.X86_64.Lit

/-! # Raw RC4 on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rc4.X86_64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact X86_64.target {
    notes := [
      "Secret-indexed table operations visit every quadword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`."]
    code := Impl.Rc4.X86_64.init
    verified := Proof.Rc4.X86_64.init_verified },
  Spec.Rc4.applyApi.artifact X86_64.target {
    notes := [
      "Secret-indexed table operations visit every quadword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`."]
    code := Impl.Rc4.X86_64.apply
    verified := Proof.Rc4.X86_64.apply_verified }]

end VG.Artifacts.Rc4.X86_64
