module

public import VerifiedGarbage.Proof.X448.X86.Verified
public import VerifiedGarbage.Proof.X448.X86.Base
import VerifiedGarbage.Proof.X448.X86.Lit
public import VerifiedGarbage.Proof.X448.X86.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # X448 (RFC 7748) on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.X448.X86

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact X86.target {
    code := Impl.Xdh.X86.exchange "vg_x448" Impl.X448.X86.x448 56
    stack := 40
    verified := Proof.X448.X86.Exchange.exchange_verified },
  Spec.X448.x448BaseApi.artifact X86.target {
    code := Impl.X448.X86.x448Base
    stack := 100
    verified := Proof.X448.X86.x448Base_verified }]

end VG.Artifacts.X448.X86
