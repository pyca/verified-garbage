module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SearchInit
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSA key generation (FIPS 186-5 A.1.3) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.X86_64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact X86_64.target {
    code := Impl.RsaKeyGen.X86_64.Key.code
    verified := Proof.RsaKeyGen.X86_64.Key.key_verified },
  Spec.RsaKeyGen.primeInitApi.artifact X86_64.target {
    code := Impl.RsaKeyGen.X86_64.SearchInit.init
    verified := Proof.RsaKeyGen.X86_64.SearchInit.init_verified }]

end VG.Artifacts.RsaKeyGen.X86_64
