module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarBaseOk
public import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # Ed448 public-key derivation on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Ed448PublicKey.X86

open VG.X86

def artifacts : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact X86.target {
    code := Impl.Ed448.X86.PublicKey.code Impl.Ed448.X86.scalarBase
    stack := 280
    verified := Proof.Ed448.X86.PublicKey.publicKey_verified Proof.Ed448.X86.scalarBase_calleeOk }]

end VG.Artifacts.Ed448PublicKey.X86
