module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarBaseOk
public import VerifiedGarbage.Proof.Ed448.X86.SignCached.Verified
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 signing with a cached public key on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Ed448SignCached.X86

open VG.X86

def artifacts : List Artifact := [
  Spec.Ed448.signCachedApi.artifact X86.target {
    code := Impl.Ed448.X86.SignCached.code Impl.Ed448.X86.scalarBase
    stack := 280
    verified := Proof.Ed448.X86.SignCached.signCached_verified Proof.Ed448.X86.scalarBase_calleeOk }]

end VG.Artifacts.Ed448SignCached.X86
