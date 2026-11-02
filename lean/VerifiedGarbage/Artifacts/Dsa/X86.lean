module

public import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
public import VerifiedGarbage.Proof.Dsa.X86.DerivingVerified
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyVerified
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Registration
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicVerified
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateVerified
public import VerifiedGarbage.Proof.Dsa.X86.RandomSignInstance
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA key generation, signing with a sampled nonce, and verification, on baseline i686 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86

def artifacts : List Artifact := [
  Spec.Dsa.generateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Comb.generateKey
    verified := Proof.Dsa.X86.Comb.key_verified
    stack := 232 },
  Spec.Dsa.deriveKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Generate.deriveKey
    verified := Proof.Dsa.X86.deriving_verified
    stack := 108 },
  Spec.Dsa.randomSignApi.artifact X86.target {
    code := Impl.Dsa.X86.RandomSign.code Proof.Dsa.X86.signFn.name Proof.Dsa.X86.signFn.code
    verified := Proof.Dsa.X86.randomSigning_verified
    stack := 232 },
  Spec.Dsa.verifyApi.artifact X86.target {
    code := Impl.Dsa.X86.Entry.operation false
    verified := Proof.Dsa.X86.verifying_verified
    stack := 108 }]

end VG.Artifacts.Dsa.X86
