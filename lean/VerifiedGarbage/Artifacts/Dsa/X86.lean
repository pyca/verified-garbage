module

public import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
public import VerifiedGarbage.Proof.Dsa.X86.DerivingVerified
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyVerified
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicVerified
public import VerifiedGarbage.Proof.Dsa.X86.RandomSignInstance
public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Init
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA key generation, signing with a sampled nonce, verification, and the start of the parameter search, on baseline i686 -/

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
  Spec.Dsa.validatePublicKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Prevalidated.validate
    verified := Proof.Dsa.X86.validating_verified
    stack := 108 },
  Spec.Dsa.verifyPrevalidatedApi.artifact X86.target {
    code := Impl.Dsa.X86.Prevalidated.verify
    verified := Proof.Dsa.X86.prevalidated_verified
    stack := 108 },
  Spec.Dsa.parameterInitApi.artifact X86.target {
    code := Impl.Dsa.X86.Generation.init
    verified := Proof.Dsa.X86.Generation.Init.init_verified }]

end VG.Artifacts.Dsa.X86
