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

/-! DSA signing with a supplied or a sampled nonce, and verification, on baseline i686. -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86

def combPrepare (n e : Nat) (h : Proof.Dsa.X86.Comb.Supported n e) : Artifact :=
  (Spec.Dsa.FixedBaseComb.prepareApi (Impl.Dsa.X86.Comb.layout n e)).artifact X86.target {
    code := Impl.Dsa.X86.Comb.body true n e
    verified := Proof.Dsa.X86.Comb.public_verified h
    stack := 20
    spSafe := Proof.Dsa.X86.Comb.body_spSafe h true }

def combPower (n e : Nat) (h : Proof.Dsa.X86.Comb.Supported n e) : Artifact :=
  (Spec.Dsa.FixedBaseComb.powerApi (Impl.Dsa.X86.Comb.layout n e)).artifact X86.target {
    code := Impl.Dsa.X86.Comb.body false n e
    verified := Proof.Dsa.X86.Comb.private_verified h
    stack := 20
    spSafe := Proof.Dsa.X86.Comb.body_spSafe h false }

def artifacts : List Artifact := [
  Spec.Dsa.generateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Comb.generateKey
    verified := Proof.Dsa.X86.Comb.key_verified
    stack := 232 },
  Spec.Dsa.deriveKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Generate.deriveKey
    verified := Proof.Dsa.X86.deriving_verified
    stack := 108 },
  Spec.Dsa.checkParametersApi.artifact X86.target {
    code := Impl.Dsa.X86.Generate.checkParameters
    verified := Proof.Dsa.X86.checking_verified
    stack := 108 },
  Spec.Dsa.randomSignApi.artifact X86.target {
    code := Impl.Dsa.X86.RandomSign.code Proof.Dsa.X86.signFn.name Proof.Dsa.X86.signFn.code
    verified := Proof.Dsa.X86.randomSigning_verified
    stack := 232 },
  Spec.Dsa.signApi.artifact X86.target {
    code := Impl.Dsa.X86.Entry.operation true
    verified := Proof.Dsa.X86.signing_verified
    stack := 108 },
  Spec.Dsa.verifyApi.artifact X86.target {
    code := Impl.Dsa.X86.Entry.operation false
    verified := Proof.Dsa.X86.verifying_verified
    stack := 108 },
  combPrepare 16 5 Proof.Dsa.X86.Comb.supported_16_5,
  combPower 16 5 Proof.Dsa.X86.Comb.supported_16_5,
  combPrepare 32 5 Proof.Dsa.X86.Comb.supported_32_5,
  combPower 32 5 Proof.Dsa.X86.Comb.supported_32_5,
  combPrepare 32 7 Proof.Dsa.X86.Comb.supported_32_7,
  combPower 32 7 Proof.Dsa.X86.Comb.supported_32_7,
  combPrepare 32 8 Proof.Dsa.X86.Comb.supported_32_8,
  combPower 32 8 Proof.Dsa.X86.Comb.supported_32_8,
  combPrepare 48 8 Proof.Dsa.X86.Comb.supported_48_8,
  combPower 48 8 Proof.Dsa.X86.Comb.supported_48_8]

end VG.Artifacts.Dsa.X86
