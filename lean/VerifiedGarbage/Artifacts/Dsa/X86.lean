module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Instance
public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyVerified
import VerifiedGarbage.Proof.Dsa.X86.Comb.Registration
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
    notes := ["Checks the domain once and retains RSA's five-tooth comb for the sampled private exponent. \
      Public-modulus setup accelerates the subgroup check; private exponentiation uses a fixed schedule \
      and masked selection. Every exit clears the sampled scalar; failure clears the output and reports \
      exact tape consumption. The checker and prevalidated derivation are internal bodies."]
    code := Impl.Dsa.X86.Comb.generateKey
    verified := Proof.Dsa.X86.Comb.key_verified
    stack := 156 },
  Spec.Dsa.deriveKeyApi.artifact X86.target {
    notes := ["Checks the generator subgroup once and derives the public key with fixed-iteration \
      Montgomery exponentiation. The public key subgroup identity follows from the generator \
      check. A mask clears every output component on failure; saved registers reside in scratch."]
    code := Impl.Dsa.X86.Generate.deriveKey
    verified := Proof.Dsa.X86.deriving_verified
    stack := 32 },
  Spec.Dsa.checkParametersApi.artifact X86.target {
    notes := ["Uses the signer's public-width dispatch and Montgomery arithmetic. \
      The domain's generator range and subgroup power are checked once; the mask \
      also checks that q divides p-1. Callee-saved registers reside in scratch."]
    code := Impl.Dsa.X86.Generate.checkParameters
    verified := Proof.Dsa.X86.checking_verified
    stack := 32 },
  Spec.Dsa.randomSignApi.artifact X86.target {
    notes := ["Rejection sampling and signing retries are verified against the bounded \
      random-tape specification; each signing attempt calls `vg_dsa_sign`. Every failure zeros \
      the entire output. Callee-saved registers and the loop's state reside in a stack frame."]
    code := Impl.Dsa.X86.RandomSign.code Proof.Dsa.X86.signFn.name Proof.Dsa.X86.signFn.code
    verified := Proof.Dsa.X86.randomSigning_verified
    stack := 156 },
  Spec.Dsa.signApi.artifact X86.target {
    notes := ["Each supported (p, q) width has its own code, chosen by the public lengths. \
      Arithmetic loops over the words of a runtime-modulus Montgomery workspace in `scratch`; \
      exponentiation uses fixed-iteration square-and-multiply with a masked selection. \
      The digest's prefix, clamped to q's actual byte width, is reduced byte by byte. \
      Validation accumulates a mask; every failure zeros the entire output. Callee-saved \
      registers reside in `scratch`."]
    code := Impl.Dsa.X86.Entry.operation true
    verified := Proof.Dsa.X86.signing_verified
    stack := 32 },
  Spec.Dsa.verifyApi.artifact X86.target {
    notes := ["Each supported (p, q) width has its own code, chosen by the public lengths. \
      Arithmetic loops over the words of a runtime-modulus Montgomery workspace in `scratch`. \
      Signature scalars and the digest do not affect the leakage trace. Callee-saved \
      registers reside in `scratch`."]
    code := Impl.Dsa.X86.Entry.operation false
    verified := Proof.Dsa.X86.verifying_verified
    stack := 32 },
  combPrepare 16 5 (Proof.Dsa.X86.Comb.supported 16 5),
  combPower 16 5 (Proof.Dsa.X86.Comb.supported 16 5),
  combPrepare 32 5 (Proof.Dsa.X86.Comb.supported 32 5),
  combPower 32 5 (Proof.Dsa.X86.Comb.supported 32 5),
  combPrepare 32 7 (Proof.Dsa.X86.Comb.supported 32 7),
  combPower 32 7 (Proof.Dsa.X86.Comb.supported 32 7),
  combPrepare 32 8 (Proof.Dsa.X86.Comb.supported 32 8),
  combPower 32 8 (Proof.Dsa.X86.Comb.supported 32 8),
  combPrepare 48 8 (Proof.Dsa.X86.Comb.supported 48 8),
  combPower 48 8 (Proof.Dsa.X86.Comb.supported 48 8)]

end VG.Artifacts.Dsa.X86
