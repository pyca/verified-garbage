module

public import VerifiedGarbage.Proof.Dsa.X86.RandomSignInstance
public import VerifiedGarbage.Proof.Framework.Registration

/-! DSA signing with a supplied or a sampled nonce, and verification, on baseline i686. -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86

def artifacts : List Artifact := [
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
    stack := 32 }]

end VG.Artifacts.Dsa.X86
