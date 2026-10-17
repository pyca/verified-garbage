module

public import VerifiedGarbage.Proof.Dsa.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! DSA signing with a supplied nonce, and verification, on baseline i686. -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86

def artifacts : List Artifact := [
  Spec.Dsa.signApi.artifact X86.target {
    notes := ["Each supported (p, q) width has its own code, chosen by the public lengths. \
      Arithmetic loops over the words of a runtime-modulus Montgomery workspace in `scratch`; \
      exponentiation uses fixed-iteration square-and-multiply with a masked selection. \
      The digest's prefix, clamped to q's actual byte width, is reduced byte by byte. \
      Validation accumulates a mask; every failure zeros the entire output. Callee-saved \
      registers reside in `scratch`."]
    code := Impl.Dsa.X86.Entry.operation true
    verified := Proof.Dsa.X86.signing_verified
    stack := 20 },
  Spec.Dsa.verifyApi.artifact X86.target {
    notes := ["Each supported (p, q) width has its own code, chosen by the public lengths. \
      Arithmetic loops over the words of a runtime-modulus Montgomery workspace in `scratch`. \
      Signature scalars and the digest do not affect the leakage trace. Callee-saved \
      registers reside in `scratch`."]
    code := Impl.Dsa.X86.Entry.operation false
    verified := Proof.Dsa.X86.verifying_verified
    stack := 20 }]

end VG.Artifacts.Dsa.X86
