module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyVerified
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySafety

/-! # Native RSA key generation on baseline i686 -/

@[expose] public section
namespace VG.Artifacts.RsaKeyGen.X86

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact X86.target {
    stack := 36
    notes := ["Native paired-word multiplication and fixed-schedule arithmetic. The factors are \
      ordered by masks, and their predecessors' LCM uses common halving and a prime-width binary \
      GCD. For an odd public exponent, the private exponent uses a 64-bit inverse of L mod e \
      modulo e and a small correction quotient; even exponents use a modulus-width inverse. \
      The CRT inverse is prime-width. Final checks mask all seven outputs; control flow depends \
      only on public widths, the public exponent and the released retry status."]
    code := Impl.RsaKeyGen.X86.Key.code
    verified := by exact Proof.RsaKeyGen.X86.Key.verified
    spSafe := by exact Proof.RsaKeyGen.X86.Key.code_sp }]

end VG.Artifacts.RsaKeyGen.X86
