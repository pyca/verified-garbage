module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Safety
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Inverse
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Safety

/-! # Native RSA key generation on baseline i686 -/

@[expose] public section
namespace VG.Artifacts.RsaKeyGen.X86

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact X86.target {
    stack := 68
    notes := ["Shared runtime-width division with native paired-word multiplication; each inversion calls \
      `vg_rsa_keygen_inverse` at its own width. The factors are \
      ordered by masks, and their predecessors' LCM uses common halving and a prime-width binary \
      GCD. For an odd public exponent, the private exponent uses a 64-bit inverse of L mod e \
      modulo e and a small correction quotient; even exponents use a modulus-width inverse. \
      The CRT inverse is prime-width. Final checks mask all seven outputs; control flow depends \
      only on public widths, the public exponent and the released retry status."]
    code := Impl.RsaKeyGen.X86.KeyRuntime.code
    verified := Proof.RsaKeyGen.X86.KeyRuntime.verified
    spSafe := Proof.RsaKeyGen.X86.KeyRuntime.code_sp },
  Spec.RsaKeyGen.inverseApi.artifact X86.target {
    stack := 36
    notes := ["`KeyRt.inverse` on the caller's working space, in the frame of the registers cdecl \
      preserves, at the width of its length argument."]
    code := Impl.RsaKeyGen.X86.Inverse.code
    verified := Proof.RsaKeyGen.X86.Inverse.verified
    spSafe := Proof.RsaKeyGen.X86.Inverse.code_sp }]

end VG.Artifacts.RsaKeyGen.X86
