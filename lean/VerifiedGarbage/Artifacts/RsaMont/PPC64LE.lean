module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication in the RSA working space on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaMont.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact PPC64LE.target {
    notes := ["Coarsely integrated operand scanning in radix 2^64, the carries through XER's CA \
        (`addc`, `addze`), with `-m⁻¹ mod 2^64` computed from the header's `-m⁻¹ mod 2^32` by a step \
        of Newton's iteration; then the subtraction of `m`, on 32-bit digits with the borrow in the \
        sign bit of each difference, selected with a mask. The nonvolatile registers it uses are \
        saved in a 112-byte stack frame."]
    code := Impl.StackScratch.PPC64LE.withStackScratch 112 .r8 Impl.Bignum.PPC64LE.mul
    stack := 112
    verified := Proof.Bignum.PPC64LE.mul_verified }]

end VG.Artifacts.RsaMont.PPC64LE
