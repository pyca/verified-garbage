module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication in the RSA working space on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaMont.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact PPC64LE.target {
    notes := ["Finely integrated operand scanning in radix 2^64: each round computes `t_j + a_i b_j + \
        u m_j` and the two carries for each word in one pass over the accumulator, the carries through \
        XER's CA (`addc`, `addze`), four words at a time after `(w - 1) mod 4` single ones, with \
        `-m⁻¹ mod 2^64` computed from the header's `-m⁻¹ mod 2^32` by a step of Newton's iteration; \
        then the subtraction of `m`, word by word with the borrow in CA (`subfc`, `subfe`), selected \
        with a mask. The nonvolatile registers it uses are saved in a 112-byte stack frame."]
    code := Impl.StackScratch.PPC64LE.withStackScratch 112 .r8 Impl.Bignum.PPC64LE.mul
    stack := 112
    verified := Proof.Bignum.PPC64LE.mul_verified }]

end VG.Artifacts.RsaMont.PPC64LE
