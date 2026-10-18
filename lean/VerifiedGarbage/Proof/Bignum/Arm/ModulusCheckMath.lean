module

public import VerifiedGarbage.Proof.Bignum.ModulusCheckMath

/-! # Shared bounded comparisons for ARMv7 RSA modulus validation -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (bounded_sub_sign parity_word threshold_word modulusCheck_value)
end VG.Proof.Bignum.Arm
