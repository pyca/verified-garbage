module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.ModulusCheckMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub


/-! # Shared bounded comparisons for ARMv7 RSA modulus validation -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (bounded_sub_sign parity_word threshold_word modulusCheck_value)
end VG.Proof.Bignum.Arm
