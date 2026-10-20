module
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.ExponentCheckMath


@[expose] public section
namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (exponentHigh exponentHigh_step exponentLow_step exponentHigh_bound exponent_valid_words)
end VG.Proof.Bignum.Arm
