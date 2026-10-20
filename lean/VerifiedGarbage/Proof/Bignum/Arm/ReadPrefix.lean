module
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.ReadPrefix


/-! # Shared prefix-read lemmas for ARMv7 RSA array exports -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (read_prefix read_prefix_value)
end VG.Proof.Bignum.Arm
