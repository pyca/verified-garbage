module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegionsSub


/-! # Shared prefix-read lemmas for ARMv7 RSA array exports -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (read_prefix read_prefix_value)
end VG.Proof.Bignum.Arm
