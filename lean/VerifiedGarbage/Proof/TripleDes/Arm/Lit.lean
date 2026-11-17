module

public import VerifiedGarbage.Impl.TripleDes.Arm.Permutation
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.Arm.Permutation
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! The key schedule's permutations on ARMv7, as literals. -/

@[expose] public section

namespace VG.Impl.TripleDes.Arm

materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.Arm
