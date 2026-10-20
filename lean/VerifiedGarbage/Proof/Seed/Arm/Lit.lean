module

public import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-!
# SEED on Arm: the code as literals

The code of the key expansion and of ECB in both directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again in
each of them.
Not flattened (`materialize_flat_code`): its unfolding measured slower here.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

materialize_code expandKeyCode := Impl.Seed.Arm.expandKey
materialize_code ecbEncrypt := Impl.Seed.Arm.ecb .encrypt
materialize_code ecbDecrypt := Impl.Seed.Arm.ecb .decrypt

end VG.Proof.Seed.Arm
