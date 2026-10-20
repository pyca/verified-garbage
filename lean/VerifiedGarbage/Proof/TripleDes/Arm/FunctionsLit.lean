module

import VerifiedGarbage.Proof.TripleDes.Arm.Lit
meta import VerifiedGarbage.Proof.TripleDes.Arm.Lit
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
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

@[expose] public section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.Arm.roundBody
materialize_value Impl.TripleDes.Arm.blockLoad

/-! The functions. -/

materialize_code Impl.TripleDes.Arm.encryptBlock
materialize_code Impl.TripleDes.Arm.decryptBlock
materialize_code Impl.TripleDes.Arm.Key.expandKey
materialize_code Impl.TripleDes.Arm.Ecb.encrypt
materialize_code Impl.TripleDes.Arm.Ecb.decrypt

end VG
