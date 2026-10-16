module

import VerifiedGarbage.Proof.TripleDes.Arm.Lit
meta import VerifiedGarbage.Proof.TripleDes.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
meta import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

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
