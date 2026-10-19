module

import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
meta import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Block
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.AArch64.roundBody
materialize_value Impl.TripleDes.AArch64.blockLoad
materialize_value Impl.TripleDes.AArch64.blockStore

/-! The functions. -/

materialize_code Impl.TripleDes.AArch64.encryptBlock
materialize_code Impl.TripleDes.AArch64.decryptBlock
materialize_code Impl.TripleDes.AArch64.Key.expandKey

end VG
