module

import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
meta import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
public import VerifiedGarbage.Impl.TripleDes.AArch64.Permutation
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Permutation
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

materialize_code initialPermutation
materialize_code finalPermutation
materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.AArch64
