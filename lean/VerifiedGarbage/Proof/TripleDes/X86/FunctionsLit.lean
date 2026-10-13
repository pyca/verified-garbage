module

public import VerifiedGarbage.Proof.TripleDes.X86.RoundLit
meta import VerifiedGarbage.Proof.TripleDes.X86.RoundLit
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
meta import VerifiedGarbage.Impl.TripleDes.X86.Ecb
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

materialize_value Impl.TripleDes.X86.roundBody
materialize_value Impl.TripleDes.X86.blockLoad
materialize_value Impl.TripleDes.X86.finalSave

/-! The functions. -/

materialize_code Impl.TripleDes.X86.encryptBlock
materialize_code Impl.TripleDes.X86.decryptBlock
materialize_code Impl.TripleDes.X86.Key.expandKey
materialize_code Impl.TripleDes.X86.Ecb.encrypt
materialize_code Impl.TripleDes.X86.Ecb.decrypt

end VG
