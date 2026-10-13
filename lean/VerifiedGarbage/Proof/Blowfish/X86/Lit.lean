module

public import VerifiedGarbage.Impl.Blowfish.X86
meta import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! Literal code keeps the unrolled S-box scans cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Blowfish.X86
materialize_code encrypt
materialize_code decrypt
end VG.Impl.Blowfish.X86
