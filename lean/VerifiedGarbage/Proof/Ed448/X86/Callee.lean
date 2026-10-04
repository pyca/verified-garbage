import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 on x86 (32-bit): what the complete operations assume of a callee

The complete operations call `vg_ed448_scalar_base` and
`vg_ed448_verify_equation` through code they take as a parameter, and are
proven for any code meeting `CalleeOk` of its local contract
(`Proof/Ed448/X86/BaseLocal.lean`, `VerifyLocal.lean`): correct and
constant time under it, never writing `esp`, and using at most the 20 bytes
of stack below its return address that the frame of a complete operation
leaves it.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86

structure CalleeOk (k : Contract isa) (c : Prog isa) : Prop where
  ok : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  nosp : NoSp c
  stack : stackUse c ≤ 20

end VG.Proof.Ed448.X86
