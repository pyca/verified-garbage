module

import VerifiedGarbage.Impl.Dsa.X86_64.Random
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.TCB.Artifact

/-! Byte-subtraction lemma used by the scalar range check. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64

/-- For byte-sized operands (including an incoming borrow), the high bit of
64-bit subtraction is precisely the unsigned borrow. -/
theorem random_byte_borrow (a b : BitVec 64) (ha : a.toNat ≤ 255) (hb : b.toNat ≤ 256) :
    ((a - b) >>> 63).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> omega

open VG VG.X86_64 VG.Proof.MlKem.X86_64

end VG.Proof.Dsa.X86_64
