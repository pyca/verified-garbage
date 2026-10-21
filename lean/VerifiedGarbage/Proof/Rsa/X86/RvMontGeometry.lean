module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Montgomery arithmetic within the prime-recovery workspace

The callee `vg_rsa_mont_mul_at` has the four narrow arrays from `mAcc` (16
to 19) for its own; the modulus is in `mBase`, and its inverse in the header
word `sInv`. The operands lie below or above the callee's range
(`MontIndex`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

/-- A narrow array apart from the callee's range. -/
abbrev MontIndex (j : Nat) : Prop := j < nArr ∧ (j < mAcc ∨ mAcc + 4 ≤ j)

theorem words_eq_num {g : Geo} {m : Mem} {j : Nat}
    (h : num m g.B g.w j < 2 ^ (64 * g.n)) :
    wordsVal m g.B (arr g.w j) g.n = num m g.B g.w j := by
  rw [wordsVal_eq_val32]
  apply VG.Proof.Dsa.val32_prefix_of_lt
  · change 2 * g.n ≤ 2 * g.n + 2; omega
  · simpa only [← Nat.mul_assoc] using h

/-- The modulus `m` in `mBase`, below `R = 2^(64 n)`, and `-m⁻¹ mod 2³²` in `sInv`. -/
structure MR (g : Geo) (m : Nat) (s : State) : Prop where
  positive : 0 < g.n
  modulus : num s.mem g.B g.w mBase = m
  bound : m < 2 ^ (64 * g.n)
  inverse : (m * w32 s.mem g.B sInv + 1) % 2 ^ 32 = 0

end VG.Proof.Rsa.X86.Recover
