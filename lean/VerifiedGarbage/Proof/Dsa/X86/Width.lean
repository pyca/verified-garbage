module
public import VerifiedGarbage.Impl.Dsa.X86.Width
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Correctness of the exact-width mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Proof.Ecdsa.X86

theorem widthMask_ok {s : State} {base : Addr} {size n a tmp bits : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hb : 0 < bits) (hbn : bits ≤ 64 * n) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (widthMask n a tmp bits) s fun t =>
      t.gpr .edx = mask32 (2 ^ (bits - 1) ≤ wordsVal s.mem base a n ∧ wordsVal s.mem base a n < 2 ^ bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold widthMask
  refine WP.seq (WP.mono (lessThanConstant_ok hs hn ha ht
    (Nat.pow_lt_pow_right (by decide) (by omega)) hsep) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.seq (wp_logicS (.inr rfl) rfl fun v uv => ?_)
  refine wp_movS rfl fun w uw _ => WP.block_nil ?_
  have Kw : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s w := ((Ku.mono (by decide)).widen uv.keeps).widen uw.keeps
  have Ow : Outside base tmp (8 * n) s.mem w.mem := by rw [uw.mem, uv.mem]; exact Ou
  have Ew : w.gpr .ebx = mask32 (2 ^ (bits - 1) ≤ wordsVal s.mem base a n) := by
    rw [uw.gpr, uv.gpr, Vu]
    simp only [reduceCtorEq, ite_false, mask_not, Nat.not_lt]
  by_cases hsmall : bits < 64 * n
  · rw [ite_eq_left hsmall]
    refine WP.seq (WP.mono (lessThanConstant_ok (hs.of_keeps Kw (by decide)) hn ha ht
      (Nat.pow_lt_pow_right (by decide) hsmall) hsep) fun x ⟨Vx, Kx, Ox⟩ => ?_)
    refine wp_logicS (.inl rfl) rfl fun y uy => ?_
    refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, ((Kw.widen Kx).widen uy.keeps).widen ut.keeps, ?_⟩
    · rw [ut.gpr, uy.gpr, Vx, Kx.1 _ (by decide), Ew,
        Ow.wordsVal hsep (by have := hs.nowrap; omega)]
      simp only [ite_true, mask32_and, and_comm]
    · rw [ut.mem, uy.mem]
      exact Ow.trans Ox
  · rw [ite_eq_right hsmall]
    refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, Kw.widen ut.keeps, ut.mem ▸ Ow⟩
    have eq : bits = 64 * n := by omega
    rw [ut.gpr, Ew, eq]
    simp only [wordsVal_lt s.mem base a n, and_true]

theorem widthMask_bitLength {s : State} {base : Addr} {size n a tmp bits : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hb : 0 < bits) (hbn : bits ≤ 64 * n) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (widthMask n a tmp bits) s fun t =>
      t.gpr .edx = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base a n) = bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  simpa only [VG.Proof.Dsa.bitLength_iff_bounds hb] using widthMask_ok hs hn ha ht hb hbn hsep

theorem optionalWidth_ok {s : State} {base : Addr} {size n a tmp bits : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hb : 0 < bits) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (optionalWidth n a tmp bits) s fun t =>
      t.gpr .edx = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base a n) = bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold optionalWidth
  by_cases hbn : bits ≤ 64 * n
  · rw [ite_eq_left hbn]
    exact widthMask_bitLength hs hn ha ht hb hbn hsep
  · rw [ite_eq_right hbn]
    have hnot : Spec.Dsa.bitLength (wordsVal s.mem base a n) ≠ bits := by
      intro h
      have lower := ((VG.Proof.Dsa.bitLength_iff_bounds hb).mp h).1
      have upper := wordsVal_lt s.mem base a n
      have powers : 2 ^ (64 * n) ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, ut.keeps.mono (by decide), ?_⟩
    · rw [ut.gpr, mask32, ite_eq_right hnot]
    · rw [ut.mem]
      exact Outside.refl _ _ _ _

end VG.Proof.Dsa.X86
