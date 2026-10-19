module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks

import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Excluding zero and one from public generator and key values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem lowerTwo_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) :
    WP isa (Validate.lowerTwo n) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&&
        mask32 (2 ≤ wordsVal s.mem base (slot n 5) n) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t ∧
      Outs base [(slot n 7, 8 * n), (Layout.field .mask, 4)] s.mem t.mem := by
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have sep := slot_le (n := n) (i := 5) (j := 7) (by decide)
  simp only [stride] at b5 b7 sep
  have fit : 2 < 2 ^ (64 * n) := Nat.lt_of_lt_of_le (by decide : 2 < 2 ^ 64)
    (Nat.pow_le_pow_right (by decide) (by omega))
  unfold Validate.lowerTwo Validate.accumulate
  refine WP.seq (WP.mono (lessThanConstant_ok hs hn (by omega) (by omega) fit (.inl (by omega)))
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_logicS (.inr rfl) rfl fun v uv => ?_
  refine wp_movS rfl fun w uw _ => ?_
  have Kw := (Ku.widen uv.keeps).widen uw.keeps
  refine WP.mono (andFlag_ok (Layout.field .mask) (hs.of_keeps Kw (by decide))
    (by change 8248 ≤ size; omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, Kw.widen Kt, ?_⟩
  · rw [Vt, uw.gpr, uv.gpr, Vu]
    simp only [reduceCtorEq, ite_false, mask_not, Nat.not_lt]
    have F : flagW base (Layout.field .mask) w = flagW base (Layout.field .mask) s := by
      unfold flagW
      rw [uw.mem, uv.mem]
      apply BitVec.eq_of_toNat_eq
      exact Ou.w32 (.inr (by change slot n 7 + 8 * n ≤ 8244; omega)) (by decide)
    rw [F]
  · have Ow : Outside base (slot n 7) (8 * n) s.mem w.mem := by rw [uw.mem, uv.mem]; exact Ou
    exact (Outs.of_outside Ow (by simp)).trans (Outs.of_outside Ot (by simp))

end VG.Proof.Dsa.X86
