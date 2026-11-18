module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Dsa.X86.ValidateRangeMask`, which the modules that import this one used -/

section

/-! ### `Dsa.X86.ValidateLower`, which this module and modules that import it used -/

section

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
    (Nat.pow_le_pow_right (by decide) (by omega_using [hn]))
  unfold Validate.lowerTwo Validate.accumulate
  refine WP.seq (WP.mono (lessThanConstant_ok hs hn (by omega_using [cb, hsize, b5]) (by omega_using [cb, hsize, b7]) fit (.inl (by omega_using [sep])))
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_logicS (.inr rfl) rfl fun v uv => ?_
  refine wp_movS rfl fun w uw _ => ?_
  have Kw := (Ku.widen uv.keeps).widen uw.keeps
  refine WP.mono (andFlag_ok (Layout.field .mask) (hs.of_keeps Kw (by decide))
    (by change 8248 ≤ size; omega_using [hsize])) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, Kw.widen Kt, ?_⟩
  · rw [Vt, uw.gpr, uv.gpr, Vu]
    simp only [reduceCtorEq, ite_false, mask_not, Nat.not_lt]
    have F : flagW base (Layout.field .mask) w = flagW base (Layout.field .mask) s := by
      unfold flagW
      rw [uw.mem, uv.mem]
      apply BitVec.eq_of_toNat_eq
      exact Ou.w32 (.inr (by change slot n 7 + 8 * n ≤ 8244; omega_using [cb, b7])) (by decide)
    rw [F]
  · have Ow : Outside base (slot n 7) (8 * n) s.mem w.mem := by rw [uw.mem, uv.mem]; exact Ou
    exact (Outs.of_outside Ow (by simp)).trans (Outs.of_outside Ot (by simp))

end VG.Proof.Dsa.X86

end

end

/-! # Range masks for private scalars and public group elements -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validation_tmp_whole {s t : State} {base : Addr} {n i : Nat}
    (O : Outs base [(slot n i, 8 * n), (Layout.field .mask, 4)] s.mem t.mem) (hi : i < 9) :
    Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have b := slot_bound (n := n) hi
  simp only [stride] at b
  intro x hx
  apply O x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have H := hx (0, contextBytes n) (by simp)
    omega
  · exact hx _ (by simp)

theorem rangeMask_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (aboveOne : Bool) :
    WP isa (.seq (checkRange n (slot n 5) (slot n 0) (Layout.field .mask))
      (if aboveOne then Validate.lowerTwo n else .block [])) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&&
        mask32 ((if aboveOne then 1 else 0) < wordsVal s.mem base (slot n 5) n ∧
          wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 0) n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at b0 b5
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.checkRange_ok n (Layout.field .mask) hs hn
    (by omega_using [cb, hsize, b5]) (by omega_using [cb, hsize, b0]) (by change 8248 ≤ size; omega_using [hsize])) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  cases aboveOne with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact WP.block_nil ⟨Vu, Ku, Outs.of_outside Ou (by simp)⟩
  | true =>
    simp only [ite_true]
    refine WP.mono (lowerTwo_ok (hs.of_keeps Ku (by decide)) hz hn hn48) fun t ⟨Vt, Kt, Ot⟩ => ?_
    refine ⟨?_, Ku.trans (Kt.mono (by decide)), (Outs.of_outside Ou (by simp)).trans (validation_tmp_whole Ot (by decide))⟩
    rw [Vt, Vu, Ou.wordsVal (.inl (by change slot n 5 + 8 * n ≤ 8244; omega_using [cb, b5])) (by omega_using [cb, b5]),
      BitVec.and_assoc, mask32_and]
    have he : ((0 < wordsVal s.mem base (slot n 5) n ∧
        wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 0) n) ∧
        2 ≤ wordsVal s.mem base (slot n 5) n) ↔
      (1 < wordsVal s.mem base (slot n 5) n ∧ wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 0) n) := by omega_using []
    simp only [mask32, he]

end VG.Proof.Dsa.X86

end

end

/-! # Paired component loading without assuming a valid modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem rawInputs_ok {s : State} {base : Addr} {size n al bl i j : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : n ≤ 48)
    (hi : i < 9) (hj : j < 9) (hij : i ≠ j)
    (ha4 : 4 ≤ al) (ha : al ≤ 8 * n) (hb4 : 4 ≤ bl) (hb : bl ≤ 8 * n) (hwa : al % 4 = 0) (hwb : bl % 4 = 0)
    (Ra : OperandReady s base n a al) (Rb : OperandReady s base n b bl) :
    WP isa (.seq (Core.load n al (slot n i) a) (Core.load n bl (slot n j) b)) s fun t =>
      wordsVal t.mem base (slot n i) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) al) ∧
      wordsVal t.mem base (slot n j) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) bl) ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps loadClob s t := by
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hsize : 8256 ≤ size := hz
  have bound (k : Nat) (hk : k < 9) : slot n k + 8 * n ≤ size := by
    have := slot_bound (n := n) hk
    simp only [stride] at *
    omega_using [cb, hsize, this]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (bound i hi) ha4 ha hwa
    Ra.toReadableComponent (Ra.slot hi)) fun u ⟨Au, Ku, Ou⟩ => ?_)
  have OWu := slotOutside_whole Ou hi
  have Rbu := Rb.keep Ku (by decide) OWu hn
  refine WP.mono (coreLoad_ok (hs.of_keeps Ku (by decide)) hz (bound j hj) hb4 hb hwb
    Rbu.toReadableComponent (Rbu.slot hj)) fun t ⟨Bt, Kt, Ot⟩ => ?_
  refine ⟨?_, ?_, OWu.trans (slotOutside_whole Ot hj), Ku.trans Kt⟩
  · rw [slotOutside_val Ot hij (by have := bound i hi; have := hs.nowrap; omega_arith), Au]
  · rw [Bt, Rb.bytes Ku (by decide) OWu hn]

end VG.Proof.Dsa.X86
