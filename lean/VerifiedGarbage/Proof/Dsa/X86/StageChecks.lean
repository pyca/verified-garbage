module

public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Dsa.X86.ValidateRange`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.RawInputs`, which this module and modules that import it used -/

section

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

end

end

/-! # Range validation on encoded DSA components -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateRange_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rm : OperandReady s base n (.input modulus) len) (Ri : OperandReady s base n input len)
    (aboveOne : Bool) :
    WP isa (Validate.range len modulus input aboveOne) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) <
            Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len)) ∧
      Keeps powerClob s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  unfold Validate.range
  dsimp only
  rw [← hn]
  refine wp_seq_assoc (WP.seq (WP.mono (rawInputs_ok hs hz hn48 (by decide) (by decide) (by decide)
    h4 (by omega_using [hn]) h4 (by omega_using [hn]) hw4 hw4 Rm Ri) fun u ⟨Mu, Iu, Ou, Ku⟩ => ?_))
  have Fu : flagW base (Layout.field .mask) u = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ku (by decide) Ou (by omega_using [cb]) (.input .mask)
  refine WP.mono (rangeMask_ok (hs.of_keeps Ku (by decide)) hz (by omega_using [hn, h4]) hn48 aboveOne)
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Fu, Iu, Mu], (Ku.mono (by decide)).trans (Kt.mono (by decide)),
    (Outs.of_outside Ou (by simp)).trans Ot⟩

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ValidateMasks`, which this module and modules that import it used -/

section

/-! # Accumulating validation results into the DSA acceptance mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem accumulateEqual_ok {s : State} {base : Addr} {size n a b flag : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (hb : b + 8 * n ≤ size)
    (hf : flag + 4 ≤ size) :
    WP isa (.seq (equal n a b) (.block (andFlag flag))) s fun t =>
      flagW base flag t = flagW base flag s &&& mask32 (wordsVal s.mem base a n = wordsVal s.mem base b n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base flag 4 s.mem t.mem := by
  refine WP.seq (WP.mono (equal_ok n hs hn ha hb) fun u ⟨Vu, Ku, Mu⟩ => ?_)
  refine WP.mono (andFlag_ok flag (hs.of_keeps Ku (by decide)) hf) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, Ku.widen Kt, Mu ▸ Ot⟩
  rw [Vt, Vu]
  simp only [flagW, Mu]

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ValidateZero`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.CheckZero`, which this module and modules that import it used -/

section

/-! # Zero and nonzero checks with accumulated acceptance masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem checkZero_ok {s : State} {base : Addr} {size n a flag : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (hf : flag + 4 ≤ size)
    (wantNonzero : Bool) :
    WP isa (checkZero n a flag wantNonzero) s fun t =>
      flagW base flag t = flagW base flag s &&&
        mask32 (if wantNonzero then wordsVal s.mem base a n ≠ 0 else wordsVal s.mem base a n = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t ∧ Outside base flag 4 s.mem t.mem := by
  unfold checkZero
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.nonzero_ok n hs hn ha) fun u ⟨Vu, Ku, Mu⟩ => ?_)
  cases wantNonzero with
  | true =>
    simp only [ite_true, List.nil_append]
    refine WP.mono (andFlag_ok flag (hs.of_keeps Ku (by decide)) hf) fun t ⟨Vt, Kt, Ot⟩ => ?_
    exact ⟨by rw [Vt, Vu]; simp only [flagW, Mu], (Ku.mono (by decide)).widen Kt, Mu ▸ Ot⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.singleton_append]
    refine wp_logicS (.inr rfl) rfl fun v uv => ?_
    have Kv := Ku.widen uv.keeps
    refine WP.mono (andFlag_ok flag (hs.of_keeps Kv (by decide)) hf) fun t ⟨Vt, Kt, Ot⟩ => ?_
    refine ⟨?_, (Kv.mono (by decide)).widen Kt, ?_⟩
    · rw [Vt, uv.gpr, Vu]
      simp only [reduceCtorEq, ite_false, mask_not, ne_eq, not_not, flagW, uv.mem, Mu]
    · rw [uv.mem, Mu] at Ot
      exact Ot

end VG.Proof.Dsa.X86

end

end

/-! # Zero checks on encoded DSA intermediates -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateZero_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base n input len) (wantNonzero : Bool) :
    WP isa (Validate.zero len input wantNonzero) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (if wantNonzero then Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) ≠ 0
          else Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) = 0) ∧
      Keeps powerClob s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at b5
  unfold Validate.zero
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega_using [cb, hsize, b5]) h4 (by omega_using [hn]) hw4 R.toReadableComponent
    (R.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have OWu := slotOutside_whole Ou (by decide)
  have Fu : flagW base (Layout.field .mask) u = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ku (by decide) OWu (by omega_using [cb]) (.input .mask)
  refine WP.mono (checkZero_ok (hs.of_keeps Ku (by decide)) (by omega_using [hn, h4]) (by omega_using [cb, hsize, b5])
    (by change 8248 ≤ size; omega_using [hsize]) wantNonzero) fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Fu, Vu], (Ku.mono (by decide)).widen Kt,
    (Outs.of_outside OWu (by simp)).trans (Outs.of_outside Ot (by simp))⟩

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ValidateOne`, which this module and modules that import it used -/

section

/-! # Checking that a public subgroup power equals one -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateOne_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base n input len) :
    WP isa (Validate.isOne len input) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) = 1) ∧
      Keeps powerClob s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega_arith
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b5 b8
  have fit : 1 < 2 ^ (64 * n) := Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 64)
    (Nat.pow_le_pow_right (by decide) (by omega_arith))
  unfold Validate.isOne Validate.accumulate
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega_arith) h4 (by omega_arith) hw4 R.toReadableComponent
    (R.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.seq (WP.mono (setConstW_ok (hs.of_keeps Ku (by decide)) (k := 2 * n) (o := slot n 8) (x := 1)
    (by omega_arith) (by omega_arith) (by rw [show 32 * (2 * n) = 64 * n by omega_arith]; exact fit)) fun v ⟨Vv, Kv, Ov⟩ => ?_)
  rw [show 4 * (2 * n) = 8 * n by omega_arith] at Ov
  rw [← wordsVal_eq_val32] at Vv
  have Opre := (slotOutside_whole Ou (by decide)).trans (slotOutside_whole Ov (by decide))
  have Ksv : Keeps powerClob s v := (Ku.mono (by decide)).trans (Kv.mono (by decide))
  have Fu : flagW base (Layout.field .mask) v = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ksv (by decide) Opre (by omega_arith) (.input .mask)
  refine WP.mono (accumulateEqual_ok (hs.of_keeps Ksv (by decide)) (by omega_arith) (by omega_arith) (by omega_arith)
    (by change 8248 ≤ size; omega_arith)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, Ksv.trans (Kt.mono (by decide)),
    (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))⟩
  rw [Vt, Fu, Vv, slotOutside_val Ov (by decide) (by omega_arith), Vu]

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.ValidateEqual`, which this module and modules that import it used -/

section

/-! # Equality validation of encoded DSA values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateEqual_ok {s : State} {base : Addr} {size len n : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len) :
    WP isa (Validate.equalValues len a b) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len)) ∧
      Keeps powerClob s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b5 b8
  unfold Validate.equalValues Validate.accumulate
  dsimp only
  rw [← hn]
  refine wp_seq_assoc (WP.seq (WP.mono (rawInputs_ok hs hz hn48 (by decide) (by decide) (by decide)
    h4 (by omega_using [hn]) h4 (by omega_using [hn]) hw4 hw4 Ra Rb) fun u ⟨Au, Bu, Ou, Ku⟩ => ?_))
  have Fu : flagW base (Layout.field .mask) u = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ku (by decide) Ou (by omega_using [cb]) (.input .mask)
  refine WP.mono (accumulateEqual_ok (hs.of_keeps Ku (by decide)) (by omega_using [hn, h4]) (by omega_using [cb, hsize, b5]) (by omega_using [cb, hsize, b8])
    (by change 8248 ≤ size; omega_using [hsize])) fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Fu, Au, Bu], (Ku.mono (by decide)).widen Kt,
    (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp))⟩

end VG.Proof.Dsa.X86

end

end

/-! # Validation stages preserve moduli and persistent intermediate values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem stageRange_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {input : Pointer} {modulus : Field}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rm : OperandReady s base ((len + 7) / 8) (.input modulus) len)
    (Ri : OperandReady s base ((len + 7) / 8) input len) (aboveOne : Bool) :
    WP isa (Validate.range len modulus input aboveOne) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        ((if aboveOne then 1 else 0) < operandValue s base input len ∧ operandValue s base input len < operandValue s base (.input modulus) len) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateRange_ok M.scr M.saved rfl h4 hmax hw4 Rm Ri aboveOne) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega_using [hmax])
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem stageEqual_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Ra : OperandReady s base ((len + 7) / 8) a len)
    (Rb : OperandReady s base ((len + 7) / 8) b len) :
    WP isa (Validate.equalValues len a b) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (operandValue s base a len = operandValue s base b len) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateEqual_ok M.scr M.saved rfl h4 hmax hw4 Ra Rb) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega_using [hmax])
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem stageOne_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {input : Pointer}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base ((len + 7) / 8) input len) :
    WP isa (Validate.isOne len input) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (operandValue s base input len = 1) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateOne_ok M.scr M.saved rfl h4 hmax hw4 R) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega_using [hmax])
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem stageZero_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {input : Pointer}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base ((len + 7) / 8) input len) (wantNonzero : Bool) :
    WP isa (Validate.zero len input wantNonzero) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (if wantNonzero then operandValue s base input len ≠ 0 else operandValue s base input len = 0) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateZero_ok M.scr M.saved rfl h4 hmax hw4 R wantNonzero) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega_using [hmax])
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem StageFrame.scalar_keep_mask {base : Addr} {size pLen qLen p q d : Nat} {s t : State}
    (F : StageFrame base s t (Layout.field .mask) 4) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.scalars) :
    operandValue t base (.local d) qLen = operandValue s base (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  exact F.local_value_keep M.scr (by have := M.lengths; omega_using [this])
    (by change 7048 ≤ d; omega_using [H]) (Nat.le_trans (M.scalarFit hd) M.extent)
    (by have Hs : 8256 ≤ size := M.saved; change 8248 ≤ size; omega_using [Hs]) (M.scalarFit hd)
    (.inr (by change 8248 ≤ d; omega_using [H]))

theorem StageFrame.mask_keep {base : Addr} {s t : State} {output len : Nat}
    (F : StageFrame base s t output len) (ho : r ≤ output) :
    flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s := by
  have lo : 14720 ≤ output := ho
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem base (Layout.field .mask) 1 = val32 s.mem base (Layout.field .mask) 1 := by
    apply F.mem.val32
    · intro pair hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · change 8248 ≤ 0 ∨ 7048 ≤ 8244
        omega_using []
      · change 8248 ≤ output ∨ output + len ≤ 8244
        omega_using [lo]
    · decide
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.Dsa.X86
