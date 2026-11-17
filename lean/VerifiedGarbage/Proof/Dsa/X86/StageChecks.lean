module

public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.ValidateRange
import VerifiedGarbage.Proof.Dsa.X86.StageValues
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Dsa.X86.RawInputs
import VerifiedGarbage.Proof.Dsa.X86.ValidateMasks
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

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
