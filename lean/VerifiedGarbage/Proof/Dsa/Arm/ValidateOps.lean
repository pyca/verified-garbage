module

public import VerifiedGarbage.Impl.Dsa.Arm.Validate
public import VerifiedGarbage.Proof.Dsa.Arm.CoreOps
public import VerifiedGarbage.Proof.Dsa.Arm.Checks
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-!
# DSA on 32-bit ARM: the checks of the validation

Each check loads its operands into a context's slots and ands its mask into
the flag word at offset 116 (`maskW`): `range_ok` (`0 < [a] < m`, or
`1 < [a] < m`), `zero_ok` (`[a] = 0` or `≠ 0`), `isOne_ok`, `equalValues_ok`;
`minus_ok` stores `m - amount`. Each changes only the arithmetic and the flag
word (`Stage` with output 116).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

/-- The flag word. -/
abbrev maskW (base : Addr) (s : State) : BitVec 32 := flagW base 116 s

theorem maskW_keep {base : Addr} {rs : List (Nat × Nat)} {s t : State} (O : Outs base rs s.mem t.mem)
    (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 116 ∨ 120 ≤ r.1) : maskW base t = maskW base s :=
  (Mem.readW_congr fun i hi => (O _ fun r hr => by
    have := hO r hr
    rw [ofs_off base (by omega)]
    omega).symm).symm

theorem maskW_arith {base : Addr} {s t : State} (O : Outs base arithRanges s.mem t.mem) :
    maskW base t = maskW base s :=
  maskW_keep O (by decide)

/-- An operand in a context's slot `i`, loaded from its bytes. -/
theorem loadSlot_ok {s : State} {base : Addr} {size len n i : Nat} {p : Pointer} (hs : Ws s base size)
    (hz : 4960 ≤ size) (w : Width len n) (hi : i < 12) (R : Ready s base p len) :
    WP isa (Core.load n len (slot n i) p) s fun t => Ws t base size ∧
      val32 t.mem base (slot n i) (2 * n) = operand base s p len ∧
      Rest coreClob s t ∧ Outside base (slot n i) (8 * n) s.mem t.mem := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have si := slot_lt (i := i) n48 hi
  refine WP.mono (load_ok hs (by omega) R (by omega) (by omega) (by omega) w.four hl w.word (by omega))
    fun t ⟨wt, Vt, Rt, Ot⟩ => ⟨wt, Vt, Rt.mono (by decide), Ot⟩

/-- A number in another slot is kept by a load. -/
theorem slot_keep {base : Addr} {n i j : Nat} {m m' : Mem} (O : Outside base (slot n i) (8 * n) m m')
    (hij : i ≠ j) (hn : n ≤ 48) (hj : j < 12) : val32 m' base (slot n j) (2 * n) = val32 m base (slot n j) (2 * n) := by
  have := slot_sep (n := n) hij
  have := slot_lt (i := j) hn hj
  simp only [stride] at *
  exact O.val32 (by omega) (by omega)

theorem andFlag_mask {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 4960 ≤ size) :
    WP isa (.block Validate.accumulate) s fun t =>
      maskW base t = maskW base s &&& s.gpr .r2 ∧ Rest [.r4] s t ∧ Outside base 116 4 s.mem t.mem :=
  andFlag_ok hs (flag := 116) (by omega) (by decide)

theorem range_ok {s : State} {base : Addr} {size len n : Nat} {modulus : Field} {input : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (Rq : Ready s base (.input modulus) len)
    (Ri : Ready s base input len) (aboveOne : Bool) :
    WP isa (Validate.range len modulus input aboveOne) s fun t =>
      maskW base t = maskW base s &&& mask32 ((if aboveOne then 1 else 0) < operand base s input len ∧
        operand base s input len < operand base s (.input modulus) len) ∧
      Stage base s t 116 4 := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have nw := hs.nowrap
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s10 := slot_lt (i := 10) n48 (by decide)
  unfold Validate.range
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (loadSlot_ok (i := 0) hs hz w (by decide) Rq) fun u₁ ⟨w₁, M₁, R₁, O₁⟩ => ?_)
  have Ri₁ := Ri.keep_rest R₁ (O := Outs.of_slot (i := 0) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.seq (WP.mono (loadSlot_ok (i := 8) w₁ hz w (by decide) Ri₁) fun u₂ ⟨w₂, A₂, R₂, O₂⟩ => ?_)
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Outs.of_slot (i := 0) O₁ (by decide) n48).trans (Outs.of_slot (i := 8) O₂ (by decide) n48)
  have Rs₂ : Rest coreClob s u₂ := R₁.trans R₂
  have A : val32 u₂.mem base (slot n 8) (2 * n) = operand base s input len := by
    rw [A₂, operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 0) O₁ (by decide) n48)
      arith_hdr Ri.ok, Ri.bytes (Outs.of_slot (i := 0) O₁ (by decide) n48) (by decide)]
  have M : val32 u₂.mem base (slot n 0) (2 * n) = operand base s (.input modulus) len := by
    rw [slot_keep O₂ (by decide) n48 (by decide), M₁]
  refine WP.seq (WP.mono (checkRange_ok w₂ (k := 2 * n) (a := baseS n) (m := modS n) (flag := 116) (by omega)
    (by simp only [baseS]; omega) (by simp only [modS]; omega) (by simp only [baseS]; omega)
    (by simp only [modS]; omega) (by omega) (by decide)) fun u₃ ⟨F₃, R₃, O₃⟩ => ?_)
  have f₂ : flagW base 116 u₂ = maskW base s := maskW_arith K₂
  rw [f₂] at F₃
  change val32 u₂.mem base (slot n 8) (2 * n) = _ at A
  change val32 u₂.mem base (slot n 0) (2 * n) = _ at M
  simp only [show baseS n = slot n 8 from rfl, show modS n = slot n 0 from rfl, A, M] at F₃
  have w₃ := w₂.of_rest R₃ (by decide)
  have Rs₃ : Rest coreClob s u₃ := Rs₂.trans (R₃.mono (by decide))
  have K₃ : Outs base (arithRanges ++ [(116, 4)]) s.mem u₃.mem := (Outs.arith_out K₂ _ _).trans (Outs.out O₃)
  cases aboveOne
  · exact WP.block_nil ⟨F₃.trans (congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte]))),
      Rs₃, K₃⟩
  · simp only [↓reduceIte, Validate.lowerTwo]
    have two_lt : 2 < 2 ^ (32 * (2 * n)) :=
      Nat.lt_of_lt_of_le (by decide : 2 < 2 ^ 32) (Nat.pow_le_pow_right (by decide) (by omega))
    have A₃ : val32 u₃.mem base (slot n 8) (2 * n) = operand base s input len := by
      rw [O₃.val32 (by omega) (by omega), A]
    refine WP.seq (WP.mono (lessThanConstant_ok w₃ (k := 2 * n) (a := baseS n) (tmp := prodS n) (x := 2)
      (by omega) (by simp only [baseS]; omega) (by simp only [prodS]; omega) (by simp only [baseS]; omega)
      (by simp only [prodS]; omega) (by omega) two_lt
      (by simp only [baseS, prodS, slot, stride] at *; omega)) fun u₄ ⟨e₄, R₄, O₄⟩ => ?_)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine wp_not e₄ fun u₅ e₅ R₅ m₅ => WP.mono (andFlag_ok (flag := 116) (w₃.of_rest (R₄.trans (R₅.mono
      (by decide))) (by decide)) (by omega) (by decide)) fun t ⟨Ft, Rt, Ot⟩ => ⟨?_, ?_, ?_⟩
    · have O₄' : Outs base arithRanges u₃.mem u₄.mem := by
        rw [show 4 * (2 * n) = 8 * n by omega] at O₄; exact Outs.of_slot (i := 10) O₄ (by decide) n48
      have A₃' : val32 u₃.mem base (baseS n) (2 * n) = operand base s input len := A₃
      have F₃' : maskW base u₃ = _ := F₃
      refine Ft.trans ?_
      have f₅ : flagW base 116 u₅ = maskW base u₄ := congrArg (fun m => Mem.readW m (off base 116) 32) m₅
      rw [e₅, f₅, maskW_arith O₄', F₃', A₃',
        BitVec.and_assoc, mask32_and]
      exact congrArg _ (mask32_iff (by omega))
    · exact ((Rs₃.trans (R₄.mono (by decide))).trans (R₅.mono (by decide))).trans (Rt.mono (by decide))
    · rw [show 4 * (2 * n) = 8 * n by omega] at O₄
      rw [m₅] at Ot
      exact (K₃.trans (Outs.arith_out (Outs.of_slot (i := 10) O₄ (by decide) n48) _ _)).trans (Outs.out Ot)

theorem zero_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (Ri : Ready s base input len) (want : Bool) :
    WP isa (Validate.zero len input want) s fun t =>
      maskW base t = maskW base s &&&
        mask32 (if want then operand base s input len ≠ 0 else operand base s input len = 0) ∧
      Stage base s t 116 4 := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s8 := slot_lt (i := 8) n48 (by decide)
  unfold Validate.zero
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (loadSlot_ok (i := 8) hs hz w (by decide) Ri) fun u ⟨wu, Au, Ru, Ou⟩ => ?_)
  refine WP.mono (checkZero_ok wu (k := 2 * n) (a := baseS n) (flag := 116) (by omega) (by simp only [baseS]; omega)
    (by simp only [baseS]; omega) (by omega) (by decide) want) fun t ⟨Ft, Rt, Ot⟩ =>
    ⟨Ft.trans ?_, Ru.trans (Rt.mono (by decide)),
      (Outs.arith_out (Outs.of_slot (i := 8) Ou (by decide) n48) _ _).trans (Outs.out Ot)⟩
  rw [show flagW base 116 u = maskW base u from rfl, maskW_arith (Outs.of_slot (i := 8) Ou (by decide) n48),
    show baseS n = slot n 8 from rfl, Au]

theorem isOne_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (Ri : Ready s base input len) :
    WP isa (Validate.isOne len input) s fun t =>
      maskW base t = maskW base s &&& mask32 (operand base s input len = 1) ∧ Stage base s t 116 4 := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  unfold Validate.isOne
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (loadSlot_ok (i := 8) hs hz w (by decide) Ri) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_)
  refine WP.seq (WP.mono (setConst_ok w₁ (k := 2 * n) (o := expS n) (x := 1) (by omega)
    (by simp only [expS]; omega) (by simp only [expS]; omega) (by omega)) fun u₂ ⟨E₂, R₂, O₂⟩ => ?_)
  rw [show 4 * (2 * n) = 8 * n by omega] at O₂
  have w₂ := w₁.of_rest R₂ (by decide)
  refine WP.seq (WP.mono (equal_ok w₂ (k := 2 * n) (a := baseS n) (b := expS n) (by omega)
    (by simp only [baseS]; omega) (by simp only [expS]; omega) (by simp only [baseS]; omega)
    (by simp only [expS]; omega)) fun u₃ ⟨e₃, R₃, m₃⟩ => ?_)
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Outs.of_slot (i := 8) O₁ (by decide) n48).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  refine WP.mono (andFlag_mask (w₂.of_rest R₃ (by decide)) hz) fun t ⟨Ft, Rt, Ot⟩ =>
    ⟨Ft.trans ?_, ((R₁.trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans (Rt.mono (by decide)),
      by rw [m₃] at Ot; exact (Outs.arith_out K₂ _ _).trans (Outs.out Ot)⟩
  have A₂ : val32 u₂.mem base (baseS n) (2 * n) = operand base s input len :=
    (slot_keep O₂ (by decide) n48 (by decide)).trans A₁
  have one : 1 < 2 ^ (32 * (2 * n)) := Nat.one_lt_two_pow (by omega)
  have E₂' : val32 u₂.mem base (expS n) (2 * n) = 1 := by rw [E₂, Nat.mod_eq_of_lt one]
  rw [show maskW base u₃ = maskW base u₂ by simp only [maskW, flagW, m₃], maskW_arith K₂, e₃, A₂, E₂']

theorem equalValues_ok {s : State} {base : Addr} {size len n : Nat} {a b : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (Ra : Ready s base a len) (Rb : Ready s base b len) :
    WP isa (Validate.equalValues len a b) s fun t =>
      maskW base t = maskW base s &&& mask32 (operand base s a len = operand base s b len) ∧
      Stage base s t 116 4 := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  unfold Validate.equalValues
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (loadSlot_ok (i := 8) hs hz w (by decide) Ra) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_)
  have Rb₁ := Rb.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.seq (WP.mono (loadSlot_ok (i := 11) w₁ hz w (by decide) Rb₁) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_)
  refine WP.seq (WP.mono (equal_ok w₂ (k := 2 * n) (a := baseS n) (b := expS n) (by omega)
    (by simp only [baseS]; omega) (by simp only [expS]; omega) (by simp only [baseS]; omega)
    (by simp only [expS]; omega)) fun u₃ ⟨e₃, R₃, m₃⟩ => ?_)
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Outs.of_slot (i := 8) O₁ (by decide) n48).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  refine WP.mono (andFlag_mask (w₂.of_rest R₃ (by decide)) hz) fun t ⟨Ft, Rt, Ot⟩ =>
    ⟨Ft.trans ?_, ((R₁.trans R₂).trans (R₃.mono (by decide))).trans (Rt.mono (by decide)),
      by rw [m₃] at Ot; exact (Outs.arith_out K₂ _ _).trans (Outs.out Ot)⟩
  have A₂ : val32 u₂.mem base (baseS n) (2 * n) = operand base s a len :=
    (slot_keep O₂ (by decide) n48 (by decide)).trans A₁
  have B₂' : val32 u₂.mem base (expS n) (2 * n) = operand base s b len := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr
      Rb.ok, Rb.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
  rw [show maskW base u₃ = maskW base u₂ by simp only [maskW, flagW, m₃], maskW_arith K₂, e₃, A₂, B₂']

/-- `[output] = m - amount`. -/
theorem minus_ok {s : State} {base : Addr} {size len n m amount output : Nat} {modulus : Field}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (Rq : Ready s base (.input modulus) len)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1) (ha : amount ≤ m)
    (ha0 : 0 < amount) (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Validate.minus len modulus amount output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len (m - amount) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s9 := slot_lt (i := 9) n48 (by decide)
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Validate.minus
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (setup_ok hs hz w Rq hm hm1 hodd) fun u ⟨cu, Ou, Ru⟩ => ?_)
  refine WP.seq (WP.mono (modulusMinus_ok cu ha (by omega)) fun v ⟨cv, Vv, Ov, Rv⟩ => ?_)
  refine WP.mono (store_ok (output := output) cv.ws w.n_eq.symm w.four w.word (by omega) (by omega) ho'
    h16o (by omega)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, (Ru.trans (Rv.mono (by decide))).trans (Rt.mono (by decide)),
      ((Outs.arith_out Ou _ _).trans (Outs.arith_out (Outs.arith Ov (streamRanges_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  rw [Vt, result_bytes w.word hl mlt (by rw [Vv]; omega), Vv]

end VG.Proof.Dsa.Arm
