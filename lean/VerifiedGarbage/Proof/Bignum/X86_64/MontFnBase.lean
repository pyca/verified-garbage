module

public import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
public import VerifiedGarbage.Impl.Bignum.X86_64.BaseSquare
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcStep
import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
meta import VerifiedGarbage.Impl.Bignum.X86_64.BaseSquare
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row

/-! ### `Bignum.X86_64.BaseSquareMont`, which only this module used -/

section

/-! ### `Bignum.X86_64.BaseSquareRow`, which only this module used -/

section

/-!
# The baseline square's multiply-add row (x86-64)

`BaseSquare.row`: `[r8] += rdx · [r9]` over `rbp` words with `mul`, `add` and
`adc`, its carry word in `rcx` (`row_rowOk`, `AdxSquare.RowOk`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.BaseSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.BaseSquare
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- `macR`, with its operand word at `aS` and accumulator word at `aX`. -/
theorem macR_ok (s : State) {aS aX : Addr}
    (eS : s.gpr .r9 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aS)
    (eX : s.gpr .r8 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aX)
    (hS : InRegions (s.rd ++ s.wr) aS 8) (hX : InRegions (s.rd ++ s.wr) aX 8)
    (hD : InRegions s.wr aX 8) :
    WP isa (.block macR) s fun t =>
      ∃ lo : BitVec 64, t.mem = s.mem.writeW aX lo ∧
        lo.toNat + 2 ^ 64 * (t.gpr .rcx).toNat = (s.gpr .r13).toNat * (s.mem.readW aS 64).toNat +
          (s.gpr .rcx).toNat + (s.mem.readW aX 64).toNat := by
  unfold macR
  xrun [State.ea, ix, eS, eX, hS, hX, hD, sx0]
  refine ⟨_, rfl, ?_⟩
  have hm := mul_toNat (s.mem.readW aS 64) (s.gpr .r13)
  have hl := mul_le (s.mem.readW aS 64) (s.gpr .r13)
  have hc := (s.gpr .rcx).isLt
  have hx := (s.mem.readW aX 64).isLt
  have e1 := addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .r13).toNat))
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .r13).toNat / 2 ^ 64)) (s.mem.readW aX 64) (by omega_arith)
  have e2 := addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .r13).toNat) + s.mem.readW aX 64)
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .r13).toNat / 2 ^ 64) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat *
        (s.gpr .r13).toNat)).toNat + (s.mem.readW aX 64).toNat))).setWidth 64) (s.gpr .rcx) (by omega_arith)
  rw [e2, Nat.mul_comm (s.gpr .r13).toNat]
  omega_arith

/-- `add r14, 1; cmp r14, rbp`. -/
theorem countBp_ok (s : State) {j N : Nat} (hj : s.gpr .r14 = BitVec.ofNat 64 j)
    (hN : s.gpr .rbp = BitVec.ofNat 64 N) (hjN : j + 1 < 2 ^ 64) (hN' : N < 2 ^ 64) :
    WP isa (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .rbp)]) s fun s' =>
      s'.zf = some (decide (j + 1 = N)) ∧ s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem = s.mem ∧ Keep [.r14] s s' := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.zf = some (decide (j + 1 = N)) ∧
    s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hj, hN, ofNat_add_one, ofNat_sub_beq hjN hN']

/-- After `j` steps of `row`'s loop from `s₀` (the multiplier in `r13`, the
carry in `rcx`). -/
structure RowInv (s₀ : State) (B : Addr) (Z e eb : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rcx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  val : wv t.mem B e j + 2 ^ (64 * j) * (t.gpr .rcx).toNat =
    wv s₀.mem B e j + (s₀.gpr .r13).toNat * wv s₀.mem B eb j + (s₀.gpr .rcx).toNat

theorem rowStep_ok {s₀ : State} {B : Addr} {Z e eb n : Nat}
    (h8 : s₀.gpr .r8 = off B e) (h9 : s₀.gpr .r9 = off B eb) (hbp : s₀.gpr .rbp = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 60) (hZ : e + 8 * n ≤ Z) (hZb : eb + 8 * n ≤ Z)
    (sb : eb + 8 * n ≤ e ∨ e + 8 * n ≤ eb) {j : Nat} (hj : j < n) {t : State}
    (hI : RowInv s₀ B Z e eb j t) :
    WP isa (.block macStep) t fun t' =>
      t'.zf = some (decide (j + 1 = n)) ∧ RowInv s₀ B Z e eb (j + 1) t' := by
  have hnw := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B e := (hI.keep.gpr (by decide)).trans h8
  have t9 : t.gpr .r9 = off B eb := (hI.keep.gpr (by decide)).trans h9
  have tbp : t.gpr .rbp = BitVec.ofNat 64 n := (hI.keep.gpr (by decide)).trans hbp
  have t13 : t.gpr .r13 = s₀.gpr .r13 := hI.keep.gpr (by decide)
  unfold macStep
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (macR_ok t (addr0 t9 hI.r14) (addr0 t8 hI.r14)
    (hI.scr.ld (by omega_arith)) (hI.scr.ld (by omega_arith)) (hI.scr.st (by omega_arith))) rfl) fun t₁ ⟨⟨lo, hm, hv⟩, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁bp : t₁.gpr .rbp = BitVec.ofNat 64 n := (k₁.gpr (by decide)).trans tbp
  refine WP.mono (countBp_ok t₁ t₁14 t₁bp (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hk : Keep [.rax, .rdx, .rcx, .r14] s₀ t' := ((hI.keep.trans k₁).trans k').mono (by decide)
  have hcx : t'.gpr .rcx = t₁.gpr .rcx := k'.gpr (by decide)
  have hmem : t'.mem = t.mem.writeW (off B (e + 8 * j)) lo := hm'.trans hm
  have hx : t.mem.readW (off B (e + 8 * j)) 64 = word s₀.mem B (e + 8 * j) :=
    hI.out.word (Or.inr (Nat.le_refl _)) (by omega_arith)
  have hy : t.mem.readW (off B (eb + 8 * j)) 64 = word s₀.mem B (eb + 8 * j) :=
    hI.out.word (by omega_arith) (by omega_arith)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), hk, h14, ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega_arith), hcx]
    simp only [wv]
    rw [hx, hy, t13] at hv
    have hval := hI.val
    rw [pow64_succ]
    grind

/-- `row` is a multiply-add row. -/
theorem row_ok {s : State} {B : Addr} {Z e eb n : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (hn0 : 0 < n) (hn : n < 2 ^ 60)
    (hZ : e + 8 * n ≤ Z) (hZb : eb + 8 * n ≤ Z)
    (sb : eb + 8 * n ≤ e ∨ e + 8 * n ≤ eb) :
    WP isa row s fun t =>
      wv t.mem B e n + 2 ^ (64 * n) * (t.gpr .rcx).toNat =
        wv s.mem B e n + (s.gpr .rdx).toNat * wv s.mem B eb n ∧
      Outside B e (8 * n) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 n ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s t := by
  unfold row
  have init : WP isa (.block [.mov .r13 (.reg .rdx), .mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0)]) s fun t =>
      t.gpr .r13 = s.gpr .rdx ∧ t.gpr .rcx = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
        Keep [.r13, .rcx, .r14] s t := by
    refine WP.mono (WP.keep [.r13, .rcx, .r14] (Q := fun t => t.gpr .r13 = s.gpr .rdx ∧ t.gpr .rcx = 0 ∧
      t.gpr .r14 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
    xrun
  refine WP.seq (WP.mono init fun u ⟨h13, hcx, h14, hm, ku⟩ => ?_)
  have u8 := (ku.gpr (by decide)).trans h8
  have u9 := (ku.gpr (by decide)).trans h9
  have ubp := (ku.gpr (by decide)).trans hbp
  have I0 : RowInv u B Z e eb 0 u :=
    ⟨hs.congr ku.2.2, Keep.refl _ _, h14, Outside.refl _ _ _ _, by simp [wv, hcx]⟩
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := n) hn0 (RowInv u B Z e eb)
    (fun j _ hj t hI => rowStep_ok u8 u9 ubp hn hZ hZb sb hj hI) (fun _ h => h) I0) fun t hI => ?_)
  have t13 : t.gpr .r13 = s.gpr .rdx := (hI.keep.gpr (by decide)).trans h13
  refine WP.mono (WP.keep [.rdx] (Q := fun t' => t'.gpr .rdx = s.gpr .rdx ∧ t'.mem = t.mem)
    (by xrun [t13]) rfl) fun t' ⟨⟨hdx, hm'⟩, k'⟩ => ?_
  have kt := (ku.trans hI.keep).trans k'
  have hv := hI.val
  rw [hm, h13, hcx] at hv
  refine ⟨?_, ?_, (k'.gpr (by decide)).trans hI.r14, ⟨fun r hr => ?_, kt.2⟩⟩
  · rw [hm', k'.gpr (by decide)]; simpa using hv
  · rw [hm', ← hm]; exact hI.out
  · by_cases hd : r = .rdx
    · subst hd; exact hdx
    · exact kt.1 r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind)

theorem row_rowOk : AdxSquare.RowOk row :=
  ⟨fun hs h8 h9 hbp h0 hw hZ hZb sb => row_ok hs h8 h9 hbp h0 hw hZ hZb sb⟩

end VG.Proof.Bignum.X86_64.BaseSquare

end

end

/-! ### `Bignum.X86_64.BaseSquareDiag`, which only this module used -/

section

/-!
# The baseline square's diagonal step (x86-64)

`core`: two words of the cross products doubled, the square of
`rdx` and the carry word `r15` added, by `mul`, `add` and `adc`
(`core_coreOk`, `AdxSquare.CoreOk`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.BaseSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.BaseSquare VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem add_toNat64 (x y : BitVec 64) :
    (x + y).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat = x.toNat + y.toNat := by
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- `add`, `adc`, `adc 0`: `x0 + 2⁶⁴ x1 + 2¹²⁸ x2` plus `y0 + 2⁶⁴ y1`, if it fits. -/
theorem chain3 (x0 x1 x2 y0 y1 : BitVec 64)
    (h : x0.toNat + y0.toNat + 2 ^ 64 * (x1.toNat + y1.toNat) + 2 ^ 128 * x2.toNat < 2 ^ 192) :
    (x0 + y0).toNat + 2 ^ 64 * (x1 + y1 + (BitVec.ofBool (decide (2 ^ 64 ≤ x0.toNat + y0.toNat))).setWidth 64).toNat +
      2 ^ 128 * (x2 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ x1.toNat + y1.toNat +
        (decide (2 ^ 64 ≤ x0.toNat + y0.toNat)).toNat))).setWidth 64).toNat =
      x0.toNat + y0.toNat + 2 ^ 64 * (x1.toNat + y1.toNat) + 2 ^ 128 * x2.toNat := by
  obtain e0 := add_toNat64 x0 y0
  obtain e1 := adc_toNat x1 y1 (decide (2 ^ 64 ≤ x0.toNat + y0.toNat))
  obtain e2 := adc_toNat x2 0 (decide (2 ^ 64 ≤ x1.toNat + y1.toNat + (decide (2 ^ 64 ≤ x0.toNat + y0.toNat)).toNat))
  have z : (0 : BitVec 64).toNat = 0 := rfl
  rw [z] at e2
  have : decide (2 ^ 64 ≤ x2.toNat + 0 + (decide (2 ^ 64 ≤ x1.toNat + y1.toNat +
      (decide (2 ^ 64 ≤ x0.toNat + y0.toNat)).toNat)).toNat) = false := by
    simp only [decide_eq_false_iff_not, Nat.not_le]
    have := (x0 + y0).isLt
    have := (x1 + y1 + (BitVec.ofBool (decide (2 ^ 64 ≤ x0.toNat + y0.toNat))).setWidth 64).isLt
    omega_arith
  rw [this, Bool.toNat_false] at e2
  omega_arith

theorem core0_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdx), .mov .rsi (.reg .rdx), .mul .rsi, .mov32 .rbx (.imm 0)]) s fun t =>
      (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .rdx).toNat = (s.gpr .rdx).toNat * (s.gpr .rdx).toNat ∧
      t.gpr .rsi = s.gpr .rdx ∧ t.gpr .rbx = 0 ∧ t.mem = s.mem ∧ Keep [.rax, .rsi, .rdx, .rbx] s t := by
  refine WP.mono (WP.keep [.rax, .rsi, .rdx, .rbx] (Q := fun t =>
    (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .rdx).toNat = (s.gpr .rdx).toNat * (s.gpr .rdx).toNat ∧
      t.gpr .rsi = s.gpr .rdx ∧ t.gpr .rbx = 0 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  xrun
  exact mul_toNat _ _

theorem core1_ok (s : State)
    (h : 2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) + 2 ^ 128 * (s.gpr .rbx).toNat < 2 ^ 192) :
    WP isa (.block [.alu .add .r11 (.reg .r11), .alu .adc .r12 (.reg .r12), .alu .adc .rbx (.imm 0)]) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem ∧ Keep [.r11, .r12, .rbx] s t := by
  refine WP.mono (WP.keep [.r11, .r12, .rbx] (Q := fun t =>
    (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [sx0]
  rw [chain3 _ _ _ _ _ (by omega_arith)]
  omega_arith

theorem core2_ok (s : State)
    (h : (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + (s.gpr .rdx).toNat) +
      2 ^ 128 * (s.gpr .rbx).toNat < 2 ^ 192) :
    WP isa (.block [.alu .add .r11 (.reg .rax), .alu .adc .r12 (.reg .rdx), .alu .adc .rbx (.imm 0)]) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + (s.gpr .rdx).toNat) +
          2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem ∧ Keep [.r11, .r12, .rbx] s t := by
  refine WP.mono (WP.keep [.r11, .r12, .rbx] (Q := fun t =>
    (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + (s.gpr .rdx).toNat) +
          2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [sx0]
  exact chain3 _ _ _ _ _ h

theorem core3_ok (s : State)
    (h : (s.gpr .r11).toNat + (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r12).toNat +
      2 ^ 128 * (s.gpr .rbx).toNat < 2 ^ 192) :
    WP isa (.block [.alu .add .r11 (.reg .r15), .alu .adc .r12 (.imm 0), .alu .adc .rbx (.imm 0)]) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r12).toNat + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem ∧ Keep [.r11, .r12, .rbx] s t := by
  refine WP.mono (WP.keep [.r11, .r12, .rbx] (Q := fun t =>
    (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        (s.gpr .r11).toNat + (s.gpr .r15).toNat + 2 ^ 64 * (s.gpr .r12).toNat + 2 ^ 128 * (s.gpr .rbx).toNat ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [sx0]
  have := chain3 (s.gpr .r11) (s.gpr .r12) (s.gpr .rbx) (s.gpr .r15) 0 (by
    rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith)
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this ⊢
  exact this

/-- `core`'s result, as `CoreOk` states it. -/
theorem core_ok (s : State) :
    WP isa (.block core) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + (s.gpr .r15).toNat ∧
      Keeps [.rsi, .rbx, .rax, .rcx, .r11, .r12] s t := by
  rw [show core =
    ([.mov .rax (.reg .rdx), .mov .rsi (.reg .rdx), .mul .rsi, .mov32 .rbx (.imm 0)] : List Instr) ++
    (([.alu .add .r11 (.reg .r11), .alu .adc .r12 (.reg .r12), .alu .adc .rbx (.imm 0)] : List Instr) ++
    (([.alu .add .r11 (.reg .rax), .alu .adc .r12 (.reg .rdx), .alu .adc .rbx (.imm 0)] : List Instr) ++
    (([.alu .add .r11 (.reg .r15), .alu .adc .r12 (.imm 0), .alu .adc .rbx (.imm 0)] : List Instr) ++
    ([.mov .rdx (.reg .rsi)] : List Instr)))) from rfl]
  obtain hx0 := (s.gpr .r11).isLt
  obtain hx1 := (s.gpr .r12).isLt
  obtain hc := (s.gpr .r15).isLt
  obtain hsq := mul_le (s.gpr .rdx) (s.gpr .rdx)
  rw [WP.block_append_iff]
  refine WP.mono (core0_ok s) fun s₁ ⟨hp, hsi, hbx, hm₁, k₁⟩ => ?_
  obtain e11 : s₁.gpr .r11 = s.gpr .r11 := k₁.gpr (by decide)
  obtain e12 : s₁.gpr .r12 = s.gpr .r12 := k₁.gpr (by decide)
  obtain e15 : s₁.gpr .r15 = s.gpr .r15 := k₁.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (core1_ok s₁ (by rw [e11, e12, hbx, show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith))
    fun s₂ ⟨hv₂, hm₂, k₂⟩ => ?_
  rw [e11, e12, hbx, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hv₂
  obtain r2ax : s₂.gpr .rax = s₁.gpr .rax := k₂.gpr (by decide)
  obtain r2dx : s₂.gpr .rdx = s₁.gpr .rdx := k₂.gpr (by decide)
  obtain hb₂ := (s₂.gpr .r11).isLt
  rw [WP.block_append_iff]
  refine WP.mono (core2_ok s₂ (by rw [r2ax, r2dx]; omega_arith)) fun s₃ ⟨hv₃, hm₃, k₃⟩ => ?_
  rw [r2ax, r2dx] at hv₃
  obtain r3_15 : s₃.gpr .r15 = s.gpr .r15 := ((k₂.trans k₃).gpr (by decide)).trans e15
  rw [WP.block_append_iff]
  refine WP.mono (core3_ok s₃ (by rw [r3_15]; omega_arith)) fun s₄ ⟨hv₄, hm₄, k₄⟩ => ?_
  rw [r3_15] at hv₄
  obtain r4si : s₄.gpr .rsi = s.gpr .rdx := ((k₂.trans (k₃.trans k₄)).gpr (by decide)).trans hsi
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧ t.mem = s₄.mem)
    (by xrun [r4si]) rfl) fun t ⟨⟨hdx, hm⟩, k₅⟩ => ?_
  obtain K := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  refine ⟨?_, fun r hr => ?_, hm.trans (hm₄.trans (hm₃.trans (hm₂.trans hm₁))), K.2.1, K.2.2⟩
  · rw [k₅.gpr (by decide), k₅.gpr (by decide), k₅.gpr (by decide), hv₄]
    omega_arith
  · by_cases hd : r = Reg.rdx
    · subst hd; exact hdx
    · exact K.1 r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind)

theorem core_coreOk : AdxSquare.CoreOk core := ⟨core_ok⟩

end VG.Proof.Bignum.X86_64.BaseSquare

end

end

/-! ### `Bignum.X86_64.BaseSquareRedc`, which only this module used -/

section

/-!
# The baseline square's Montgomery reduction (x86-64)

`BaseSquare.redc`: the `2 w` words of a square at `A` reduced row by row
into the `w + 2` words at `A + 8 w`, `R T = X + q m` (`redc_ok`), as
`AdxSquare.redc` does, with `-m⁻¹`, `w`, the modulus' base and the end of the
rows in `xmm15`, `xmm0`, `xmm2` and `xmm3`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.BaseSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.BaseSquare VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The low quadword that `movq r64, xmm` reads after `movq xmm, r64`. -/
theorem movq_lo (v : BitVec 64) : ((0 : BitVec 64) ++ v).extractLsb' 0 64 = v := by
  ext i h; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [h]

theorem imul_redcU (a b : BitVec 64) : BitVec.ofInt 64 (a.toInt * b.toInt) = AdxSquare.redcU a b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt, AdxSquare.redcU]
  apply BitVec.eq_of_toNat_eq
  simp

theorem head_ok {s : State} {B : Addr} {Z e : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (he : e + 8 ≤ Z) (hx : s.xmm .xmm15 = (0 : BitVec 64) ++ minv) :
    WP isa (.block head) s fun t =>
      t.gpr .rdx = AdxSquare.redcU (word s.mem B e) minv ∧ t.mem = s.mem ∧ Keep [.rdx, .rax] s t := by
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun t =>
    t.gpr .rdx = AdxSquare.redcU (word s.mem B e) minv ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold head
  xrun [State.ea, at0, h8, hs.ld he, hx, movq_lo, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    execImul, imul_redcU]

/-- The rows' end: the flags of `r8 = eT`, `eT` from `xmm3`. -/
theorem endTest_ok {s : State} {B : Addr} {e eT : Nat} (h8 : s.gpr .r8 = off B e)
    (hx : s.xmm .xmm3 = (0 : BitVec 64) ++ off B eT) (he : e < 2 ^ 64) (heT : eT < 2 ^ 64) :
    WP isa (.block [.movqR .rax .xmm3, .alu .cmp .r8 (.reg .rax)]) s fun t =>
      t.zf = some (decide (e = eT)) ∧ t.mem = s.mem ∧ t.gpr .r8 = off B e ∧ Keep [.rax, .r8] s t := by
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.zf = some (decide (e = eT)) ∧ t.mem = s.mem ∧
    t.gpr .r8 = off B e) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [h8, hx, movq_lo, off_sub_beq B he heT]

/-- One row of the reduction, as `AdxSquare.redcRow_ok`'s, its end the
flags of `e + 8 = eT`. -/
theorem redcRow_ok {s : State} {B : Addr} {Z e eN eT w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eN)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hx15 : s.xmm .xmm15 = (0 : BitVec 64) ++ minv)
    (hx3 : s.xmm .xmm3 = (0 : BitVec 64) ++ off B eT) (heT : eT < Z)
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 31) (hwn : w < n) (heZ : e + 8 * n ≤ Z) (hsep : eN + 8 * w ≤ e)
    (hinv : ((word s.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa redcRow s fun t => ∃ u < 2 ^ 64,
      2 ^ 64 * (wv t.mem B (e + 8) (n - 1) + 2 ^ (64 * w) * (t.gpr .r10).toNat) =
        wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat + u * wv s.mem B eN w ∧
      ((s.gpr .r10).toNat ≤ 1 → (t.gpr .r10).toNat ≤ 1) ∧
      Outside B e (8 * (w + 1)) s.mem t.mem ∧ t.gpr .r8 = off B (e + 8) ∧
      t.zf = some (decide (e + 8 = eT)) ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s t := by
  have hn := hs.nowrap
  unfold redcRow
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (head_ok hs h8 (by omega_arith) hx15))
    fun s₁ ⟨⟨hdx, hm₁, k₁⟩, hx₁, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (row_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h8)
    ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hbp) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith))) fun s₂ ⟨⟨hv, ho, h14, k₂⟩, hx₂, _⟩ => ?_)
  rw [hm₁, hdx] at hv
  rw [hm₁] at ho
  obtain k12 := k₁.trans k₂
  obtain hlow := AdxSquare.redc_low (by omega_arith) hinv hv
  obtain top : word s₂.mem B (e + 8 * w) = word s.mem B (e + 8 * w) := ho.word (by omega_arith) (by omega_arith)
  obtain c10 : s₂.gpr .r10 = s.gpr .r10 := k12.gpr (by decide)
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (AdxSquare.redcTail_ok (hs.congr k12.2.2)
    ((k12.gpr (by decide)).trans h8) h14 (by omega_arith))) fun s₃ ⟨⟨lo, hm₃, ht, hc, h8₃, k₃⟩, hx₃, _⟩ => ?_)
  rw [top, c10] at ht
  rw [c10] at hc
  obtain out₃ : Outside B (e + 8 * w) 8 s₂.mem s₃.mem := by
    rw [hm₃]; exact writeW_outside _ _ _ (by omega_arith)
  obtain allout : Outside B e (8 * (w + 1)) s.mem s₃.mem :=
    (ho.mono (o' := e) (n' := 8 * (w + 1)) (Nat.le_refl _) (by omega_arith)).trans
      (out₃.mono (o' := e) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith))
  obtain low₃ : word s₃.mem B e = 0 := (out₃.word (by omega_arith) (by omega_arith)).trans hlow
  obtain pre₃ : wv s₃.mem B e w = wv s₂.mem B e w := out₃.wv (by omega_arith) (by omega_arith)
  obtain top₃ : word s₃.mem B (e + 8 * w) = lo := by rw [hm₃, word_writeW_self]
  obtain high₃ : wv s₃.mem B (e + 8 * w + 8) (n - (w + 1)) =
      wv s.mem B (e + 8 * w + 8) (n - (w + 1)) := allout.wv (by omega_arith) (by omega_arith)
  obtain eq : wv s₃.mem B e n + 2 ^ (64 * w) * 2 ^ 64 * (s₃.gpr .r10).toNat =
      wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat +
        (AdxSquare.redcU (word s.mem B e) minv).toNat * wv s.mem B eN w := by
    rw [AdxSquare.wv_at_word _ _ _ _ _ hwn, AdxSquare.wv_at_word s.mem _ _ _ _ hwn, pre₃, top₃, high₃]
    grind
  obtain shifted : wv s₃.mem B e n = 2 ^ 64 * wv s₃.mem B (e + 8) (n - 1) := by
    rw [show n = (n - 1) + 1 by omega_arith, wv_low, low₃]
    simp
  rw [shifted] at eq
  obtain k123 := k12.trans k₃
  obtain hx₃' : s₃.xmm .xmm3 = (0 : BitVec 64) ++ off B eT := by rw [hx₃, hx₂, hx₁, hx3]
  refine WP.mono (endTest_ok h8₃ hx₃' (by omega_arith) (by omega_arith)) fun t ⟨hz, hm, h8', kt⟩ => ?_
  refine ⟨(AdxSquare.redcU (word s.mem B e) minv).toNat, (AdxSquare.redcU (word s.mem B e) minv).isLt, ?_, ?_, ?_,
    h8', hz, (k123.trans kt).mono (by decide)⟩
  · rw [hm, kt.gpr (by decide)]
    grind
  · rw [kt.gpr (by decide)]; exact hc
  · rw [hm]; exact allout

/-- After reduction rows `0, …, i - 1` from `s₀`, of the square's `2 w`
words at `A`, with the modulus at `eN`. -/
structure RedcInv (s₀ : State) (B : Addr) (Z A eN w : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s₀ t
  xmm : t.xmm = s₀.xmm
  r8 : t.gpr .r8 = off B (A + 8 * i)
  carry : (t.gpr .r10).toNat ≤ 1
  out : Outside B A (16 * w) s₀.mem t.mem
  val : ∃ q < 2 ^ (64 * i),
    2 ^ (64 * i) * (wv t.mem B (A + 8 * i) (2 * w - i) + 2 ^ (64 * w) * (t.gpr .r10).toNat) =
      wv s₀.mem B A (2 * w) + q * wv s₀.mem B eN w

theorem redcStep_ok {s₀ t : State} {B : Addr} {Z A eN w i : Nat} {minv : BitVec 64}
    (h9 : s₀.gpr .r9 = off B eN) (hbp : s₀.gpr .rbp = BitVec.ofNat 64 w)
    (hx15 : s₀.xmm .xmm15 = (0 : BitVec 64) ++ minv) (hx3 : s₀.xmm .xmm3 = (0 : BitVec 64) ++ off B (A + 8 * w))
    (hA : A + 16 * w + 16 ≤ Z) (hsep : eN + 8 * w ≤ A) (hw1 : 1 ≤ w) (hw : w < 2 ^ 31) (hi : i < w)
    (hinv : ((word s₀.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hI : RedcInv s₀ B Z A eN w i t) :
    WP isa redcRow t fun t' => t'.zf = some (decide (i + 1 = w)) ∧ RedcInv s₀ B Z A eN w (i + 1) t' := by
  have hn := hI.scr.nowrap
  have kp := hI.keep
  obtain hN : wv t.mem B eN w = wv s₀.mem B eN w := hI.out.wv (by omega_arith) (by omega_arith)
  obtain hN0 : word t.mem B eN = word s₀.mem B eN := hI.out.word (by omega_arith) (by omega_arith)
  refine WP.mono (WP.vecKeep (by decide) (redcRow_ok (n := 2 * w - i) (eT := A + 8 * w) hI.scr hI.r8
    ((kp.gpr (by decide)).trans h9) ((kp.gpr (by decide)).trans hbp) (by rw [hI.xmm]; exact hx15)
    (by rw [hI.xmm]; exact hx3) (by omega_arith) hw1 hw (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hN0]; exact hinv)))
    fun t' ⟨⟨u, hu, hv, hc, ho, h8', hz, kt⟩, hx', _⟩ => ⟨?_, ?_⟩
  · rw [hz]
    congr 1
    exact decide_eq_decide.mpr (by omega_arith)
  rw [hN, show A + 8 * i + 8 = A + 8 * (i + 1) by omega_arith, show 2 * w - i - 1 = 2 * w - (i + 1) by omega_arith] at hv
  refine ⟨hI.scr.congr kt.2.2, (kp.trans kt).mono (by decide), hx'.trans hI.xmm, ?_, hc hI.carry, ?_, ?_⟩
  · rw [h8']; congr 1
  · exact hI.out.trans (ho.mono (o' := A) (n' := 16 * w) (by omega_arith) (by omega_arith))
  · obtain ⟨q, hq, heq⟩ := hI.val
    refine ⟨q + 2 ^ (64 * i) * u, ?_, ?_⟩
    · rw [pow64_succ]
      exact AdxSquare.digit_bound hq hu
    · rw [pow64_succ]
      grind

/-- `redc`: `R T = X + q m` for the square `X` at `A` and the result `T`,
its `w + 2` words at `A + 8 w`. -/
theorem redc_ok {s : State} {B : Addr} {Z A eN w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (hx0 : s.xmm .xmm0 = (0 : BitVec 64) ++ BitVec.ofNat 64 w)
    (hx2 : s.xmm .xmm2 = (0 : BitVec 64) ++ off B eN) (hx15 : s.xmm .xmm15 = (0 : BitVec 64) ++ minv)
    (hx3 : s.xmm .xmm3 = (0 : BitVec 64) ++ off B (A + 8 * w))
    (hA : A + 16 * w + 16 ≤ Z) (hsep : eN + 8 * w ≤ A) (hw1 : 1 ≤ w) (hw : w < 2 ^ 31)
    (hinv : ((word s.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa redc s fun t =>
      (∃ q < 2 ^ (64 * w), 2 ^ (64 * w) * wv t.mem B (A + 8 * w) (w + 2) =
        wv s.mem B A (2 * w) + q * wv s.mem B eN w) ∧
      Outside B A (16 * w + 16) s.mem t.mem ∧ t.gpr .r8 = off B (A + 8 * w) ∧ t.xmm = s.xmm ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8, .r9, .rbp] s t := by
  have hn := hs.nowrap
  unfold redc
  obtain init : WP isa (.block [.movqR .r9 .xmm2, .movqR .rbp .xmm0, .mov32 .r10 (.imm 0)]) s fun t =>
      t.gpr .r9 = off B eN ∧ t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem ∧
        Keep [.r9, .rbp, .r10] s t := by
    refine WP.mono (WP.keep [.r9, .rbp, .r10] (Q := fun t => t.gpr .r9 = off B eN ∧
      t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
    xrun [hx0, hx2, movq_lo, RegUpd.xmm_setReg]
  refine WP.seq (WP.mono (WP.vecKeep (by decide) init) fun s₁ ⟨⟨h9, hbp, h10, hm₁, k₁⟩, hx₁, _⟩ => ?_)
  rw [← hm₁] at hinv
  obtain I0 : RedcInv s₁ B Z A eN w 0 s₁ := by
    refine ⟨hs.congr k₁.2.2, Keep.refl _ _, rfl, by simpa using (k₁.gpr (by decide)).trans h8, by simp [h10],
      Outside.refl _ _ _ _, 0, by decide, ?_⟩
    simp [h10]
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := w) (by omega_arith) (RedcInv s₁ B Z A eN w)
    (fun i _ hi t h => redcStep_ok h9 hbp (by rw [hx₁]; exact hx15) (by rw [hx₁]; exact hx3) hA hsep hw1 hw hi
      hinv h) (fun _ h => h) I0) fun s₂ hI => ?_)
  refine WP.mono (WP.vecKeep (by decide) (AdxSquare.redcFinish_ok hI.scr hI.r8
    ((hI.keep.gpr (by decide)).trans hbp) (by omega_arith))) fun t ⟨⟨hv, ho, kt⟩, hxt, _⟩ => ?_
  obtain ⟨q, hq, heq⟩ := hI.val
  rw [show 2 * w - w = w by omega_arith, hm₁] at heq
  have o₁ := hI.out
  rw [hm₁] at o₁
  refine ⟨⟨q, hq, ?_⟩, ?_, ?_, ?_, ((k₁.trans hI.keep).trans kt).mono (by decide)⟩
  · rw [hv]; exact heq
  · exact (o₁.mono (o' := A) (n' := 16 * w + 16) (Nat.le_refl _) (by omega_arith)).trans
      (ho.mono (o' := A) (n' := 16 * w + 16) (by omega_arith) (by omega_arith))
  · rw [kt.gpr (by decide)]; exact hI.r8
  · rw [hxt, hI.xmm, hx₁]

end VG.Proof.Bignum.X86_64.BaseSquare

end

end


/-!
# The baseline Montgomery square (x86-64)

`BaseSquare.square`: `[o] ≡ [a]² R⁻¹ (mod m)` from `basesR`'s registers,
below `R`, and below `m` if `[a] < m` (`square_ok`), as `mmTailLazy_ok` says
of `montMul`'s rounds; and `BaseSquare.mulTail`, which takes the square for
`a = b` and the rounds otherwise (`tail_ok`). The square writes the vector
registers `stashed` only.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.BaseSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.BaseSquare VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The vector registers `stash` writes. -/
def stashed : List XReg := [.xmm14, .xmm15, .xmm0, .xmm1, .xmm2, .xmm3]

theorem xmm_setXmm (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

theorem stash_ok (s : State) :
    WP isa (.block stash) s fun t =>
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ t.mem = s.mem ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2, k⟩
  unfold stash
  xrun [XOp.exec, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm]
  simp only [xmm_setXmm, reduceCtorEq, ite_true, ite_false, true_and]
  intro x hx
  simp only [stashed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp only [hx, ite_false]

/-- `square` up to the reduction: `[a]²` at `aAcc + 16`, over `2 w` words,
the vector registers stashed. -/
theorem sqRaw_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (h9 : s.gpr .r9 = off B (slot w a)) (h8 : s.gpr .r8 = off B (slot w aAcc))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) :
    WP isa raw s fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w) = wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16 + 8 * (2 * w)) 2 = 0 ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧ t.gpr .r8 = off B (slot w aAcc + 16) ∧
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  let A := slot w aAcc + 16
  let eb := slot w a
  obtain hA : A + 8 * (2 * w + 2) ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold A slot aAcc aTmp at *
    omega_arith
  obtain hb : eb + 8 * w ≤ Z := by have := slot_le (w := w) ha; omega_arith
  obtain sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *
    omega_arith
  unfold raw
  -- The stash, and the cross products' registers.
  obtain pS : WP isa (.block (stash ++ ([.mov .rbx (.reg .r12), .alu .add .r8 (.imm 16)] : List Instr))) s fun t =>
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ t.gpr .rbx = BitVec.ofNat 64 w ∧ t.gpr .r8 = off B A ∧
      t.mem = s.mem ∧ Keep [.rbx, .r8] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (stash_ok s) fun u ⟨x14, x15, x0, x1, x2, x3, xo, hm, k⟩ => ?_
    refine WP.mono (WP.vecKeep (by decide) (WP.keep [.rbx, .r8] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B A ∧ t.mem = u.mem) (by xrun [(k.gpr (by decide) : u.gpr .r12 = _).trans h12,
        (k.gpr (by decide) : u.gpr .r8 = _).trans h8, off_add16]; rfl) rfl))
      fun t ⟨⟨⟨hbx, h8', hm'⟩, k'⟩, hx, _⟩ => ?_
    rw [hx]
    exact ⟨x14, x15, x0, x1, x2, x3, xo, hbx, h8', hm'.trans hm, (k.trans k').mono (by decide)⟩
  refine WP.seq (WP.mono pS fun s₁ ⟨x14, x15, x0, x1, x2, x3, xo, hbx₁, h8₁, hm₁, k₁⟩ => ?_)
  obtain h9₁ : s₁.gpr .r9 = off B eb := (k₁.gpr (by decide)).trans h9
  -- The cross products.
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (AdxSquare.crossWith_ok row_rowOk (hs.congr k₁.2.2) h8₁ h9₁ hbx₁
    hw (by omega_arith) hA hb sb)) fun s₂ ⟨⟨hv₂, ho₂, hz₂, k₂⟩, hx₂, _⟩ => ?_)
  rw [hm₁] at hv₂ ho₂
  obtain k12 := k₁.trans k₂
  obtain h9₂ : s₂.gpr .r9 = off B eb := (k₂.gpr (by decide)).trans h9₁
  obtain read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) :=
    fun j hj => ho₂.word (by omega_arith) (by omega_arith)
  obtain lo₂ : wv s₂.mem B A (2 * w) = AdxSquare.crossValue s.mem B eb w := by
    obtain zero₂ : wv s₂.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
      rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega_arith]
      exact hz₂ _ (by omega_arith) (by omega_arith)
    rw [wv_add, zero₂, Nat.mul_zero, Nat.add_zero] at hv₂
    exact hv₂
  -- The diagonal's registers.
  obtain pD : WP isa (.block [.movqR .r8 .xmm1, .alu .add .r8 (.imm 16), .movqR .r10 .xmm0]) s₂ fun t =>
      t.gpr .r8 = off B A ∧ t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₂.mem ∧ Keep [.r8, .r10] s₂ t := by
    refine WP.mono (WP.keep [.r8, .r10] (Q := fun t => t.gpr .r8 = off B A ∧ t.gpr .r10 = BitVec.ofNat 64 w ∧
      t.mem = s₂.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
    xrun [hx₂, x1, x0, h8, h12, movq_lo, off_add16, RegUpd.xmm_setReg, RegUpd.xmm_setFlags]
    rfl
  refine WP.seq (WP.mono (WP.vecKeep (by decide) pD) fun s₃ ⟨⟨h8₃, h10₃, hm₃, k₃⟩, hx₃, _⟩ => ?_)
  obtain k13 := k12.trans k₃
  -- The diagonal.
  refine WP.mono (WP.vecKeep (by decide) (AdxSquare.diagonalWith_ok core_coreOk (hs.congr k13.2.2) h8₃
    ((k₃.gpr (by decide)).trans h9₂) h10₃ (by omega_arith) (by omega_arith) (by omega_arith) hb (by omega_arith)))
    fun t ⟨⟨hv, ho, kt⟩, hxt, _⟩ => ?_
  rw [hm₃] at hv ho
  rw [lo₂, AdxSquare.diagonalValue_congr read₂, AdxSquare.square_decomposition] at hv
  obtain bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    obtain hl := wv_lt s.mem B eb w
    obtain hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_arith] at hp
    exact hp
  obtain carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    obtain hc' : 1 ≤ (t.gpr .r15).toNat := by omega_arith
    obtain hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega_arith
  obtain hxs : t.xmm = s₁.xmm := by rw [hxt, hx₃, hx₂]
  refine ⟨?_, ?_, ho₂.trans (ho.mono (o' := A) (n' := 8 * (2 * w + 2)) (Nat.le_refl _) (by omega_arith)),
    (kt.gpr (by decide)).trans h8₃, by rw [hxs]; exact x14, by rw [hxs]; exact x15, by rw [hxs]; exact x0,
    by rw [hxs]; exact x1, by rw [hxs]; exact x2, by rw [hxs]; exact x3, fun x hx => by rw [hxs]; exact xo x hx,
    (k13.trans kt).mono (by decide)⟩
  · rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  · exact wv_zero fun k hk => by
      rw [ho.word (by omega_arith) (by omega_arith)]
      rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega_arith]
      exact hz₂ _ (by omega_arith) (by omega_arith)

theorem unstash_ok {s : State} {B : Addr} {o e : Nat} {w : Nat} {eN : Nat}
    (x0 : s.xmm .xmm0 = (0 : BitVec 64) ++ BitVec.ofNat 64 w) (x1 : s.xmm .xmm1 = (0 : BitVec 64) ++ off B e)
    (x2 : s.xmm .xmm2 = (0 : BitVec 64) ++ off B eN) (x14 : s.xmm .xmm14 = (0 : BitVec 64) ++ off B o) :
    WP isa (.block unstash) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B e ∧ t.gpr .r10 = off B eN ∧ t.gpr .rbx = off B o ∧
        t.mem = s.mem ∧ Keep [.r12, .rsi, .r10, .rbx] s t := by
  refine WP.mono (WP.keep [.r12, .rsi, .r10, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
    t.gpr .rsi = off B e ∧ t.gpr .r10 = off B eN ∧ t.gpr .rbx = off B o ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold unstash
  xrun [x0, x1, x2, x14, movq_lo, RegUpd.xmm_setReg]

/-- `square`: `[o] ≡ [a]² R⁻¹ (mod m)`, below `R`, and below `m` if `[a] < m`, from
`basesR`'s registers, `r9` the base of `a`, as `mmTailLazy_ok` says of the rounds. -/
theorem square_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hbx : s.gpr .rbx = off B (slot w o)) (h9 : s.gpr .r9 = off B (slot w a))
    (h10 : s.gpr .r10 = off B (slot w aN)) (h8 : s.gpr .r8 = off B (slot w aAcc))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h15 : s.gpr .r15 = minv) (hsi : s.gpr .rsi = off B (slot w aTmp))
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa square s fun t =>
      wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧ (∀ x, x ∉ stashed → t.xmm x = s.xmm x) := by
  have hn := hs.nowrap
  obtain sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  obtain hAT : slot w aAcc + 16 + 8 * w = slot w aTmp := by unfold slot aAcc aTmp; omega_arith
  obtain hNA : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_arith
  obtain hTs := sl aTmp (by decide)
  obtain hN0 : 0 < wv s.mem B (slot w aN) w := wv_pos_of_inv (by omega_arith) hinv
  obtain soX : slot w o + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := by
    have := slot_sep (w := w) ho1; have := slot_sep (w := w) ho2; unfold slot aAcc aTmp at *; omega_arith
  unfold square
  refine WP.seq (WP.mono (sqRaw_ok hs hZ hw hw' ha ha1 ha2 h9 h8 h12)
    fun s₁ ⟨hv₁, _, ho₁, h8₁, x14, x15, x0, x1, x2, x3, xo, k₁⟩ => ?_)
  obtain hNw : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega_arith) (by omega_arith)
  obtain hNv : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega_arith) (by omega_arith)
  -- The reduction.
  refine WP.seq (WP.mono (redc_ok (A := slot w aAcc + 16) (eN := slot w aN) (minv := minv)
    (hs.congr k₁.2.2) h8₁ (by rw [x0, h12]) (by rw [x2, h10]) (by rw [x15, h15]) (by rw [x3, hsi, hAT])
    (by omega_arith) (by omega_arith) (by omega_arith) hw' (by rw [hNw]; exact hinv))
    fun s₂ ⟨⟨q, hq, heq⟩, ho₂, h8₂, hx₂, k₂⟩ => ?_)
  rw [hAT, hv₁, hNv] at heq
  rw [hAT] at h8₂
  obtain k12 := k₁.trans k₂
  obtain hs₂ := hs.congr k12.2.2
  -- The registers of the subtraction and the selection.
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (unstash_ok (s := s₂) (B := B) (w := w) (e := slot w aAcc)
    (eN := slot w aN) (o := slot w o) (by rw [hx₂, x0, h12]) (by rw [hx₂, x1, h8]) (by rw [hx₂, x2, h10])
    (by rw [hx₂, x14, hbx]))) fun s₃ ⟨⟨h12₃, hsi₃, h10₃, hbx₃, hm₃, k₃⟩, hx₃, _⟩ => ?_)
  obtain h8₃ : s₃.gpr .r8 = off B (slot w aTmp) := (k₃.gpr (by decide)).trans h8₂
  -- `T - m`.
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (subMod_ok (hs₂.congr k₃.2.2) h8₃ h10₃ hsi₃ h12₃ (by omega_arith) hw' (by omega_arith)
    (by have := sl aN (by decide); omega_arith) (by have := sl aAcc (by decide); omega_arith) (by omega_arith) (by omega_arith)))
    fun s₄ ⟨⟨c, lt, hbp, hlt, hD, ho₄, k₄⟩, hx₄, _⟩ => ?_)
  rw [hm₃] at hlt hD ho₄
  -- The selection.
  refine WP.mono (WP.vecKeep (by decide) (selectAcc_ok (hs₂.congr (k₃.trans k₄).2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans hsi₃) ((k₄.gpr (by decide)).trans hbx₃) ((k₄.gpr (by decide)).trans h12₃) hbp
    (by omega_arith) hw' (by omega_arith) (by have := sl aAcc (by decide); omega_arith) (by have := sl o ho; omega_arith)
    (by omega_arith) (by omega_arith))) fun t ⟨⟨hv, hot, k₅⟩, hx₅, _⟩ => ?_
  -- The words of `T` (at `aTmp`), as after the reduction.
  obtain hT₄ : wv s₄.mem B (slot w aTmp) w = wv s₂.mem B (slot w aTmp) w :=
    ho₄.wv (by unfold slot aAcc aTmp; omega_arith) (by omega_arith)
  obtain hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    (ho₂.wv (by omega_arith) (by omega_arith)).trans hNv
  rw [hN₂] at hD
  obtain hsel : wv t.mem B (slot w o) w = if (word s₂.mem B (slot w aTmp + 8 * w)).toNat < c.toNat then
      wv s₂.mem B (slot w aTmp) w else wv s₄.mem B (slot w aAcc) w := by
    rw [hv, hT₄, hlt]
    by_cases h : (word s₂.mem B (slot w aTmp + 8 * w)).toNat < c.toNat <;> simp [h]
  obtain hNR := wv_lt s.mem B (slot w aN) w
  obtain hAR := wv_lt s.mem B (slot w a) w
  obtain hR0 : 0 < 2 ^ (64 * w) := Nat.two_pow_pos _
  rw [wv_top2] at heq
  obtain hTlt : wv s₂.mem B (slot w aTmp) w + 2 ^ (64 * w) * ((word s₂.mem B (slot w aTmp + 8 * w)).toNat +
      2 ^ 64 * (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) < wv s.mem B (slot w aN) w + 2 ^ (64 * w) := by
    have := redc_lt_add hq (Nat.mul_lt_mul'' hAR hAR) heq
    omega_arith
  obtain ⟨hlz, hlm⟩ := VG.Proof.Bignum.csub_lazy (Tl := wv s₂.mem B (slot w aTmp) w)
      (Tw := (word s₂.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₄.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      hNR (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _) hTlt hD
  refine ⟨?_, fun hA => ?_, ?_, ?_, ((k12.trans (k₃.trans k₄)).trans k₅).mono (by decide), fun x hx => ?_⟩
  · rw [hsel]; exact hlz
  · have h2m : wv s₂.mem B (slot w aTmp) w + 2 ^ (64 * w) * ((word s₂.mem B (slot w aTmp + 8 * w)).toNat +
        2 ^ 64 * (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) < 2 * wv s.mem B (slot w aN) w := by
      generalize wv s₂.mem B (slot w aTmp) w + 2 ^ (64 * w) * ((word s₂.mem B (slot w aTmp + 8 * w)).toNat +
        2 ^ 64 * (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) = T at heq ⊢
      obtain hX : wv s.mem B (slot w a) w * wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w * 2 ^ (64 * w) :=
        Nat.mul_lt_mul'' hA hAR
      obtain hqm : q * wv s.mem B (slot w aN) w < 2 ^ (64 * w) * wv s.mem B (slot w aN) w :=
        Nat.mul_lt_mul_of_pos_right hq hN0
      obtain hb : 2 ^ (64 * w) * T < 2 ^ (64 * w) * (2 * wv s.mem B (slot w aN) w) := by
        rw [heq, Nat.mul_comm (wv s.mem B (slot w aN) w) (2 ^ (64 * w)) ] at *
        rw [show 2 ^ (64 * w) * (2 * wv s.mem B (slot w aN) w) =
          2 ^ (64 * w) * wv s.mem B (slot w aN) w + 2 ^ (64 * w) * wv s.mem B (slot w aN) w by grind]
        omega_arith
      exact Nat.lt_of_mul_lt_mul_left hb
    rw [hsel, VG.Proof.Bignum.csub_result (Tl := wv s₂.mem B (slot w aTmp) w)
      (Tw := (word s₂.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₄.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      hNR (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _) h2m hD]
    exact Nat.mod_lt _ hN0
  · rw [hsel, Nat.mul_mod, hlm, ← Nat.mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    obtain h1 := hx aAcc (by simp)
    obtain h2 := hx aTmp (by simp)
    obtain h3 := hx o (by simp)
    rw [hot x (by omega_arith), ho₄ x (by unfold slot aAcc aTmp at *; omega_arith)]
    rw [ho₂ x (by unfold slot aAcc aTmp at *; omega_arith), ho₁ x (by unfold slot aAcc aTmp at *; omega_arith)]
  · rw [hx₅, hx₄, hx₃, hx₂]; exact xo x hx

/-- `cmp r11, r9`: ZF for the bases of `a` and `b`, so for `a = b`. -/
theorem cmpBases_ok {s : State} {B : Addr} {Z w a b : Nat} (hs : Scr s B Z) (hZ : slot w 8 ≤ Z)
    (ha : a < 8) (hb : b < 8) (h11 : s.gpr .r11 = off B (slot w a)) (h9 : s.gpr .r9 = off B (slot w b)) :
    WP isa (.block [.alu .cmp .r11 (.reg .r9)]) s fun t =>
      t.zf = some (decide (a = b)) ∧ t.gpr .r11 = off B (slot w a) ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  have hn := hs.nowrap
  obtain hsa := slot_le (w := w) ha
  obtain hsb := slot_le (w := w) hb
  obtain hab : decide (slot w a = slot w b) = decide (a = b) := by
    by_cases h : a = b
    · subst h; simp
    · have := slot_sep (w := w) h
      simp only [h, decide_false, decide_eq_false_iff_not]
      omega_arith
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.zf = some (decide (a = b)) ∧ t.gpr .r11 = off B (slot w a) ∧
    t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [h11, h9, off_sub_beq B (show slot w a < 2 ^ 64 by omega_arith) (show slot w b < 2 ^ 64 by omega_arith), hab]

/-- `mulTail`: what `mmTailLazy_ok` says of `montMul`'s rounds, by the rounds or,
for `a = b`, the square, which writes no vector register but `stashed`. -/
theorem tail_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hbx : s.gpr .rbx = off B (slot w o)) (h11 : s.gpr .r11 = off B (slot w a)) (h9 : s.gpr .r9 = off B (slot w b))
    (h10 : s.gpr .r10 = off B (slot w aN)) (h8 : s.gpr .r8 = off B (slot w aAcc))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h15 : s.gpr .r15 = minv) (hsi : s.gpr .rsi = off B (slot w aTmp))
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulTail s fun t =>
      wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧ (∀ x, x ∉ stashed → t.xmm x = s.xmm x) := by
  unfold mulTail
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (cmpBases_ok hs hZ ha hb h11 h9))
    fun s₁ ⟨⟨hz, h11₁, hm₁, k₁⟩, hx₁, _⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  rw [← hm₁] at hinv ⊢
  obtain post : ∀ t, (wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s₁.mem B (slot w b) w < wv s₁.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t ∧ (∀ x, x ∉ stashed → t.xmm x = s₁.xmm x)) →
      (wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s₁.mem B (slot w b) w < wv s₁.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t ∧ (∀ x, x ∉ stashed → t.xmm x = s.xmm x)) :=
    fun t ⟨h1, h2, h3, h4, k, hx⟩ => ⟨h1, h2, h3, h4, (k₁.trans k).mono (by decide), fun x h => (hx x h).trans
      (by rw [hx₁])⟩
  obtain r : ∀ {r : Reg}, r ≠ .r11 → s₁.gpr r = s.gpr r := fun h => k₁.gpr (by simp [h])
  by_cases hab : a = b
  · subst b
    refine WP.ite true (by simp [eval, hz]) (fun _ => ?_) (by simp)
    exact WP.mono (square_ok hs₁ hZ hw hw' ho ha ho1 ho2 ha1 ha2 ((r (by decide)).trans hbx)
      ((r (by decide)).trans h9) ((r (by decide)).trans h10) ((r (by decide)).trans h8) ((r (by decide)).trans h12)
      ((r (by decide)).trans h15) ((r (by decide)).trans hsi) hinv) post
  · refine WP.ite false (by simp [eval, hz, hab]) (by simp) (fun _ => ?_)
    refine WP.mono (WP.vecKeep (by decide) (mmTailLazy_ok hs₁ hZ hw hw' (by decide) (by decide) (by decide) ho ha
      hb (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2)
      ((r (by decide)).trans hbx) h11₁ ((r (by decide)).trans h9) ((r (by decide)).trans h10)
      ((r (by decide)).trans h8) ((r (by decide)).trans h12) ((r (by decide)).trans h15) ((r (by decide)).trans hsi)
      hinv)) fun t ⟨⟨h1, h2, h3, h4, k⟩, hx, _⟩ => post t ⟨h1, h2, h3, h4, k, fun x _ => by rw [hx]⟩
end VG.Proof.Bignum.X86_64.BaseSquare

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
theorem setXmm_mem (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
theorem setXmm_rd (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
theorem setXmm_wr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl
theorem setXmm_xmm (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl
theorem setReg_xmm (s : State) (d : Reg) (v : BitVec 64) : (s.setReg d v).xmm = s.xmm := rfl

theorem qword_movq (v : BitVec 64) : qword ((0 : BitVec 64) ++ v) 0 = v := by
  ext i hi; simp only [qword, BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [hi]

theorem ofNat32_64 {o : Nat} (h : o < 2 ^ 32) : (BitVec.ofNat 32 o).setWidth 64 = BitVec.ofNat 64 o := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega_arith

theorem arr_off (B : Addr) {j : Nat} (hj : j < 2 ^ 32) :
    off (B + (BitVec.ofNat 32 j).setWidth 64 * 8#64) (8 * sArr 0) = off B (8 * sArr j) := by
  rw [ofNat32_64 hj]
  simp only [off, sArr, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow]
  omega_arith

/-- The callee-saved registers of `s` in the low quadwords of `xmm8`–`xmm13`
of `t`, as `saves` leaves them. -/
def Saved (s t : State) : Prop :=
  t.xmm .xmm8 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm9 = (0 : BitVec 64) ++ s.gpr .rbp ∧
    t.xmm .xmm10 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm11 = (0 : BitVec 64) ++ s.gpr .r13 ∧
    t.xmm .xmm12 = (0 : BitVec 64) ++ s.gpr .r14 ∧ t.xmm .xmm13 = (0 : BitVec 64) ++ s.gpr .r15

theorem Saved.of_xmm {s t t' : State} (h : Saved s t) (hx : t'.xmm = t.xmm) : Saved s t' := by
  unfold Saved at *; rw [hx]; exact h

theorem Saved.of_stashed {s t t' : State} (h : Saved s t) (hx : ∀ x, x ∉ BaseSquare.stashed → t'.xmm x = t.xmm x) :
    Saved s t' := by
  unfold Saved at *
  rw [hx .xmm8 (by decide), hx .xmm9 (by decide), hx .xmm10 (by decide), hx .xmm11 (by decide),
    hx .xmm12 (by decide), hx .xmm13 (by decide)]
  exact h

theorem Saved.of_keep {s s' t : State} {rs : List Reg} (h : Saved s' t) (hk : Keep rs s s')
    (hr : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], r ∉ rs) : Saved s t := by
  unfold Saved at *
  rw [hk.gpr (hr .rbx (by simp)), hk.gpr (hr .rbp (by simp)), hk.gpr (hr .r12 (by simp)),
    hk.gpr (hr .r13 (by simp)), hk.gpr (hr .r14 (by simp)), hk.gpr (hr .r15 (by simp))] at h
  exact h

/-- `enter` and `basesR`: the bases of the arrays whose indices are in `edx`,
`ecx` and `r8d`, as `bases` gives them, and the callee-saved registers in
`xmm8`–`xmm13`. -/
theorem fnHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block (enter ++ basesR)) s fun t =>
      t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧ t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem ∧
      Keep [.rdx, .rcx, .r8, .rbx, .r11, .r9, .r10, .r12, .r15, .rsi] s t ∧
      Saved s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rdx, .rcx, .r8, .rbx, .r11, .r9, .r10, .r12, .r15, .rsi] (c := .block (enter ++ basesR))
    (Q := fun t => t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧
      t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem ∧
      Saved s t) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, k, h.2.2.2.2.2.2.2.2.2⟩
  unfold enter zext saves basesR Saved
  simp only [List.cons_append, List.nil_append]
  xrun [XOp.exec, setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr, setXmm_xmm, setReg_xmm, XBinOp.eval, qword_movq,
    State.ea, arrAt, hdr, hdi, hdx, hcx, h8, hdrOff, arr_off B (show o < 2 ^ 32 by omega_arith),
    arr_off B (show a < 2 ^ 32 by omega_arith), arr_off B (show b < 2 ^ 32 by omega_arith),
    hl (sArr o) (by unfold sArr; omega_arith), hl (sArr a) (by unfold sArr; omega_arith), hl (sArr b) (by unfold sArr; omega_arith),
    hl (sArr aN) (by decide), hl (sArr aAcc) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide),
    hl sMinv (by decide), hH.harr o ho, hH.harr a ha, hH.harr b hb, hH.harr aN (by decide),
    hH.harr aAcc (by decide), hH.harr aTmp (by decide), hH.hw, hH.hminv]

/-! ## Restoring the callee-saved registers -/

theorem fnExtract_lo (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  ext i h; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [h]

/-- A write of `w` bits changes only those bytes. -/
theorem writeW_outsideN (m : Mem) (base : Addr) {d w : Nat} (v : BitVec w) (h : d + w / 8 ≤ 2 ^ 64)
    (hw : 0 < w / 8) :
    Outside base d (w / 8) m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega_arith)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

/-- `unsaves`: the callee-saved registers of `s` back, from `t`'s `xmm8`–`xmm13`
as `saves` left them. -/
theorem unsaves_ok {s t : State} (h : Saved s t) :
    WP isa (.block unsaves) t fun t' =>
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t'.gpr r = s.gpr r) ∧ t'.mem = t.mem ∧
        t'.xmm = t.xmm ∧ Keep [.rbx, .rbp, .r12, .r13, .r14, .r15] t t' := by
  obtain ⟨x8, x9, x10, x11, x12, x13⟩ := h
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (c := .block unsaves)
    (Q := fun t' => (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t'.gpr r = s.gpr r) ∧ t'.mem = t.mem ∧
      t'.xmm = t.xmm) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold unsaves
  xrun [setReg_xmm, x8, x9, x10, x11, x12, x13, fnExtract_lo]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

/-- `vg_rsa_mont_mul`'s code: `[o] = [a] [b] R⁻¹ mod m` for the arrays whose
indices are in `edx`, `ecx` and `r8d`, as `montMul` computes it, changing
only `aAcc`, `aTmp` and `o`; and the callee-saved registers as they were. -/
theorem mulBase_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa mulBase s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  unfold mulBase
  refine WP.seq (WP.mono (fnHead_ok hs hdi hH hZ ho ha hb hdx hcx h8)
    fun s₁ ⟨hbx, h11, h9, h10, h8₁, h12, h15, hsi₁, hm₁, k₁, sv⟩ => ?_)
  rw [← hm₁] at hinv hB
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (BaseSquare.tail_ok hs₁ hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hbx h11 h9 h10 h8₁ h12
    h15 hsi₁ hinv) fun s₂ ⟨_, hlt, heq, har, k₂, hx₂⟩ => ?_)
  refine WP.mono (unsaves_ok (sv.of_stashed hx₂)) fun t ⟨rs, mt, _, k₃⟩ => ?_
  have hlt := hlt hB
  rw [hm₁] at hlt heq har
  rw [← mt] at hlt heq har
  exact ⟨hlt, heq, har, ((k₁.trans k₂).trans k₃).mono (by decide), rs⟩

/-- The indices, as `args` leaves them. -/
theorem fnArgs_ok (s : State) (o a b : Nat) :
    WP isa (.block (args o a b)) s fun t =>
      (t.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o ∧ (t.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a ∧
      (t.gpr .r8).setWidth 32 = BitVec.ofNat 32 b ∧ t.mem = s.mem ∧ Keep [.rdx, .rcx, .r8] s t := by
  refine WP.mono (WP.keep [.rdx, .rcx, .r8] (c := .block (args o a b))
    (Q := fun t => (t.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o ∧ (t.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a ∧
      (t.gpr .r8).setWidth 32 = BitVec.ofNat 32 b ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold args
  xrun

/-- The call of `vg_rsa_mont_mul`, inlined: what calls of it run as. -/
def mmFnBase (o a b : Nat) : Prog isa := (call "vg_rsa_mont_mul" mulBase o a b).inline

theorem mmFnBase_eq (o a b : Nat) : mmFnBase o a b = .seq (.block (args o a b)) mulBase := rfl

theorem mmFnBase_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₁ : (taint.check (Taint.ofRegs [.rdi]) (.seq (.block (args o a b)) (.block (enter ++ basesR))) hc₁).isSome = true)
    (h₂ : (taint.check (Taint.ofRegs [.rbx, .r11, .r9, .r10, .r8, .r12, .rsi])
      (.seq BaseSquare.mulTail (.block leave)) hc₂).isSome = true) :
    RelCT isa (Two GoodW) (mmFnBase o a b) fun _ _ => True := by
  rw [mmFnBase_eq]
  unfold mulBase
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := BasesL aN aAcc aTmp o a b) [.rdi] pins_goodW h₁
    fun L s ⟨_, hg, hZ⟩ => ?_) (two_taint _ (pins_bases aN aAcc aTmp o a b) h₂))
  refine WP.seq (WP.mono (fnArgs_ok s o a b) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
  have hH : Hdr t.mem L.B L.w _ := hm ▸ hg.hdr
  exact WP.mono (fnHead_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) hH hZ ho ha hb hdx hcx h8)
    fun u ⟨h1, h2, h3, h4, h5, h6, _, h8', _⟩ => ⟨h1, h2, h3, h4, h5, h6, h8'⟩

/-- Montgomery multiplication by calls of `vg_rsa_mont_mul`, as inlined code. -/
def Mont.fnBase : Mont where
  mm := mmFnBase
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d5 d4 d6 hinv hB := by
    rw [mmFnBase_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv hB ⊢
    refine WP.mono (mulBase_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ hw hw'
      ho ha hb d1 d2 d3 d5 d4 d6 hdx hcx h8 hinv hB) fun t' ⟨h1, h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      h1, h2, h3, (k.trans k').mono (by decide)⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact mmFnBase_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
