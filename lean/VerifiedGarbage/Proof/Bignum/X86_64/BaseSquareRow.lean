module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRow
public import VerifiedGarbage.Impl.Bignum.X86_64.BaseSquare
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.Omega

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
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .r13).toNat / 2 ^ 64)) (s.mem.readW aX 64) (by omega)
  have e2 := addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .r13).toNat) + s.mem.readW aX 64)
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .r13).toNat / 2 ^ 64) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat *
        (s.gpr .r13).toNat)).toNat + (s.mem.readW aX 64).toNat))).setWidth 64) (s.gpr .rcx) (by omega)
  rw [e2, Nat.mul_comm (s.gpr .r13).toNat]
  omega

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
    (hI.scr.ld (by omega)) (hI.scr.ld (by omega)) (hI.scr.st (by omega))) rfl) fun t₁ ⟨⟨lo, hm, hv⟩, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁bp : t₁.gpr .rbp = BitVec.ofNat 64 n := (k₁.gpr (by decide)).trans tbp
  refine WP.mono (countBp_ok t₁ t₁14 t₁bp (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hk : Keep [.rax, .rdx, .rcx, .r14] s₀ t' := ((hI.keep.trans k₁).trans k').mono (by decide)
  have hcx : t'.gpr .rcx = t₁.gpr .rcx := k'.gpr (by decide)
  have hmem : t'.mem = t.mem.writeW (off B (e + 8 * j)) lo := hm'.trans hm
  have hx : t.mem.readW (off B (e + 8 * j)) 64 = word s₀.mem B (e + 8 * j) :=
    hI.out.word (Or.inr (Nat.le_refl _)) (by omega)
  have hy : t.mem.readW (off B (eb + 8 * j)) 64 = word s₀.mem B (eb + 8 * j) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), hk, h14, ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega), hcx]
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
