module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKeyCore
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-! ### `Rsa.X86_64.KeyDbl`, which only this module used -/

section

/-!
# `vg_rsa_check_key` on x86-64: doubling with a carry in

`dblIn`: `[o] := 2 [o] + c mod m` for `[o] < m` and the carry `c` in `rbp`
(`dblIn_ok`), as `double_ok` proves `vg_rsa_public`'s doubling from no
carry: the double into the accumulator (`w + 1` words) and its difference
from the modulus share a limb scan, then `selectRem` chooses the result.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Selecting the remainder -/

theorem selectRem_ok {s : State} {B : Addr} {Z w eA eT eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (hsi : s.gpr .rsi = off B eT) (hbx : s.gpr .rbx = off B eo)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {lt : Bool} (hbp : s.gpr .rbp = mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) (sT : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa selectRem s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eT w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have hn := hs.nowrap
  unfold selectRem
  obtain h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      SelInv s B Z eA eT eo lt 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by
      cases lt <;> rfl⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_arith) hw' (SelInv s B Z eA eT eo lt) h0 ?_)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩
  intro j _ hj t hI
  obtain t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  obtain tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  obtain tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  obtain t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain tbp : t.gpr .rbp = mask lt := (hI.keep.gpr (by decide)).trans hbp
  obtain hx : word t.mem B (eA + 8 * j) = word s.mem B (eA + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  obtain hy : word t.mem B (eT + 8 * j) = word s.mem B (eT + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if lt then word s.mem B (eA + 8 * j) else word s.mem B (eT + 8 * j)) ∧
      t₁.gpr .rbp = t.gpr .rbp) (by
      cases lt <;> xrun [mask, State.ea, ix, addr0 t8 hI.r14, addr0 tsi hI.r14, addr0 tbx hI.r14, tbp,
        hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith), hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega_arith),
        hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_arith), hx, hy, execCmov, eval]) rfl)
    fun t₁ ⟨⟨hm, hbp₁⟩, k₁'⟩ => ?_
  -- TEST updates flags but preserves the mask register.
  obtain k₁ : Keep [.rax, .rdx] t t₁ := ⟨fun r hr => by
    by_cases he : r = .rbp
    · subst r; exact hbp₁
    · exact k₁'.gpr (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or, and_assoc] using And.intro hr he), k₁'.2⟩
  obtain t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  obtain t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hI.val]
    cases lt <;> simp [wv]


/-- Prefix sums of the fused doubling and subtraction scan. -/
structure DblSubInv (s₀ : State) (B : Addr) (Z eA eT eo em : Nat) (c₀ : Bool)
    (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  frm : Frm B [(eA, 8 * j), (eT, 8 * j)] s₀.mem t.mem
  val : ∃ c b : Bool, t.gpr .rbp = mask c ∧ t.gpr .rdx = mask b ∧
    wv t.mem B eA j + 2 ^ (64 * j) * c.toNat = 2 * wv s₀.mem B eo j + c₀.toNat ∧
    wv t.mem B eT j + wv s₀.mem B em j = wv t.mem B eA j + 2 ^ (64 * j) * b.toNat

theorem dblSubStep_ok {s₀ : State} {B : Addr} {Z w eA eT eo em : Nat} {c₀ : Bool}
    (h8 : s₀.gpr .r8 = off B eA) (hbx : s₀.gpr .rbx = off B eo)
    (h10 : s₀.gpr .r10 = off B em) (hsi : s₀.gpr .rsi = off B eT)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32)
    (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z) (hm : em + 8 * w ≤ Z)
    (sAo : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo)
    (sAm : em + 8 * w ≤ eA ∨ eA + 8 * w ≤ em)
    (sAT : eT + 8 * w ≤ eA ∨ eA + 8 * w ≤ eT)
    (sTm : em + 8 * w ≤ eT ∨ eT + 8 * w ≤ em)
    (sTo : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : DblSubInv s₀ B Z eA eT eo em c₀ j t) :
    WP isa (.block (dblSubWord ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ DblSubInv s₀ B Z eA eT eo em c₀ (j + 1) t' := by
  have hn := hI.scr.nowrap
  obtain t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  obtain tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  obtain t10 : t.gpr .r10 = off B em := (hI.keep.gpr (by decide)).trans h10
  obtain tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  obtain t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain hx : word t.mem B (eo + 8 * j) = word s₀.mem B (eo + 8 * j) :=
    hI.frm.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith) (by omega_arith)
  obtain hy : word t.mem B (em + 8 * j) = word s₀.mem B (em + 8 * j) :=
    hI.frm.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith) (by omega_arith)
  have hMA (v : BitVec 64) : word (t.mem.writeW (off B (eA + 8 * j)) v) B (em + 8 * j) =
      word t.mem B (em + 8 * j) :=
    (writeW_outside t.mem B v (by omega_arith)).word (by omega_arith) (by omega_arith)
  obtain ⟨c, b, hbp, hdx, hD, hS⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp, .rdx] (Q := fun t₁ =>
      ∃ c' b' : Bool, ∃ a d : BitVec 64,
        t₁.gpr .rbp = mask c' ∧ t₁.gpr .rdx = mask b' ∧
        t₁.mem = (t.mem.writeW (off B (eA + 8 * j)) a).writeW (off B (eT + 8 * j)) d ∧
        a.toNat + 2 ^ 64 * c'.toNat = 2 * (word s₀.mem B (eo + 8 * j)).toNat + c.toNat ∧
        d.toNat + (word s₀.mem B (em + 8 * j)).toNat + b.toNat = a.toNat + 2 ^ 64 * b'.toNat) (by
      unfold dblSubWord cfFromRbp cfToRbp
      xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tbx hI.r14, addr0 t10 hI.r14, addr0 tsi hI.r14,
        hbp, hdx, cf_mask, hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega_arith),
        hI.scr.ld (show em + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega_arith),
        hI.scr.st (show eT + 8 * j + 8 ≤ Z by omega_arith), hMA, hx, hy]
      refine ⟨_, _, _, _, rfl, rfl, rfl, ?_, sbb_toNat _ _ _⟩
      rw [adc_toNat]; omega_arith) rfl)
    fun t₁ ⟨⟨c', b', a, d, hc', hb', hm₁, hDa, hSd⟩, k₁⟩ => ?_
  obtain t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  obtain t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  obtain hvA : wv t'.mem B eA (j + 1) = wv t.mem B eA j + 2 ^ (64 * j) * a.toNat := by
    rw [hm', hm₁, (writeW_outside _ B d (by omega_arith)).wv (by omega_arith) (by omega_arith),
      wv_writeW_top _ _ _ _ _ (by omega_arith)]
  obtain hvT : wv t'.mem B eT (j + 1) = wv t.mem B eT j + 2 ^ (64 * j) * d.toNat := by
    rw [hm', hm₁, wv_writeW_top _ _ _ _ _ (by omega_arith),
      (writeW_outside _ B a (by omega_arith)).wv (by omega_arith) (by omega_arith)]
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    c', b', (k'.gpr (by decide)).trans hc', (k'.gpr (by decide)).trans hb', ?_, ?_⟩
  · rw [hm', hm₁]
    intro x hout
    obtain hxa := hout (eA, 8 * (j + 1)) (by simp)
    obtain hxt := hout (eT, 8 * (j + 1)) (by simp)
    rw [writeW_outside _ B d (by omega_arith) x (by omega_arith),
      writeW_outside _ B a (by omega_arith) x (by omega_arith)]
    exact hI.frm x fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith
  · rw [hvA, pow64_succ]
    simp only [wv]
    grind
  · rw [hvA, hvT, pow64_succ]
    simp only [wv]
    grind

/-- `[o] := 2 [o] + c mod m`, for `[o] < m` and the carry `c` in `rbp`;
the accumulator at `eA` (`w + 1` words) and the temporary at `eT`. -/
theorem dblIn_ok {s : State} {B : Addr} {Z w eo em eA eT : Nat} {c₀ : Bool} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eo) (h10 : s.gpr .r10 = off B em) (h8 : s.gpr .r8 = off B eA)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hsi : s.gpr .rsi = off B eT) (hbp : s.gpr .rbp = mask c₀)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ho : eo + 8 * w ≤ Z) (hm : em + 8 * w ≤ Z) (hA : eA + 8 * (w + 1) ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sAo : eo + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eo) (sAm : em + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ em)
    (sAT : eT + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eT) (sTm : eT + 8 * w ≤ em ∨ em + 8 * w ≤ eT)
    (sTo : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa dblIn s fun t =>
      (wv s.mem B eo w < wv s.mem B em w →
        wv t.mem B eo w = (2 * wv s.mem B eo w + c₀.toNat) % wv s.mem B em w) ∧
      Frm B [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)] s.mem t.mem ∧
      Keep [.rax, .rbp, .r14, .rdx] s t := by
  have hn := hs.nowrap
  unfold dblIn
  refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun t => t.mem = s.mem ∧ t.gpr .rdx = mask false)
    (by xrun) rfl) fun s₁ ⟨⟨hm₁, hdx₁⟩, k₁⟩ => ?_)
  obtain h8₁ : s₁.gpr .r8 = off B eA := (k₁.gpr (by decide)).trans h8
  obtain hbx₁ : s₁.gpr .rbx = off B eo := (k₁.gpr (by decide)).trans hbx
  obtain h10₁ : s₁.gpr .r10 = off B em := (k₁.gpr (by decide)).trans h10
  obtain hsi₁ : s₁.gpr .rsi = off B eT := (k₁.gpr (by decide)).trans hsi
  obtain h12₁ : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  obtain hbp₁ : s₁.gpr .rbp = mask c₀ := (k₁.gpr (by decide)).trans hbp
  obtain h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      DblSubInv s₁ B Z eA eT eo em c₀ 0 t := fun t h14 hm k _ =>
    ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by decide), h14, by rw [hm]; exact Frm.refl _ _ _,
      c₀, false, (k.gpr (by decide)).trans hbp₁, (k.gpr (by decide)).trans hdx₁,
      by simp [wv], by simp [wv]⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_arith) hw'
    (DblSubInv s₁ B Z eA eT eo em c₀) h0
    (fun j _ hj t hI => dblSubStep_ok h8₁ hbx₁ h10₁ hsi₁ h12₁ (by omega_arith)
      (by omega_arith) hT ho hm (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) sTo hj hI))
    fun s₂ hI => ?_)
  obtain ⟨c, b, hc, hb, hD, hS⟩ := hI.val
  rw [hm₁] at hD hS
  obtain k12 := k₁.trans hI.keep
  obtain h8₂ : s₂.gpr .r8 = off B eA := (k12.gpr (by decide)).trans h8
  obtain h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 w := (k12.gpr (by decide)).trans h12
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp, .rdx] (Q := fun t => ∃ v : BitVec 64,
      t.mem = s₂.mem.writeW (off B (eA + 8 * w)) v ∧ v.toNat = c.toNat ∧
      t.gpr .rbp = mask (decide (c.toNat < b.toNat))) (by
      unfold cfFromRbp cfToRbp
      xrun [State.ea, ix, addr0 h8₂ h12₂, hc, hb, cf_mask,
        hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega_arith), sx0]
      refine ⟨_, rfl, ?_, ?_⟩ <;> cases c <;> cases b <;> rfl) rfl)
    fun s₃ ⟨⟨v, hm₃, hv, hbp₃⟩, k₃⟩ => ?_)
  obtain k13 := k12.trans k₃
  obtain hs₃ := hI.scr.congr k₃.2.2
  obtain hAlow : wv s₃.mem B eA w = wv s₂.mem B eA w := by
    rw [hm₃]; exact (writeW_outside _ B v (by omega_arith)).wv (.inl (by omega_arith)) (by omega_arith)
  obtain hTlow : wv s₃.mem B eT w = wv s₂.mem B eT w := by
    rw [hm₃]; exact (writeW_outside _ B v (by omega_arith)).wv (by omega_arith) (by omega_arith)
  obtain f3 : Frm B [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)] s.mem s₃.mem := by
    rw [hm₃, ← hm₁]
    intro x hx
    obtain ha := hx (eA, 8 * (w + 1)) (by simp)
    obtain ht := hx (eT, 8 * w) (by simp)
    rw [writeW_outside _ B v (by omega_arith) x (by omega_arith)]
    exact hI.frm x fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith
  refine WP.mono (selectRem_ok hs₃ ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans hsi)
    ((k13.gpr (by decide)).trans hbx) ((k13.gpr (by decide)).trans h12) hbp₃ hw hw'
    (by omega_arith) hT ho (by omega_arith) sTo) fun t ⟨hSel, hot, kt⟩ => ?_
  refine ⟨fun hlt => ?_, f3.trans (Frm.of_outside hot (by simp)), (k13.trans kt).mono (by decide)⟩
  obtain hM0 : 0 < wv s.mem B em w := by omega_arith
  obtain h2 : 2 * wv s.mem B eo w + c₀.toNat < 2 * wv s.mem B em w := by
    have := Bool.toNat_le c₀; omega_arith
  obtain result := VG.Proof.Bignum.csub_result (Tl := wv s₂.mem B eA w) (Tw := c.toNat) (Tw1 := 0)
    (D := wv s₂.mem B eT w) (m := wv s.mem B em w) (R := 2 ^ (64 * w)) (c := b.toNat)
    (wv_lt _ _ _ _) (wv_lt _ _ _ _) (Bool.toNat_le b) (wv_lt _ _ _ _)
    (by rw [Nat.mul_zero, Nat.add_zero]; omega_arith) hS
  rw [Nat.mul_zero, Nat.add_zero, hD] at result
  rw [hSel, hAlow, hTlow, ← result]
  by_cases h : c.toNat < b.toNat <;> simp [h]

end VG.Proof.Rsa.X86_64.Key

end

end


/-!
# `vg_rsa_check_key` on x86-64: reduction by restoring division

The loop of the reduction: for each word of `x` from the top (`wordStep`,
`wordStep_ok`), each of its bits from the top (`bitStep`, `bitStep_ok`) is
shifted out of `r15` as the carry of `dblIn`: `r := 2 r + b mod m`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Bits -/

theorem shl_add_self (V : BitVec 64) (b : Nat) : (V <<< b) + (V <<< b) = V <<< (b + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_succ]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, ← Nat.two_mul, Nat.mul_comm 2, Nat.mul_assoc]

/-- The carry of doubling `V <<< b` is bit `63 - b` of `V`. -/
theorem cf_shl (V : BitVec 64) {b : Nat} (hb : b < 64) :
    decide (2 ^ 64 ≤ (V <<< b).toNat + (V <<< b).toNat) = decide (V.toNat / 2 ^ (63 - b) % 2 = 1) := by
  obtain h1 : decide (2 ^ 64 ≤ (V <<< b).toNat + (V <<< b).toNat) = (V <<< b).msb := by
    rw [BitVec.msb_eq_decide]; simp only [Nat.add_one_sub_one]; congr 1; apply propext; omega_using []
  rw [h1, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD]
  obtain e1 : 64 - 1 - b = 63 - b := by omega_using []
  rw [e1, show decide (64 - 1 < 64) = true by decide, show decide (64 - 1 < b) = false by simp; omega_using [hb],
    Nat.testBit_eq_decide_div_mod_eq]
  rfl

theorem bit_split (V k : Nat) : V / 2 ^ k = 2 * (V / 2 ^ (k + 1)) + V / 2 ^ k % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega_using []

theorem ofNat_sub_one {n : Nat} (h1 : 1 ≤ n) (_h2 : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1' : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub, h1']
  simp only [BitVec.toNat_ofNat]
  omega_using [h1]

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e; have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this; exact this
  · intro e; subst e; rfl

theorem dbl_mod (X c M : Nat) : (2 * (X % M) + c) % M = (2 * X + c) % M := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem toNat_decide {n : Nat} (p : Prop) [Decidable p] (h : p ↔ (n : Nat) % 2 = 1) :
    (decide p).toNat = n % 2 := by
  by_cases hp : p
  · simp only [hp, decide_true, Bool.toNat_true]; exact (h.mp hp).symm
  · have := mt h.mpr hp
    simp only [hp, decide_false, Bool.toNat_false]; omega_using [this]

/-! ## One bit -/

/-- The working arrays the reduction writes: `dblIn`'s accumulator and
temporary, and `r`. -/
def redRs (eA eT eo w : Nat) : List (Nat × Nat) := [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)]

/-- Where the reduction's loop works: `r` at `eo`, `m` at `em`, the accumulator
and temporary at `eA` and `eT`, and `x` at `eS`, `cnt` words. -/
structure RedLay (B : Addr) (Z w eo em eA eT eS cnt : Nat) : Prop where
  w1 : 1 ≤ w
  w2 : w < 2 ^ 31
  cnt1 : 1 ≤ cnt
  cnt2 : cnt < 2 ^ 31
  ho : eo + 8 * w ≤ Z
  hm : em + 8 * w ≤ Z
  hA : eA + 8 * (w + 1) ≤ Z
  hT : eT + 8 * w ≤ Z
  hS : eS + 8 * cnt ≤ Z
  sAo : eo + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eo
  sAm : em + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ em
  sAT : eT + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eT
  sTm : eT + 8 * w ≤ em ∨ em + 8 * w ≤ eT
  sTo : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo
  som : eo + 8 * w ≤ em ∨ em + 8 * w ≤ eo
  sSA : eS + 8 * cnt ≤ eA ∨ eA + 8 * (w + 1) ≤ eS
  sST : eS + 8 * cnt ≤ eT ∨ eT + 8 * w ≤ eS
  sSo : eS + 8 * cnt ≤ eo ∨ eo + 8 * w ≤ eS

/-- The registers the reduction's loop keeps. -/
structure RedRegs (B : Addr) (w eo em eA eT eS : Nat) (t : State) : Prop where
  bx : t.gpr .rbx = off B eo
  r10 : t.gpr .r10 = off B em
  r8 : t.gpr .r8 = off B eA
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  si : t.gpr .rsi = off B eT
  r9 : t.gpr .r9 = off B eS

theorem RedRegs.keep {B : Addr} {w eo em eA eT eS : Nat} {t t' : State} (h : RedRegs B w eo em eA eT eS t)
    {rs : List Reg} (k : Keep rs t t') (hr : ∀ r ∈ [Reg.rbx, .r10, .r8, .r12, .rsi, .r9], r ∉ rs) :
    RedRegs B w eo em eA eT eS t' :=
  ⟨(k.gpr (hr _ (by simp))).trans h.bx, (k.gpr (hr _ (by simp))).trans h.r10, (k.gpr (hr _ (by simp))).trans h.r8,
    (k.gpr (hr _ (by simp))).trans h.r12, (k.gpr (hr _ (by simp))).trans h.si, (k.gpr (hr _ (by simp))).trans h.r9⟩

/-- After `b` bits of the word `V`, from `r = P mod M` (`M` the number at
`em`, unchanged). -/
structure BitInv (Q : Prop) (s₁ : State) (B : Addr) (Z w eo em eA eT eS : Nat) (P : Nat) (V : BitVec 64) (b : Nat)
    (t : State) : Prop where
  scr : Scr t B Z
  regs : RedRegs B w eo em eA eT eS t
  keep : Keep [.rax, .rbp, .r14, .rdx, .r11, .r15] s₁ t
  r15 : t.gpr .r15 = V <<< b
  r11 : t.gpr .r11 = BitVec.ofNat 64 (64 - b)
  frm : Frm B (redRs eA eT eo w) s₁.mem t.mem
  val : Q → 0 < wv s₁.mem B em w →
    wv t.mem B eo w = (P * 2 ^ b + V.toNat / 2 ^ (64 - b)) % wv s₁.mem B em w

theorem bitStep_ok {Q : Prop} {s₁ : State} {B : Addr} {Z w eo em eA eT eS cnt : Nat} {P : Nat} {V : BitVec 64}
    (hL : RedLay B Z w eo em eA eT eS cnt) {b : Nat} (hb : b < 64) {t : State}
    (hI : BitInv Q s₁ B Z w eo em eA eT eS P V b t) :
    WP isa bitStep t fun t' => t'.zf = some (decide (b + 1 = 64)) ∧
      BitInv Q s₁ B Z w eo em eA eT eS P V (b + 1) t' := by
  have hn := hI.scr.nowrap
  obtain ⟨w1, w2, -, -, ho, hm, hA, hT, -, sAo, sAm, sAT, sTm, sTo, som, -, -, -⟩ := hL
  obtain hM : wv t.mem B em w = wv s₁.mem B em w :=
    hI.frm.wv_eq (fun r hr => by
      simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [sAm, sTm, som]) (by omega_using [hn, hm])
  unfold bitStep
  refine WP.seq (WP.mono (WP.keep [.rax, .r15, .rbp] (Q := fun t₁ =>
      t₁.gpr .r15 = V <<< (b + 1) ∧ t₁.gpr .rbp = mask (decide (V.toNat / 2 ^ (63 - b) % 2 = 1)) ∧
      t₁.mem = t.mem) (by
    xrun [hI.r15, shl_add_self]
    rw [cf_shl V hb]; rfl) rfl) fun t₁ ⟨⟨h15, hbp, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hI.scr.congr k₁.2.2
  obtain rg₁ := hI.regs.keep k₁ (by decide)
  refine WP.seq (WP.mono (dblIn_ok hs₁ rg₁.bx rg₁.r10 rg₁.r8 rg₁.r12 rg₁.si hbp w1 w2 ho hm hA hT sAo sAm sAT
    sTm sTo) fun t₂ ⟨hv₂, hf₂, k₂⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain rg₂ := rg₁.keep k₂ (by decide)
  obtain h11 : t₂.gpr .r11 = BitVec.ofNat 64 (64 - b) := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hI.r11)
  refine WP.mono (WP.keep [.r11] (Q := fun t' => t'.zf = some (decide (b + 1 = 64)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 (64 - (b + 1)) ∧ t'.mem = t₂.mem) (by
    xrun [h11, ofNat_sub_one (n := 64 - b) (by omega_using [hb]) (by omega_using []),
        ofNat_beq_zero (show 64 - b - 1 < 2 ^ 64 by omega_using [])]
    exact ⟨by congr 1; apply propext; omega_using [hb], by congr 1⟩) rfl)
    fun t' ⟨⟨hz, h11', hm'⟩, k'⟩ => ⟨hz, ?_⟩
  obtain k12 := (k₁.trans k₂).trans k'
  refine ⟨hs₂.congr k'.2.2, rg₂.keep k' (by decide), (hI.keep.trans k12).mono (by decide),
    (k'.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h15), h11', ?_, fun hq hM0 => ?_⟩
  · rw [hm']
    exact hI.frm.trans (by rw [← hm₁]; exact hf₂)
  · rw [hm']
    obtain hR : wv t₁.mem B eo w = (P * 2 ^ b + V.toNat / 2 ^ (64 - b)) % wv s₁.mem B em w := by
      rw [hm₁]; exact hI.val hq hM0
    obtain hM₁ : wv t₁.mem B em w = wv s₁.mem B em w := by rw [hm₁]; exact hM
    rw [hM₁] at hv₂
    rw [hv₂ (by rw [hR]; exact Nat.mod_lt _ hM0), hR, dbl_mod]
    congr 1
    obtain hc := toNat_decide (V.toNat / 2 ^ (63 - b) % 2 = 1) (n := V.toNat / 2 ^ (63 - b)) Iff.rfl
    obtain hs := bit_split V.toNat (63 - b)
    rw [show 63 - b + 1 = 64 - b by omega_using [hb]] at hs
    rw [hc, show 64 - (b + 1) = 63 - b by omega_using [], Nat.pow_succ, ← Nat.mul_assoc]
    omega_using [hs]

/-! ## One word, and the loop -/

/-- After the top `i` words of `x` (`cnt` words at `eS`): `r` their number
modulo `M`. -/
structure WInv (Q : Prop) (s₀ : State) (B : Addr) (Z w eo em eA eT eS cnt : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  regs : RedRegs B w eo em eA eT eS t
  keep : Keep [.rax, .rbp, .r14, .rdx, .r11, .r15, .r13] s₀ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 (cnt - i)
  frm : Frm B (redRs eA eT eo w) s₀.mem t.mem
  val : Q → 0 < wv s₀.mem B em w →
    wv t.mem B eo w = wv s₀.mem B (eS + 8 * (cnt - i)) i % wv s₀.mem B em w

theorem frm_word {B : Addr} {Z w eo eA eT d : Nat} {m m' : Mem} (h : Frm B (redRs eA eT eo w) m m')
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 ≤ Z) (sA : d + 8 ≤ eA ∨ eA + 8 * (w + 1) ≤ d)
    (sT : d + 8 ≤ eT ∨ eT + 8 * w ≤ d) (so : d + 8 ≤ eo ∨ eo + 8 * w ≤ d) : word m' B d = word m B d :=
  h.word_eq (fun r hr => by
    simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [sA, sT, so]) (by omega_using [hn, hd])

theorem frm_wv {B : Addr} {Z w eo eA eT d k : Nat} {m m' : Mem} (h : Frm B (redRs eA eT eo w) m m')
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 * k ≤ Z) (sA : d + 8 * k ≤ eA ∨ eA + 8 * (w + 1) ≤ d)
    (sT : d + 8 * k ≤ eT ∨ eT + 8 * w ≤ d) (so : d + 8 * k ≤ eo ∨ eo + 8 * w ≤ d) : wv m' B d k = wv m B d k :=
  h.wv_eq (fun r hr => by
    simp only [redRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [sA, sT, so]) (by omega_using [hn, hd])

theorem wordStep_ok {Q : Prop} {s₀ : State} {B : Addr} {Z w eo em eA eT eS cnt : Nat}
    (hL : RedLay B Z w eo em eA eT eS cnt) {i : Nat} (hi : i < cnt) {t : State}
    (hI : WInv Q s₀ B Z w eo em eA eT eS cnt i t) :
    WP isa wordStep t fun t' => t'.zf = some (decide (i + 1 = cnt)) ∧
      WInv Q s₀ B Z w eo em eA eT eS cnt (i + 1) t' := by
  have hn := hI.scr.nowrap
  have hL' := hL
  obtain ⟨w1, w2, c1, c2, ho, hm, hA, hT, hS, sAo, sAm, sAT, sTm, sTo, som, sSA, sST, sSo⟩ := hL'
  obtain hM : wv t.mem B em w = wv s₀.mem B em w := frm_wv hI.frm hn hm sAm (by omega_using [sTm]) (by omega_using [som])
  obtain hV : word t.mem B (eS + 8 * (cnt - i - 1)) = word s₀.mem B (eS + 8 * (cnt - i - 1)) :=
    frm_word hI.frm hn (by omega_using [c1, hS]) (by omega_using [c1, sSA]) (by omega_using [c1, sST]) (by omega_using [c1, sSo])
  unfold wordStep
  refine WP.seq (WP.mono (WP.keep [.r13, .r15, .r11] (Q := fun t₁ =>
      t₁.gpr .r13 = BitVec.ofNat 64 (cnt - i - 1) ∧
      t₁.gpr .r15 = word s₀.mem B (eS + 8 * (cnt - i - 1)) ∧ t₁.gpr .r11 = BitVec.ofNat 64 64 ∧
      t₁.mem = t.mem) (by
    xrun [hI.r13, ofNat_sub_one (n := cnt - i) (by omega_using [hi]) (by omega_using [c2]), State.ea, ix,
      addr0 hI.regs.r9 rfl, hI.scr.ld (show eS + 8 * (cnt - i - 1) + 8 ≤ Z by omega_using [c1, hS]),
          hV]) rfl) fun t₁ ⟨⟨h13, h15, h11, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hI.scr.congr k₁.2.2
  obtain rg₁ := hI.regs.keep k₁ (by decide)
  obtain hb0 : BitInv Q t₁ B Z w eo em eA eT eS (wv s₀.mem B (eS + 8 * (cnt - i)) i)
      (word s₀.mem B (eS + 8 * (cnt - i - 1))) 0 t₁ :=
    ⟨hs₁, rg₁, Keep.refl _ _, by rw [h15, BitVec.shiftLeft_zero], h11, Frm.refl _ _ _, fun hq hM0 => by
      rw [hm₁] at hM0 ⊢
      rw [hM] at hM0 ⊢
      rw [hI.val hq hM0, Nat.pow_zero, Nat.mul_one, Nat.sub_zero,
        Nat.div_eq_of_lt (word s₀.mem B (eS + 8 * (cnt - i - 1))).isLt, Nat.add_zero]⟩
  refine WP.seq (wp_upto (a := 0) (N := 64) (by decide)
    (BitInv Q t₁ B Z w eo em eA eT eS (wv s₀.mem B (eS + 8 * (cnt - i)) i) (word s₀.mem B (eS + 8 * (cnt - i - 1))))
    (fun b _ hb t hb' => bitStep_ok hL hb hb') (fun t₂ hB => ?_) hb0)
  obtain h13₂ : t₂.gpr .r13 = BitVec.ofNat 64 (cnt - i - 1) := (hB.keep.gpr (by decide)).trans h13
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.zf = some (decide (i + 1 = cnt)) ∧ t'.mem = t₂.mem ∧
      t'.gpr .r13 = BitVec.ofNat 64 (cnt - i - 1)) (by
    xrun [h13₂, BitVec.and_self, ofNat_beq_zero (show cnt - i - 1 < 2 ^ 64 by omega_using [c2])]
    congr 1; apply propext; omega_using [hi]) rfl) fun t' ⟨⟨hz, hm', h13'⟩, k'⟩ => ⟨hz, ?_⟩
  obtain k2 := hB.keep.trans k'
  refine ⟨hB.scr.congr k'.2.2, hB.regs.keep k' (by decide), ((hI.keep.trans k₁).trans k2).mono (by decide),
    by rw [h13', show cnt - (i + 1) = cnt - i - 1 by omega_using []], ?_, fun hq hM0 => ?_⟩
  · rw [hm']
    exact hI.frm.trans (by rw [← hm₁]; exact hB.frm)
  · have hM₁ : wv t₁.mem B em w = wv s₀.mem B em w := by rw [hm₁, hM]
    rw [hm', hB.val hq (by rw [hM₁]; exact hM0), hM₁, Nat.sub_self, Nat.pow_zero, Nat.div_one,
      show cnt - (i + 1) = cnt - i - 1 by omega_using [], show i + 1 = 1 + i by omega_using [], wv_add,
      show eS + 8 * (cnt - i - 1) + 8 * 1 = eS + 8 * (cnt - i) by omega_using [hi]]
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero,
      show 64 * 1 = 64 from rfl]
    rw [Nat.mul_comm (2 ^ 64), Nat.add_comm]

end VG.Proof.Rsa.X86_64.Key
