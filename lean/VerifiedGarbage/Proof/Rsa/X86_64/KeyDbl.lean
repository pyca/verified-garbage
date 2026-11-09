module
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKeyCore

import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math

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
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      SelInv s B Z eA eT eo lt 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by
      cases lt <;> rfl⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_arith) hw' (SelInv s B Z eA eT eo lt) h0 ?_)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩
  intro j _ hj t hI
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tbp : t.gpr .rbp = mask lt := (hI.keep.gpr (by decide)).trans hbp
  have hx : word t.mem B (eA + 8 * j) = word s.mem B (eA + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  have hy : word t.mem B (eT + 8 * j) = word s.mem B (eT + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if lt then word s.mem B (eA + 8 * j) else word s.mem B (eT + 8 * j)) ∧
      t₁.gpr .rbp = t.gpr .rbp) (by
      cases lt <;> xrun [mask, State.ea, ix, addr0 t8 hI.r14, addr0 tsi hI.r14, addr0 tbx hI.r14, tbp,
        hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith), hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega_arith),
        hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_arith), hx, hy, execCmov, eval]) rfl)
    fun t₁ ⟨⟨hm, hbp₁⟩, k₁'⟩ => ?_
  -- TEST updates flags but preserves the mask register.
  have k₁ : Keep [.rax, .rdx] t t₁ := ⟨fun r hr => by
    by_cases he : r = .rbp
    · subst r; exact hbp₁
    · exact k₁'.gpr (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or, and_assoc] using And.intro hr he), k₁'.2⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
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
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B em := (hI.keep.gpr (by decide)).trans h10
  have tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eo + 8 * j) = word s₀.mem B (eo + 8 * j) :=
    hI.frm.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith) (by omega_arith)
  have hy : word t.mem B (em + 8 * j) = word s₀.mem B (em + 8 * j) :=
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
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hvA : wv t'.mem B eA (j + 1) = wv t.mem B eA j + 2 ^ (64 * j) * a.toNat := by
    rw [hm', hm₁, (writeW_outside _ B d (by omega_arith)).wv (by omega_arith) (by omega_arith),
      wv_writeW_top _ _ _ _ _ (by omega_arith)]
  have hvT : wv t'.mem B eT (j + 1) = wv t.mem B eT j + 2 ^ (64 * j) * d.toNat := by
    rw [hm', hm₁, wv_writeW_top _ _ _ _ _ (by omega_arith),
      (writeW_outside _ B a (by omega_arith)).wv (by omega_arith) (by omega_arith)]
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    c', b', (k'.gpr (by decide)).trans hc', (k'.gpr (by decide)).trans hb', ?_, ?_⟩
  · rw [hm', hm₁]
    intro x hout
    have hxa := hout (eA, 8 * (j + 1)) (by simp)
    have hxt := hout (eT, 8 * (j + 1)) (by simp)
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
  have h8₁ : s₁.gpr .r8 = off B eA := (k₁.gpr (by decide)).trans h8
  have hbx₁ : s₁.gpr .rbx = off B eo := (k₁.gpr (by decide)).trans hbx
  have h10₁ : s₁.gpr .r10 = off B em := (k₁.gpr (by decide)).trans h10
  have hsi₁ : s₁.gpr .rsi = off B eT := (k₁.gpr (by decide)).trans hsi
  have h12₁ : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have hbp₁ : s₁.gpr .rbp = mask c₀ := (k₁.gpr (by decide)).trans hbp
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
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
  have k12 := k₁.trans hI.keep
  have h8₂ : s₂.gpr .r8 = off B eA := (k12.gpr (by decide)).trans h8
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 w := (k12.gpr (by decide)).trans h12
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp, .rdx] (Q := fun t => ∃ v : BitVec 64,
      t.mem = s₂.mem.writeW (off B (eA + 8 * w)) v ∧ v.toNat = c.toNat ∧
      t.gpr .rbp = mask (decide (c.toNat < b.toNat))) (by
      unfold cfFromRbp cfToRbp
      xrun [State.ea, ix, addr0 h8₂ h12₂, hc, hb, cf_mask,
        hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega_arith), sx0]
      refine ⟨_, rfl, ?_, ?_⟩ <;> cases c <;> cases b <;> rfl) rfl)
    fun s₃ ⟨⟨v, hm₃, hv, hbp₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have hs₃ := hI.scr.congr k₃.2.2
  have hAlow : wv s₃.mem B eA w = wv s₂.mem B eA w := by
    rw [hm₃]; exact (writeW_outside _ B v (by omega_arith)).wv (.inl (by omega_arith)) (by omega_arith)
  have hTlow : wv s₃.mem B eT w = wv s₂.mem B eT w := by
    rw [hm₃]; exact (writeW_outside _ B v (by omega_arith)).wv (by omega_arith) (by omega_arith)
  have f3 : Frm B [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)] s.mem s₃.mem := by
    rw [hm₃, ← hm₁]
    intro x hx
    have ha := hx (eA, 8 * (w + 1)) (by simp)
    have ht := hx (eT, 8 * w) (by simp)
    rw [writeW_outside _ B v (by omega_arith) x (by omega_arith)]
    exact hI.frm x fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith
  refine WP.mono (selectRem_ok hs₃ ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans hsi)
    ((k13.gpr (by decide)).trans hbx) ((k13.gpr (by decide)).trans h12) hbp₃ hw hw'
    (by omega_arith) hT ho (by omega_arith) sTo) fun t ⟨hSel, hot, kt⟩ => ?_
  refine ⟨fun hlt => ?_, f3.trans (Frm.of_outside hot (by simp)), (k13.trans kt).mono (by decide)⟩
  have hM0 : 0 < wv s.mem B em w := by omega_arith
  have h2 : 2 * wv s.mem B eo w + c₀.toNat < 2 * wv s.mem B em w := by
    have := Bool.toNat_le c₀; omega_arith
  have result := VG.Proof.Bignum.csub_result (Tl := wv s₂.mem B eA w) (Tw := c.toNat) (Tw1 := 0)
    (D := wv s₂.mem B eT w) (m := wv s.mem B em w) (R := 2 ^ (64 * w)) (c := b.toNat)
    (wv_lt _ _ _ _) (wv_lt _ _ _ _) (Bool.toNat_le b) (wv_lt _ _ _ _)
    (by rw [Nat.mul_zero, Nat.add_zero]; omega_arith) hS
  rw [Nat.mul_zero, Nat.add_zero, hD] at result
  rw [hSel, hAlow, hTlow, ← result]
  by_cases h : c.toNat < b.toNat <;> simp [h]

end VG.Proof.Rsa.X86_64.Key
