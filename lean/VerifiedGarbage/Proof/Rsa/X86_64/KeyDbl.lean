import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey

/-!
# `vg_rsa_check_key` on x86-64: doubling with a carry in

`dblIn`: `[o] := 2 [o] + c mod m` for `[o] < m` and the carry `c` in `rbp`
(`dblIn_ok`), as `double_ok` proves `vg_rsa_public`'s doubling from no
carry: the double into the accumulator (`w + 1` words), then `subMod` and
`selectAcc`.
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- After `j` words of `dblIn`'s loop, from the carry `c₀`:
`A_j + 2^(64 j) c = 2 O_j + c₀`. -/
structure DblInInv (s₀ : State) (B : Addr) (Z eA eo : Nat) (c₀ : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eA j + 2 ^ (64 * j) * c.toNat = 2 * wv s₀.mem B eo j + c₀.toNat

theorem dblInStep_ok {s₀ : State} {B : Addr} {Z w eA eo : Nat} {c₀ : Bool}
    (h8 : s₀.gpr .r8 = off B eA) (hbx : s₀.gpr .rbx = off B eo) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) {j : Nat} (hj : j < w) {t : State}
    (hI : DblInInv s₀ B Z eA eo c₀ j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.reg .rax),
        .store (ix .r8 .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ DblInInv s₀ B Z eA eo c₀ (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eA + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = 2 * (word t.mem B (eo + 8 * j)).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tbx hI.r14, hbp, cf_mask,
      hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    rw [adc_toNat]
    show (word t.mem B (eo + 8 * j)).toNat + (word t.mem B (eo + 8 * j)).toNat + c.toNat = _
    omega
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eo + 8 * j) = word s₀.mem B (eo + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
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
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      DblInInv s B Z eA eo c₀ 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨c₀, (k.gpr (by decide)).trans hbp, by rw [hm]; simp [wv]⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (DblInInv s B Z eA eo c₀) h0
    (fun j _ hj t hI => dblInStep_ok h8 hbx h12 (by omega) (by omega) ho (by omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have s₂si : s₂.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rsi = off B eT ∧
      ∃ v : BitVec 64, v.toNat = c.toNat ∧ t.mem = s₂.mem.writeW (off B (eA + 8 * w)) v)
    (by
      unfold cfFromRbp
      xrun [State.ea, ix, s₂si, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega), sx0]
      refine ⟨_, ?_, rfl⟩
      cases c <;> rfl) rfl) fun s₃ ⟨⟨hsi₃, v, hv, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have k13 := (hI.keep.trans k₃)
  have o3 : Outside B eA (8 * (w + 1)) s.mem s₃.mem := by
    rw [hm₃]
    intro x hx
    rw [writeW_outside s₂.mem B v (by omega) x (by omega)]
    exact hI.out x (by omega)
  have fN : wv s₃.mem B em w = wv s.mem B em w := o3.wv (by omega) (by omega)
  have hTl : wv s₃.mem B eA w = wv s₂.mem B eA w := by
    rw [hm₃]; exact (writeW_outside s₂.mem B v (by omega)).wv (Or.inl (by omega)) (by omega)
  have hTw : (word s₃.mem B (eA + 8 * w)).toNat = c.toNat := by
    rw [hm₃, word_writeW_self, hv]
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans h10)
    hsi₃ ((k13.gpr (by decide)).trans h12) (by omega) hw' hA hm hT sAT sTm)
    fun s₄ ⟨c', lt, hbp', hlt, hD, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have k14 := k13.trans k₄
  refine WP.mono (selectAcc_ok hs₄ ((k14.gpr (by decide)).trans h8) ((k₄.gpr (by decide)).trans hsi₃)
    ((k14.gpr (by decide)).trans hbx) ((k14.gpr (by decide)).trans h12) hbp' (by omega) hw'
    (by omega) hT ho (by omega) sTo) fun t ⟨hv', hot, k₅⟩ => ?_
  have hacc₄ : wv s₄.mem B eA w = wv s₃.mem B eA w := ho₄.wv (by omega) (by omega)
  rw [fN] at hD
  have hO₃ : wv s₂.mem B eo w = wv s.mem B eo w := hI.out.wv (by omega) (by omega)
  refine ⟨fun hlt' => ?_, ?_, (k14.trans k₅).mono (by decide)⟩
  · have hN0 : 0 < wv s.mem B em w := by omega
    rw [hv', hacc₄, hlt, hTw]
    have h2 : 2 * wv s.mem B eo w + c₀.toNat < 2 * wv s.mem B em w := by
      have := Bool.toNat_le c₀; omega
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B eA w) (Tw := c.toNat) (Tw1 := 0)
      (D := wv s₄.mem B eT w) (m := wv s.mem B em w) (R := 2 ^ (64 * w))
      (c := c'.toNat) (by have := wv_lt s.mem B em w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : c.toNat < c'.toNat <;> simp [h, hTl]
  · have f3 : Frm B [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)] s.mem s₃.mem :=
      Frm.of_outside o3 (by simp)
    have f4 : Frm B [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)] s₃.mem s₄.mem :=
      Frm.of_outside ho₄ (by simp)
    have f5 : Frm B [(eA, 8 * (w + 1)), (eT, 8 * w), (eo, 8 * w)] s₄.mem t.mem :=
      Frm.of_outside hot (by simp)
    exact (f3.trans f4).trans f5

end VG.Proof.Rsa.X86_64.Key
