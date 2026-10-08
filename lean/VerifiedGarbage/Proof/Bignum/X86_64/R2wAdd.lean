import VerifiedGarbage.Proof.Bignum.X86_64.R2wSub
import VerifiedGarbage.Proof.Bignum.X86_64.Copy

/-!
# `R² mod m` by word steps on x86-64: adding `m` back

`addBack` adds `m` to `t` (`w + 1` words) if `t`'s top bit is set, modulo
`2^(64 (w + 1))` (`addBack_ok`).
-/

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

/-- `mov rax, [r8 + 8 r12]; add rax, rax; sbb r11, r11; mov ebp, 0`: the mask
of the top bit of `t`'s word `w` into `r11`. -/
theorem addHead_ok (s : State) {aT : Addr}
    (eT : s.gpr .r8 + s.gpr .r12 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aT)
    (hT : InRegions (s.rd ++ s.wr) aT 8) :
    WP isa (.block addHead) s fun t =>
      t.gpr .r11 = mask (decide (2 ^ 63 ≤ (s.mem.readW aT 64).toNat)) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem ∧ Keep [.rax, .r11, .rbp] s t := by
  refine WP.mono (WP.keep [.rax, .r11, .rbp] (Q := fun t =>
      t.gpr .r11 = mask (decide (2 ^ 63 ≤ (s.mem.readW aT 64).toNat)) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold addHead
  xrun [State.ea, ix, eT, hT]
  have := (s.mem.readW aT 64).isLt
  unfold mask
  congr 2
  exact congrArg _ (decide_eq_decide.mpr (by omega))

/-- `mov rax, [r10 + 8 r14]; and rax, r11; add rbp, rbp; adc rax, [r8 + 8 r14];
sbb rbp, rbp; mov [r8 + 8 r14], rax`: `v + 2^64 c' = (mᵢ & mask) + tᵢ + c`. -/
theorem addSt_ok (s : State) {aM aT : Addr} {c n : Bool}
    (eM : s.gpr .r10 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aM)
    (eT : s.gpr .r8 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aT)
    (hM : InRegions (s.rd ++ s.wr) aM 8) (hTr : InRegions (s.rd ++ s.wr) aT 8) (hT : InRegions s.wr aT 8)
    (hbp : s.gpr .rbp = mask c) (h11 : s.gpr .r11 = mask n) :
    WP isa (.block addBody) s fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aT v ∧ t.gpr .rbp = mask c' ∧
        v.toNat + 2 ^ 64 * c'.toNat = (if n then (s.mem.readW aM 64).toNat else 0) + (s.mem.readW aT 64).toNat +
          c.toNat ∧
      Keep [.rax, .rbp] s t := by
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aT v ∧ t.gpr .rbp = mask c' ∧
        v.toNat + 2 ^ 64 * c'.toNat = (if n then (s.mem.readW aM 64).toNat else 0) + (s.mem.readW aT 64).toNat +
          c.toNat) ?_ rfl) fun t ⟨h, k⟩ => let ⟨v, c', h1, h2, h3⟩ := h; ⟨v, c', h1, h2, h3, k⟩
  unfold addBody cfFromRbp cfToRbp
  xrun [State.ea, ix, eM, eT, hM, hTr, hT, hbp, h11, cf_mask]
  refine ⟨_, _, rfl, rfl, ?_⟩
  rw [adc_toNat, and_mask_toNat]

/-- `mov rax, [r8 + 8 r12]; add rbp, rbp; adc rax, 0; mov [r8 + 8 r12], rax`. -/
theorem addTop_ok (s : State) {aT : Addr} {c : Bool}
    (eT : s.gpr .r8 + s.gpr .r12 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aT)
    (hTr : InRegions (s.rd ++ s.wr) aT 8) (hT : InRegions s.wr aT 8) (hbp : s.gpr .rbp = mask c) :
    WP isa (.block addTop) s fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aT v ∧
        v.toNat + 2 ^ 64 * c'.toNat = (s.mem.readW aT 64).toNat + c.toNat ∧ Keep [.rax, .rbp] s t := by
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aT v ∧
        v.toNat + 2 ^ 64 * c'.toNat = (s.mem.readW aT 64).toNat + c.toNat) ?_ rfl)
    fun t ⟨h, k⟩ => let ⟨v, c', h1, h2⟩ := h; ⟨v, c', h1, h2, k⟩
  unfold addTop cfFromRbp
  xrun [State.ea, ix, eT, hTr, hT, hbp, cf_mask, sx0]
  have := adc_toNat (s.mem.readW aT 64) 0 c
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this
  exact ⟨_, _, rfl, this⟩

/-- After words `0, …, j - 1` of `addBack`'s loop from `s₀`, adding `m` iff
`n`: `T'_j + 2^(64 j) c = T_j + n M_j`. -/
structure AbInv (s₀ : State) (B : Addr) (Z em et : Nat) (n : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B et (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B et j + 2 ^ (64 * j) * c.toNat = wv s₀.mem B et j + if n then wv s₀.mem B em j else 0

theorem abStep_ok {s₀ : State} {B : Addr} {Z w em et : Nat} {n : Bool}
    (h10 : s₀.gpr .r10 = off B em) (h8 : s₀.gpr .r8 = off B et) (h11 : s₀.gpr .r11 = mask n)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 31) (hM : em + 8 * w ≤ Z)
    (hT : et + 8 * (w + 1) ≤ Z) (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et)
    {j : Nat} (hj : j < w) {t : State} (hI : AbInv s₀ B Z em et n j t) :
    WP isa (.block (addBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ AbInv s₀ B Z em et n (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t10 : t.gpr .r10 = off B em := (hI.keep.gpr (by decide)).trans h10
  have t8 : t.gpr .r8 = off B et := (hI.keep.gpr (by decide)).trans h8
  have t11 : t.gpr .r11 = mask n := (hI.keep.gpr (by decide)).trans h11
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (addSt_ok t (addr0 t10 hI.r14) (addr0 t8 hI.r14) (hI.scr.ld (by omega)) (hI.scr.ld (by omega))
    (hI.scr.st (by omega)) hbp t11) fun t₁ ⟨v, c', hm₁, hbp₁, hv₁, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : t.mem.readW (off B (et + 8 * j)) 64 = word s₀.mem B (et + 8 * j) :=
    hI.out.word (Or.inr (Nat.le_refl _)) (by omega)
  have hy : t.mem.readW (off B (em + 8 * j)) 64 = word s₀.mem B (em + 8 * j) :=
    hI.out.word (by omega) (by omega)
  rw [hx, hy] at hv₁
  have hmem : t'.mem = t.mem.writeW (off B (et + 8 * j)) v := by rw [hm', hm₁]
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans hbp₁, ?_⟩⟩
  · rw [hmem]
    intro x hx'
    rw [writeW_outside t.mem B v (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    cases n <;> simp only [ite_true, ite_false, Bool.false_eq_true, Nat.add_zero] at hval hv₁ ⊢ <;> grind

/-- `t := t + m` (both from `s`) if the top bit of `t`'s word `w` is set,
modulo `2^(64 (w + 1))`, for `t` at `r8` and `m` at `r10`. -/
theorem addBack_ok {s : State} {B : Addr} {Z w em et : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B em) (h8 : s.gpr .r8 = off B et) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hM : em + 8 * w ≤ Z) (hT : et + 8 * (w + 1) ≤ Z)
    (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et) :
    WP isa addBack s fun t => ∃ c : Bool,
      wv t.mem B et (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat = wv s.mem B et (w + 1) +
        (if 2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat then wv s.mem B em w else 0) ∧
      Outside B et (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .r11, .rbp, .r14] s t := by
  have hn := hs.nowrap
  unfold addBack
  refine WP.seq (WP.mono (addHead_ok s (addr0 h8 h12) (hs.ld (by omega))) fun t₁ ⟨h11, hbp₁, hm₁, k₁⟩ => ?_)
  generalize hN : decide (2 ^ 63 ≤ (s.mem.readW (off B (et + 8 * w)) 64).toNat) = N at h11
  have t₁10 : t₁.gpr .r10 = off B em := (k₁.gpr (by decide)).trans h10
  have t₁8 : t₁.gpr .r8 = off B et := (k₁.gpr (by decide)).trans h8
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = t₁.mem → Keep [.r14] t₁ t → t.cf = t₁.cf →
      AbInv t₁ B Z em et N 0 t := fun t h14 hm k _ =>
    ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp₁, by cases N <;> simp [wv]⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (AbInv t₁ B Z em et N) h0
    (fun j _ hj t hI => abStep_ok t₁10 t₁8 h11 t₁12 hw' hM hT sM hj hI)) fun t₂ hI => ?_)
  obtain ⟨c, hbp₂, hval⟩ := hI.val
  have t₂8 : t₂.gpr .r8 = off B et := (hI.keep.gpr (by decide)).trans t₁8
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans t₁12
  refine WP.mono (addTop_ok t₂ (addr0 t₂8 t₂12) (hI.scr.ld (by omega)) (hI.scr.st (by omega)) hbp₂)
    fun t ⟨v, c', hm, hv, k⟩ => ⟨c', ?_, ?_, ((k₁.trans hI.keep).trans k).mono (by decide)⟩
  · have hx : t₂.mem.readW (off B (et + 8 * w)) 64 = word s.mem B (et + 8 * w) := by
      show word t₂.mem B (et + 8 * w) = _
      rw [hI.out.word (Or.inr (Nat.le_refl _)) (by omega), hm₁]
    rw [hx] at hv
    rw [hm, wv_writeW_top _ _ _ _ _ (by omega)]
    rw [hm₁] at hval
    have hN' : (2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat) = (N = true) := by
      rw [← hN]; simp only [decide_eq_true_eq]
    simp only [wv]
    rw [pow64_succ]
    cases N <;> simp only [hN', ite_true, ite_false, Bool.false_eq_true, Nat.add_zero] at hval ⊢ <;>
      grind
  · rw [hm]
    intro x hx
    rw [writeW_outside t₂.mem B v (by omega) x (by omega)]
    rw [hI.out x (by omega), hm₁]

end VG.Proof.Bignum.X86_64.R2w
