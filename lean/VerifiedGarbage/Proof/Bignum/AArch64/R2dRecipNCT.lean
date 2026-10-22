module

public import VerifiedGarbage.Proof.Bignum.AArch64.R2dCT
public import VerifiedGarbage.Proof.Bignum.Recip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecipN
import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dCT
meta import VerifiedGarbage.Proof.Bignum.Recip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecipN
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# The reciprocal by Newton steps leaks only `m`

`R2Div.recipN`'s loops branch on `v` and `d`, which agree in runs that agree
on `m`: `d` is `m`'s top word, and `v` starts as `guessV d`. The relations fix
`m` (`R2pF1`), then also `d` and `v` (`RD`, `RU`); `recipN_ct` takes
`neg`'s relation to `recip`'s (`R2dF2`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Proof.Bignum VG.Proof.Bignum.Recip
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)

/-- After `neg`, with `m`. -/
def R2pF1 (q : Ws × Nat) (s : State) : Prop := R2dF1 q.1 s ∧ wv s.mem q.1.B (slot q.1.w aN) q.1.w = q.2

/-- `m`'s top word. -/
def topW (q : Ws × Nat) : Nat := q.2 / 2 ^ (64 * (q.1.w - 1)) % 2 ^ 64

theorem topW_lt (q : Ws × Nat) : topW q < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem R2pF1.top {q : Ws × Nat} {s : State} (h : R2pF1 q s) :
    word s.mem q.1.B (slot q.1.w aN + 8 * (q.1.w - 1)) = BitVec.ofNat 64 (topW q) := by
  obtain ⟨⟨⟨⟨_, -, hw, -⟩, -, -⟩, -⟩, hn⟩ := h
  have hsplit := wv_split1 s.mem q.1.B (slot q.1.w aN) (show 1 ≤ q.1.w by omega)
  rw [hn] at hsplit
  have hlt := wv_lt s.mem q.1.B (slot q.1.w aN) (q.1.w - 1)
  have hP := Nat.two_pow_pos (64 * (q.1.w - 1))
  have hT : q.2 / 2 ^ (64 * (q.1.w - 1)) = (word s.mem q.1.B (slot q.1.w aN + 8 * (q.1.w - 1))).toNat := by
    rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hlt, Nat.zero_add]
  apply BitVec.eq_of_toNat_eq
  rw [topW, hT, BitVec.toNat_ofNat, Nat.mod_mod]
  exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm

theorem pins_R2pF1 : Pins R2pF1 [.x9, .x6, .x12, .x7] := fun q s₁ s₂ h₁ h₂ => pins_R2dF1 q.1 s₁ s₂ h₁.1 h₂.1

/-- `R2pF1` after code that keeps memory and `x0`, `x6`, `x7`, `x9`, `x12`. -/
theorem R2pF1.keep {q : Ws × Nat} {s t : State} {rs : List Reg} (h : R2pF1 q s) (hm : t.mem = s.mem)
    (k : Keep rs s t) (h0 : .x0 ∉ rs) (h6 : .x6 ∉ rs) (h7 : .x7 ∉ rs) (h9 : .x9 ∉ rs) (h12 : .x12 ∉ rs) :
    R2pF1 q t := by
  obtain ⟨⟨hf, a9, a6, a12, a7, hx⟩, hn⟩ := h
  exact ⟨⟨hf.arr k h0 (j := aR2) (by decide) (by decide) (by rw [hm]; exact fun _ _ => rfl), (k.gpr .x9 h9).trans a9,
    (k.gpr .x6 h6).trans a6, (k.gpr .x12 h12).trans a12, (k.gpr .x7 h7).trans a7, by rw [hm]; exact hx⟩,
    by rw [hm]; exact hn⟩

/-! ## The corrections -/

/-- `R2pF1`, `d` in `x5` and the word `v` in `x10`. -/
def RD (q : (Ws × Nat) × Nat) (s : State) : Prop :=
  R2pF1 q.1 s ∧ s.gpr .x5 = BitVec.ofNat 64 (topW q.1) ∧ s.gpr .x10 = BitVec.ofNat 64 q.2 ∧ q.2 < 2 ^ 64

theorem pins_RD (n : Nat) : Pins (fun a s => RD (a, n) s) [.x10, .x5] := by
  intro a s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.1, h₂.2.1]

theorem RD.keep {q : (Ws × Nat) × Nat} {s t : State} {rs : List Reg} (h : RD q s) (hm : t.mem = s.mem)
    (k : Keep rs s t) (h0 : .x0 ∉ rs) (h5 : .x5 ∉ rs) (h6 : .x6 ∉ rs) (h7 : .x7 ∉ rs) (h9 : .x9 ∉ rs)
    (h12 : .x12 ∉ rs) {v : Nat} (h10 : t.gpr .x10 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) : RD (q.1, v) t :=
  ⟨h.1.keep hm k h0 h6 h7 h9 h12, (k.gpr .x5 h5).trans h.2.1, h10, hv⟩

/-- With `(2^64 + v) d < 2^128`. -/
def RU0 (q : (Ws × Nat) × Nat) (s : State) : Prop := RD q s ∧ over q.2 (topW q.1) = false

/-- `RU0`, with `x15` one. -/
def RU (q : (Ws × Nat) × Nat) (s : State) : Prop := RU0 q s ∧ s.gpr .x15 = BitVec.ofNat 64 1

theorem downLoop_ct : RelCT isa (Two RD) (.loop (.block recipDown) (.nonzero .x .x16)) (Two RU0) := by
  have key : ∀ n, RelCT isa (Two fun a s => RD (a, n) s) (.loop (.block recipDown) (.nonzero .x .x16)) (Two RU0) := by
    refine RelCT.loop (M := isa) (fun n => Two fun a s => RD (a, n) s) fun n => ?_
    refine (two_post (Φ := fun a s => RD (a, n) s)
      (Ψ := fun a s => RD (a, n - (over n (topW a)).toNat) s ∧
        isa.eval (.nonzero .x .x16) s = some (over n (topW a)))
      (two_taint [.x10, .x5] (pins_RD n) (by taint_decide)) fun a s h => ?_).mono (fun _ _ h => h) ?_
    · have h7 : s.gpr .x7 = 0 := h.1.1.2.2.2.2.1
      exact WP.mono (down_ok h.2.2.1 h.2.2.2 h.2.1 (topW_lt a) h7) fun t ⟨⟨h10, h16, hm⟩, k⟩ =>
        ⟨h.keep hm k (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h10
          (by omega_using [h.2.2.2]), by rw [eval_nonzero, h16, bit_ne_zero]⟩
    · rintro s₁ s₂ ⟨a, ⟨h₁, z₁⟩, ⟨h₂, z₂⟩, hsp⟩
      refine ⟨by rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
      · have ho : over n (topW a) = false := Option.some.inj (z₁.symm.trans hf)
        rw [ho, Bool.toNat_false, Nat.sub_zero] at h₁ h₂
        exact ⟨(a, n), ⟨h₁, ho⟩, ⟨h₂, ho⟩, hsp⟩
      · have ho : over n (topW a) = true := Option.some.inj (z₁.symm.trans ht)
        rw [ho, Bool.toNat_true] at h₁ h₂
        exact ⟨n - 1, by have := over_pos (topW_lt a) ho; omega_using [this], a, h₁, h₂, hsp⟩
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂, hsp⟩ e₁ e₂ => key q.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨q.1, h₁, h₂, hsp⟩ e₁ e₂

theorem upLoop_ct : RelCT isa (Two RU) (.loop (.block recipUp) (.nonzero .x .x16))
    (Two fun q s => RU q s ∧ up q.2 (topW q.1) = false) := by
  have key : ∀ n, RelCT isa (Two fun (q : (Ws × Nat) × Nat) s => n = 2 ^ 64 - q.2 ∧ RU q s)
      (.loop (.block recipUp) (.nonzero .x .x16)) (Two fun q s => RU q s ∧ up q.2 (topW q.1) = false) := by
    refine RelCT.loop (M := isa) (fun n => Two fun (q : (Ws × Nat) × Nat) s => n = 2 ^ 64 - q.2 ∧ RU q s)
      fun n => ?_
    refine (two_post (Φ := fun (q : (Ws × Nat) × Nat) s => n = 2 ^ 64 - q.2 ∧ RU q s)
      (Ψ := fun q s => n = 2 ^ 64 - q.2 ∧ RD (q.1, q.2 + (up q.2 (topW q.1)).toNat) s ∧
        s.gpr .x15 = BitVec.ofNat 64 1 ∧ over q.2 (topW q.1) = false ∧
        isa.eval (.nonzero .x .x16) s = some (up q.2 (topW q.1)))
      (two_taint [.x10, .x5] (fun q s₁ s₂ h₁ h₂ => pins_RD q.2 q.1 s₁ s₂ h₁.2.1.1 h₂.2.1.1) (by taint_decide))
      fun q s h => ?_).mono (fun _ _ h => h) ?_
    · obtain ⟨hn, ⟨hd, ho⟩, h15⟩ := h
      have h7 : s.gpr .x7 = 0 := hd.1.1.2.2.2.2.1
      have hb : q.2 + (up q.2 (topW q.1)).toNat < 2 ^ 64 := by
        cases hu : up q.2 (topW q.1)
        · simp only [Bool.toNat_false, Nat.add_zero]; exact hd.2.2.2
        · unfold up at hu
          rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hu
          simp only [Bool.toNat_true]; omega_using [hd.2.2.2, hu.1]
      exact WP.mono (up_ok hd.2.2.1 hd.2.2.2 hd.2.1 (topW_lt q.1) h7 h15) fun t ⟨⟨h10, h16, hm⟩, k⟩ =>
        ⟨hn, hd.keep hm k (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h10 hb,
          (k.gpr .x15 (by decide)).trans h15, ho, by rw [eval_nonzero, h16, bit_ne_zero]⟩
    · rintro s₁ s₂ ⟨q, ⟨hn, h₁, f₁, ho, z₁⟩, ⟨-, h₂, f₂, -, z₂⟩, hsp⟩
      refine ⟨by rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
      · have hu : up q.2 (topW q.1) = false := Option.some.inj (z₁.symm.trans hf)
        rw [hu, Bool.toNat_false, Nat.add_zero] at h₁ h₂
        exact ⟨q, ⟨⟨⟨h₁, ho⟩, f₁⟩, hu⟩, ⟨⟨⟨h₂, ho⟩, f₂⟩, hu⟩, hsp⟩
      · have hu : up q.2 (topW q.1) = true := Option.some.inj (z₁.symm.trans ht)
        rw [hu, Bool.toNat_true] at h₁ h₂
        unfold up at hu
        rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not] at hu
        exact ⟨2 ^ 64 - (q.2 + 1), by omega_using [hn, h₁.2.2.2, hu.1], (q.1, q.2 + 1),
          ⟨rfl, ⟨h₁, hu.2⟩, f₁⟩, ⟨rfl, ⟨h₂, hu.2⟩, f₂⟩, hsp⟩
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂, hsp⟩ e₁ e₂ =>
    key (2 ^ 64 - q.2) s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩, hsp⟩ e₁ e₂

/-! ## The reciprocal -/

/-- `recipN` leaks the same in runs that agree on `m`, and does what `recip`
does. -/
theorem recipN_ct : RelCT isa (Two R2pF1) recipN (Two fun (q : Ws × Nat) s => R2dF2 q.1 s) := by
  unfold recipN
  simp only [seqs]
  -- The guess.
  have hguess : RelCT isa (Two R2pF1) (.block recipGuess) (Two RD) := by
    refine (two_piece (Ψ := fun (q : Ws × Nat) s => RD (q, (guessV (BitVec.ofNat 64 (topW q))).toNat) s)
      _ pins_R2pF1 (by taint_decide) fun q s h => ?_).mono (fun _ _ h => h)
        fun s₁ s₂ ⟨q, h₁, h₂, hsp⟩ => ⟨(q, (guessV (BitVec.ofNat 64 (topW q))).toNat), h₁, h₂, hsp⟩
    have ht := h.top
    obtain ⟨⟨hf, h9, h6, h12, h7, -⟩, -⟩ := id h
    obtain ⟨_, hg, hw, hw'⟩ := hf.1
    have hsm := slot_le (w := q.1.w) (show aN < 8 by decide)
    refine WP.mono (recipGuess_ok hg.1.scr h9 h12 h7 (by omega) hw' (by have := hg.2; omega))
      fun t ⟨h5, h10, _, hm, k⟩ => ?_
    rw [ht] at h5 h10
    exact ⟨h.keep hm k (by decide) (by decide) (by decide) (by decide) (by decide), h5,
      by rw [h10, BitVec.ofNat_toNat, BitVec.setWidth_eq], BitVec.isLt _⟩
  refine RelCT.seq hguess (RelCT.seq downLoop_ct ?_)
  -- `x15 := 1`.
  refine RelCT.seq (two_piece (Ψ := RU) [] (fun _ _ _ _ _ _ hr => absurd hr (List.not_mem_nil))
    (by taint_decide) fun q s h => ?_) ?_
  · refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = BitVec.ofNat 64 1 ∧ t.mem = s.mem)
      (by brun) (by decide)) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨⟨?_, h.2⟩, h15⟩
    exact h.1.keep hm k (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((k.gpr .x10 (by decide)).trans h.1.2.2.1) h.1.2.2.2
  refine RelCT.seq upLoop_ct ?_
  -- `v` to the temporary.
  refine (two_piece (Ψ := fun q s => R2dF2 q.1.1 s) [.x6] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.1.1.1.1.2.2.1, h₂.1.1.1.1.1.2.2.1])
    (by taint_decide) fun q s h => ?_).mono (fun _ _ h => h) fun s₁ s₂ ⟨q, h₁, h₂, hsp⟩ => ⟨q.1, h₁, h₂, hsp⟩
  obtain ⟨⟨⟨hd, ho⟩, -⟩, hu⟩ := h
  obtain ⟨hp, h5, h10, hv⟩ := hd
  obtain ⟨⟨hf, h9, h6, h12, h7, hx⟩, hN⟩ := hp
  obtain ⟨_, hg, hw, hw'⟩ := hf.1
  have hs := hg.1.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot q.1.1.w j + 8 * (q.1.1.w + 2) ≤ q.1.1.Z := fun j hj => Nat.le_trans (slot_le hj) hg.2
  have lN := sl aN (by decide)
  have lT := sl aTmp (by decide)
  have lX := sl aR2 (by decide)
  have sTN := slot_sep (w := q.1.1.w) (show aTmp ≠ aN by decide)
  have sTX := slot_sep (w := q.1.1.w) (show aTmp ≠ aR2 by decide)
  have eT := R2pF1.top ⟨⟨hf, h9, h6, h12, h7, hx⟩, hN⟩
  have hD : 2 ^ 63 ≤ topW q.1 := by
    have := hf.2.2; rw [eT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (topW_lt _)] at this; exact this
  have hvx := recip_exact hD (topW_lt q.1) ho hu
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off q.1.1.B (slot q.1.1.w aTmp)) (s.gpr .x10))
    (by brun [h6, hs.st (show slot q.1.1.w aTmp + 8 ≤ q.1.1.Z by omega)]) (by decide)) fun t ⟨hm, k⟩ => ?_
  have o : Outside q.1.1.B (slot q.1.1.w aTmp) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega)
  have ha : Arrays q.1.1.B q.1.1.w [aTmp] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega)
  have hf' := hf.arr k (by decide) (j := aTmp) (by decide) (by decide) ha
  have hN' : wv t.mem q.1.1.B (slot q.1.1.w aN) q.1.1.w = wv s.mem q.1.1.B (slot q.1.1.w aN) q.1.1.w :=
    o.wv (by omega) (by omega)
  have hX : wv t.mem q.1.1.B (slot q.1.1.w aR2) q.1.1.w = wv s.mem q.1.1.B (slot q.1.1.w aR2) q.1.1.w :=
    o.wv (by omega) (by omega)
  have hDt : word t.mem q.1.1.B (slot q.1.1.w aN + 8 * (q.1.1.w - 1)) =
      word s.mem q.1.1.B (slot q.1.1.w aN + 8 * (q.1.1.w - 1)) := o.word (by omega) (by omega)
  refine ⟨hf', by rw [hN', hX, hx], ?_⟩
  rw [hDt, eT, toNat_ofNat64 (topW_lt _), hm, word_writeW_self, h10, toNat_ofNat64 hv, hvx]

end VG.Proof.Bignum.AArch64
