import VerifiedGarbage.Proof.Bignum.X86_64.R2wFast
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2

/-!
# `R² mod m` by word steps on x86-64: constant time but for `m`

A step's addresses and branches depend only on the working space and `w`
(`step_ct`): its arithmetic on the words of `m` and `x` is branch-free, the
division's 64 bits counted in a register. The steps' count is `w / 4`
(`steps_ct`), and `choice` branches on the top bit of `m` and on `w`
(`choice_ct`), which are public.
-/

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

/-- After a step's loads. -/
def StepB (L : Lay) (t : State) : Prop :=
  GoodL L t ∧ t.gpr .rbx = off L.B (slot L.w aR2) ∧ t.gpr .r10 = off L.B (slot L.w aN) ∧
    t.gpr .r8 = off L.B (slot L.w aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧
    t.gpr .rbp = off L.B (slot L.w aTmp)

theorem pins_stepB : Pins StepB [.rbx, .r10, .r8, .r12, .rbp] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

theorem step_eq : step =
    .seq (.block R2Words.bases) (.seq (.block quot) (.seq mulSub (.seq addBack (.seq addBack copyBack)))) := rfl

/-- A step leaks the same in runs with the same working space. -/
theorem step_ct : RelCT isa (Two GoodL) step fun _ _ => True := by
  rw [step_eq]
  refine RelCT.seq (two_piece (Ψ := StepB) _ pins_good (by taint_decide) fun L s hg => ?_)
    (two_taint _ pins_stepB (by taint_decide))
  exact WP.mono (stepBases_ok hg) fun t ⟨h1, h2, h3, h4, h5, hm, k⟩ =>
    ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, h1, h2, h3, h4, h5⟩

/-! ## The steps -/

/-- The public data of `steps`: the working space and the count. -/
structure StPub where
  L : Lay
  c : Nat

/-- What `steps` keeps, after `j` steps. -/
def StepsAt (p : StPub) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (X M T : Nat), StepsInv σ p.L.B p.L.Z p.L.w p.L.minv p.c X M T j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.c < 2 ^ 31 ∧ 0 < M ∧ 2 ^ 63 ≤ T

theorem stepsAt_good {p : StPub} {j : Nat} {t : State} (h : StepsAt p j t) : GoodL p.L t :=
  let ⟨_, _, _, _, hI, hZ, _⟩ := h; ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

/-- `steps`' hypotheses. -/
def StepsPre (p : StPub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ 1 ≤ p.c ∧ p.c < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.c ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w < wv s.mem p.L.B (slot p.L.w aN) p.L.w

/-- `steps` leaks the same in runs with the same working space and count. -/
theorem steps_ct : RelCT isa (Two StepsPre) steps (Two fun p s => StepsAt p p.c s) := by
  rw [steps_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ StepsAt p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨hg, hw, hw', hc1, hc', hcx, hT, hv, hO⟩
    have hM : 0 < wv s.mem p.L.B (slot p.L.w aN) p.L.w := Nat.lt_of_le_of_lt (Nat.zero_le _) hO
    exact WP.mono (stepsStart_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hcx hO hv)
      fun t hI => ⟨by omega, s, _, _, _, hI, hg.2, hw, hw', hc', hM, hT⟩
  refine two_loop (Φ := StepsAt) (fun p => p.c) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun (q : StPub × Nat) s => GoodL q.1.L s)
      (two_map (·.1.L) (fun _ _ h => stepsAt_good h.2) step_ct) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_good q.1.L s₁ s₂ h₁ h₂) (by taint_decide))
    rintro ⟨p, j⟩ s ⟨hj, σ, X, M, T, hI, hZ, hw, hw', hc', hM, hT⟩
    have hlt : wv s.mem p.L.B (slot p.L.w aR2) p.L.w < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by
      rw [hI.xv, hI.nv]; exact Nat.mod_lt _ hM
    exact WP.mono (step_ok (L := p.L) ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩ hw hw' (by rw [hI.top]; exact hT)
      (by rw [hI.rcp, hI.top]) hlt)
      fun t ⟨hg, _⟩ => hg
  · rintro p j s hj ⟨σ, X, M, T, hI, hZ, hw, hw', hc', hM, hT⟩
    exact WP.mono (stepIter_ok hZ hw hw' hc' hM hT hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, X, M, T, hI', hZ, hw, hw', hc', hM, hT⟩,
        fun e => e ▸ ⟨σ, X, M, T, hI', hZ, hw, hw', hc', hM, hT⟩⟩

/-! ## `fast` -/

/-- `fast`'s hypotheses: `r2_ok`'s, `m`'s top bit set and `w` a multiple of 4. -/
def FPre (p : R2Pub) (s : State) : Prop := R2Pre p s ∧ 2 ^ 63 ≤ p.top ∧ p.L.w % 4 = 0

/-- After `fast`'s loads. -/
def F1 (p : R2Pub) (s : State) : Prop :=
  FPre p s ∧ s.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ s.gpr .rbp = mask false ∧
    s.gpr .r8 = off p.L.B (slot p.L.w aTmp)

/-- What `fast` keeps from `R - m` on. -/
def FB (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.L.w % 4 = 0 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    ((word s.mem p.L.B (slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w < p.N

/-- After `R - m`. -/
def F2 (p : R2Pub) (s : State) : Prop :=
  FB p s ∧ s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
    s.gpr .r8 = off p.L.B (slot p.L.w aTmp)

/-- After `v`. -/
def F2v (p : R2Pub) (s : State) : Prop :=
  FB p s ∧ (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
    (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64

/-- Before the steps. -/
def F3 (p : R2Pub) (s : State) : Prop := F2v p s ∧ s.gpr .rcx = BitVec.ofNat 64 (p.L.w / 4)

theorem pins_F1 : Pins F1 [.rbx, .r10, .r12, .r8] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.1.1.2.2.2.2.2.2.1, h₂.1.1.2.2.2.2.2.2.1]
  · rw [h₁.1.1.2.2.2.2.2.1, h₂.1.1.2.2.2.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

theorem pins_F2 : Pins F2 [.r10, .r12, .r8] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

theorem fast_ct (M : Mont) : RelCT isa (Two FPre) (fast M.mm) fun _ _ => True := by
  rw [fast_eq M.mm]
  -- The loads.
  refine RelCT.seq (two_piece (Ψ := F1) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega)
    refine WP.mono (WP.keep [.rbx, .r10, .r12, .r8, .rbp] (Q := fun t =>
        t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .r8 = off p.L.B (slot p.L.w aTmp) ∧ t.gpr .rbp = mask false ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
        hl (sArr aTmp) (by decide), hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aN (by decide), hg.1.hdr.hw,
        hg.1.hdr.harr aTmp (by decide)]) rfl)
      fun t ⟨⟨hbx, h10, h12, h8, hbp, hm⟩, k⟩ => ⟨⟨?_, h.2⟩, hbx, hbp, h8⟩
    obtain ⟨⟨hg, hw, hw', hN, hinv, -, -, hodd, hlo⟩, -⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, h12, h10, hodd, hlo⟩
  -- `R - m`.
  refine RelCT.seq (two_piece (Ψ := F2) _ pins_F1 (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩, hT, h4⟩, hbx, hbp, h8⟩
    obtain ⟨hT', -⟩ := R2Pre.top ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    have hN0 : 0 < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by rw [hN]; omega
    have hng := neg_ok hs hbx h10 h12 hbp (by omega) (by omega) (by omega) (by omega) (by omega) hN0
    refine WP.mono hng fun t ⟨hx, ho, k⟩ => ?_
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega)
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by omega
    -- `m > R / 2`.
    have hhalf : 2 ^ (64 * p.L.w) < 2 * p.N := by
      have e : p.N = wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1) +
          2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
        rw [← hN, show p.L.w = (p.L.w - 1) + 1 by omega, wv_succ, show p.L.w - 1 + 1 - 1 = p.L.w - 1 by omega]
      have hp : 2 ^ (64 * p.L.w) = 2 * (2 ^ (64 * (p.L.w - 1)) * 2 ^ 63) := by
        rw [← Nat.pow_add, show 64 * p.L.w = 1 + (64 * (p.L.w - 1) + 63) by omega, Nat.pow_add, Nat.pow_one]
      rw [hT'] at e
      have hle := Nat.mul_le_mul_left (2 ^ (64 * (p.L.w - 1))) hT
      have hev : 2 ^ (64 * (p.L.w - 1)) * 2 ^ 63 % 2 = 0 := by
        rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
      omega
    refine ⟨⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv,
      by rw [ho.word (by omega) (by omega), hT']; exact hT, ?_⟩,
      (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h8⟩
    rw [hx, hN]; omega
  -- `v`.
  refine RelCT.seq (two_piece (Ψ := F2v) _ pins_F2 (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨hg, hw, hw', h4, hN, hinv, hT, hx⟩, h10, h12, h8⟩
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have hsv := slot_le (w := p.L.w) (show aTmp < 8 by decide)
    have sXV := slot_sep (w := p.L.w) (show aR2 ≠ aTmp by decide)
    have sMV := slot_sep (w := p.L.w) (show aN ≠ aTmp by decide)
    refine WP.mono (recip_ok hs h10 h12 h8 (by omega) (by omega) (by omega) hT) fun t ⟨hm, k⟩ => ?_
    have o : Outside p.L.B (slot p.L.w aTmp) 8 s.mem t.mem := by rw [hm]; exact writeW_outside _ _ _ (by omega)
    have ha : Arrays p.L.B p.L.w [aTmp] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega)
    have hvlt : (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 < 2 ^ 64 := by
      have : (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat < 2 ^ 65 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      omega
    have hT₁ : word t.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1)) =
        word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1)) := o.word (by omega) (by omega)
    refine ⟨⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
      by rw [o.wv (by omega) (by omega)]; exact hN, by rw [o.word (by omega) (by omega)]; exact hinv,
      by rw [hT₁]; exact hT, by rw [o.wv (by omega) (by omega)]; exact hx⟩, ?_⟩
    rw [hT₁, hm, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  -- The count.
  refine RelCT.seq (two_piece (Ψ := F3) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega)
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (p.L.w / 4) ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl sW (by decide), hg.1.hdr.hw,
        shr2_ofNat (show p.L.w < 2 ^ 64 by have := h.1.2.2.1; omega)]) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨?_, hcx⟩
    obtain ⟨⟨hg, hw, hw', h4, hN, hinv, hT, hx⟩, hv⟩ := h
    exact ⟨⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw', h4,
      hm ▸ hN, hm ▸ hinv, hm ▸ hT, hm ▸ hx⟩, hm ▸ hv⟩
  -- The steps.
  refine RelCT.seq (two_post (Ψ := fun p s => SqPre p.L s) ((two_map (fun p => (⟨p.L, p.L.w / 4⟩ : StPub))
    (fun p s h => ?_) steps_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) ?_) ?_
  · obtain ⟨⟨⟨hg, hw, hw', h4, hN, -, hT, hx⟩, hv⟩, hcx⟩ := h
    have hc1 : 1 ≤ p.L.w / 4 := by omega
    have hc2 : p.L.w / 4 < 2 ^ 31 := by omega
    exact ⟨hg, hw, hw', hc1, hc2, hcx, hT, hv, by rw [hN]; exact hx⟩
  · intro p s h
    obtain ⟨⟨⟨hg, hw, hw', h4, hN, hinv, hT, hx⟩, hv⟩, hcx⟩ := h
    have hc1 : 1 ≤ p.L.w / 4 := by omega
    have hc2 : p.L.w / 4 < 2 ^ 31 := by omega
    have hw31 : p.L.w < 2 ^ 31 := by omega
    have hx2 : wv s.mem p.L.B (slot p.L.w aR2) p.L.w < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by
      rw [hN]; exact hx
    have hsk := steps_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hw hw' (c := p.L.w / 4) hc1 hc2 hcx hT hv hx2
    refine WP.mono hsk fun t ht => ?_
    obtain ⟨hx', hn', hw0, -, hg', k⟩ := ht
    refine ⟨⟨hg', hg.2⟩, hw, hw31, ?_, ?_⟩
    · rw [hw0]; exact hinv
    rw [hx', hn', hN]
    exact Nat.mod_lt _ (by omega)
  -- The squarings.
  exact two_map (·.L) (fun _ _ h => h) (sqs_ct M 1)

/-! ## The choice -/

/-- After `fastTest`. -/
def R2t (p : R2Pub) (s : State) : Prop :=
  R2Pre p s ∧ s.zf = some (decide (2 ^ 63 ≤ p.top ∧ p.L.w % 4 = 0))

/-- `choice` leaks the same in runs that agree on `m`. -/
theorem choice_ct (M : Mont) : RelCT isa (Two R2Pre) (choice M.mm) fun _ _ => True := by
  unfold choice
  refine RelCT.seq (two_piece (Ψ := R2t) _ pins_r2Pre (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hT, -⟩ := h.top
    have hn := h.1.1.scr.nowrap
    have := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (2 ^ 63 ≤ p.top ∧ p.L.w % 4 = 0)) ∧
        t.mem = s.mem) (by
      unfold fastTest
      xrun [State.ea, ix, addrm8 h.2.2.2.2.2.2.1 h.2.2.2.2.2.1 (by have := h.2.1; omega),
        h.1.1.scr.ld (show slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega)]
      rw [h.2.2.2.2.2.1]
      refine (fastFlag _ (by have := h.2.2.1; omega)).trans ?_
      rw [← hT]) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨?_, hz⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map id (fun p s ⟨⟨h, hz⟩, hc⟩ => by
      simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at hc
      exact ⟨h, hc.1, hc.2⟩) (fast_ct M)
  · rw [old_eq]
    exact two_map id (fun p s h => h.1.1) (r2_ct M)

end VG.Proof.Bignum.X86_64.R2w
