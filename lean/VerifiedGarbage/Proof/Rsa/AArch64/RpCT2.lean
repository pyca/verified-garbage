import VerifiedGarbage.Proof.Rsa.AArch64.RpCT1

/-!
# `vg_rsa_recover_primes` on AArch64: constant time, the halvings

`64 Bw` halvings, a public count (`halving_ct`): the counter in `x6` is
pinned by correctness. Each halving reloads `w` and `Bw` from the header
twice, so it is checked in two parts, the registers they need pinned after
each block of bases (`halfA_ct`, `halfC_ct`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Impl.Bignum.Public (aN)
open VG.Spec.Rsa (splitTwos)
open VG.Proof.Rsa (halve_le)

/-- The first block of a halving. -/
abbrev halfA : List Instr := ws ++ bw ++ base aM .x16 ++ base aH .x17

/-- The second. -/
abbrev halfC : List Instr := ws ++ bw ++ base aH .x16 ++ base aM .x17 ++
  [ld .x3 .x17, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1, ldh .x3 sT, .sub .x .x3 .x3 .x15,
    sth .x3 sT]

/-- The rest of a halving after `shr`. -/
abbrev halfR : Prog isa := .seq (.block halfC) (.seq VG.Impl.Rsa.AArch64.Crt.selLoop (.block [.subImm .x .x6 .x6 1]))

theorem halfBody_eq : seqs (halfShift ++ [VG.Impl.Rsa.AArch64.Crt.selLoop, .block [.subImm .x .x6 .x6 1]]) =
    .seq (.block halfA) (.seq (countLoop .x14 shrBody) halfR) := rfl

/-- The header's `e_len`, after halvings. -/
theorem HalfInv.el {s₁ t : State} {B : Addr} {Z w m j el : Nat} (hI : HalfInv s₁ B Z w m j t)
    (hel : word s₁.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) :
    word t.mem B (8 * Public.sElen) = BitVec.ofNat 64 el := by
  have hZ := hI.ws.hZ
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have eHM := slot_aH w
  have eT : 8 * sT = 216 := rfl
  have eE : 8 * Public.sElen = 160 := rfl
  rw [hI.frm.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)]
  exact hel

/-- `halfA` and `shr`: the working space, and the header's `e_len`. -/
theorem halfMid_ok {s : State} {B : Addr} {Z w el : Nat} (h : Ws s B Z w)
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el) (he2 : el ≤ 8 * w) :
    WP isa (.seq (.block halfA) (countLoop .x14 shrBody)) s fun t =>
      Ws t B Z w ∧ word t.mem B (8 * Public.sElen) = BitVec.ofNat 64 el := by
  have hn := h.scr.nowrap
  have hw2 := h.w2
  have hZ := h.hZ
  have sH := slot_lt (w := w) (show aH + 1 < 16 by decide)
  have eHM := slot_aH w
  have eH1 : slot w (aH + 1) = slot w aH + 8 * (w + 2) := by simp only [slot, hdrBytes, aH]; omega
  have hT0 := hdr_lt_slot w aM (show Public.sElen < 32 by decide)
  have eE : 8 * Public.sElen = 160 := rfl
  obtain ⟨Bw, hBw⟩ : ∃ Bw, w + (el + 7) / 8 = Bw := ⟨_, rfl⟩
  have hBw2 : Bw + 1 ≤ 2 * (w + 2) := by omega
  refine WP.seq (WP.mono (wsBw2_ok h hel (by omega) aM aH) fun t₁ ⟨⟨h16, h17, h14, _, _, m₁⟩, k₁⟩ => ?_)
  rw [hBw] at h14
  have hs₁ := h.scr.congr k₁.wr
  refine WP.mono (shr_ok hs₁ h16 h17 h14 (by omega) (by omega) (by omega) (by omega) (Or.inr (Or.inl (by omega))))
    fun t₂ ⟨_, _, o₂, k₂⟩ => ⟨h.congrR (rs := [(slot w aH, 8 * Bw)]) (fun x hx => by
      rw [o₂ x (hx _ (List.mem_singleton_self _)), m₁]) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact RMut.ofSlot _ _ _) (k₁.trans k₂) (by decide), ?_⟩
  rw [o₂.word (Or.inl (by omega)) (by omega), m₁, hel]

/-- `halfC`'s bases and `Bw`. -/
theorem halfC_pins {s : State} {B : Addr} {Z w el : Nat} (h : Ws s B Z w)
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block halfC) s fun t => t.gpr .x16 = off B (slot w aH) ∧ t.gpr .x17 = off B (slot w aM) ∧
      t.gpr .x14 = BitVec.ofNat 64 (w + (el + 7) / 8) := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have h256 := h.h256
  have sH := slot_lt (w := w) (show aH + 1 < 16 by decide)
  have sM := slot_lt (w := w) (show aM < aH by decide)
  have sH' := slot_mono (w := w) (show aH ≤ aH + 1 by decide)
  have hT0 := hdr_lt_slot w aM (show sT < 32 by decide)
  have eT : 8 * sT = 216 := rfl
  refine WP.block_append_iff.mpr (WP.mono (wsBw2_ok h hel hel' aH aM)
    fun t₃ ⟨⟨h16₃, h17₃, h14₃, _, _, m₃⟩, k₃⟩ => ?_)
  have hs₃ := h.scr.congr k₃.wr
  have h0₃ : t₃.gpr .x0 = B := (k₃.gpr .x0 (by decide)).trans h.x0
  refine WP.mono (WP.keep [.x3, .x4, .x15] (Q := fun _ => True)
    (by
      brun [h16₃, h17₃, h14₃, h0₃, hdr_enc (show sT < 32 by decide), hs₃.ld (d := slot w aM) (by omega),
        hs₃.ld (d := 8 * sT) (by omega), hs₃.st (d := 8 * sT) (by omega)]
      exact ⟨_, rfl⟩)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨_, k⟩ =>
      ⟨(k.gpr .x16 (by decide)).trans h16₃, (k.gpr .x17 (by decide)).trans h17₃, (k.gpr .x14 (by decide)).trans h14₃⟩

namespace Rp

/-- On entry to `rest`. -/
def GR0 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RestPre I m₀ I.N (I.D * I.E - 1) s ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true

/-- The halvings' count, `64 Bw`. -/
abbrev hN (p : RpP) : Nat := 64 * (wk p.k + (p.el + 7) / 8)

/-- After `j` halvings, from `s₁`. -/
def HL (p : RpP) (j : Nat) (s : State) : Prop :=
  ∃ (s₁ : State) (m : Nat), word s₁.mem p.B (8 * Public.sElen) = BitVec.ofNat 64 p.el ∧ 1 ≤ p.el ∧
    p.el ≤ 8 * wk p.k ∧ m < 2 ^ (64 * (wk p.k + (p.el + 7) / 8)) ∧ HalfInv s₁ p.B p.Z (wk p.k) m j s ∧
    s.gpr .x6 = BitVec.ofNat 64 (hN p - j)

/-- Between `shr` and `halfC`. -/
def HM (q : RpP × Nat) (t : State) : Prop :=
  Ws t q.1.B q.1.Z (wk q.1.k) ∧ word t.mem q.1.B (8 * Public.sElen) = BitVec.ofNat 64 q.1.el ∧ q.1.el < 2 ^ 32 ∧
    WP isa halfR t fun _ => True

/-- The registers `shr` needs pinned. -/
def halfAVal (q : RpP × Nat) : Reg → BitVec 64
  | .x16 => off q.1.B (slot (wk q.1.k) aM)
  | .x17 => off q.1.B (slot (wk q.1.k) aH)
  | .x14 => BitVec.ofNat 64 (wk q.1.k + (q.1.el + 7) / 8)
  | _ => 0

/-- The registers `selLoop` needs pinned. -/
def halfCVal (q : RpP × Nat) : Reg → BitVec 64
  | .x16 => off q.1.B (slot (wk q.1.k) aH)
  | .x17 => off q.1.B (slot (wk q.1.k) aM)
  | .x14 => BitVec.ofNat 64 (wk q.1.k + (q.1.el + 7) / 8)
  | _ => 0

theorem halfA_ct : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < hN q.1 ∧ HL q.1 q.2 s)
    (.seq (.block halfA) (countLoop .x14 shrBody)) (Two HM) := by
  have e : halfA = ws ++ (bw ++ base aM .x16 ++ base aH .x17) := by simp only [halfA, List.append_assoc]
  rw [e]
  refine ws_pin_ct (fun q : RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun q s h => by obtain ⟨-, s₁, m, -, -, -, -, hI, -⟩ := h; exact hI.ws) (by taint_decide)
    [.x16, .x17, .x14] halfAVal (fun q s h => ?_) (by taint_decide) fun q s h => ?_
  · rw [← e]
    obtain ⟨-, s₁, m, hel, he1, he2, -, hI, -⟩ := h
    exact WP.mono (wsBw2_ok hI.ws (hI.el hel) (by have := hI.ws.w2; omega) aM aH)
      fun t ⟨⟨h16, h17, h14, _⟩, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h16
        · exact h17
        · exact h14
  · rw [← e]
    obtain ⟨hj, s₁, m, hel, he1, he2, hm, hI, -⟩ := h
    have hw2 := hI.ws.w2
    have := halfStep_ok hI hel he1 he2 hm hj
    rw [halfBody_eq] at this
    exact WP.mono (WP.and (halfMid_ok hI.ws (hI.el hel) he1 he2) (WP.seq_iff.mp (WP.assoc' this)))
      fun t ⟨⟨hw, hel'⟩, hr⟩ => ⟨hw, hel', by omega, WP.mono hr fun _ _ => trivial⟩

theorem halfC_ct : RelCT isa (Two HM) halfR (Two fun (_ : RpP × Nat) (_ : State) => True) := by
  have e : halfC = ws ++ (bw ++ base aH .x16 ++ base aM .x17 ++ [ld .x3 .x17, movi .x4 1,
      .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1, ldh .x3 sT, .sub .x .x3 .x3 .x15, sth .x3 sT]) := by
    simp only [halfC, List.append_assoc]
  unfold halfR
  rw [e]
  refine ws_pin_ct (fun q : RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun q s h => h.1) (by taint_decide) [.x16, .x17, .x14] halfCVal (fun q s h => ?_) (by taint_decide)
    fun q s h => ?_
  · rw [← e]
    exact WP.mono (halfC_pins h.1 h.2.1 h.2.2.1) fun t ⟨h16, h17, h14⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h16
      · exact h17
      · exact h14
  · rw [← e]
    exact h.2.2.2

theorem halfBody_ct : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < hN q.1 ∧ HL q.1 q.2 s)
    (seqs (halfShift ++ [VG.Impl.Rsa.AArch64.Crt.selLoop, .block [.subImm .x .x6 .x6 1]])) fun _ _ => True := by
  rw [halfBody_eq]
  exact (RelCT.assoc (RelCT.seq halfA_ct halfC_ct)).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- After the halvings: `r` and `t`, and what Montgomery form needs. -/
def GR1 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ I.N % 2 = 1 ∧ 2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧
    wv s.mem I.B (slot (wk I.k) aN) (wk I.k) = I.N ∧
    ((word s.mem I.B (slot (wk I.k) aN)).toNat * (word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = (splitTwos (I.D * I.E - 1)).2 ∧
    word s.mem I.B (8 * sT) = BitVec.ofNat 64 (splitTwos (I.D * I.E - 1)).1 ∧
    0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0 ∧ I.D * I.E - 1 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

theorem halfInit_ct : RelCT isa (Two GR0) (.block halfInit) (Two fun p s => 0 < hN p ∧ HL p 0 s) :=
  two_piece [.x0] (fun _ _ _ ⟨_, _, e₁, h₁, _⟩ ⟨_, _, e₂, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.S.ws.x0, h₂.S.ws.x0]
      exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm)
    (by taint_decide) fun p s h => by
      obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
      dsimp only [RpIn.pub]
      have hw := h.S.ws
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      have hZ := hw.hZ
      have hT0 := hdr_lt_slot (wk I.k) aM (show sT < 32 by decide)
      have L := h.L
      refine WP.mono (halfInit_ok hw h.S.args.el (by have := L.el2; have := L.k2; omega))
        fun t ⟨h6, m₁, k₁⟩ => ⟨by show 0 < 64 * (wk I.k + (I.el + 7) / 8); unfold wk; have := L.k1; omega, t,
          I.D * I.E - 1, ?_, L.el1, by show I.el ≤ 8 * wk I.k; have := L.el2; unfold wk; omega, h.mlt, ?_,
          by rw [h6, Nat.sub_zero]⟩
      · have o₁ := writeW_outside s.mem I.B (BitVec.ofNat 64 0) (d := 8 * sT) (by simp only [sT, sFn]; omega)
        rw [← m₁] at o₁
        rw [o₁.word (Or.inl (by simp only [Public.sElen, sFn, sT]; omega))
          (by simp only [Public.sElen, sFn]; omega)]
        exact h.S.args.el
      · have o₁ := writeW_outside s.mem I.B (BitVec.ofNat 64 0) (d := 8 * sT) (by simp only [sT, sFn]; omega)
        rw [← m₁] at o₁
        have hf₁ : Frm I.B [(slot (wk I.k) aM, 16 * (wk I.k + 2)), (slot (wk I.k) aH, 16 * (wk I.k + 2)),
            (8 * sT, 8)] s.mem t.mem :=
          fun x hx => o₁ x (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        have sM := slot_lt (w := wk I.k) (show aM + 1 < 16 by decide)
        have eM1 := slot_aM1 (wk I.k)
        dsimp only
        exact ⟨hw.congrR hf₁ (half_rmut _) k₁ (by decide), Keep.refl _ _, Frm.refl _ _ _,
          by rw [o₁.wv (Or.inr (by omega)) (by omega), h.M]; rfl, by rw [m₁, word_writeW_self]; rfl⟩

theorem halfLoop_ct : RelCT isa (Two fun p s => 0 < hN p ∧ HL p 0 s)
    (.loop (seqs (halfShift ++ [VG.Impl.Rsa.AArch64.Crt.selLoop, .block [.subImm .x .x6 .x6 1]])) (.nonzero .x .x6))
    (Two fun (_ : RpP) (_ : State) => True) :=
  two_loop hN halfBody_ct fun p j s hj h => by
    obtain ⟨s₁, m, hel, he1, he2, hm, hI, h6⟩ := h
    have hw2 := hI.ws.w2
    refine WP.mono (halfStep_ok hI hel he1 he2 hm hj) fun s' ⟨hI', h6'⟩ => ?_
    have e6 : s'.gpr .x6 = BitVec.ofNat 64 (hN p - (j + 1)) := by
      rw [h6', h6]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have : hN p < 2 ^ 63 := by show 64 * (wk p.k + (p.el + 7) / 8) < 2 ^ 63; omega
      omega
    refine ⟨?_, fun _ => ⟨s₁, m, hel, he1, he2, hm, hI', e6⟩, fun _ => trivial⟩
    rw [eval_nonzero, ne_zero_iff, e6]
    have : hN p < 2 ^ 63 := by show 64 * (wk p.k + (p.el + 7) / 8) < 2 ^ 63; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem halving_ct : RelCT isa (Two GR0) halving (Two GR1) :=
  two_post ((RelCT.seq halfInit_ct halfLoop_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => by
    obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
    have L := h.L
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := h.S.ws.scr.nowrap; have := h.S.ws.hZ; omega
    refine WP.mono (halving_ok h.S.ws h.S.args.el L.el1 (by have := L.el2; unfold wk; omega) h.M h.m0 h.mlt)
      fun t ⟨_, hr₁, ht₁, hf₁', k₁⟩ => ?_
    have hf₁ := frm_halving hf₁'
    refine ⟨I, m₀, rfl, h.S.step hf₁ (by decide) (by decide) k₁ (by decide), L, O, hv, h.odd, h.lo, ?_, ?_, hr₁, ht₁,
      h.m0, h.even, h.mlt⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact h.n
    · rw [hf₁.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact h.inv

end Rp

end VG.Proof.Rsa.AArch64
