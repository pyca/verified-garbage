import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest

/-!
# `vg_rsa_public_precomputed` on AArch64: constant time but for `pre` and `e`

Every piece's addresses and branches depend only on the pointers, the
lengths, `pre` and `e`: the load and the checks of `pre` (`pdLoad_ct`),
`rest` (`pdRest_ct`), and the whole function (`pdCode_constantTime`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

variable {M : Mont}

/-! ## The load and the checks -/

/-- The public data of `vg_rsa_public_precomputed`: `rest`'s, `pre` and the
stack pointer. -/
structure CPubD where
  d : DPub
  pp : Addr
  sp : Addr

/-- What the load keeps. -/
def LH (p : CPubD) (t : State) : Prop :=
  Scr t p.d.B p.d.Z ∧ t.gpr .x0 = p.d.B ∧ slot ((p.d.k + 7) / 8) 8 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
    word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k ∧ word t.mem p.d.B (8 * sN) = p.pp ∧
    (∀ i < 2 * ((p.d.k + 7) / 8), InRegions (t.rd ++ t.wr) (off p.pp (8 * i)) 8) ∧
    (∀ j < 16 * ((p.d.k + 7) / 8), p.d.Z ≤ ofs p.d.B (p.pp + BitVec.ofNat 64 j))

theorem LH.congr {p : CPubD} {s t : State} (h : LH p s) {rs : List (Nat × Nat)} (hf : Frm p.d.B rs s.mem t.mem)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : LH p t := by
  obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, hpr, hps⟩ := h
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, hZ, hk1, hk2, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, fun i hi => by rw [k.rd, k.wr]; exact hpr i hi, hps⟩

theorem pins_LH : Pins LH [.x0] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- `LH` with the header's `w` and bases. -/
def LW (p : CPubD) (t : State) : Prop :=
  LH p t ∧ word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, word t.mem p.d.B (8 * sArr j) = off p.d.B (slot ((p.d.k + 7) / 8) j))

theorem LW.mem {p : CPubD} {s t : State} (h : LW p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : LW p t :=
  ⟨h.1.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k hr, by rw [hm]; exact h.2.1,
    fun j hj => by rw [hm]; exact h.2.2 j hj⟩

/-- A copy of `w` words from `pre + 8 c` into array `j`. -/
theorem ldCopy_ok {p : CPubD} {t : State} (h : LW p t) {c j : Nat} (hc : c ≤ (p.d.k + 7) / 8) (hj : j < 8)
    (h16 : t.gpr .x16 = off p.pp (8 * c)) (h17 : t.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) j))
    (h12 : t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) :
    WP isa copyWords t fun t' => LW p t' ∧ t'.gpr .x16 = off p.pp (8 * c + 8 * ((p.d.k + 7) / 8)) ∧
      Keep [.x3, .x14, .x16, .x17] t t' := by
  have h₀ : LH p t := h.1
  obtain ⟨⟨hs, h0, hZ, hk1, hk2, hK, hN, hpr, hps⟩, hW, hb⟩ := h
  have hn := hs.nowrap
  have hsl := slot_le (w := (p.d.k + 7) / 8) hj
  have hge := hdr_lt_slot ((p.d.k + 7) / 8) j (show 31 < 32 by decide)
  refine WP.mono (copyWords_ok (S := p.pp) (eS := 8 * c) h16 h17 h12 (by omega) (by omega) (by omega)
    (fun i hi => by rw [show 8 * c + 8 * i = 8 * (c + i) by omega]; exact hpr _ (by omega))
    (fun i hi => hs.st (by omega))
    (fun i hi b hb => Or.inr (by
      have := hps (8 * c + 8 * i + b) (by omega)
      rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; omega))) fun t' ⟨_, _, ho, h16', _, k⟩ => ?_
  refine ⟨⟨h₀.congr (Frm.of_outside ho (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; left; omega) k (by decide),
    by rw [ho.word (by unfold sW; omega) (by unfold sW; omega)]; exact hW,
    fun i hi => by rw [ho.word (d := 8 * sArr i) (by unfold sArr; omega) (by unfold sArr; omega)]; exact hb i hi⟩,
    h16', k⟩

/-- The load and the checks leak the same in runs with the same public data. -/
theorem pdLoad_ct : RelCT isa (Two LH) (seqs Precomputed.load) fun _ _ => True := by
  unfold Precomputed.load
  -- `w`, the bases, and the first copy's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .x16 = off p.pp (8 * 0) ∧
      t.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) _
    pins_LH (by taint_decide) ?_) ?_
  · intro p t h
    have h' := h
    obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, -⟩ := h'
    refine WP.mono (pdHead_ok hs h0 hZ (by omega) hK hN) fun t' ⟨h16, h17, h12, hW, hb, hf, k⟩ =>
      ⟨⟨h.congr hf (fun r hr => ?_) k (by decide), hW, hb⟩, h16, h17, h12⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .x16 = off p.pp (8 * ((p.d.k + 7) / 8)) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.x16, .x17, .x12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, h16, h17, h12⟩
    exact WP.mono (ldCopy_ok h (Nat.zero_le _) (by decide) h16 h17 h12) fun t' ⟨h', h16', k⟩ =>
      ⟨h', by rw [h16', Nat.mul_zero, Nat.zero_add], (k.gpr .x12 (by decide)).trans h12⟩
  -- `R² mod m`'s base.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .x16 = off p.pp (8 * ((p.d.k + 7) / 8)) ∧
      t.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧ t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8))
    [.x0] (fun p s₁ s₂ h₁ h₂ => pins_LH p s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, h16, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (WP.keep [.x17] (Q := fun t' => t'.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧
        t'.mem = t.mem) (by
      brun [h.1.2.1, hdr_enc (show sArr aR2 < 32 by decide), hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
        h.2.2 aR2 (by decide)]) (by decide) (by decide) (by decide +kernel))
      fun t' ⟨⟨h17, hm⟩, k⟩ => ⟨h.mem hm k (by decide), (k.gpr .x16 (by decide)).trans h16, h17,
        (k.gpr .x12 (by decide)).trans h12⟩
  -- `R² mod m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8))
    [.x16, .x17, .x12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, h16, h17, h12⟩
    exact WP.mono (ldCopy_ok h (Nat.le_refl _) (by decide) h16 h17 h12) fun t' ⟨h', _, k⟩ =>
      ⟨h', (k.gpr .x12 (by decide)).trans h12⟩
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .x16 = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧
      t.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .x14 = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
      t.c = true ∧ t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.x0, .x12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.2.1, h₂.1.1.2.1]
    · rw [h₁.2, h₂.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (WP.keep [.x3, .x7, .x14, .x16, .x17] (Q := fun t' =>
        t'.gpr .x16 = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧ t'.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧
        t'.gpr .x14 = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧ t'.c = true ∧ t'.mem = t.mem) (by
      brun [h.1.2.1, hdr_enc (show sArr aR2 < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
        hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega), hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
        h.2.2 aR2 (by decide), h.2.2 aN (by decide), h12]) (by decide) (by decide) (by decide +kernel))
      fun t' ⟨⟨h16, h17, h14, hc, hm⟩, k⟩ => ⟨h.mem hm k (by decide), h16, h17, h14, hc,
        (k.gpr .x12 (by decide)).trans h12⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8))
    [.x14, .x16, .x17] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, h16, h17, h14, hc, h12⟩
    have hZ := h.1.2.2.1
    have hk1 := h.1.2.2.2.1
    have hk2 := h.1.2.2.2.2.1
    exact WP.mono (cmpLoop_ok h.1.1 h16 h17 h14 hc (by omega) (by omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aR2 < 8 by decide); omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aN < 8 by decide); omega)) fun t' ⟨_, hm, k⟩ =>
      ⟨h.mem hm k (by decide), (k.gpr .x12 (by decide)).trans h12⟩
  -- The checks: `m`'s base, then its words.
  refine RelCT.block_append (l₁ := ([movi .x8 1, .csel .x .x9 .x7 .x8, ldh .x17 (sArr aN)] : List Instr))
    (l₂ := ([ld .x3 .x17, .logic .and .x .x3 .x3 .x8, .logic .and .x .x9 .x9 .x3, .subImm .x .x4 .x12 1,
      .lsl .x .x4 .x4 3, .add .x .x4 .x17 .x4, ld .x3 .x4, .subs .x .x3 .x3 .x8, .csel .x .x3 .x8 .x7,
      .logic .and .x .x9 .x9 .x3] : List Instr))
    (RelCT.seq (two_piece (Φ := fun (p : CPubD) t => LW p t ∧ t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8))
      (Ψ := fun (p : CPubD) t => t.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.x0] (fun p s₁ s₂ h₁ h₂ => pins_LH p s₁ s₂ h₁.1.1 h₂.1.1)
      (by taint_decide) ?_)
    (two_taint [.x17, .x12] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2, h₂.2]) (by taint_decide)))
  rintro p t ⟨h, h12⟩
  have hs := h.1.1
  have hn := hs.nowrap
  have hZ := h.1.2.2.1
  obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
  refine WP.mono (WP.keep [.x8, .x9, .x17] (Q := fun t' =>
      t'.gpr .x17 = off p.d.B (slot ((p.d.k + 7) / 8) aN)) (by
    brun [h.1.2.1, hdr_enc (show sArr aN < 32 by decide), hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
      h.2.2 aN (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨h17, k⟩ => ⟨h17, (k.gpr .x12 (by decide)).trans h12⟩

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def CR (p : CPubD) (s : State) : Prop :=
  pdContract.pre s ∧ s.sp = p.sp ∧ stackArg s 0 = p.d.B ∧ (stackArg s 1).toNat * 8 = p.d.Z ∧
    (s.gpr .x1).toNat = p.d.k ∧ s.gpr .x0 = p.d.op ∧ s.gpr .x2 = p.pp ∧ s.gpr .x4 = p.d.ep ∧
    s.gpr .x6 = p.d.ip ∧ (s.gpr .x5).toNat = p.d.len ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = p.d.eb ∧
    wv s.mem (s.gpr .x2) 0 (((s.gpr .x1).toNat + 7) / 8) = p.d.N ∧
    wv s.mem (s.gpr .x2) (8 * (((s.gpr .x1).toNat + 7) / 8)) (((s.gpr .x1).toNat + 7) / 8) = p.d.R

/-- What `entry` leaves (`pdEntry_ok`). -/
def PdEnt (s t : State) : Prop :=
  t.gpr .x0 = stackArg s 0 ∧
    word t.mem (stackArg s 0) (8 * sOut) = s.gpr .x0 ∧ word t.mem (stackArg s 0) (8 * sN) = s.gpr .x2 ∧
    word t.mem (stackArg s 0) (8 * sK) = s.gpr .x1 ∧ word t.mem (stackArg s 0) (8 * sE) = s.gpr .x4 ∧
    word t.mem (stackArg s 0) (8 * sElen) = s.gpr .x5 ∧ word t.mem (stackArg s 0) (8 * sIn) = s.gpr .x6 ∧
    Outside (stackArg s 0) 0 (8 * 22) s.mem t.mem ∧ Keep [.x0, .x8] s t

theorem pdEntry_split : Precomputed.entry false =
    ([.ldrSp .x8 0] : List Instr) ++ (Precomputed.entry false).drop 1 := rfl

/-- After `entry`'s first instruction. -/
def CE1 (p : CPubD) (t : State) : Prop :=
  ∃ s, CR p s ∧ t.gpr .x8 = p.d.B ∧ WP isa (.block ((Precomputed.entry false).drop 1)) t (PdEnt s)

/-- After `entry`. -/
def CE2 (p : CPubD) (t : State) : Prop := ∃ s, CR p s ∧ PdEnt s t

/-- After the load and the checks (`pdLoad_ok`). -/
def CL (p : CPubD) (t : State) : Prop :=
  ∃ s t₁, CR p s ∧ PdEnt s t₁ ∧
    wv t.mem p.d.B (slot ((p.d.k + 7) / 8) aN) ((p.d.k + 7) / 8) = p.d.N ∧
    wv t.mem p.d.B (slot ((p.d.k + 7) / 8) aR2) ((p.d.k + 7) / 8) = p.d.R ∧
    word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, word t.mem p.d.B (8 * sArr j) = off p.d.B (slot ((p.d.k + 7) / 8) j)) ∧
    t.gpr .x9 = BitVec.ofNat 64 (chkv ((p.d.k + 7) / 8) p.d.N p.d.R).toNat ∧
    Frm p.d.B (pdLoadRanges ((p.d.k + 7) / 8)) t₁.mem t.mem ∧ Keep mmRegs t₁ t

theorem ce2_lh {p : CPubD} {t : State} (h : CE2 p t) : LH p t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, sp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, -, hpp, -⟩, h0, -, hN, hK, -, -, -, -, kk⟩ := h
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hpp
  exact ⟨c.hs.congr kk.wr, h0, by dsimp only; unfold slot hdrBytes; omega, c.hk1, c.hk2,
    by rw [hK, ofNat_toNat64], hN, fun i hi => by rw [kk.rd, kk.wr]; exact c.hpr i hi, c.hps⟩

/-- The load's post, from `entry`'s. -/
theorem ce2_load {p : CPubD} {t : State} (h : CE2 p t) : WP isa (seqs Precomputed.load) t (CL p) := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, sp⟩ := p
  obtain ⟨s, hs, he⟩ := h
  have hs' := hs
  have he' := he
  obtain ⟨h0, -, hN, hK, -, -, -, ho₁, k₁⟩ := he'
  obtain ⟨hpre, -, hB, hZ, hk, -, hpp, -, -, -, -, hNv, hRv⟩ := hs
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  have hn := c.hs.nowrap
  have i₁ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t.mem := InScr.of_outside ho₁ (by omega)
  have hz : slot (((s.gpr .x1).toNat + 7) / 8) 8 ≤ (stackArg s 1).toNat * 8 := by unfold slot hdrBytes; omega
  refine WP.mono (pdLoad_ok (c.hs.congr k₁.wr) h0 hz (by omega) (by omega) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.rd, k₁.wr]; exact c.hpr i hi) c.hps) fun t' ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_
  rw [Bool.and_comm (decide (wv _ _ _ _ < _)), chk_eq (by omega)] at hz₂
  rw [pre_wv_entry c i₁ (by omega), hNv] at hN₂
  rw [pre_wv_entry c i₁ (by omega), hRv] at hR₂
  rw [hN₂, hR₂] at hz₂
  subst hB hZ hk hpp
  exact ⟨s, t, hs', he, hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩

/-- What `fail` needs after the load. -/
theorem cl_fail {p : CPubD} {t : State} (h : CL p t) :
    Scr t p.d.B p.d.Z ∧ t.gpr .x0 = p.d.B ∧ 8 * 32 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
      word t.mem p.d.B (8 * sOut) = p.d.op ∧ word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, sp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, -⟩, ⟨h0, hO, -, hK, -, -, -, -, k₁⟩, -, -, -, -, -,
    f, k⟩ := h
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hop
  have x := Fixed.of_frm f (pdLoadRanges_fixed _)
  exact ⟨c.hs.congr (k₁.trans k).wr, (k.gpr .x0 (by decide)).trans h0, by dsimp only; omega, c.hk1, c.hk2,
    (x sOut (by decide)).trans hO, by rw [x sK (by decide), hK, ofNat_toNat64]⟩

/-- `rest`'s hypotheses after the load, for values that pass the checks. -/
theorem cl_rest {p : CPubD} {t : State} (h : CL p t) (he : isa.eval (.zero .x .x9) t = some false) :
    DRel p.d t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, sp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, hpp, hep, hip, hlen, heb, -⟩,
    ⟨h0, hO, -, hK, hE, hL, hIn, ho₁, k₁⟩, hN, hR, hW, hb, hz, f, k₂⟩ := h
  dsimp only at hN hR hW hb hz f k₂ ⊢
  have c := pdCtx_of hpre
  have := c.hk1
  subst hB hZ hk hop hpp hep hip hlen heb
  have hchk : chkv (((s.gpr .x1).toNat + 7) / 8) N R = true := by
    rw [eval_zero, hz] at he
    cases hv : chkv (((s.gpr .x1).toNat + 7) / 8) N R
    · rw [hv] at he; simp at he
    · rfl
  rw [← hN, ← hR, ← chk_eq (by omega)] at hchk
  obtain ⟨hodd, hN1, hRN⟩ := checks_facts (by omega) hchk
  have hp := pdPre_of c h0 hO hK hE hL hIn ho₁ k₁ hW hb f k₂ hodd hN1 hRN
  rw [hN, hR] at hp
  exact ⟨_, hp⟩

/-- `vg_rsa_public_precomputed` leaks the same in runs that agree on the public
data. -/
theorem pdCode_ct : RelCT isa (Two CR) (Precomputed.code M.mm) fun _ _ => True := by
  unfold Precomputed.code
  refine RelCT.seq (R := Two CE2) ?_ ?_
  · rw [pdEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CE1) [] (fun _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide) ?_)
      (two_piece [.x8] (fun p s₁ s₂ ⟨_, _, a₁, _⟩ ⟨_, _, a₂, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) (by taint_decide)
        fun p t ⟨s, hs, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := pdCtx_of hs.1
    have hZ := c.hZ
    have hk1 := c.hk1
    have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 0) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
    have hh : WP isa (.block (([.ldrSp .x8 0] : List Instr) ++ (Precomputed.entry false).drop 1)) s
        (PdEnt s) := by
      rw [← pdEntry_split]; exact pdEntry_ok rfl hw c.ha0
    have ha0' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := c.ha0
    have hB' : s.mem.readW s.sp 64 = stackArg s 0 := by
      simp only [stackArg, stackArgAddr, Nat.mul_zero, off_zero]
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 0)
      (by brun [exec_ldrSp_x' _ (show 0 % 8 = 0 ∧ 0 < 32768 by decide) ha0', hB']) (by decide) (by decide)
        (by decide +kernel))) fun t ⟨hw', h8, _⟩ => ⟨s, hs, h8.trans hs.2.2.1, hw'⟩
  refine RelCT.seq (R := Two CL) (two_post (pdLoad_ct.mono (fun _ _ h => two_mono (fun _ _ h => ce2_lh h) h)
    fun _ _ h => h) fun p t h => ce2_load h) ?_
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, _, _, z₂, _⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold Precomputed.fail
    refine RelCT.seq (two_piece (Ψ := fun (p : CPubD) t => t.gpr .x1 = p.d.op + BitVec.ofNat 64 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 p.d.k) [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(cl_fail h₁.1).2.1, (cl_fail h₂.1).2.1])
      (by taint_decide) ?_)
      (two_taint [.x1, .x2] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨hs, h0, hZ, hk1, hk2, hO, hK⟩ := cl_fail h
    have hn := hs.nowrap
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.d.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.d.op + BitVec.ofNat 64 0 ∧
        t'.gpr .x2 = BitVec.ofNat 64 p.d.k) (by
      brun [h0, hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide), hl sOut (by decide),
        hl sK (by decide), hO, hK]) (by decide) (by decide) (by decide +kernel))
      fun t' ⟨h, _⟩ => h
  · -- `rest`.
    exact two_map (fun p => p.d) (fun _ _ h => cl_rest h.1 h.2) pdRest_ct

/-- The public data of a state. -/
def cpubOfD (s : State) : CPubD :=
  ⟨⟨stackArg s 0, (stackArg s 1).toNat * 8, (s.gpr .x1).toNat, s.gpr .x0, s.gpr .x4, s.gpr .x6,
    (s.gpr .x5).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat,
    wv s.mem (s.gpr .x2) 0 (((s.gpr .x1).toNat + 7) / 8),
    wv s.mem (s.gpr .x2) (8 * (((s.gpr .x1).toNat + 7) / 8)) (((s.gpr .x1).toNat + 7) / 8)⟩,
    s.gpr .x2, s.sp⟩

/-- `vg_rsa_public_precomputed` is constant time but for `pre` and `e`. -/
theorem pdCode_constantTime : ConstantTime isa pdContract.pre pdContract.pub (Precomputed.code M.mm) := by
  refine RelCT.constantTime (pdCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpubOfD s₁, ?_, ?_, hp.1⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hsp, a0, a1, a2, a3, a4, a5, a6, -, s0, s1, hw, he⟩ := hp
    have c := pdCtx_of h₂
    have hpl := c.hpl
    rw [← a3, ← a1] at hpl
    rw [← a2, ← a3] at hw
    refine ⟨h₂, hsp.symm, s0.symm, by rw [← s1]; rfl, by rw [← a1]; rfl, a0.symm, a2.symm, a4.symm, a6.symm,
      by rw [← a5]; rfl, he.symm, ?_, ?_⟩
    · rw [← a2, ← a1, show (0 : Nat) = 8 * 0 from rfl]
      exact (wv_of_wordsAt hw (by omega)).symm
    · rw [← a2, ← a1]
      exact (wv_of_wordsAt hw (by omega)).symm

end VG.Proof.Bignum.AArch64
