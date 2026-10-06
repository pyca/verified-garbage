import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain

/-!
# RSA with the CRT on AArch64: the result in constant time

`finish` sums `m_q + q h` into the modulus' accumulators (`finishSum`), whose
parts keep the header and the primes' workspaces (`FA`), and stores it masked
(`outArr_ct`): `crtFinish_ct`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The store -/

/-- The public data of the result, without `-n⁻¹`. -/
structure OPubW where
  B : Addr
  Z : Nat
  w : Nat
  k : Nat
  op : Addr

/-- `outArr_ok`'s hypotheses, for some `-n⁻¹` and mask. -/
def OPreW (p : OPubW) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), Good s p.B p.Z p.w minv ∧ p.w = (p.k + 7) / 8 ∧ slot p.w 8 ≤ p.Z ∧ 1 ≤ p.k ∧
    p.k < 2 ^ 31 ∧ word s.mem p.B (8 * sOut) = p.op ∧ word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word s.mem p.B (8 * sMask) = mask c ∧ (∀ i < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 i) 1) ∧
    (∀ i < p.k, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i))

/-- Before `storeBE`, from array `j`. -/
def O1Arr (j : Nat) (p : OPubW) (s : State) : Prop :=
  ∃ c : Bool, Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ p.w = (p.k + 7) / 8 ∧ slot p.w 8 ≤ p.Z ∧ 1 ≤ p.k ∧
    p.k < 2 ^ 31 ∧ s.gpr .x8 = off p.B (slot p.w j) ∧ s.gpr .x1 = p.op + BitVec.ofNat 64 p.k ∧
    s.gpr .x9 = BitVec.ofNat 64 p.k ∧ s.gpr .x15 = mask c ∧
    (∀ i < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 i) 1) ∧
    (∀ i < p.k, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i))

/-- The result's store from array `j`, given that the taint analysis checks
its loads. -/
theorem outArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr j), ldh .x1 sOut, ldh .x9 sK,
      .add .x .x1 .x1 .x9, ldh .x15 sMask]) hc).isSome = true) :
    RelCT isa (Two OPreW) (seqs (outStepsArr j)) fun _ _ => True := by
  unfold outStepsArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := O1Arr j) [.x0]
    (pins_x0B (fun p : OPubW => p.B) fun _ _ ⟨_, _, hg, _⟩ => hg.x0) hT ?_) ?_
  · rintro p s ⟨minv, c, hg, hw, hZ, hk1, hk, hO, hK, hM, hout, hsep⟩
    have hs := hg.scr
    refine WP.mono (WP.keep [.x1, .x8, .x9, .x15] (Q := fun t => t.gpr .x8 = off p.B (slot p.w j) ∧
        t.gpr .x1 = p.op + BitVec.ofNat 64 p.k ∧ t.gpr .x9 = BitVec.ofNat 64 p.k ∧ t.gpr .x15 = mask c)
      (by brun [hg.x0, hdr_enc (sArr_lt hj), hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide),
        hdr_enc (show sMask < 32 by decide), hg.ld hZ (sArr_lt hj), hg.ld hZ (show sOut < 32 by decide),
        hg.ld hZ (show sK < 32 by decide), hg.ld hZ (show sMask < 32 by decide), hg.hdr.harr j hj, hO, hK, hM])
      rfl rfl rfl) fun t ⟨⟨h8, h1, h9, h15⟩, k⟩ => ⟨c, hs.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, hw, hZ,
        hk1, hk, h8, h1, h9, h15, fun i hi => by rw [k.wr]; exact hout i hi, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x0 = p.B) [.x8, .x1, .x9]
    (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, a₁, b₁, c₁, _⟩ ⟨_, _, _, _, _, _, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hs, h0, hw, hZ, hk1, hk, h8, h1, h9, h15, hout, hsep⟩
    exact WP.mono (storeBE_ok hs h8 h1 h9 h15 hk1 hk hw (by have := slot_le (w := p.w) hj; omega) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr .x0 (by decide)).trans h0
  exact two_taint [.x0] (pins_x0B (fun p : OPubW => p.B) fun _ _ h => h) (by taint_decide)

/-! ## The sum -/

/-- What `finishSum`'s parts need, which they keep: the workspaces, `m_q`'s
base and the sizes. -/
def FA (p : RowsPub) (s : State) : Prop :=
  GoodW ⟨p.B, p.Z, p.w⟩ s ∧ RowsPre aY p s ∧
    word s.mem p.B (p.oq + 8 * sArr aY) = off p.B (p.oq + slot p.wq aY) ∧ 1 ≤ p.wq ∧ p.wq ≤ p.w ∧
    p.w < 2 ^ 29

/-- `FA` after changes to the modulus' accumulators only. -/
theorem FA.outside {p : RowsPub} {s t : State} (h : FA p s) {n : Nat} (ho : Outside p.B (slot p.w aAcc) n s.mem t.mem)
    (hn : n ≤ 8 * (2 * p.w + 2)) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : FA p t := by
  obtain ⟨⟨minv, hg, hZ⟩, ⟨hs, h0, hacc, hp, hq, hpw, hqw, hpa, hqa, hja, hlo, hop, hoq⟩, hqy, hwq, hwq', hw⟩ := h
  have hZ' : slot p.w 8 ≤ p.Z := hZ
  have hnw := hs.nowrap
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  have eY : sArr aY = 14 := rfl
  have hA := accs_le p.w
  have hh : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi =>
    ho.word (Or.inl (by have := hdr_lt_slot p.w aAcc hi; omega)) (by omega)
  have hab : ∀ {d : Nat}, slot p.w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem p.B d = word s.mem p.B d :=
    fun h1 h2 => ho.word (Or.inr (by omega)) h2
  have h8p := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  exact ⟨⟨minv, ⟨hg.scr.congr k.wr, (k.gpr .x0 hr).trans hg.x0, ⟨(hh _ (by decide)).trans hg.hdr.hw,
      (hh _ (by decide)).trans hg.hdr.hminv, fun j hj => (hh _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩,
      hZ⟩,
    ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, (hh _ (by decide)).trans hacc, (hh _ (by decide)).trans hp,
      (hh _ (by decide)).trans hq, (hab (by omega) (by omega)).trans hpw, (hab (by omega) (by omega)).trans hqw,
      (hab (by omega) (by omega)).trans hpa, (hab (by omega) (by omega)).trans hqa, hja, hlo,
      hop, hoq⟩,
    (hab (by omega) (by omega)).trans hqy, hwq, hwq', hw⟩

/-- `finishSum`'s copy of `m_q`, in two parts: `q`'s workspace's base, then
its header through it. -/
theorem finishCopy_split : finishCopy = ([ldh .x5 Crt.sWsQ] : List Instr) ++
    ([ldw .x16 .x5 (sArr aY), ldw .x12 .x5 sW, ldh .x17 (sArr aAcc)] : List Instr) := rfl

/-- After the copy's loads. -/
def FC (p : RowsPub) (s : State) : Prop :=
  FA p s ∧ s.gpr .x16 = off p.B (p.oq + slot p.wq aY) ∧ s.gpr .x12 = BitVec.ofNat 64 p.wq ∧
    s.gpr .x17 = off p.B (slot p.w aAcc)

/-- `finishSum` leaks the same in runs that agree on the workspaces. -/
theorem finSum_ct : RelCT isa (Two FA) (seqs finishSum) fun _ _ => True := by
  unfold finishSum
  refine RelCT.seqs_append (by simp [zeroAccs]) (by simp) (RelCT.seq (R := Two FA) ?_ ?_)
  · refine two_post (two_map (fun p : RowsPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h.1) zeroAccs_ct)
      fun p s h => ?_
    obtain ⟨⟨minv, hg, hZ⟩, -, -, -, -, hw⟩ := id h
    exact WP.mono (zeroAccs_ok hg hZ (show p.w < 2 ^ 30 by omega)) fun t ⟨_, ho, k⟩ =>
      h.outside ho (Nat.le_refl _) k (by decide)
  simp only [seqs]
  refine RelCT.seq (R := Two FC) ?_ (RelCT.seq (R := Two FA) ?_
    (two_map id (fun _ _ h => h.2.1) (rows_ct (ja := aY) (by taint_decide))))
  · rw [finishCopy_split]
    refine RelCT.block_append (RelCT.seq (R := Two fun (p : RowsPub) t => FA p t ∧ t.gpr .x5 = off p.B p.oq)
      (two_piece [.x0] (pins_of (fun p _ => p.B) fun p s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.2.1.2.1) (by taint_decide) fun p s h => ?_)
      (two_piece [.x0, .x5] (pins_of (fun p r => if r = .x0 then p.B else off p.B p.oq) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1.2.1
        · exact h.2) (by taint_decide) fun p s h => ?_))
    · obtain ⟨hl, -, -⟩ := h.2.1.hl
      obtain ⟨-, ⟨-, h0, -, -, hq, -⟩, -⟩ := id h
      exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off p.B p.oq ∧ t.mem = s.mem)
        (by brun [h0, hdr_enc (show Crt.sWsQ < 32 by decide), hl Crt.sWsQ (by decide), hq])
        (by decide) (by decide) (by decide +kernel))
        fun t ⟨⟨h5, hm⟩, k⟩ => ⟨h.outside (n := 0) (by rw [hm]; exact Outside.refl _ _ _ _) (by omega) k
          (by decide), h5⟩
    · obtain ⟨h, h5⟩ := h
      obtain ⟨hl, -, hlq⟩ := h.2.1.hl
      obtain ⟨-, ⟨-, h0, hacc, -, -, -, hqw, -⟩, hqy, -⟩ := id h
      have l1 := hl (sArr aAcc) (by decide)
      have l2 := hlq (sArr aY) (by decide)
      have l3 := hlq sW (by decide)
      exact WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t => t.gpr .x16 = off p.B (p.oq + slot p.wq aY) ∧
          t.gpr .x12 = BitVec.ofNat 64 p.wq ∧ t.gpr .x17 = off p.B (slot p.w aAcc) ∧ t.mem = s.mem)
        (by brun [ldw, h0, h5, hdr_enc (sArr_lt (show aY < 8 by decide)), hdr_enc (show sW < 32 by decide),
          hdr_enc (sArr_lt (show aAcc < 8 by decide)), l1, l2, l3, hqy, hqw, hacc])
        (by decide) (by decide) (by decide +kernel))
        fun t ⟨⟨h16, h12, h17, hm⟩, k⟩ => ⟨h.outside (n := 0) (by rw [hm]; exact Outside.refl _ _ _ _) (by omega) k
          (by decide), h16, h12, h17⟩
  · refine two_post (two_taint [.x16, .x17, .x12] (pins_of (fun p r => if r = .x16 then
        off p.B (p.oq + slot p.wq aY) else if r = .x17 then off p.B (slot p.w aAcc) else BitVec.ofNat 64 p.wq)
        fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.2
          · exact h.2.2.1) (by taint_decide)) fun p s h => ?_
    obtain ⟨hf, h16, h12, h17⟩ := h
    obtain ⟨-, ⟨hs, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩, -, hwq, hwq', hw⟩ := id hf
    have hn := hs.nowrap
    have hA := accs_le p.w
    have hqY := slot_le (w := p.wq) (show aY < 8 by decide)
    refine WP.mono (copyWords_ok h16 h17 h12 hwq (by omega) (by omega)
      (fun j hj => hs.ld (by omega)) (fun j hj => hs.st (by omega))
      (fun j hj b hb => by rw [ofs_off p.B (by omega)]; omega)) fun t ⟨_, _, ho, _, _, k⟩ =>
        hf.outside ho (by omega) k (by decide)

/-- `finishSum`'s hypotheses after `p`'s phase. -/
theorem stage5_fa {p : CrtPub} {t : State} (h : Stage R5 p t) :
    FA ⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl, wsWords p.pl, wsWords p.ql⟩ t := by
  unfold CrtPub.w
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega
  have hwq := wsWords_le (len := p.ql) (w := (p.k + 7) / 8) (by omega) (by omega)
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega
  unfold FA RowsPre
  dsimp only
  exact ⟨⟨minv, hr.good, hZ⟩, ⟨hr.good.scr, hr.good.x0, hr.good.hdr.harr aAcc (by decide), hr.wsP, hr.wsQ,
      by rw [← word_off]; exact hr.pws.hdr.hw, by rw [← word_off]; exact hr.qws.hdr.hw,
      by rw [← word_off, hr.pws.hdr.harr _ (by decide), off_off],
      by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off], by decide, Nat.le_refl _,
      by unfold offQ offP; omega, by omega⟩,
    by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off], by omega, hwq, by omega⟩

/-- `finishSum` leaves what the store needs. -/
theorem finSum_out {p : CrtPub} {t₂ : State} (h : Stage R5 p t₂) :
    WP isa (seqs finishSum) t₂ (OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩) := by
  have hfa := stage5_fa h
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩, -, hwq, hwq', hw⟩ := hfa
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hpl1 := h.pl1
  have hZq := h.z
  have hn := hr.good.scr.nowrap
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega
  have hwp := wsWords_le (len := p.pl) (w := (p.k + 7) / 8) (by omega) (by omega)
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega
  refine WP.mono (finishSum_ok hr.good (by unfold CrtPub.w at hw; omega) hr.wsP hr.wsQ
    (by rw [← word_off]; exact hr.pws.hdr.hw) (by rw [← word_off]; exact hr.qws.hdr.hw)
    (by rw [← word_off, hr.pws.hdr.harr _ (by decide), off_off]) (by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off])
    (by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off]) (Nat.le_refl _) (by unfold offQ offP; omega) hZq
    (by omega) hwp (by omega) hwq') fun t₃ ⟨_, ho₃, k₃⟩ => ?_
  have hacc := accs_le ((p.k + 7) / 8)
  have hb₃ : ∀ i < 32, word t₃.mem p.B (8 * i) = word t₂.mem p.B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((p.k + 7) / 8) Public.aAcc hi; omega)) (by omega)
  have hfx : ∀ i < 32, hFixed i = true → word t₃.mem p.B (8 * i) = word σ.mem p.B (8 * i) := fun i hi hf => by
    rw [hb₃ i hi]; exact hr.hfix i hi hf
  have k03 := hr.keep.trans k₃
  unfold OPreW
  dsimp only
  exact ⟨minv, p.mask xb pb qb qib, ⟨hr.good.scr.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans hr.good.x0,
      ⟨(hb₃ _ (by decide)).trans hr.good.hdr.hw, (hb₃ _ (by decide)).trans hr.good.hdr.hminv,
        fun j hj => (hb₃ _ (by unfold sArr; omega)).trans (hr.good.hdr.harr j hj)⟩⟩, rfl, hZ, by omega,
    by omega, by rw [hfx _ (by decide) (by decide)]; exact h.hO, by rw [hfx _ (by decide) (by decide)]; exact h.hK,
    by rw [hb₃ _ (by decide)]; exact hr.msk, fun j hj => by rw [k03.wr]; exact h.out j hj, h.outSep⟩

/-- `finish` leaks the same in runs that agree on the public data. -/
theorem crtFinish_ct : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True := by
  rw [finish_out]
  refine RelCT.seqs_append (by simp [finishSum, zeroAccs]) (by simp [outStepsArr])
    (RelCT.seq (R := Two OPreW) ?_ (outArr_ct (j := Public.aAcc) (by decide) (by taint_decide)))
  refine (two_post (Ψ := fun (p : CrtPub) t => OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩ t)
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : RowsPub))
      (fun _ _ h => stage5_fa h) finSum_ct) fun p t h => finSum_out h).mono (fun _ _ h => h)
    fun _ _ h => two_bind (fun (p : CrtPub) _ _ h₁ h₂ => ⟨(⟨p.B, p.Z, p.w, p.k, p.op⟩ : OPubW), h₁, h₂⟩) h

end VG.Proof.Bignum.AArch64
