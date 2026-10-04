import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain

/-!
# RSA with the CRT on x86-64: the result in constant time

`finish` sums `m_q + q h` into the modulus' accumulators (`finishSum`), whose
parts keep the header and the primes' workspaces (`FA`), and stores it masked
(`outArr_ct`): `finish_ct`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- What `finishSum`'s parts need, which they keep: the workspaces, `m_q`'s
base and the sizes. -/
def FA (p : RowsPub) (s : State) : Prop :=
  GoodW ⟨p.B, p.Z, p.w⟩ s ∧ RowsPre aY p s ∧
    word s.mem (off p.B p.oq) (8 * sArr aY) = off p.B (p.oq + slot p.wq aY) ∧ 1 ≤ p.wq ∧ p.wq ≤ p.w ∧
    p.w < 2 ^ 29

/-- `FA` after changes to the modulus' accumulators only. -/
theorem FA.outside {p : RowsPub} {s t : State} (h : FA p s) {n : Nat} (ho : Outside p.B (slot p.w aAcc) n s.mem t.mem)
    (hn : n ≤ 8 * (2 * p.w + 2)) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : FA p t := by
  obtain ⟨⟨minv, hg, hZ⟩, ⟨hs, hdi, hacc, hp, hq, hpw, hqw, hpa, hqa, hja, hlo, hop, hoq⟩, hqy, hwq, hwq', hw⟩ := h
  have hZ' : slot p.w 8 ≤ p.Z := hZ
  have hnw := hs.nowrap
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  have eY : sArr aY = 14 := rfl
  have hA := accs_le p.w
  have hh : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi =>
    ho.word (Or.inl (by have := hdr_lt_slot p.w aAcc hi; omega)) (by omega)
  have hab : ∀ {o d : Nat}, slot p.w 8 ≤ o → o + d + 8 ≤ 2 ^ 64 → word t.mem (off p.B o) d = word s.mem (off p.B o) d :=
    fun h1 h2 => word_above ho (by omega) h2
  have h8p := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  exact ⟨⟨minv, ⟨hg.scr.congr k.2.2, (k.gpr hr).trans hg.rdi, hg.hdr.of_outside ho (by
      unfold slot; omega)⟩, hZ⟩,
    ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, (hh _ (by decide)).trans hacc, (hh _ (by decide)).trans hp,
      (hh _ (by decide)).trans hq, (hab hlo (by omega)).trans hpw, (hab (by omega) (by omega)).trans hqw,
      (hab hlo (by unfold sArr; omega)).trans hpa, (hab (by omega) (by omega)).trans hqa, hja, hlo, hop, hoq⟩,
    (hab (by omega) (by omega)).trans hqy, hwq, hwq', hw⟩

/-- `finishSum`'s copy of `m_q`, in two parts: `q`'s workspace's base, then
its header through it. -/
theorem finishCopy_split : finishCopy = ([.mov .rax (.mem (hdr Crt.sWsQ))] : List Instr) ++
    ([.mov .rsi (.mem (Crt.ws .rax (sArr aY))), .mov .r12 (.mem (Crt.ws .rax sW)),
      .mov .rbx (.mem (hdr (sArr aAcc)))] : List Instr) := rfl

/-- After the copy's loads. -/
def FC (p : RowsPub) (s : State) : Prop :=
  FA p s ∧ s.gpr .rsi = off p.B (p.oq + slot p.wq aY) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wq ∧
    s.gpr .rbx = off p.B (slot p.w aAcc)

/-- `finishSum` leaks the same in runs that agree on the workspaces. -/
theorem finSum_ct : RelCT isa (Two FA) (seqs finishSum) fun _ _ => True := by
  unfold finishSum
  refine RelCT.seqs_append (by simp [Crt.zeroAccs]) (by simp) (RelCT.seq (R := Two FA) ?_ ?_)
  · refine two_post (two_map (fun p : RowsPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h.1) zeroAccs_ct)
      fun p s h => ?_
    obtain ⟨⟨minv, hg, hZ⟩, -, -, -, -, hw⟩ := id h
    exact WP.mono (zeroAccs_ok hg hZ (show p.w < 2 ^ 30 by omega)) fun t ⟨_, ho, k⟩ =>
      h.outside ho (le_refl _) k (by decide)
  simp only [seqs]
  refine RelCT.seq (R := Two FC) ?_ (RelCT.seq (R := Two FA) ?_
    (two_map id (fun _ _ h => h.2.1) (rows_ct (ja := aY) (by taint_decide))))
  · rw [finishCopy_split]
    refine RelCT.block_append (RelCT.seq (R := Two fun (p : RowsPub) t => FA p t ∧ t.gpr .rax = off p.B p.oq)
      (two_piece [.rdi] (pins_of (fun p _ => p.B) fun p s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.2.1.2.1) (by taint_decide) fun p s h => ?_)
      (two_piece [.rdi, .rax] (pins_of (fun p r => if r = .rdi then p.B else off p.B p.oq) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1.2.1
        · exact h.2) (by taint_decide) fun p s h => ?_))
    · obtain ⟨hl, -, -⟩ := h.2.1.hl
      obtain ⟨-, ⟨-, hdi, -, -, hq, -⟩, -⟩ := id h
      exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = off p.B p.oq ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, hdi, hdrOff, hl Crt.sWsQ (by decide), hq]) rfl)
        fun t ⟨⟨hax, hm⟩, k⟩ => ⟨h.outside (n := 0) (by rw [hm]; exact Outside.refl _ _ _ _) (by omega) k
          (by decide), hax⟩
    · obtain ⟨h, hax⟩ := h
      obtain ⟨hl, -, hlq⟩ := h.2.1.hl
      obtain ⟨-, ⟨-, hdi, hacc, -, -, -, hqw, -⟩, hqy, -⟩ := id h
      exact WP.mono (WP.keep [.rsi, .r12, .rbx] (Q := fun t => t.gpr .rsi = off p.B (p.oq + slot p.wq aY) ∧
          t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .rbx = off p.B (slot p.w aAcc) ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, Crt.ws, hdi, hax, hdrOff, hl (sArr aAcc) (by decide),
          hlq (sArr aY) (by decide), hlq sW (by decide), hqy, hqw, hacc]) rfl)
        fun t ⟨⟨hsi, h12, hbx, hm⟩, k⟩ => ⟨h.outside (n := 0) (by rw [hm]; exact Outside.refl _ _ _ _) (by omega) k
          (by decide), hsi, h12, hbx⟩
  · refine two_post (two_taint [.rsi, .rbx, .r12] (pins_of (fun p r => if r = .rsi then off p.B (p.oq + slot p.wq aY)
        else if r = .rbx then off p.B (slot p.w aAcc) else BitVec.ofNat 64 p.wq) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.2
          · exact h.2.2.1) (by taint_decide)) fun p s h => ?_
    obtain ⟨hf, hsi, h12, hbx⟩ := h
    obtain ⟨-, ⟨hs, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩, -, hwq, hwq', hw⟩ := id hf
    have hn := hs.nowrap
    have hA := accs_le p.w
    have hqY := slot_le (w := p.wq) (show aY < 8 by decide)
    refine WP.mono (copyWords_ok hsi hbx h12 hwq (by omega) (by omega)
      (fun j hj => hs.ld (by omega)) (fun j hj => hs.st (by omega))
      (fun j hj b hb => by rw [ofs_off p.B (by omega)]; omega)) fun t ⟨_, _, ho, k⟩ =>
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
  exact ⟨⟨minv, hr.good, hZ⟩, ⟨hr.good.scr, hr.good.rdi, hr.good.hdr.harr aAcc (by decide), hr.wsP, hr.wsQ,
      hr.pws.hdr.hw, hr.qws.hdr.hw, by rw [hr.pws.hdr.harr _ (by decide), off_off],
      by rw [hr.qws.hdr.harr _ (by decide), off_off], by decide, le_refl _, by unfold offQ offP; omega, hZq⟩,
    by rw [hr.qws.hdr.harr _ (by decide), off_off], by omega, hwq, by omega⟩

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
  refine WP.mono (finishSum_ok hr.good (by unfold CrtPub.w at hw; omega) hr.wsP hr.wsQ hr.pws.hdr.hw hr.qws.hdr.hw
    (by rw [hr.pws.hdr.harr _ (by decide), off_off]) (by rw [hr.qws.hdr.harr _ (by decide), off_off])
    (by rw [hr.qws.hdr.harr _ (by decide), off_off]) hlo hop hoq (by omega) hwp (by omega) hwq')
    fun t₃ ⟨_, ho₃, k₃⟩ => ?_
  have hacc := accs_le ((p.k + 7) / 8)
  have hb₃ : ∀ i < 32, word t₃.mem p.B (8 * i) = word t₂.mem p.B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((p.k + 7) / 8) Public.aAcc hi; omega)) (by omega)
  have hfx : ∀ i < 32, hFixed i = true → word t₃.mem p.B (8 * i) = word σ.mem p.B (8 * i) := fun i hi hf => by
    rw [hb₃ i hi]; exact hr.hfix i hi hf
  have k03 := hr.keep.trans k₃
  unfold OPreW OPre
  dsimp only
  exact ⟨minv, p.mask xb pb qb qib, ⟨hr.good.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hr.good.rdi,
      ⟨(hb₃ _ (by decide)).trans hr.good.hdr.hw, (hb₃ _ (by decide)).trans hr.good.hdr.hminv,
        fun j hj => (hb₃ _ (by unfold sArr; omega)).trans (hr.good.hdr.harr j hj)⟩⟩, rfl, hZ, by omega,
    by omega, by rw [hfx _ (by decide) (by decide)]; exact h.hO, by rw [hfx _ (by decide) (by decide)]; exact h.hK,
    by rw [hb₃ _ (by decide)]; exact hr.msk, fun j hj => by rw [k03.2.2]; exact h.out j hj, h.outSep⟩

/-- `finish` leaks the same in runs that agree on the public data. -/
theorem finish_ct : RelCT isa (Two (Stage R5)) (seqs Crt.finish) fun _ _ => True := by
  rw [finish_out]
  refine RelCT.seqs_append (by simp [finishSum, Crt.zeroAccs]) (by simp [outStepsArr])
    (RelCT.seq (R := Two OPreW) ?_ (outArr_ct (j := Public.aAcc) (by decide) (by taint_decide)))
  refine (two_post (Ψ := fun (p : CrtPub) t => OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩ t)
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : RowsPub))
      (fun _ _ h => stage5_fa h) finSum_ct) fun p t h => finSum_out h).mono (fun _ _ h => h)
    fun _ _ h => two_bind (fun (p : CrtPub) _ _ h₁ h₂ => ⟨(⟨p.B, p.Z, p.w, p.k, p.op⟩ : OPubW), h₁, h₂⟩) h

end VG.Proof.Bignum.X86_64
