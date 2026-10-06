import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain

/-!
# `vg_rsa_crt_values` on AArch64: constant time but for `n`

`main` leaks the same in runs that agree on the public data (`cvMain_ct`),
and so do `entry`, the modulus' check and `fail` (`cvCode_ct`): the
contract's `ConstantTime` (`cvCode_constantTime`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN)

/-! ## `main` -/

/-- On entry to `main`. -/
def GM (p : CvP) (s : State) : Prop := ∃ I : CvIn, I.pub = p ∧ CvPre I s

theorem pins_GM : Pins GM [.x0] := fun _ _ _ ⟨_, e₁, h₁⟩ ⟨_, e₂, h₂⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0]
  exact (congrArg CvP.B e₁).trans (congrArg CvP.B e₂).symm

theorem CvPre.outs {I : CvIn} {s : State} (h : CvPre I s) : CvOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oQi.wr i hi, fun i hi => by rw [← h.wr]; exact h.oDp.wr i hi,
    fun i hi => by rw [← h.wr]; exact h.oDq.wr i hi, h.oQi.sep, h.oDp.sep, h.oDq.sep, h.a1, h.a2, h.a3⟩

theorem head_ct : RelCT isa (Two GM) (.block head) (Two GA) :=
  two_piece [.x0] pins_GM (by taint_decide) fun _ s ⟨I, e, h⟩ =>
    WP.mono (cvHeadS_ok h) fun _ ⟨ht, hm⟩ => ⟨I, s.mem, true, e, ht, h.L, h.outs, hm⟩

/-- `main` leaks the same in two runs with the same public data. -/
theorem cvMain_ct : RelCT isa (Two GM) main fun _ _ => True := by
  rw [main_eq]
  exact (ct_app (by simp) (by simp [loadA]) (ct_one head_ct)
    (ct_app (by simp [loadA]) (by simp [pqCheck]) loads_ct
    (ct_app (by simp [pqCheck]) (by simp [invPart, invSetup]) pqCheck_ct
    (ct_app (by simp [invPart, invSetup]) (by simp [divisor]) invPart_ct
    (ct_app (by simp [divisor]) (by simp)
      (ct_app (by simp [divisor]) (by simp) (divisor_ct (by decide) (by decide) (by taint_decide))
        (ct_one (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp) (by simp [divisor])
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
        (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))
    (ct_app (by simp [divisor]) (by simp [storeA])
      (ct_app (by simp [divisor]) (by simp) (divisor_ct (by decide) (by decide) (by taint_decide))
        (ct_one (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))))
      (stores_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.gs) h) fun _ _ h => h)))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GF (p : CvP) (s : State) : Prop :=
  ∃ I : CvIn, I.pub = p ∧ Scr s I.B I.Z ∧ s.gpr .x0 = I.B ∧
    CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD ∧ s.wr = I.W ∧ CvLens I ∧
    CvOuts I

theorem pins_GF : Pins GF [.x0] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg CvP.B e₁).trans (congrArg CvP.B e₂).symm

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

theorem zeroOut_ct {sPtr sLen : Nat} (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr) (len : CvP → Nat)
    (hA : ∀ p s, GF p s → word s.mem p.B (8 * sPtr) = ptr p ∧ word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∀ i < len p, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < len p, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)) ∧ 1 ≤ len p ∧ len p < 2 ^ 31)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 sLen, movi .x3 0]) hc).isSome = true) :
    RelCT isa (Two GF) (zeroOut sPtr sLen) (Two GF) :=
  pin_ct [.x0] [.x1, .x2] (fun p => zoVal (ptr p) (len p)) pins_GF ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, h0, -, -, L, -⟩ := h
      dsimp only [CvIn.pub] at hp hl
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = ptr I.pub ∧
        t.gpr .x2 = BitVec.ofNat 64 (len I.pub)) (by
        brun [h0, hdr_enc hP, hdr_enc hL, hl' sPtr hP, hl' sLen hL]
        exact ⟨hp, hl⟩) rfl rfl rfl)
        fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, hwr, hsep, hl1, hl2⟩ := hA p s h
      obtain ⟨I, rfl, hs, h0, ha, hW, L, O⟩ := h
      dsimp only [CvIn.pub] at hp hl hwr hsep hl1 hl2 ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      refine WP.mono (zeroOut_ok hs h0 h256 hP hL hp hl hl1 hl2 ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩)
        fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega)
      exact ⟨I, rfl, hs.congr k.wr, (k.gpr .x0 (by decide)).trans h0, ha.congr fun i hi => fw i (by
        unfold argSlot at hi; omega), k.wr.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem fail_ct : RelCT isa (Two GF) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOut_ct (by decide) (by decide) CvP.pDp CvP.pl (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOut_ct (by decide) (by decide) CvP.pDq CvP.ql (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOut_ct (by decide) (by decide) CvP.pQi CvP.pl (fun p s h => ?_) (by taint_decide))
    (ct_one (Ψ := fun (_ : CvP) (_ : State) => True) (two_post (two_taint [.x0] pins_GF (by taint_decide))
      fun _ _ _ => WP.mono (WP.keep [.x0] (Q := fun _ => True) (by brun; exact ⟨_, rfl⟩) rfl rfl rfl) fun _ _ => trivial))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [CvIn.pub]
    have := L.k2
  · exact ⟨ha.dp, ha.pl, O.dp, O.sdp, L.pl1, by have := L.pl2; omega⟩
  · exact ⟨ha.dq, ha.ql, O.dq, O.sdq, L.ql1, by have := L.ql2; omega⟩
  · exact ⟨ha.qi, ha.pl, O.qi, O.sqi, L.pl1, by have := L.pl2; omega⟩

/-! ## The code -/

/-- A state the contract allows, with the public data `p`. -/
def CVRel (p : CvP) (s : State) : Prop := cvA.pre s ∧ (cvIn s).pub = p

theorem cvEntry_split : entry = ([.ldrSp .x8 48] : List Instr) ++ entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def CV1 (p : CvP) (t : State) : Prop :=
  ∃ s, CVRel p s ∧ t.gpr .x8 = p.B ∧ t.gpr .x6 = p.pN ∧ t.gpr .x7 = BitVec.ofNat 64 p.k ∧
    WP isa (.block (entry.drop 1)) t (CvHeadPost s)

/-- After `entry`. -/
def CV2 (p : CvP) (t : State) : Prop := ∃ s, CVRel p s ∧ CvHeadPost s t

/-- After the modulus' check. -/
def CV3 (p : CvP) (t : State) : Prop :=
  ∃ s t₁, CVRel p s ∧ CvHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k).toNat

theorem cvRel_x6 {p : CvP} {s : State} (h : CVRel p s) : s.gpr .x6 = p.pN := congrArg CvP.pN h.2

theorem cvRel_x7 {p : CvP} {s : State} (h : CVRel p s) : s.gpr .x7 = BitVec.ofNat 64 p.k := by
  rw [← congrArg CvP.k h.2]; exact (ofNat_toNat64 _).symm

/-- `entry` leaks the same in runs with the same public data. -/
theorem cvEntry_ct : RelCT isa (Two CVRel) (.block entry) (Two CV2) := by
  rw [cvEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CV1) [.x6, .x7] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [cvRel_x6 h₁, cvRel_x6 h₂]
    · rw [cvRel_x7 h₁, cvRel_x7 h₂]) (by taint_decide) ?_)
    (two_piece [.x8, .x6, .x7] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro p s hs
  have c := cvCtx_of hs.1
  have hh : WP isa (.block (([.ldrSp .x8 48] : List Instr) ++ entry.drop 1)) s (CvHeadPost s) := by
    rw [← cvEntry_split]; exact cvHead_ok' c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 48) 64 = stackArg s 6 := rfl
  have ha6 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 48) 8 := c.ha 6 (by decide)
  have ho : 48 % 8 = 0 ∧ 48 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 6)
    (by brun [exec_ldrSp ho ha6, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
      ⟨s, hs, h8.trans (congrArg CvP.B hs.2), (k.gpr .x6 (by decide)).trans (cvRel_x6 hs),
        (k.gpr .x7 (by decide)).trans (cvRel_x7 hs), hw⟩

/-- `vg_rsa_crt_values` leaks the same in runs that agree on the public
data. -/
theorem cvCode_ct : RelCT isa (Two CVRel) CrtValues.code fun _ _ => True := by
  unfold CrtValues.code
  refine RelCT.seq (R := Two CV3) (RelCT.block_append (RelCT.seq cvEntry_ct ?_)) ?_
  -- The modulus' check.
  · refine two_piece [.x2, .x3] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.x2, h₂.x2, cvRel_x6 c₁, cvRel_x6 c₂]
      · rw [h₁.x3, h₂.x3, ofNat_toNat64, ofNat_toNat64, cvRel_x7 c₁, cvRel_x7 c₂])
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := cvCtx_of hs.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (cvIn s).nb.length = (s.gpr .x7).toNat := bytesAt_length _ _ _
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h.x2 h.x3 c.L.k1 c.L.k2 hnl
      (fun i hi => hnb.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hz, hm, _⟩, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) ?_ ?_
  · exact fail_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := cvPre_of (cvCtx_of hs.1) h hm k
      exact ⟨cvIn s, hs.2, hpre.scr, hpre.x0, hpre.args, hpre.wr, hpre.L, hpre.outs⟩) h) fun _ _ h => h
  · exact cvMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
      ⟨cvIn s, hs.2, cvPre_of (cvCtx_of hs.1) h hm k⟩) h) fun _ _ h => h

/-- `vg_rsa_crt_values` is constant time but for `n`. -/
theorem cvCode_constantTime : ConstantTime isa cvA.pre cvA.pub CrtValues.code := by
  refine RelCT.constantTime (cvCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(cvIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩,
    hp.2.1⟩) fun _ _ h => h)
  obtain ⟨hr, hsp, ha, hn⟩ := hp
  have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have a : ∀ j < 8, stackArg s₂ j = stackArg s₁ j := fun j hj => by
    have := congrArg (fun l => l[j]?) ha
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [CvIn.pub, cvIn, CvP.mk.injEq]
  refine ⟨a 6 (by decide), by rw [a 7 (by decide)], by rw [r .x7 (by decide)], by rw [a 1 (by decide)],
    by rw [a 3 (by decide)], by rw [a 5 (by decide)], r .x0 (by decide), r .x2 (by decide), r .x4 (by decide),
    r .x6 (by decide), a 0 (by decide), a 2 (by decide), a 4 (by decide), hn.symm, ?_⟩
  rw [w₁, w₂, r .x0 (by decide), r .x1 (by decide), r .x2 (by decide), r .x3 (by decide), r .x4 (by decide),
    r .x5 (by decide), a 6 (by decide), a 7 (by decide)]

end VG.Proof.Rsa.AArch64
