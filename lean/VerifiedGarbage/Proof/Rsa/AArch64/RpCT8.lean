import VerifiedGarbage.Proof.Rsa.AArch64.RpCT7
import VerifiedGarbage.Proof.Rsa.AArch64.RpCode
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode

/-!
# `vg_rsa_recover_primes` on AArch64: constant time but for `n`, `e` and the tries

`rest` (`rest_ct`), `fail` (`failR_ct`) and `main` (`rpMain_ct`): `main`'s
branch on `d e` is the public number of tries being 0. Then the entry and
the modulus' check (`rpCode_ct`), and the contract's `ConstantTime`
(`rpCode_constantTime`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Rsa (recoverPrimes)

namespace Rp

/-- After the halvings, Montgomery form, the candidates and the factors. -/
theorem rest_ct (M : Mont) : RelCT isa (Two GR0) (rest M.mm) fun _ _ => True := by
  rw [show rest M.mm = seqs ([halving] ++ (mont M.mm ++ ([candLoop M.mm] ++ fin M.mm))) by
    simp only [rest, List.append_assoc]]
  exact (ct_app (by simp) (by simp [mont, VG.Impl.Rsa.AArch64.r2Steps]) (ct_one halving_ct)
    (ct_app (by simp [mont, VG.Impl.Rsa.AArch64.r2Steps]) (by simp [fin]) (mont_ct M)
    (ct_app (by simp) (by simp [fin]) (ct_one (candLoop_ct M)) (fin_ct M)))).mono (fun _ _ h => h)
      fun _ _ _ => trivial

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GFr (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, I.pub = p ∧ Scr s I.B I.Z ∧ s.gpr .x0 = I.B ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD ∧ s.wr = I.W ∧ RpLens I ∧ RpOuts I

theorem pins_GFr : Pins GFr [.x0] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

theorem zeroOutR_ct {sPtr : Nat} (hP : sPtr < 32) (ptr : RpP → Addr)
    (hA : ∀ p s, GFr p s → word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 Public.sK, movi .x3 0]) hc).isSome
      = true) :
    RelCT isa (Two GFr) (zeroOut sPtr Public.sK) (Two GFr) :=
  pin_ct [.x0] [.x1, .x2] (fun p => zoVal (ptr p) p.k) pins_GFr ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, h0, ha, -, L, -⟩ := h
      dsimp only [RpIn.pub] at hp
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = ptr I.pub ∧
        t.gpr .x2 = BitVec.ofNat 64 I.k) (by
        brun [h0, hdr_enc hP, hdr_enc (show Public.sK < 32 by decide), hl' sPtr hP,
          hl' Public.sK (by decide)]
        exact ⟨hp, ha.k⟩) rfl rfl rfl)
        fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, rfl, hs, h0, ha, hW, L, O⟩ := h
      dsimp only [RpIn.pub] at hp hwr hsep ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (zeroOut_ok hs h0 h256 hP (by decide) hp ha.k (by omega) (by omega)
        ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩) fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega)
      exact ⟨I, rfl, hs.congr k.wr, (k.gpr .x0 (by decide)).trans h0, ha.congr fun i hi => fw i (by
        unfold rArg at hi; omega), k.wr.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem failR_ct : RelCT isa (Two GFr) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pP (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide))
    (ct_one (Ψ := fun (_ : RpP) (_ : State) => True) (two_post (two_taint [.x0] pins_GFr (by taint_decide))
      fun _ _ _ => WP.mono (WP.keep [.x0] (Q := fun _ => True) (by brun; exact ⟨_, rfl⟩) rfl rfl rfl)
        fun _ _ => trivial)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [RpIn.pub]
  · exact ⟨ha.p, O.p, O.sp⟩
  · exact ⟨ha.q, O.q, O.sq⟩

/-! ## `main` -/

/-- The public number of tries is 0 iff `d e` fails step 1. -/
theorem cnt_zero {I : RpIn} (hv : Spec.Rsa.modulusValid I.N I.k = true) (L : RpLens I) :
    I.pub.cnt = 0 ↔ ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by
  have e : I.pub.cnt = (recoverPrimes I.N I.E I.D).2 := by
    show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = _
    simp only [Spec.Rsa.primesKey, L.nbl, hv, ite_true]
    split <;> simp_all
  rw [e]
  by_cases h : I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1
  · rw [VG.Proof.Rsa.recoverPrimes_none h]; omega
  · rw [VG.Proof.Rsa.recoverPrimes_go h]
    have := VG.Proof.Rsa.go_pos I.N (Spec.Rsa.splitTwos (I.D * I.E - 1)).1
      (Spec.Rsa.splitTwos (I.D * I.E - 1)).2 _ (Nat.le_refl _)
    omega

/-- After `main`'s prefix. -/
def GMP (p : RpP) (s : State) : Prop :=
  ∃ (σ : State) (I : RpIn), I.pub = p ∧ RpPre I σ ∧ Spec.Rsa.modulusValid I.N I.k = true ∧ RpS I σ.mem s ∧
    (s.gpr .x10 = 0 ↔ I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) ∧
    wv s.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E - I.D * I.E % 2 ∧
    wv s.mem I.B (slot (wk I.k) Public.aN) (wk I.k) = I.N ∧
    ((word s.mem I.B (slot (wk I.k) Public.aN)).toNat * (word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    I.D * I.E < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

theorem gmp_eval {p : RpP} {s : State} (h : GMP p s) : isa.eval (.zero .x .x10) s = some (!decide (p.cnt = 0)) := by
  obtain ⟨σ, I, rfl, hp, hv, -, hz, -⟩ := h
  rw [eval_zero]
  congr 1
  have := cnt_zero hv hp.L
  rw [Bool.eq_iff_iff, beq_iff_eq, hz]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, this, Classical.not_not]

/-- `main` leaks the same in runs that agree on the public data. -/
theorem rpMain_ct (M : Mont) : RelCT isa (Two GM) (main M.mm) fun _ _ => True := by
  rw [rpMain_eq']
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two GMP) (two_post (prefix_ct.mono
    (fun _ _ h => h) fun _ _ _ => trivial) fun p s ⟨I, e, h, hv⟩ => WP.mono (rpPrefix_ok h hv)
      fun t ⟨S, hz, vM, vN, hi, hDE, _⟩ => ⟨s, I, e, h, hv, S, hz, vM, vN, hi, hDE⟩) ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [gmp_eval h₁, gmp_eval h₂]) ?_ ?_
  · refine (rest_ct M).mono (fun _ _ h => two_mono (fun p t ⟨h, hf⟩ => ?_) h) fun _ _ h => h
    have hev := gmp_eval h
    obtain ⟨σ, I, rfl, hp, hv, S, hz, vM, vN, hi, hDE⟩ := h
    rw [hev] at hf
    have hb : I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E := by
      have := cnt_zero hv hp.L
      simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at hf
      by_contra hn; exact hf (this.mpr hn)
    have L := hp.L
    have k1 := L.k1
    have k2 := L.k2
    obtain ⟨hNo, hlo⟩ := valid_lo hv
    have hlo' : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
      refine Nat.le_trans ?_ hlo
      rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega)
    exact ⟨I, σ.mem, rfl, ⟨S, L, hNo, hlo', vN, hi, by rw [vM]; omega, by omega, by omega, by omega,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oP.wr i hi, hp.oP.sep⟩,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oQ.wr i hi, hp.oQ.sep⟩, hp.a⟩, hp.outs, hv⟩
  · exact failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨σ, I, e, hp, hv, S, _⟩, _⟩ =>
      ⟨I, e, S.ws.scr, S.ws.x0, S.args, S.wr, hp.L, hp.outs⟩) h) fun _ _ h => h

end Rp

/-! ## The code -/

/-- A state the contract allows, with the public data `p`. -/
def RPRel (p : RpP) (s : State) : Prop := rpA.pre s ∧ (rpIn s).pub = p

theorem rpEntry_split : entry = ([.ldrSp .x8 16] : List Instr) ++ entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def RP1 (p : RpP) (t : State) : Prop :=
  ∃ s, RPRel p s ∧ t.gpr .x8 = p.B ∧ t.gpr .x4 = p.pN ∧ t.gpr .x5 = BitVec.ofNat 64 p.k ∧
    WP isa (.block (entry.drop 1)) t (RpHeadPost s)

/-- After `entry`. -/
def RP2 (p : RpP) (t : State) : Prop := ∃ s, RPRel p s ∧ RpHeadPost s t

/-- After the modulus' check. -/
def RP3 (p : RpP) (t : State) : Prop :=
  ∃ s t₁, RPRel p s ∧ RpHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k).toNat

theorem rpRel_x4 {p : RpP} {s : State} (h : RPRel p s) : s.gpr .x4 = p.pN := congrArg RpP.pN h.2

theorem rpRel_x5 {p : RpP} {s : State} (h : RPRel p s) : s.gpr .x5 = BitVec.ofNat 64 p.k := by
  rw [← congrArg RpP.k h.2]; exact (ofNat_toNat64 _).symm

/-- `entry` leaks the same in runs with the same public data. -/
theorem rpEntry_ct : RelCT isa (Two RPRel) (.block entry) (Two RP2) := by
  rw [rpEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := RP1) [.x4, .x5] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [rpRel_x4 h₁, rpRel_x4 h₂]
    · rw [rpRel_x5 h₁, rpRel_x5 h₂]) (by taint_decide) ?_)
    (two_piece [.x8, .x4, .x5] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro p s hs
  have c := rpCtx_of hs.1
  have hh : WP isa (.block (([.ldrSp .x8 16] : List Instr) ++ entry.drop 1)) s (RpHeadPost s) := by
    rw [← rpEntry_split]; exact rpHead_ok' c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg s 2 := rfl
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := c.ha 2 (by decide)
  have ho : 16 % 8 = 0 ∧ 16 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 2)
    (by brun [exec_ldrSp ho ha2, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
      ⟨s, hs, h8.trans (congrArg RpP.B hs.2), (k.gpr .x4 (by decide)).trans (rpRel_x4 hs),
        (k.gpr .x5 (by decide)).trans (rpRel_x5 hs), hw⟩

/-- `vg_rsa_recover_primes` leaks the same in runs that agree on the public
data. -/
theorem rpCode_ct (M : Mont) : RelCT isa (Two RPRel) (code M.mm) fun _ _ => True := by
  unfold code
  refine RelCT.seq (R := Two RP3) (RelCT.block_append (RelCT.seq rpEntry_ct ?_)) ?_
  -- The modulus' check.
  · refine two_piece [.x2, .x3] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.x2, h₂.x2, rpRel_x4 c₁, rpRel_x4 c₂]
      · rw [h₁.x3, h₂.x3, ofNat_toNat64, ofNat_toNat64, rpRel_x5 c₁, rpRel_x5 c₂])
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := rpCtx_of hs.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (rpIn s).nb.length = (s.gpr .x5).toNat := bytesAt_length _ _ _
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h.x2 h.x3 c.L.k1 c.L.k2 hnl
      (fun i hi => hnb.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hz, hm, _⟩, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) ?_ ?_
  · exact Rp.failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := rpPre_of (rpCtx_of hs.1) h hm k
      exact ⟨rpIn s, hs.2, hpre.scr, hpre.x0, hpre.args, hpre.wr, hpre.L, hpre.outs⟩) h) fun _ _ h => h
  · exact (Rp.rpMain_ct M).mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => by
      refine ⟨rpIn s, hs.2, rpPre_of (rpCtx_of hs.1) h hm k, ?_⟩
      have e : (rpIn s).pub = p := hs.2
      subst e
      have z' : t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k).toNat :=
        z
      rw [eval_zero, z'] at hf
      show Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k = true
      revert hf
      cases Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k <;> simp) h) fun _ _ h => h

/-- `vg_rsa_recover_primes` is constant time but for `n`, `e` and the number
of tries. -/
theorem rpCode_constantTime (M : Mont) : ConstantTime isa rpA.pre rpA.pub (code M.mm) := by
  refine RelCT.constantTime ((rpCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(rpIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩,
    hp.2.1⟩) fun _ _ h => h)
  obtain ⟨hr, hsp, ha, hn, he, hc⟩ := hp
  have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have a : ∀ j < 4, stackArg s₂ j = stackArg s₁ j := fun j hj => by
    have := congrArg (fun l => l[j]?) ha
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [RpIn.pub, rpIn, RpP.mk.injEq]
  refine ⟨a 2 (by decide), by rw [a 3 (by decide)], by rw [r .x5 (by decide)], by rw [r .x7 (by decide)],
    by rw [a 1 (by decide)], r .x0 (by decide), r .x2 (by decide), r .x4 (by decide), r .x6 (by decide),
    a 0 (by decide), hn.symm, he.symm, ?_, hc.symm⟩
  rw [w₁, w₂, r .x0 (by decide), r .x1 (by decide), r .x2 (by decide), r .x3 (by decide), a 2 (by decide),
    a 3 (by decide)]

end VG.Proof.Rsa.AArch64
