import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTIfma
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain

/-!
# RSA with AVX512_IFMA on x86-64, any size: `main` in constant time

`main` is `Crt.main` with a branch on the
sizes, which are public (`anySizes`), and within the IFMA branch another for the
vector code of each layout (`ifmaAny`): the IFMA branch's parts
(`pre`, `ifma`, `post`) are constant time for their correctness lemmas'
hypotheses (`pre_ct`, `ifma_ct`, `post_ct`), which the states of a run
between them satisfy (`prePre_of`, `ifPre_of`, `postPre_of`); the last
`else` is `vg_rsa_private_crt`'s (`qS_ct`, `pS_ct`). So `main` is
(`main_ct`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.CrtIfma (Lay lay2048 lay3072 lay4096 sizes ifma vec result region sIfma)
open VG.Proof.Bignum.X86_64 (NSafe nsafe_word preRanges_nsafe APost PrePub PrePre pre_ct PostPub PostPre
  post_ct pins_eqs StageRel Stage stage_step two_stage R0 R1 R2 R3 R5 CrtPub RedcCT LoadCT
  SetupCT ChecksCT QPhaseCT PPhaseCT setupS_ct checksS_ct qS_ct pS_ct nSetup_ct nPart_ok RelCT.seqs_append
  pre_ok)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## The parts' hypotheses from a run's states -/

/-- `pre_ok`'s hypotheses, after the checks. -/
theorem prePre_of (hl : LayOk l) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W) :
    PrePre ⟨B, Z, (k + 7) / 8, minv, Spec.Rsa.os2ip nb, offP ((k + 7) / 8), offQ ((k + 7) / 8) pl, l.W⟩ t₀ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  dsimp only [PrePre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + tabBytes l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact ⟨mp, mq, _, _, C, hr.good, by omega, le_refl _, by rw [hoq]; rfl, by omega, by omega, by omega,
    hr.wsP, hr.wsQ, pws, qws, hr.nv, hr.xm, pxv, hP'.1, hP'.2, qxv, hQ'.1, hQ'.2⟩

/-- `ifma`'s hypotheses, after `pre` (as `branchA2_ok` runs it). -/
theorem ifPre_of (hl : LayOk l) {s t₀ s₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hZa : offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W + 2 * l.D + 8 ≤ Z)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    IfPre l ⟨B, Z, (k + 7) / 8, offP ((k + 7) / 8), offQ ((k + 7) / 8) pl,
      offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W, dpp, dqp, pl, ql⟩ s₁ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  dsimp only [IfPre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hEW : l.E = 8 * l.W := rfl
  have hpl' : pl ≤ l.E := by unfold wsWords at hpl; omega
  have hql' : ql ≤ l.E := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + tabBytes l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have hh₀ : ∀ i < 32, hFixed i = true → word t₀.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  obtain ⟨hg₁, hN₁, rp, rq, f₁, k₁, mk₁⟩ := hA
  have ns₁ := preRanges_nsafe (w := (k + 7) / 8) (wp := l.W) (wq := l.W) (le_refl (offP ((k + 7) / 8)))
    (show slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl by rw [hoq]; omega)
  have hpr : ∀ r ∈ preRanges ((k + 7) / 8) (offP ((k + 7) / 8)) l.W (offQ ((k + 7) / 8) pl) l.W,
      r.1 + r.2 ≤ offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W := fun r hr => by
    simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl | rfl | rfl
    · have := (gRanges_lt _ r hr).2; rw [hoq]; omega
    · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); rw [hoq]; simp only; omega
    · simp only [xRange]; omega
    · simp only [xRange]; rw [hoq, hop]; omega
  have i₀₁ : InScr B Z t₀.mem s₁.mem := InScr.of_frm f₁ fun r hr => by have := hpr r hr; omega
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word s₁.mem B (8 * i) = word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => nsafe_word f₁ ns₁ hi h1 h2
  have hf₁ : ∀ i < 32, hFixed i = true → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hf => by
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₁ i hi h1 h2, hh₀ i hi hf]
  have kk₁ := hr.keep.trans k₁
  have ip : IPre l s₁.mem B ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) minv mp mq (mask Mk)
      (if Mk then P else 3) (if Mk then Q else 3) dpp dqp dpb.length dqb.length :=
    ⟨hg₁.hdr, by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP,
      by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ, rp.ws, rq.ws, rp.x.n, rp.x.inv, rp.x.one,
      rq.x.n, rq.x.inv, rq.x.one, mk₁.trans hr.pmask, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDp,
      by rw [hf₁ _ (by decide) (by decide), h.dpl]; exact h.hPl, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDq,
      by rw [hf₁ _ (by decide) (by decide), h.dql]; exact h.hQl⟩
  exact ⟨minv, mp, mq, mask Mk, _, _, dpb, dqb, hg₁.scr, hg₁.rdi, ip, le_refl _, by rw [hoq, hop], rfl,
    by omega, hP'.2, hQ'.2, rp.ylt, rq.ylt, rp.clt, rq.clt, h.dp.congrK (hr.iscr.trans i₀₁) kk₁,
    h.dq.congrK (hr.iscr.trans i₀₁) kk₁, by rw [h.dpl]; exact hpl1, by rw [h.dpl]; exact hpl',
    by rw [h.dql]; exact hql1, by rw [h.dql]; exact hql', h.dpl, h.dql⟩

/-- `post`'s hypotheses, after `ifma` (as `branchB_ok` runs it). -/
theorem postPre_of (hl : LayOk l) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hd : IDone l s t₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W) :
    PostPre ⟨B, Z, (k + 7) / 8, offP ((k + 7) / 8), wsWords pl, offQ ((k + 7) / 8) pl, qip, pl⟩ t₁ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hZq := h.z
  have hqil := h.qil
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  dsimp only [PostPre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hd.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hpl' : (pl + 7) / 8 ≤ l.W := by unfold wsWords at hpl; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot (wsWords pl) 8 + tabBytes (wsWords pl) := rfl
  have hW8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hm := hd.im
  exact ⟨minv, mp, mq, _, qib, Mk, hd.good, by omega, by rw [hpl]; omega, hm.wsQ, by rw [hpl]; exact hm.qws,
    by have := hZq; rw [hql] at this; rw [hpl]; exact this, le_refl _, by rw [hoq, hop], by rw [hpl]; omega,
    hm.wsP, by rw [hpl]; exact hm.pws, by rw [hpl]; exact ⟨hm.pn, hm.pinv, hm.pone⟩, hP'.1,
    by rw [hpl]; exact hd.plt, hm.pmk, hd.qi, by rw [hqil]; exact hm.pl, h.qi.congrK hd.iscr hd.keep,
    by rw [hqil]; exact hpl1, by rw [hqil]; omega, by rw [hqil, hpl]; omega,
    fun hm' => by obtain ⟨_, _, hqi⟩ := hMk' hm'; simp only [hm', ↓reduceIte, hQIe]; exact hqi, hqil⟩

/-- `pre`, from the checks: what `pre_ok` leaves. -/
theorem pre_apost (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W) :
    WP isa (seqs (CrtIfma.pre M.mm)) t₀ fun t => APost t₀ t B Z ((k + 7) / 8) (offP ((k + 7) / 8))
      (offQ ((k + 7) / 8) pl) l.W minv mp mq (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3)
      (if Mk then Spec.Rsa.os2ip qb else 3) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + tabBytes l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact pre_ok M (wp := l.W) hr.good (by omega) (le_refl _) (by rw [hoq]; exact Nat.le_refl _) (by omega)
    (by omega) (by omega) hr.wsP hr.wsQ pws qws hr.nv hr.xm pxv hP'.1 hP'.2 qxv hQ'.1 hQ'.2

/-! ## The stages of the IFMA branch -/

/-- After the checks, with the sizes of the IFMA branch. -/
def R3I (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R3 p σ xb pb qb dpb dqb qib t ∧ p.w = 2 * l.W ∧ wsWords p.pl = l.W ∧ wsWords p.ql = l.W

/-- After `pre`. -/
def RAp (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : StageRel := fun p σ xb pb qb _ _ qib t =>
  ∃ (minv mp mq : BitVec 64) (t₀ : State),
  CrtReady σ t₀ p.B p.Z p.w p.pl p.ql minv mp mq p.N (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
    (p.mask xb pb qb qib) ∧ p.w = 2 * l.W ∧ wsWords p.pl = l.W ∧ wsWords p.ql = l.W ∧
  APost t₀ t p.B p.Z p.w (offP p.w) (offQ p.w p.pl) l.W minv mp mq p.N
    (if p.mask xb pb qb qib then Spec.Rsa.os2ip pb else 3) (if p.mask xb pb qb qib then Spec.Rsa.os2ip qb else 3)
    (Spec.Rsa.os2ip xb)

/-- After `ifma`. -/
def RID (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  ∃ (minv mp mq : BitVec 64),
  IDone l σ t p.B p.Z p.w (offP p.w) (offQ p.w p.pl) (offQ p.w p.pl + slot l.W 8 + tabBytes l.W) minv mp mq p.N
    (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) p.dpp p.dqp p.qip p.pl p.ql dpb dqb
    (p.mask xb pb qb qib) ∧ p.w = 2 * l.W ∧ wsWords p.pl = l.W ∧ wsWords p.ql = l.W

theorem preS_ct (hl : LayOk l) (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two (Stage (R3I l))) (seqs (CrtIfma.pre M.mm)) (Two (Stage (RAp l))) :=
  stage_step ((pre_ct M hR2 hXm).mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    offQ p.w p.pl, l.W⟩ : PrePub)) (fun _ _ _ _ _ _ _ _ _ h hv ⟨⟨minv, _, _, hr⟩, hw, hp, hq⟩ =>
      ⟨minv, hr.nv, prePre_of hl h hv hr rfl hw hp hq⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ t h hv ⟨⟨minv, mp, mq, hr⟩, hw, hp, hq⟩ =>
      WP.mono (pre_apost hl M h hv hr rfl hw hp hq) fun _ hA => ⟨minv, mp, mq, t, hr, hw, hp, hq, hA⟩

theorem ifmaS_ct (hl : LayOk l) : RelCT isa (Two (Stage (RAp l))) (seqs (ifma l)) (Two (Stage (RID l))) :=
  stage_step ((ifma_ct hl).mono (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl,
    offQ p.w p.pl + slot l.W 8 + tabBytes l.W, p.dpp, p.dqp, p.pl, p.ql⟩ : IfPub))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, _, _, _, hr, hw, hp, hq, hA⟩ =>
      ⟨minv, hA.2.1, ifPre_of hl h hv hr rfl hw hp hq (ifmaZ_of hl h.zk hw hp) hA⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, _, hr, hw, hp, hq, hA⟩ =>
      WP.mono (branchA2_ok hl h hv hr rfl hw hp hq (ifmaZ_of hl h.zk hw hp) hA) fun _ ⟨hd, _⟩ =>
        ⟨minv, mp, mq, hd, hw, hp, hq⟩

theorem postS_ct (hl : LayOk l) (M : Mont) (hR2 : RedcCT M Public.aR2) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage (RID l))) (seqs (CrtIfma.post M.mm)) (Two (Stage R5)) :=
  stage_step ((post_ct M hR2 hL).mono (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offP p.w,
    wsWords p.pl, offQ p.w p.pl, p.qip, p.pl⟩ : PostPub))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, _, _, hd, hw, hp, hq⟩ =>
      ⟨minv, hd.nv, postPre_of hl h hv hd rfl hw hp hq⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, hd, hw, hp, hq⟩ =>
      WP.mono (branchB_ok hl M h hv hd rfl hw hp hq hpost) fun _ ⟨hp', _⟩ => ⟨minv, mp, mq, hp'⟩

/-- After the sizes' check. -/
def R3Z (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R3 p σ xb pb qb dpb dqb qib t ∧
    t.zf = some (decide (p.w = 2 * l.W ∧ (p.pl + 7) / 8 = l.W ∧ (p.ql + 7) / 8 = l.W))

theorem sizesT (hl : LayOk l) : TOk [.rdi] (.block (sizes l)) := by
  rcases hl with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem sizesS_ct (hl : LayOk l) : RelCT isa (Two (Stage R3)) (.block (sizes l)) (Two (Stage (R3Z l))) := by
  obtain ⟨_, hT⟩ := sizesT hl
  refine stage_step (two_taint [.rdi] (pins_eqs (fun p _ => p.B) fun p t h r hr => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hr'⟩ := h
      rw [List.mem_singleton.mp hr]; exact hr'.good.rdi) hT) ?_
  intro p _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, hr⟩
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((p.k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  exact WP.mono (sizes_ok hl (pl := p.pl) (ql := p.ql) hr.good
    (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hPl) (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hQl)
    (by unfold offQ at hZq; omega) (show (p.k + 7) / 8 < 2 ^ 64 by omega) (by omega) (by omega))
    fun t' ⟨zf, me, k⟩ => ⟨⟨minv, mp, mq, hr.of_regs me k⟩, zf⟩

local notation "CLay" => VG.Impl.Rsa.X86_64.CrtIfma.Lay

/-- The layout of a key with `w` words, if it has one. -/
def layOf (w : Nat) : CLay :=
  if w = 2 * lay2048.W then lay2048 else if w = 2 * lay3072.W then lay3072 else lay4096

theorem layOf_ok (w : Nat) : LayOk (layOf w) := by
  unfold layOf; split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

theorem layOf_two (hl : LayOk l) : layOf (2 * l.W) = l := by
  rcases hl with rfl | rfl | rfl <;> rfl

/-- A relation of each layout, for the layout of the key's sizes. -/
def AtLay (R : CLay → StageRel) : StageRel := fun p => R (layOf p.w) p

/-- A part constant time from each layout's stage to the next, for the layout of the sizes. -/
theorem atLay_ct {R R' : CLay → StageRel} {c : Prog isa}
    (h : ∀ l, LayOk l → RelCT isa (Two (Stage (R l))) c (Two (Stage (R' l))))
    (hw : ∀ l p σ xb pb qb dpb dqb qib t, LayOk l → R' l p σ xb pb qb dpb dqb qib t → p.w = 2 * l.W) :
    RelCT isa (Two (Stage (AtLay R))) c (Two (Stage (AtLay R'))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  obtain ⟨ht, p', ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr⟩, ⟨σ', xb', pb', qb', dpb', dqb', qib', hσ', hv', hr'⟩⟩ :=
    h (layOf p.w) (layOf_ok _) s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  have e : layOf p'.w = layOf p.w := by
    rw [hw _ _ _ _ _ _ _ _ _ _ (layOf_ok _) hr, layOf_two (layOf_ok _)]
  refine ⟨ht, p', ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ?_⟩, ⟨σ', xb', pb', qb', dpb', dqb', qib', hσ', hv', ?_⟩⟩
  · show R' (layOf p'.w) p' σ xb pb qb dpb dqb qib s₁'
    rw [e]; exact hr
  · show R' (layOf p'.w) p' σ' xb' pb' qb' dpb' dqb' qib' s₂'
    rw [e]; exact hr'

/-- The sizes of one of the layouts. -/
abbrev AnyOf (w pl ql : Nat) : Prop := SizesOf lay2048 w pl ql ∨ SizesOf lay3072 w pl ql ∨ SizesOf lay4096 w pl ql

theorem sizesOf_layOf {w pl ql : Nat} (h : AnyOf w pl ql) : SizesOf (layOf w) w pl ql := by
  rcases h with h | h | h
  · rw [show layOf w = lay2048 by rw [h.1, layOf_two (.inl rfl)]]; exact h
  · rw [show layOf w = lay3072 by rw [h.1, layOf_two (.inr (.inl rfl))]]; exact h
  · rw [show layOf w = lay4096 by rw [h.1, layOf_two (.inr (.inr rfl))]]; exact h

/-- After `anySizes`. -/
def R3A : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R3 p σ xb pb qb dpb dqb qib t ∧ t.zf = some (decide (AnyOf p.w p.pl p.ql))

theorem anySizes_ct : RelCT isa (Two (Stage R3)) CrtIfma.anySizes (Two (Stage R3A)) := by
  have cond : ∀ {l : CLay} (p : CrtPub) (s₁ s₂ : State), Stage (R3Z l) p s₁ → Stage (R3Z l) p s₂ →
      isa.eval .e s₁ = isa.eval .e s₂ := fun p s₁ s₂ h₁ h₂ => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, z₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, z₂⟩ := h₂
    simp only [eval, z₁, z₂]
  have drop : ∀ {l : CLay} {b : Bool} (x y : State),
      Two (fun p s => Stage (R3Z l) p s ∧ isa.eval .e s = some b) x y → Two (Stage R3) x y :=
    fun _ _ h => two_mono (fun p s ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, _⟩, _⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr⟩) h
  have hct : RelCT isa (Two (Stage R3)) CrtIfma.anySizes fun _ _ => True := by
    unfold CrtIfma.anySizes
    refine RelCT.seq (sizesS_ct (Or.inl rfl)) (two_ite cond (VG.RelCT.block_nil fun _ _ _ => trivial) ?_)
    refine (RelCT.seq (sizesS_ct (Or.inr (Or.inl rfl))) (two_ite cond (VG.RelCT.block_nil fun _ _ _ => trivial)
      ((sizesS_ct (Or.inr (Or.inr rfl))).mono drop fun _ _ _ => trivial))).mono drop fun _ _ h => h
  exact stage_step hct fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
    WP.mono (anySizes_ok h hr) fun t' ⟨zf, hr', _⟩ => ⟨⟨minv, mp, mq, hr'⟩, zf⟩

/-- `sizes l` after `pre`, with any condition `X` on the public data. -/
theorem sizesAS_ct (hl : LayOk l) (X : CrtPub → Prop) :
    RelCT isa (Two (Stage fun p σ xb pb qb dpb dqb qib t => AtLay RAp p σ xb pb qb dpb dqb qib t ∧ X p))
      (.block (sizes l)) (Two (Stage fun p σ xb pb qb dpb dqb qib t =>
        (AtLay RAp p σ xb pb qb dpb dqb qib t ∧ X p) ∧ t.zf = some (decide (SizesOf l p.w p.pl p.ql)))) := by
  obtain ⟨_, hT⟩ := sizesT hl
  refine stage_step (two_taint [.rdi] (pins_eqs (fun p _ => p.B) fun p t h r hr => ?_) hT) ?_
  · obtain ⟨_, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, hA⟩, _⟩ := h
    rw [List.mem_singleton.mp hr]; exact hA.1.rdi
  · intro p σ xb pb qb dpb dqb qib t h hv ⟨⟨minv, mp, mq, t₀, hr, hw, hp, hq, hA⟩, hX⟩
    exact WP.mono (sizesA_ok hl h hr hA) fun t' ⟨zf, a', _⟩ => ⟨⟨⟨minv, mp, mq, t₀, hr, hw, hp, hq, a'⟩, hX⟩, zf⟩

/-- `RAp` of the layout of the sizes is that of the layout whose sizes they are. -/
theorem rap_of {l : CLay} (hl : LayOk l) {p : CrtPub} {σ : State} {xb pb qb dpb dqb qib : List Byte} {t : State}
    (h : AtLay RAp p σ xb pb qb dpb dqb qib t) (hs : SizesOf l p.w p.pl p.ql) :
    RAp l p σ xb pb qb dpb dqb qib t := by
  have e : layOf p.w = l := by rw [hs.1, layOf_two hl]
  unfold AtLay at h; rw [e] at h; exact h

/-- `RAp` of the layout of the sizes: the key has its sizes. -/
theorem sizes_of_rap {p : CrtPub} {σ : State} {xb pb qb dpb dqb qib : List Byte} {t : State}
    (h : AtLay RAp p σ xb pb qb dpb dqb qib t) : SizesOf (layOf p.w) p.w p.pl p.ql := by
  obtain ⟨_, _, _, _, _, hw, hp, hq, _⟩ := h
  obtain ⟨hW1, -⟩ := W_bounds (layOf_ok p.w)
  unfold wsWords at hp hq
  exact ⟨hw, by omega, by omega⟩

/-- The vector code of `l`, for the states where the sizes are `l`'s. -/
theorem ifmaL_ct (hl : LayOk l) (X : CrtPub → Prop)
    (hX : ∀ p σ xb pb qb dpb dqb qib t, AtLay RAp p σ xb pb qb dpb dqb qib t → X p → SizesOf l p.w p.pl p.ql) :
    RelCT isa (Two (Stage fun p σ xb pb qb dpb dqb qib t => AtLay RAp p σ xb pb qb dpb dqb qib t ∧ X p))
      (seqs (ifma l)) (Two (Stage (AtLay RID))) :=
  (ifmaS_ct hl).mono
    (fun _ _ h => two_mono (fun p s ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, h, hx⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, rap_of hl h (hX _ _ _ _ _ _ _ _ _ h hx)⟩) h)
    fun _ _ h => two_mono (fun p s ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, h⟩ => ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ,
      hv, by
        have e : layOf p.w = l := by obtain ⟨_, _, _, _, hw, _⟩ := h; rw [hw, layOf_two hl]
        show RID (layOf p.w) p σ xb pb qb dpb dqb qib s
        rw [e]; exact h⟩) h

theorem ifmaAny_ct : RelCT isa (Two (Stage (AtLay RAp))) CrtIfma.ifmaAny (Two (Stage (AtLay RID))) := by
  have cond : ∀ {l : CLay} {X : CrtPub → Prop} (p : CrtPub) (s₁ s₂ : State),
      Stage (fun p σ xb pb qb dpb dqb qib t => (AtLay RAp p σ xb pb qb dpb dqb qib t ∧ X p) ∧
        t.zf = some (decide (SizesOf l p.w p.pl p.ql))) p s₁ →
      Stage (fun p σ xb pb qb dpb dqb qib t => (AtLay RAp p σ xb pb qb dpb dqb qib t ∧ X p) ∧
        t.zf = some (decide (SizesOf l p.w p.pl p.ql))) p s₂ →
      isa.eval .e s₁ = isa.eval .e s₂ := fun p s₁ s₂ h₁ h₂ => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, z₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, z₂⟩ := h₂
    simp only [eval, z₁, z₂]
  -- A branch's state: `X` and what the test said.
  have cont : ∀ {l : CLay} {X Y : CrtPub → Prop} {b : Bool},
      (∀ p, X p → (decide (SizesOf l p.w p.pl p.ql) = b) → Y p) → ∀ x y,
      Two (fun p s => Stage (fun p σ xb pb qb dpb dqb qib t => (AtLay RAp p σ xb pb qb dpb dqb qib t ∧ X p) ∧
        t.zf = some (decide (SizesOf l p.w p.pl p.ql))) p s ∧ isa.eval .e s = some b) x y →
      Two (Stage fun p σ xb pb qb dpb dqb qib t => AtLay RAp p σ xb pb qb dpb dqb qib t ∧ Y p) x y :=
    fun hY _ _ h => two_mono (fun p s ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ⟨h, hx⟩, hz⟩, he⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, h, hY p hx (by simp only [eval, hz, Option.some.injEq] at he; exact he)⟩) h
  unfold CrtIfma.ifmaAny
  refine (RelCT.seq (sizesAS_ct (Or.inl rfl) (fun _ => True)) (two_ite cond
    ((ifmaL_ct (Or.inl rfl) (fun p => SizesOf lay2048 p.w p.pl p.ql) fun _ _ _ _ _ _ _ _ _ _ h => h).mono
      (cont fun _ _ e => of_decide_eq_true e) fun _ _ h => h) ?_)).mono
    (fun _ _ h => two_mono (fun p s ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, h⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, h, trivial⟩) h) fun _ _ h => h
  refine (RelCT.seq (sizesAS_ct (Or.inr (Or.inl rfl)) (fun p => ¬SizesOf lay2048 p.w p.pl p.ql)) (two_ite cond
    ((ifmaL_ct (Or.inr (Or.inl rfl)) (fun p => SizesOf lay3072 p.w p.pl p.ql) fun _ _ _ _ _ _ _ _ _ _ h => h).mono
      (cont fun _ _ e => of_decide_eq_true e) fun _ _ h => h)
    ((ifmaL_ct (Or.inr (Or.inr rfl)) (fun p => ¬SizesOf lay2048 p.w p.pl p.ql ∧ ¬SizesOf lay3072 p.w p.pl p.ql)
      fun p _ _ _ _ _ _ _ _ h ⟨n1, n2⟩ => ?_).mono
      (cont fun _ hx e => ⟨hx, of_decide_eq_false e⟩) fun _ _ h => h))).mono
    (cont fun _ _ e => of_decide_eq_false e) fun _ _ h => h
  have hs := sizes_of_rap h
  rcases layOf_ok p.w with e | e | e <;> rw [e] at hs
  · exact absurd hs n1
  · exact absurd hs n2
  · exact hs

/-- The IFMA computation, after `anySizes` found the sizes of a layout. -/
theorem ifmaPart_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm)
    (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage (AtLay R3I))) (seqs (CrtIfma.pre M.mm ++ [CrtIfma.ifmaAny] ++ CrtIfma.post M.mm))
      (Two (Stage R5)) := by
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp)
    (RelCT.seq (atLay_ct (fun l hl => preS_ct hl M hR2 hXm)
      fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, _, _, hw, _⟩ => hw) ?_)
  refine RelCT.seqs_append (by simp) (by simp [CrtIfma.post]) (RelCT.seq ifmaAny_ct ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  exact postS_ct (layOf_ok p.w) M hR2 hL hpost s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂

/-- `anySizes` and the branch on it: the IFMA computation or the CRT one. -/
theorem dispatch_ct (M : Mont) (hQ : QPhaseCT M) (hP : PPhaseCT M) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage R3)) (.seq CrtIfma.anySizes (.ite .e (seqs (CrtIfma.pre M.mm ++ [CrtIfma.ifmaAny] ++
      CrtIfma.post M.mm)) (seqs (qPhase M.mm ++ pPhase M.mm)))) (Two (Stage R5)) := by
  refine RelCT.seq anySizes_ct (two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, z₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, z₂⟩ := h₂
    simp only [eval, z₁, z₂]
  · refine (ifmaPart_ct M hR2 hXm hL hpost).mono (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, hz⟩, he⟩ := h
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    have hs := sizesOf_layOf he
    obtain ⟨hW1, -⟩ := W_bounds (layOf_ok p.w)
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, hs.1, by unfold wsWords; omega, by unfold wsWords; omega⟩
  · refine (RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (qS_ct M hQ) (pS_ct M hP))).mono
      (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, _⟩, _⟩ := h
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr⟩

/-! ## `main` -/

/-- `main` leaks the same in runs that agree on the public data, given that
its parts do. -/
theorem main_ct (M : Mont) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage R0)) (CrtIfma.main M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp) (RelCT.seq (R := Two (Stage R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks])
      (RelCT.seq (R := Two (Stage R2)) ?_ (checksS_ct hC))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (RelCT.seq (R := Two (Stage R1)) ?_ (setupS_ct hS))
    exact stage_step (nSetup_ct M) fun p σ xb _ _ _ _ _ t h hv ht => by
      subst ht; exact WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
  refine RelCT.seqs_append (by simp) (by simp [finish]) (RelCT.seq ?_ hF)
  exact dispatch_ct M hQ hP hR2 hXm hL hpost

end VG.Proof.Bignum.X86_64.Ifma
