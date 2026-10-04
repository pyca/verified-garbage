import VerifiedGarbage.Proof.Bignum.X86_64.IfmaMain
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTPre
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTIfma
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain

/-!
# RSA with AVX512_IFMA on x86-64: `main` in constant time

`CrtIfma.main` is `Crt.main` with a branch on the sizes, which are public:
the IFMA branch's parts (`pre`, `ifma`, `post`) are constant time for their
correctness lemmas' hypotheses (`pre_ct`, `ifma_ct`, `post_ct`), which the
states of a run between them satisfy (`prePre_of`, `ifPre_of`, `postPre_of`,
from `branchA_ok`'s and `branchB_ok`'s steps); the other branch is
`vg_rsa_private_crt`'s (`qS_ct`, `pS_ct`). So `main` is (`ifmaMain_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D sIfma)

/-! ## The parts' hypotheses from a run's states -/

/-- `pre_ok`'s hypotheses, after the checks. -/
theorem prePre_of {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16) :
    PrePre ⟨B, Z, (k + 7) / 8, minv, Spec.Rsa.os2ip nb, offP ((k + 7) / 8), offQ ((k + 7) / 8) pl, 16⟩ t₀ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  dsimp only [PrePre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact ⟨mp, mq, _, _, C, hr.good, by omega, le_refl _, by rw [hoq]; rfl, by omega, by decide, by omega,
    hr.wsP, hr.wsQ, pws, qws, hr.nv, hr.xm, pxv, hP'.1, hP'.2, qxv, hQ'.1, hQ'.2⟩

/-- `ifma`'s hypotheses, after `pre` (as `branchA2_ok` runs it). -/
theorem ifPre_of {s t₀ s₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16)
    (hZa : offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16 + 2 * D + 8 ≤ Z)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) 16 minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    IfPre ⟨B, Z, (k + 7) / 8, offP ((k + 7) / 8), offQ ((k + 7) / 8) pl,
      offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16, dpp, dqp, pl, ql⟩ s₁ := by
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
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hD : D = 3712 := rfl
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hql' : ql ≤ 128 := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have hh₀ : ∀ i < 32, hFixed i = true → word t₀.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  obtain ⟨hg₁, hN₁, rp, rq, f₁, k₁, mk₁⟩ := hA
  have ns₁ := preRanges_nsafe (w := (k + 7) / 8) (wp := 16) (wq := 16) (le_refl (offP ((k + 7) / 8)))
    (show slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl by rw [hoq]; omega)
  have hpr : ∀ r ∈ preRanges ((k + 7) / 8) (offP ((k + 7) / 8)) 16 (offQ ((k + 7) / 8) pl) 16,
      r.1 + r.2 ≤ offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16 := fun r hr => by
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
  have ip : IPre s₁.mem B ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) minv mp mq (mask Mk)
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
theorem postPre_of {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hd : IDone s t₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16) :
    PostPre ⟨B, Z, (k + 7) / 8, offP ((k + 7) / 8), wsWords pl, offQ ((k + 7) / 8) pl, qip, pl⟩ t₁ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hZq := h.z
  have hqil := h.qil
  dsimp only [PostPre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hd.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot (wsWords pl) 8 + tabBytes (wsWords pl) := rfl
  have hW8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hm := hd.im
  exact ⟨minv, mp, mq, _, qib, Mk, hd.good, by omega, by rw [hpl]; omega, hm.wsQ, by rw [hpl]; exact hm.qws,
    by have := hZq; rw [hql] at this; rw [hpl]; exact this, le_refl _, by rw [hoq, hop], by rw [hpl]; decide,
    hm.wsP, by rw [hpl]; exact hm.pws, by rw [hpl]; exact ⟨hm.pn, hm.pinv, hm.pone⟩, hP'.1,
    by rw [hpl]; exact hd.plt, hm.pmk, hd.qi, by rw [hqil]; exact hm.pl, h.qi.congrK hd.iscr hd.keep,
    by rw [hqil]; exact hpl1, by rw [hqil]; omega, by rw [hqil, hpl]; omega,
    fun hm' => by obtain ⟨_, _, hqi⟩ := hMk' hm'; simp only [hm', ↓reduceIte, hQIe]; exact hqi, hqil⟩

/-- `pre`, from the checks: what `pre_ok` leaves. -/
theorem pre_apost (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16) :
    WP isa (seqs (CrtIfma.pre M.mm)) t₀ fun t => APost t₀ t B Z ((k + 7) / 8) (offP ((k + 7) / 8))
      (offQ ((k + 7) / 8) pl) 16 minv mp mq (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3)
      (if Mk then Spec.Rsa.os2ip qb else 3) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact pre_ok M (wp := 16) hr.good (by omega) (le_refl _) (by rw [hoq]; exact Nat.le_refl _) (by omega)
    (by decide) (by omega) hr.wsP hr.wsQ pws qws hr.nv hr.xm pxv hP'.1 hP'.2 qxv hQ'.1 hQ'.2

/-! ## The stages of the IFMA branch -/

/-- After the checks, with the sizes of the IFMA branch. -/
def R3I : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R3 p σ xb pb qb dpb dqb qib t ∧ p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16

/-- After `pre`. -/
def RAp : StageRel := fun p σ xb pb qb _ _ qib t => ∃ (minv mp mq : BitVec 64) (t₀ : State),
  CrtReady σ t₀ p.B p.Z p.w p.pl p.ql minv mp mq p.N (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
    (p.mask xb pb qb qib) ∧ p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16 ∧
  APost t₀ t p.B p.Z p.w (offP p.w) (offQ p.w p.pl) 16 minv mp mq p.N
    (if p.mask xb pb qb qib then Spec.Rsa.os2ip pb else 3) (if p.mask xb pb qb qib then Spec.Rsa.os2ip qb else 3)
    (Spec.Rsa.os2ip xb)

/-- After `ifma`. -/
def RID : StageRel := fun p σ xb pb qb dpb dqb qib t => ∃ (minv mp mq : BitVec 64),
  IDone σ t p.B p.Z p.w (offP p.w) (offQ p.w p.pl) (offQ p.w p.pl + slot 16 8 + tabBytes 16) minv mp mq p.N
    (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) p.dpp p.dqp p.qip p.pl p.ql dpb dqb
    (p.mask xb pb qb qib) ∧ p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16

theorem preS_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two (Stage R3I)) (seqs (CrtIfma.pre M.mm)) (Two (Stage RAp)) :=
  stage_step ((pre_ct M hR2 hXm).mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    offQ p.w p.pl, 16⟩ : PrePub)) (fun _ _ _ _ _ _ _ _ _ h hv ⟨⟨minv, _, _, hr⟩, hw, hp, hq⟩ =>
      ⟨minv, hr.nv, prePre_of h hv hr rfl hw hp hq⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ t h hv ⟨⟨minv, mp, mq, hr⟩, hw, hp, hq⟩ =>
      WP.mono (pre_apost M h hv hr rfl hw hp hq) fun _ hA => ⟨minv, mp, mq, t, hr, hw, hp, hq, hA⟩

theorem ifmaS_ct : RelCT isa (Two (Stage RAp)) (seqs CrtIfma.ifma) (Two (Stage RID)) :=
  stage_step (ifma_ct.mono (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl,
    offQ p.w p.pl + slot 16 8 + tabBytes 16, p.dpp, p.dqp, p.pl, p.ql⟩ : IfPub))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, _, _, _, hr, hw, hp, hq, hA⟩ =>
      ⟨minv, hA.2.1, ifPre_of h hv hr rfl hw hp hq (ifmaZ_of h.zk hw hp) hA⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, _, hr, hw, hp, hq, hA⟩ =>
      WP.mono (branchA2_ok h hv hr rfl hw hp hq (ifmaZ_of h.zk hw hp) hA) fun _ ⟨hd, _⟩ =>
        ⟨minv, mp, mq, hd, hw, hp, hq⟩

theorem postS_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage RID)) (seqs (CrtIfma.post M.mm)) (Two (Stage R5)) :=
  stage_step ((post_ct M hR2 hL).mono (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offP p.w,
    wsWords p.pl, offQ p.w p.pl, p.qip, p.pl⟩ : PostPub))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, _, _, hd, hw, hp, hq⟩ =>
      ⟨minv, hd.nv, postPre_of h hv hd rfl hw hp hq⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, hd, hw, hp, hq⟩ =>
      WP.mono (branchB_ok M h hv hd rfl hw hp hq hpost) fun _ ⟨hp', _⟩ => ⟨minv, mp, mq, hp'⟩

/-- After the sizes' check. -/
def R3S : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R3 p σ xb pb qb dpb dqb qib t ∧ t.zf = some (decide (p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16))

theorem sizesS_ct : RelCT isa (Two (Stage R3)) (.block CrtIfma.sizes) (Two (Stage R3S)) :=
  stage_step (two_taint [.rdi] (pins_eqs (fun p _ => p.B) fun p t h r hr => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hr'⟩ := h
      rw [List.mem_singleton.mp hr]; exact hr'.good.rdi) (by taint_decide))
    fun p _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, hr⟩ => by
      have hn := hr.good.scr.nowrap
      have h8 := hdr_lt_slot ((p.k + 7) / 8) 8 (show 31 < 32 by decide)
      have hZq := h.z
      have hk2 := h.k2
      have hpl2 := h.pl2
      have hql2 := h.ql2
      exact WP.mono (sizes_ok (pl := p.pl) (ql := p.ql) hr.good
        (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hPl) (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hQl)
        (by unfold offQ at hZq; omega) (show (p.k + 7) / 8 < 2 ^ 64 by omega) (by omega) (by omega))
        fun t' ⟨zf, me, k⟩ => ⟨⟨minv, mp, mq, hr.of_regs me k⟩, zf⟩

/-- The IFMA branch. -/
theorem ifmaB_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm)
    (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage R3I)) (seqs (CrtIfma.pre M.mm ++ CrtIfma.ifma ++ CrtIfma.post M.mm))
      (Two (Stage R5)) := by
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp [CrtIfma.ifma])
    (RelCT.seq (preS_ct M hR2 hXm) ?_)
  exact RelCT.seqs_append (by simp [CrtIfma.ifma]) (by simp [CrtIfma.post])
    (RelCT.seq ifmaS_ct (postS_ct M hR2 hL hpost))

/-! ## `main` -/

/-- `main` leaks the same in runs that agree on the public data, given that
its parts do. -/
theorem ifmaMain_ct (M : Mont) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage R0)) (CrtIfma.main M.mm) fun _ _ => True := by
  rw [ifmaMain_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp) (RelCT.seq (R := Two (Stage R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks])
      (RelCT.seq (R := Two (Stage R2)) ?_ (checksS_ct hC))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (RelCT.seq (R := Two (Stage R1)) ?_ (setupS_ct hS))
    exact stage_step (nSetup_ct M) fun p σ xb _ _ _ _ _ t h hv ht => by
      subst ht; exact WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
  refine RelCT.seqs_append (by simp) (by simp [finish]) (RelCT.seq ?_ hF)
  refine RelCT.seq sizesS_ct (two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, z₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, z₂⟩ := h₂
    simp only [eval, z₁, z₂]
  · refine (ifmaB_ct M hR2 hXm hL hpost).mono (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, hz⟩, he⟩ := h
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, he⟩
  · refine (RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (qS_ct M hQ) (pS_ct M hP))).mono
      (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, _⟩, _⟩ := h
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr⟩

end VG.Proof.Bignum.X86_64
