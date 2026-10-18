module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPrePc
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTPrePc
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.MainPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.MainPc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMainPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMainPc
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64, with the precomputed values: `main` in constant time

`main` with `pc` is `Crt.main`'s with `pre` (`crtMainPc_ct`'s parts) and the
IFMA branch, whose `pre` reads `pre` (`preSPc_ct`): after it nothing reads
`pre`, so the vector code and `post` are as without it, with the values
unknown (`ok := False`): `mainPc_ct`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.CrtIfma (Lay lay2048 lay3072 lay4096 sizes ifma)
open VG.Proof.Bignum.X86_64 (PreSrc APost PrePub PrePubPc PrePrePc prePc_ct PrimeRdy StageRel Stage R0 R3o R5o CrtPub
  CrtPubPc StagePc PreAt stagePc_step stagePc_post two_stagePc nSetupPc_ct setupSPc_ct checksSPc_ct qSPc_ct pSPc_ct
  nPartPc_ok RedcCT LoadCT SetupCT ChecksCT QPhasePcCT PPhasePcCT RelCT.seqs_append crtFinish_ct prePc_ok)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

theorem _root_.VG.Proof.Bignum.X86_64.PrimeRdy.weak {t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {N X C : Nat} {ok ok' : Prop}
    (h : PrimeRdy t B o wx mx N X C ok) (f : ok' → ok) : PrimeRdy t B o wx mx N X C ok' :=
  ⟨h.ws, h.x, h.ylt, fun h' => h.yv (f h'), h.clt, fun h' => h.cv (f h')⟩

/-- `pre` with `pc`, from the checks, its values unknown. -/
theorem prePcA_ok (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    {Mk : Bool} {Pr : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk False)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hp₀ : PreSrc t₀ B Z Pr W) (hW : 2 * ((k + 7) / 8) + l.W + l.W ≤ W) :
    WP isa (seqs (CrtIfma.pre M.mm true)) t₀ fun s₁ =>
      APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
        (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
        (Spec.Rsa.os2ip xb) False False False := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + wsTab l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact WP.mono (prePc_ok M (wp := l.W) hr.good (by omega_using [hw32, hW2]) (le_refl _) (by rw [hoq])
      (by omega_using [hZq]) (by omega_using [hW1]) (by omega_using [hw32]) hr.wsP hr.wsQ pws qws hr.nv hr.xm pxv
      hP'.1 hP'.2 qxv hQ'.1 hQ'.2 hp₀ hW)
    fun _ ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c.weak False.elim, d.weak False.elim, e, f, g⟩

/-- `pre` with `pc` leaks the same in runs that agree on the public data,
after which `pre` is no longer read. -/
theorem preSPc_ct (hl : LayOk l) (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two (StagePc (R3I False l))) (seqs (CrtIfma.pre M.mm true)) (Two (Stage (RAp False l))) := by
  refine (two_post (Φ := StagePc (R3I False l)) (Ψ := fun (p : CrtPubPc) => Stage (RAp False l) p.m)
    ((prePc_ct M hR2 hXm).mono
    (fun _ _ h => two_stagePc (ok := False) (fun p minv => (⟨⟨p.m.B, p.m.Z, p.m.w, minv, p.m.N, offP p.m.w,
      offQ p.m.w p.m.pl, l.W⟩, p.P, p.W, p.rsp⟩ : PrePubPc))
      (fun _ _ _ _ _ _ _ _ _ h hv _ hb ⟨⟨minv, _, _, hr⟩, hw, hp, hq⟩ ht =>
        ⟨minv, hr.nv, prePre_of hl h hv hr rfl hw hp hq, ht, by dsimp only; omega⟩) h)
    fun _ _ _ => trivial) fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, _, hb, ⟨⟨minv, mp, mq, hr⟩, hw, hp, hq⟩, ht⟩ =>
      WP.mono (prePcA_ok hl M h hv hr rfl hw hp hq ht.1 (by simp only [CrtPub.w] at hb; omega)) fun _ hA =>
        ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, t, hr, hw, hp, hq, hA⟩).mono (fun _ _ h => h)
    fun _ _ ⟨p, h₁, h₂⟩ => ⟨p.m, h₁, h₂⟩

local notation "CLay" => VG.Impl.Rsa.X86_64.CrtIfma.Lay

/-- `atLay_ct` from `pre`'s stage to `main`'s. -/
theorem atLayPc_ct {R R' : CLay → StageRel} {c : Prog isa}
    (h : ∀ l, LayOk l → RelCT isa (Two (StagePc (R l))) c (Two (Stage (R' l))))
    (hw : ∀ l p σ xb pb qb dpb dqb qib t, LayOk l → R' l p σ xb pb qb dpb dqb qib t → p.w = 2 * l.W) :
    RelCT isa (Two (StagePc (AtLay R))) c (Two (Stage (AtLay R'))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  obtain ⟨ht, p', ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr⟩, ⟨σ', xb', pb', qb', dpb', dqb', qib', hσ', hv', hr'⟩⟩ :=
    h (layOf p.m.w) (layOf_ok _) s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  have e : layOf p'.w = layOf p.m.w := by
    rw [hw _ _ _ _ _ _ _ _ _ _ (layOf_ok _) hr, layOf_two (layOf_ok _)]
  refine ⟨ht, p', ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ?_⟩, ⟨σ', xb', pb', qb', dpb', dqb', qib', hσ', hv', ?_⟩⟩
  · show R' (layOf p'.w) p' σ xb pb qb dpb dqb qib s₁'
    rw [e]; exact hr
  · show R' (layOf p'.w) p' σ' xb' pb' qb' dpb' dqb' qib' s₂'
    rw [e]; exact hr'

/-- The IFMA computation with `pc`, after `anySizes` found the sizes of a layout. -/
theorem ifmaPartPc_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm)
    (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StagePc (AtLay (R3I False))))
      (seqs (CrtIfma.pre M.mm true ++ ([CrtIfma.ifmaAny] : List (Prog isa)) ++ CrtIfma.post M.mm))
      (Two (Stage (R5o False))) := by
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp)
    (RelCT.seq (atLayPc_ct (fun l hl => preSPc_ct hl M hR2 hXm)
      fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, _, _, hw, _⟩ => hw) ?_)
  refine RelCT.seqs_append (by simp) (by simp [CrtIfma.post]) (RelCT.seq ifmaAny_ct ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  exact postS_ct (layOf_ok p.w) M hR2 hL hpost s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂

/-- `anySizes` with `pre`'s stage. -/
theorem anySizesPc_ct : RelCT isa (Two (StagePc (R3o False))) CrtIfma.anySizes (Two (StagePc (R3A False))) :=
  stagePc_step (anySizes_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun _ _ _ _ _ _ _ _ _ h _ ha _ ⟨minv, mp, mq, hr⟩ _ => WP.mono (anySizes_ok h hr) fun _ ⟨zf, hr', _⟩ =>
      ⟨⟨⟨minv, mp, mq, hr'⟩, zf⟩, ha.congrK hr'.iscr hr'.keep (by decide)⟩

/-- `anySizes` and the branch on it with `pc`: the IFMA computation or the CRT
one. -/
theorem dispatchPc_ct (M : Mont) (hQ : QPhasePcCT M (CrtExpL.w4 M)) (hP : PPhasePcCT M (CrtExpL.w4 M))
    (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StagePc (R3o False))) (.seq CrtIfma.anySizes (.ite .e
      (seqs (CrtIfma.pre M.mm true ++ ([CrtIfma.ifmaAny] : List (Prog isa)) ++ CrtIfma.post M.mm))
      (seqs (qPhase M.mm (CrtExpL.w4 M).code true ++ pPhase M.mm (CrtExpL.w4 M).code true))))
      (Two (Stage (R5o False))) := by
  refine RelCT.seq anySizesPc_ct (two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨_, z₁⟩, _⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨_, z₂⟩, _⟩ := h₂
    simp only [eval, z₁, z₂]
  · refine (ifmaPartPc_ct M hR2 hXm hL hpost).mono (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ha, hb, ⟨hr, hz⟩, ht⟩, he⟩ := h
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    have hs := sizesOf_layOf he
    obtain ⟨hW1, -⟩ := W_bounds (layOf_ok p.m.w)
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ha, hb, ⟨hr, hs.1, by unfold wsWords; omega,
      by unfold wsWords; omega⟩, ht⟩
  · refine (RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (qSPc_ct M (CrtExpL.w4 M) hQ)
      (pSPc_ct M (CrtExpL.w4 M) hP))).mono
      (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => two_bind (fun p _ _ h₁ h₂ => ⟨p.m, h₁.stage, h₂.stage⟩) h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ha, hb, ⟨hr, _⟩, ht⟩, _⟩ := h
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, ha, hb, hr, ht⟩

/-- `main` with `pc` leaks the same in runs that agree on the public data,
given that its parts do. -/
theorem mainPc_ct (M : Mont) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhasePcCT M (CrtExpL.w4 M))
    (hP : PPhasePcCT M (CrtExpL.w4 M)) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (StagePc R0)) (CrtIfma.main M.mm true) fun _ _ => True := by
  rw [mainPc_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp) (RelCT.seq (R := Two (StagePc (R3o False))) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks])
      (RelCT.seq (R := Two (StagePc (R2o False))) ?_ (checksSPc_ct hC))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (RelCT.seq (R := Two (StagePc (R1o False))) ?_ (setupSPc_ct hS))
    exact stagePc_post (nSetupPc_ct M) fun p σ xb _ _ _ _ _ t h hv ha hb ht _ => by
      subst ht
      exact WP.mono (nPartPc_ok M h hv ha.1 (by simp only [CrtPub.w] at hb; omega)) fun _ ⟨minv, hr⟩ =>
        ⟨⟨minv, hr.weak False.elim⟩, ha.congrK hr.iscr hr.keep (by decide)⟩
  refine RelCT.seqs_append (by simp) (by simp [finish]) (RelCT.seq ?_ (crtFinish_ct (ok := False)))
  exact dispatchPc_ct M hQ hP hR2 hXm hL hpost

end VG.Proof.Bignum.X86_64.Ifma
