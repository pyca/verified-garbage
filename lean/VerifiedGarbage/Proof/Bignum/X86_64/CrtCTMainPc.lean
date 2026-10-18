module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPhasePc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPhasePc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtMainPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtMainPc
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: `main` in constant time

`main` with `pc` leaks the same in runs that agree on the public data
(`CrtPubPc`: `main`'s, `pre`'s pointer and length, and the stack pointer),
from the constant time of its parts (`crtMainPc_ct`). Its states between the
parts are those of a run from a state `CrtPre` describes with `pre`
readable outside the working space (`StagePc`), whatever `pre` holds: the
stages are those of `main` with the values unknown (`ok := False`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `main` with `pre`. -/
structure CrtPubPc where
  m : CrtPub
  P : Addr
  W : Nat
  rsp : Addr

/-- A state satisfying `R` from a start `σ`, with `pre` as at `σ`. -/
def StagePc (R : StageRel) (p : CrtPubPc) (t : State) : Prop :=
  ∃ (σ : State) (xb pb qb dpb dqb qib : List Byte),
    CrtPre σ p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp p.m.qip p.m.pl p.m.ql p.m.nb
      xb pb qb dpb dqb qib ∧
    Spec.Rsa.modulusValid p.m.N p.m.k = true ∧ PreAt p.m.B p.m.Z p.P p.W p.rsp σ ∧
    2 * p.m.w + wsWords p.m.pl + wsWords p.m.ql ≤ p.W ∧ R p.m σ xb pb qb dpb dqb qib t ∧
    PreAt p.m.B p.m.Z p.P p.W p.rsp t

theorem StagePc.stage {R : StageRel} {p : CrtPubPc} {t : State} (h : StagePc R p t) : Stage R p.m t :=
  let ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, _, _, hr, _⟩ := h
  ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩

theorem PreAt.congrK {B : Addr} {Z : Nat} {P : Addr} {W : Nat} {rsp : Addr} {s t : State} {rs : List Reg}
    (h : PreAt B Z P W rsp s) (hi : InScr B Z s.mem t.mem) (k : Keep rs s t) (hsp : Reg.rsp ∉ rs) :
    PreAt B Z P W rsp t :=
  ⟨h.1.congrK hi k hsp, (k.1 _ hsp).trans h.2⟩

/-- A part constant time from a stage, with its correctness, goes to the
next stage. -/
theorem stagePc_post {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (StagePc R)) c fun _ _ => True)
    (hw : ∀ (p : CrtPubPc) σ xb pb qb dpb dqb qib t,
      CrtPre σ p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp p.m.qip p.m.pl p.m.ql p.m.nb
        xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.m.N p.m.k = true → PreAt p.m.B p.m.Z p.P p.W p.rsp σ →
      2 * p.m.w + wsWords p.m.pl + wsWords p.m.ql ≤ p.W → R p.m σ xb pb qb dpb dqb qib t →
      PreAt p.m.B p.m.Z p.P p.W p.rsp t →
      WP isa c t fun t' => R' p.m σ xb pb qb dpb dqb qib t' ∧ PreAt p.m.B p.m.Z p.P p.W p.rsp t') :
    RelCT isa (Two (StagePc R)) c (Two (StagePc R')) :=
  two_post hct fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, ha, hb, hr, ht⟩ =>
    WP.mono (hw p σ xb pb qb dpb dqb qib t h hv ha hb hr ht) fun _ ⟨h₁, h₂⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, ha, hb, h₁, h₂⟩

/-- `stagePc_post` for a part constant time from `main`'s stage. -/
theorem stagePc_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (Stage R)) c fun _ _ => True)
    (hw : ∀ (p : CrtPubPc) σ xb pb qb dpb dqb qib t,
      CrtPre σ p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp p.m.qip p.m.pl p.m.ql p.m.nb
        xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.m.N p.m.k = true → PreAt p.m.B p.m.Z p.P p.W p.rsp σ →
      2 * p.m.w + wsWords p.m.pl + wsWords p.m.ql ≤ p.W → R p.m σ xb pb qb dpb dqb qib t →
      PreAt p.m.B p.m.Z p.P p.W p.rsp t →
      WP isa c t fun t' => R' p.m σ xb pb qb dpb dqb qib t' ∧ PreAt p.m.B p.m.Z p.P p.W p.rsp t') :
    RelCT isa (Two (StagePc R)) c (Two (StagePc R')) :=
  stagePc_post (two_map CrtPubPc.m (fun _ _ h => h.stage) hct) hw

/-- Runs at a stage agree on what a part needs, with `-n⁻¹` (the same in both
runs) among its public data. -/
theorem two_stagePc {R : StageRel} {α : Type} {Φ : α → State → Prop} {ok : Prop} (f : CrtPubPc → BitVec 64 → α)
    (m : ∀ (p : CrtPubPc) σ xb pb qb dpb dqb qib t,
      CrtPre σ p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp p.m.qip p.m.pl p.m.ql p.m.nb
        xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.m.N p.m.k = true → PreAt p.m.B p.m.Z p.P p.W p.rsp σ →
      2 * p.m.w + wsWords p.m.pl + wsWords p.m.ql ≤ p.W → R p.m σ xb pb qb dpb dqb qib t →
      PreAt p.m.B p.m.Z p.P p.W p.rsp t →
      ∃ minv, NVals t p.m.B p.m.w minv p.m.N ok ∧ Φ (f p minv) t)
    {s₁ s₂ : State} (h : Two (StagePc R) s₁ s₂) : Two Φ s₁ s₂ := by
  obtain ⟨p, ⟨σ₁, _, _, _, _, _, _, h₁, hv, a₁, b₁, r₁, t₁⟩, ⟨σ₂, _, _, _, _, _, _, h₂, hv₂, a₂, b₂, r₂, t₂⟩⟩ := h
  obtain ⟨m₁, n₁, φ₁⟩ := m p _ _ _ _ _ _ _ _ h₁ hv a₁ b₁ r₁ t₁
  obtain ⟨m₂, n₂, φ₂⟩ := m p _ _ _ _ _ _ _ _ h₂ hv₂ a₂ b₂ r₂ t₂
  obtain ⟨hodd, -, -⟩ := valid_facts hv h₁.k1
  have := h₁.k1
  obtain rfl := nv_minv n₁ n₂ hodd (show 1 ≤ p.m.w by simp only [CrtPub.w]; omega)
  exact ⟨_, φ₁, φ₂⟩

/-! ## `n`'s setup -/

/-- `loadPre`'s public data for `R² mod n`. -/
def CrtPubPc.lr (p : CrtPubPc) : LPub := ⟨p.m.B, p.m.Z, p.m.w, p.P, p.m.w, p.rsp⟩

theorem stageA_lp {p : CrtPubPc} {t : State} (h : StagePc RA p t) : LpPre Public.aR2 p.lr t ∧ True := by
  obtain ⟨σ, xb, _, _, _, _, _, h, hv, -, hb, ⟨minv, so⟩, ⟨hpre, hsp⟩⟩ := h
  have := h.k1
  have := h.k2
  have hZq := h.z
  have hZ : slot p.m.w 8 ≤ p.m.Z := show slot ((p.m.k + 7) / 8) 8 ≤ p.m.Z by unfold offQ at hZq; omega
  have sR := slot_le (w := p.m.w) (show Public.aR2 < 8 by decide)
  refine ⟨⟨⟨minv, so.good, hZ, show 1 ≤ p.m.w by simp only [CrtPub.w]; omega,
    show p.m.w < 2 ^ 31 by simp only [CrtPub.w]; omega, by decide, fun i hi => ?_, fun i hi b hb => ?_⟩,
    hsp, hpre.arg, hpre.val⟩, trivial⟩
  · have hi' : i < p.m.w := hi
    show InRegions (t.rd ++ t.wr) (off p.P (8 * p.m.w + 8 * i)) 8
    rw [show 8 * p.m.w + 8 * i = 8 * (p.m.w + i) by omega]; exact hpre.rd _ (by omega)
  · have hi' : i < p.m.w := hi
    show _ ∨ slot p.m.w Public.aR2 + 8 * (p.m.w + 2) ≤ ofs p.m.B (off p.P (8 * p.m.w + 8 * i) + _)
    have := hpre.out (p.m.w + i) (by omega) b hb
    rw [show 8 * (p.m.w + i) = 8 * p.m.w + 8 * i by omega] at this
    exact .inr (by omega)

/-- `n`'s setup with `pre` leaks the same in runs that agree on `n` and
`pre`'s pointer and length. -/
theorem nSetupPc_ct (M : Mont) : RelCT isa (Two (StagePc R0)) (seqs (nSetup M.mm true)) fun _ _ => True := by
  rw [nSetup_pc]
  refine RelCT.seqs_append (by simp [loadSteps]) (by simp) (RelCT.seq (R := Two (StagePc RA))
    (stagePc_step (nHead_ct.mono (fun _ _ h => h) fun _ _ _ => trivial) ?_) ?_)
  · rintro p σ xb _ _ _ _ _ t h hv ha _ rfl -
    obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
    have := h.k1
    have := h.k2
    have hZq := h.z
    have hZ : slot p.m.w 8 ≤ p.m.Z := show slot ((p.m.k + 7) / 8) 8 ≤ p.m.Z by unfold offQ at hZq; omega
    exact WP.mono (setup_ok h.scr h.rdi hZ (by omega) (by omega) h.hK h.hN h.hIn
      h.n h.x h.nl h.xl hodd) fun t ⟨minv, so, f, k⟩ =>
        ⟨⟨minv, so⟩, ha.congrK (InScr.of_frm f fun r hr => (setupRanges_le _ r hr).trans hZ) k (by decide)⟩
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two (StagePc RB)) ?_ ?_)
  · have hl := loadPre_ct CrtPubPc.lr (j := Public.aR2) (po := offN) (rest := []) (Q := fun _ _ => True)
      (by taint_decide) (by taint_decide) (fun _ _ _ _ _ _ => trivial) (offN_ct CrtPubPc.lr fun _ _ _ => rfl)
    rw [List.append_nil] at hl
    refine stagePc_post (hl.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, stageA_lp h₁, stageA_lp h₂⟩) fun _ _ _ => trivial) ?_
    rintro p σ xb _ _ _ _ _ t h hv _ hb ⟨minv, so⟩ ht
    obtain ⟨-, hN1, -⟩ := valid_facts hv h.k1
    have := h.k1
    have := h.k2
    have hZq := h.z
    have hZ : slot p.m.w 8 ≤ p.m.Z := show slot ((p.m.k + 7) / 8) 8 ≤ p.m.Z by unfold offQ at hZq; omega
    exact WP.mono (r2Pc_ok so hZ (by simp only [CrtPub.w]; omega) (by simp only [CrtPub.w]; omega) ht.1
      (by omega) (by omega)) fun t' ⟨hg, _, _, f, k⟩ =>
      ⟨⟨minv, hg⟩, ht.congrK (InScr.of_frm f fun r hr => (r2Ranges_le _ r hr).trans hZ) k (by decide)⟩
  simp only [seqs]
  exact two_map (fun p : CrtPubPc => (⟨p.m.B, p.m.Z, p.m.w⟩ : Ws))
    (fun p t ⟨_, _, _, _, _, _, _, h, _, _, _, ⟨minv, hg⟩, _⟩ => by
      have hZq := h.z
      exact ⟨minv, hg, show slot ((p.m.k + 7) / 8) 8 ≤ p.m.Z by unfold offQ at hZq; omega⟩)
    (M.ct (by unfold MmUse; decide))

/-! ## The other parts -/

theorem setupSPc_ct (hS : SetupCT) :
    RelCT isa (Two (StagePc (R1o False))) (seqs primesSetup) (Two (StagePc (R2o False))) :=
  stagePc_step ((setupS_ct hS).mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun _ _ _ _ _ _ _ _ _ h _ ha _ ⟨minv, hr⟩ _ => WP.mono (setupPart_ok h hr) fun _ ⟨mp, mq, h'⟩ =>
      ⟨⟨minv, mp, mq, h'⟩, ha.congrK h'.n.iscr h'.n.keep (by decide)⟩

theorem checksSPc_ct (hC : ChecksCT) :
    RelCT isa (Two (StagePc (R2o False))) (seqs checks) (Two (StagePc (R3o False))) :=
  stagePc_step ((checksS_ct hC).mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun _ _ _ _ _ _ _ _ _ h hv ha _ ⟨minv, _, _, hr⟩ _ => WP.mono (checksPart_ok h hv hr) fun _ ⟨mp', mq', h'⟩ =>
      ⟨⟨minv, mp', mq', h'⟩, ha.congrK h'.iscr h'.keep (by decide)⟩

/-- Some `C` represents `c R mod n`, whatever `R²` was. -/
theorem xm_any {p : CrtPub} {t : State} (hv : Spec.Rsa.modulusValid p.N p.k = true) (hk : 64 ≤ p.k) :
    ∃ C, wv t.mem p.B (slot p.w Public.aXm) p.w % p.N = C * 2 ^ (64 * p.w) % p.N := by
  obtain ⟨hodd, hN1, -⟩ := valid_facts hv hk
  exact VG.Proof.Bignum.exists_mont (VG.Proof.Bignum.coprime_pow2 hodd _) (by omega) _

theorem qSPc_ct (M : Mont) (E : CrtExpL M) (hQ : QPhasePcCT M E) :
    RelCT isa (Two (StagePc (R3o False))) (seqs (qPhase M.mm E.code true)) (Two (StagePc (R4o False))) := by
  refine stagePc_post (hQ.mono (fun _ _ h => two_stagePc (ok := False) (fun p minv =>
    (⟨⟨p.m.B, p.m.Z, p.m.w, minv, p.m.N, offQ p.m.w p.m.pl, wsWords p.m.ql, p.m.dqp, p.m.ql⟩, p.P, p.W, p.rsp,
      offP p.m.w, wsWords p.m.pl⟩ : QPubPc)) (fun p σ xb pb qb dpb dqb qib t h hv _ hb ⟨minv, mp, mq, hr⟩ ht => ?_) h)
      fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ha hb ⟨minv, mp, mq, hr⟩ _ =>
      WP.mono (qPartPc_ok M E h hv hr rfl ha.1 hb False.elim) fun _ h' =>
        ⟨⟨minv, mp, mq, h'⟩, ha.congrK h'.iscr h'.keep (by decide)⟩
  have hk1 := h.k1
  have hpl2 := h.pl2
  have hpl1 := h.pl1
  obtain ⟨C, hC⟩ := xm_any (t := t) hv hk1
  have hP8 : 256 ≤ slot (wsWords p.m.pl) 8 := by unfold slot hdrBytes; omega
  exact ⟨minv, hr.nv, qPre_of h hv hr hC, ht, by dsimp only; omega, hr.wsP, hr.pws.hdr.hw, le_refl _,
    show offP p.m.w + 8 * 32 ≤ offQ p.m.w p.m.pl by unfold offQ offP; omega⟩

theorem pSPc_ct (M : Mont) (E : CrtExpL M) (hP : PPhasePcCT M E) :
    RelCT isa (Two (StagePc (R4o False))) (seqs (pPhase M.mm E.code true)) (Two (StagePc (R5o False))) := by
  refine stagePc_post (hP.mono (fun _ _ h => two_stagePc (ok := False) (fun p minv =>
    (⟨⟨⟨p.m.B, p.m.Z, p.m.w, minv, p.m.N, offP p.m.w, wsWords p.m.pl, p.m.dpp, p.m.pl⟩, offQ p.m.w p.m.pl,
      wsWords p.m.ql, p.m.qip⟩, p.P, p.W, p.rsp⟩ : PPubPc))
      (fun p σ xb pb qb dpb dqb qib t h hv _ hb ⟨minv, mp, mq, hr⟩ ht => ?_) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ha hb ⟨minv, mp, mq, hr⟩ _ =>
      WP.mono (pPartPc_ok M E h hv hr rfl ha.1 (by simp only [CrtPub.w] at hb; omega) False.elim) fun _ h' =>
        ⟨⟨minv, mp, mq, h'⟩, ha.congrK h'.iscr h'.keep (by decide)⟩
  obtain ⟨C, hC⟩ := xm_any (t := t) hv h.k1
  exact ⟨minv, hr.nv, pPre_of h hv hr hC, ht, by dsimp only; omega⟩

/-! ## `main` -/

/-- `main` with `pre` leaks the same in runs that agree on the public data,
given that its parts do. -/
theorem crtMainPc_ct (M : Mont) (E : CrtExpL M) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhasePcCT M E)
    (hP : PPhasePcCT M E) : RelCT isa (Two (StagePc R0)) (Crt.main M.mm E.code true) fun _ _ => True := by
  rw [crtMain_pc]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [qPhase]) (RelCT.seq (R := Two (StagePc (R3o False))) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks])
      (RelCT.seq (R := Two (StagePc (R2o False))) ?_ (checksSPc_ct hC))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (RelCT.seq (R := Two (StagePc (R1o False))) ?_ (setupSPc_ct hS))
    exact stagePc_post (nSetupPc_ct M) fun p σ xb _ _ _ _ _ t h hv ha hb ht _ => by
      subst ht
      exact WP.mono (nPartPc_ok M h hv ha.1 (by simp only [CrtPub.w] at hb; omega)) fun _ ⟨minv, hr⟩ =>
        ⟨⟨minv, hr.weak False.elim⟩, ha.congrK hr.iscr hr.keep (by decide)⟩
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (qSPc_ct M E hQ) ?_)
  exact RelCT.seqs_append (by simp [pPhase]) (by simp [finish]) (RelCT.seq (pSPc_ct M E hP)
    (two_map CrtPubPc.m (fun _ _ h => h.stage) crtFinish_ct))

end VG.Proof.Bignum.X86_64
