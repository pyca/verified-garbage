module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.CTR2
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.CTOut
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.CTOut
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
meta import VerifiedGarbage.Proof.Bignum.CrtResult
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_precompute` on x86-64: `main` is constant time but for `n`

The stages of `vg_rsa_private_crt`'s proof (`CrtCTMain.lean`), with what
`out` needs of `pre` (`ExtS`): its setup and checks (`nSetup_ct`,
`setupS_ct`, `checksS_ct`), then `r2At sWsP` and `r2At sWsQ` (`r2At_ct`) and
`out` (`out_ct`), each from the state its correctness lemma describes
(`main_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (r2At r2Phase out outArr outAt)

/-- The public data of `main`: `vg_rsa_private_crt`'s, and `pre`'s length
in bytes. -/
structure PPPub where
  c : CrtPub
  L8 : Nat

/-- What `out` needs of `pre`, at the start of `main`. -/
def ExtS (L8 : Nat) (p : CrtPub) (σ : State) : Prop :=
  (⟨p.op, L8⟩ : Region) ∈ σ.wr ∧ p.op.toNat + L8 ≤ 2 ^ 64 ∧ (∀ x, ofs p.B x < p.Z → L8 ≤ ofs p.op x) ∧
    L8 = 8 * (2 * p.w + wsWords p.pl + wsWords p.ql)

/-- A stage, with `ExtS`. -/
def RX (L8 : Nat) (R : StageRel) : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R p σ xb pb qb dpb dqb qib t ∧ ExtS L8 p σ

/-- A state at a stage of `main`. -/
def SX (R : StageRel) (q : PPPub) (t : State) : Prop := Stage (RX q.L8 R) q.c t

theorem stageX_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (Stage R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (SX R)) c (Two (SX R')) :=
  two_post (two_map PPPub.c (fun _ _ ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, _⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩) hct)
    fun _ _ ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, hx⟩ =>
      WP.mono (hw _ _ _ _ _ _ _ _ _ h hv hr) fun _ h' => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h', hx⟩

/-- `main`'s setup and checks. -/
theorem front_ctX (M : Mont) :
    RelCT isa (Two (SX R0)) (seqs (nSetup M.mm ++ primesSetup ++ checks)) (Two (SX R3)) := by
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks]) (RelCT.seq (R := Two (SX R2)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup]) (RelCT.seq (R := Two (SX R1)) ?_ ?_)
    · exact stageX_step (nSetup_ct M) fun p σ xb _ _ _ _ _ _ h hv ht => by
        subst ht; exact WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
    · exact stageX_step ((setupS_ct setup_ct).mono (fun _ _ h => h) fun _ _ _ => trivial)
        fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, hr⟩ => WP.mono (setupPart_ok h hr) fun _ h' => ⟨minv, h'⟩
  · exact stageX_step ((checksS_ct checks_ct).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
        WP.mono (checksPart_ok h hv hr) fun _ ⟨mp', mq', h'⟩ => ⟨minv, mp', mq', h'⟩

/-- After `R_p² mod p`. -/
def RM : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, R2Mid σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (p.mask xb pb qb qib)

/-- After `R_q² mod q`. -/
def RD : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, R2Done σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (p.mask xb pb qb qib)

/-- `R_p² mod p`. -/
theorem r2P_ctX : RelCT isa (Two (SX R3)) (seqs (r2At sWsP)) (Two (SX RM)) := by
  refine stageX_step (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w, offP p.w, wsWords p.pl⟩ : RXPub))
    (fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ => ?_) (r2At_ct (by taint_decide)))
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
      WP.mono (r2P_ok h hv hr rfl) fun _ h' => ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨-, hP', -⟩ := mask_facts (rfl : p.mask xb pb qb qib = _) hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hZq := h.z
  exact ⟨minv, mp, _, hr.good, Nat.le_refl _, by dsimp only [CrtPub.w] at *; unfold offQ at hZq; unfold offP; omega,
    hr.wsP, hr.pws, hr.pxv, hP'.1, by dsimp only; unfold wsWords; omega, by dsimp only; unfold wsWords; omega,
    by decide⟩

/-- `R_q² mod q`. -/
theorem r2Q_ctX : RelCT isa (Two (SX RM)) (seqs (r2At sWsQ)) (Two (SX RD)) := by
  refine stageX_step (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w, offQ p.w p.pl, wsWords p.ql⟩ : RXPub))
    (fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ => ?_) (r2At_ct (by taint_decide)))
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
      WP.mono (r2Q_ok h hv hr rfl) fun _ h' => ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨-, -, hQ'⟩ := mask_facts (rfl : p.mask xb pb qb qib = _) hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hql2 := h.ql2
  have hZq := h.z
  exact ⟨minv, mq, _, hr.good, by dsimp only; unfold offQ; omega, hZq, hr.wsQ, hr.qws, hr.qxv,
    hQ'.1, by dsimp only; unfold wsWords; omega, by dsimp only; unfold wsWords; omega, by decide⟩

/-- `out`. -/
theorem out_ctX : RelCT isa (Two (SX RD)) (seqs out) fun _ _ => True := by
  refine two_map (fun q : PPPub => (⟨q.c.B, q.c.Z, q.c.w, offP q.c.w, wsWords q.c.pl, offQ q.c.w q.c.pl,
    wsWords q.c.ql, q.c.op, q.L8⟩ : OPub))
    (fun q t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, ⟨minv, mp, mq, hr⟩, hx⟩ => ?_) out_ct
  obtain ⟨hwr, hL, hS, hL8⟩ := hx
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  have hP8 : 256 ≤ slot (wsWords q.c.pl) 8 := by unfold slot hdrBytes; omega
  have hout : word t.mem q.c.B (8 * sOut) = q.c.op := (hr.hfix sOut (by decide) (by decide)).trans h.hO
  have hwr' : (⟨q.c.op, q.L8⟩ : Region) ∈ t.wr := by rw [hr.keep.2.2]; exact hwr
  refine ⟨minv, mp, mq, hr.good, hout, hr.wsP, hr.wsQ, hr.pws, hr.qws, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hL, hwr', hS⟩
  all_goals try dsimp only [CrtPub.w] at *
  all_goals try unfold offQ at *
  all_goals try unfold offP at *
  all_goals try unfold wsWords at *
  all_goals omega

/-- `main` leaks the same in runs that agree on the public data. -/
theorem main_ct (M : Mont) : RelCT isa (Two (SX R0)) (PrivPre.main M.mm) fun _ _ => True := by
  unfold PrivPre.main
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [out]) (RelCT.seq (R := Two (SX RD)) ?_ out_ctX)
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [r2Phase, r2At]) (RelCT.seq (front_ctX M) ?_)
  exact RelCT.seqs_append (by simp [r2At]) (by simp [r2At]) (RelCT.seq r2P_ctX r2Q_ctX)

end VG.Proof.Bignum.X86_64.PrivPre
