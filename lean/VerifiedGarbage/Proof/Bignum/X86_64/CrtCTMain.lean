import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-!
# RSA with the CRT on x86-64: `main` in constant time

`main` leaks the same in runs that agree on the public data (`CrtPub`: the
working space, the pointers, the lengths and `n`), from the constant time of
its parts (`crtMain_ct`). Its states between the parts are those of a run
from a state `CrtPre` describes (`Stage`), where the correctness lemmas of
the parts (`nPart_ok`, `setupPart_ok`, …) give what each part's claim needs.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `main`: the working space, the pointers, the
lengths and `n`'s bytes. -/
structure CrtPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  ip : Addr
  pp : Addr
  qp : Addr
  dpp : Addr
  dqp : Addr
  qip : Addr
  pl : Nat
  ql : Nat
  nb : List Byte

abbrev CrtPub.w (p : CrtPub) : Nat := (p.k + 7) / 8
abbrev CrtPub.N (p : CrtPub) : Nat := Spec.Rsa.os2ip p.nb

/-- What holds of a state of a run from a state `σ` that `CrtPre` describes
with the public data `p`, the input `xb` and the private key. -/
abbrev StageRel := CrtPub → State → List Byte → List Byte → List Byte → List Byte → List Byte → List Byte →
  State → Prop

/-- A state satisfying `R` from such a start. -/
def Stage (R : StageRel) (p : CrtPub) (t : State) : Prop :=
  ∃ (σ : State) (xb pb qb dpb dqb qib : List Byte),
    CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ R p σ xb pb qb dpb dqb qib t

/-- A part constant time from a stage, with its correctness, goes to the
next stage. -/
theorem stage_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (Stage R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (Stage R)) c (Two (Stage R')) :=
  two_post hct fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩ =>
    WP.mono (hw p σ xb pb qb dpb dqb qib t h hv hr) fun _ h' => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h'⟩

/-! ## The stages -/

def R0 : StageRel := fun _ σ _ _ _ _ _ _ t => t = σ

def R1 : StageRel := fun p σ xb _ _ _ _ _ t => ∃ minv, NReady σ t p.B p.Z p.w minv p.N (Spec.Rsa.os2ip xb)

def R2 : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, PReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)

/-- The mask of a run: whether the input and the key are valid. -/
abbrev CrtPub.mask (p : CrtPub) (xb pb qb qib : List Byte) : Bool :=
  keyMask (decide (Spec.Rsa.os2ip xb < p.N)) p.N (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)

def R3 : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, CrtReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (p.mask xb pb qb qib)

def R4 : StageRel := fun p σ xb pb qb _ dqb qib t => ∃ minv mp mq, QReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb (p.mask xb pb qb qib)

def R5 : StageRel := fun p σ xb pb qb dpb dqb qib t => ∃ minv mp mq, PDone σ t p.B p.Z p.w p.pl p.ql minv mp mq
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb (p.mask xb pb qb qib)

/-- `-n⁻¹` is the same in runs that agree on `n`. -/
theorem nv_minv {t t' : State} {B : Addr} {w : Nat} {mi mi' : BitVec 64} {N : Nat} (h : NVals t B w mi N)
    (h' : NVals t' B w mi' N) (hodd : N % 2 = 1) (hw : 1 ≤ w) : mi = mi' := by
  have e : ∀ {t : State} {mi : BitVec 64}, NVals t B w mi N →
      (word t.mem B (slot w Public.aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ hw, h.n]
  have i := h.inv
  have i' := h'.inv
  rw [e h] at i
  rw [e h'] at i'
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i i'

/-! ## `n`'s setup -/

/-- The setup's hypotheses, from `main`'s. -/
theorem stage0_sh {p : CrtPub} {s : State} (h : Stage R0 p s) : SH ⟨p.B, p.Z, p.k, p.np, p.ip, p.nb⟩ s := by
  obtain ⟨σ, xb, _, _, _, _, _, h, hv, rfl⟩ := h
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  have hZq := h.z
  exact ⟨h.scr, h.rdi, show slot ((p.k + 7) / 8) 8 ≤ p.Z by unfold offQ at hZq; omega, show 9 ≤ p.k by omega,
    show p.k < 2 ^ 31 by omega, h.hK, h.hN, h.hIn, h.n, h.nl, hodd, xb, h.x, h.xl⟩

/-- After the setup of `n` and the input. -/
def RA : StageRel := fun p _ xb _ _ _ _ _ t => ∃ minv, SetupOut t p.B p.Z p.w minv p.N (Spec.Rsa.os2ip xb)

/-- After `R² mod n`. -/
def RB : StageRel := fun p _ _ _ _ _ _ _ t => ∃ minv, Good t p.B p.Z p.w minv

/-- `n`'s setup leaks the same in runs that agree on `n`. -/
theorem nSetup_ct (M : Mont) : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True := by
  rw [nSetup_eq]
  refine RelCT.seqs_append (by simp [loadSteps]) (by simp [r2Steps]) (RelCT.seq (R := Two (Stage RA)) ?_ ?_)
  · refine stage_step (((RelCT.seqs_append (by simp [loadSteps]) (by simp [restSteps])
      (RelCT.seq setupLoad_ct (two_map (fun p : SPub => (⟨p.B, p.Z, p.w⟩ : RPub)) (fun _ _ h => h.sr)
        setupRest_ct))).mono (fun _ _ h => two_bind (fun (p : CrtPub) _ _ h₁ h₂ =>
          ⟨(⟨p.B, p.Z, p.k, p.np, p.ip, p.nb⟩ : SPub), stage0_sh h₁, stage0_sh h₂⟩) h)
        fun _ _ h => h)) ?_
    rintro p σ xb _ _ _ _ _ t h hv rfl
    obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
    have := h.k1
    have := h.k2
    have hZq := h.z
    exact WP.mono (setup_ok h.scr h.rdi (by unfold offQ at hZq; omega) (by omega) (by omega) h.hK h.hN h.hIn
      h.n h.x h.nl h.xl hodd) fun t ⟨minv, so, _⟩ => ⟨minv, so⟩
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (R := Two (Stage RB)) ?_ ?_)
  · refine stage_step ((r2_ct M).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h) ?_
    · obtain ⟨σ₁, xb₁, _, _, _, _, _, h₁, hv, mi₁, so₁⟩ := h₁
      obtain ⟨σ₂, xb₂, _, _, _, _, _, _, _, mi₂, so₂⟩ := h₂
      obtain ⟨hodd, -, hlo⟩ := valid_facts hv h₁.k1
      have := h₁.k1
      have := h₁.k2
      have hZq := h₁.z
      have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega
      obtain rfl := so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold CrtPub.w; omega)
      exact ⟨⟨⟨p.B, p.Z, p.w, mi₁⟩, p.N⟩,
        ⟨⟨so₁.good, hZ⟩, show 2 ≤ p.w by unfold CrtPub.w; omega, show p.w < 2 ^ 30 by unfold CrtPub.w; omega, so₁.n, so₁.inv, so₁.r12, so₁.r10,
          hodd, hlo⟩,
        ⟨⟨so₂.good, hZ⟩, show 2 ≤ p.w by unfold CrtPub.w; omega, show p.w < 2 ^ 30 by unfold CrtPub.w; omega, so₂.n, so₂.inv, so₂.r12, so₂.r10,
          hodd, hlo⟩⟩
    · rintro p _ xb _ _ _ _ _ t h hv ⟨minv, so⟩
      obtain ⟨hodd, -, hlo⟩ := valid_facts hv h.k1
      have := h.k1
      have := h.k2
      have hZq := h.z
      exact WP.mono (r2_ok M so.good (by unfold CrtPub.w; unfold offQ at hZq; omega) (by unfold CrtPub.w; omega)
        (by unfold CrtPub.w; omega) so.n so.inv so.r12 so.r10 hodd hlo) fun t' ⟨hg, _⟩ => ⟨minv, hg⟩
  simp only [seqs]
  exact two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p t ⟨_, _, _, _, _, _, _, h, _, minv, hg⟩ => by
    have hZq := h.z
    exact ⟨minv, hg, show slot ((p.k + 7) / 8) 8 ≤ p.Z by unfold offQ at hZq; omega⟩)
    (M.ct (by unfold MmUse; decide))

/-! ## From the stages to the parts' claims -/

/-- Runs at a stage agree on what a part needs, with `-n⁻¹` (the same in both
runs) among its public data. -/
theorem two_stage {R : StageRel} {α : Type} {Φ : α → State → Prop} (f : CrtPub → BitVec 64 → α)
    (m : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      ∃ minv, NVals t p.B p.w minv p.N ∧ Φ (f p minv) t)
    {s₁ s₂ : State} (h : Two (Stage R) s₁ s₂) : Two Φ s₁ s₂ := by
  obtain ⟨p, ⟨σ₁, xb₁, pb₁, qb₁, dpb₁, dqb₁, qib₁, h₁, hv, r₁⟩, ⟨σ₂, xb₂, pb₂, qb₂, dpb₂, dqb₂, qib₂, h₂, hv₂, r₂⟩⟩ := h
  obtain ⟨m₁, n₁, φ₁⟩ := m p _ _ _ _ _ _ _ _ h₁ hv r₁
  obtain ⟨m₂, n₂, φ₂⟩ := m p _ _ _ _ _ _ _ _ h₂ hv₂ r₂
  obtain ⟨hodd, -, -⟩ := valid_facts hv h₁.k1
  have := h₁.k1
  obtain rfl := nv_minv n₁ n₂ hodd (show 1 ≤ p.w by simp only [CrtPub.w]; omega)
  exact ⟨_, φ₁, φ₂⟩

/-- The primes' setup leaks the same in runs that agree on the public data. -/
theorem setupS_ct (hS : SetupCT) : RelCT isa (Two (Stage R1)) (seqs primesSetup) (Two (Stage R2)) := by
  refine stage_step (hS.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.pl, p.ql, p.pp, p.qp,
    p.qip⟩ : SetupPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, hr⟩ => WP.mono (setupPart_ok h hr) fun _ h' => ⟨minv, h'⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, pb, qb, qib, hr.good, by simp only [CrtPub.w]; omega, by simp only [CrtPub.w]; omega, hZq,
    by rw [hh _ (by decide) (by decide)]; exact h.hPl, by rw [hh _ (by decide) (by decide)]; exact h.hQl,
    by rw [hh _ (by decide) (by decide)]; exact h.hP, by rw [hh _ (by decide) (by decide)]; exact h.hQ,
    by rw [hh _ (by decide) (by decide)]; exact h.hQi, h.p.congrK hr.iscr hr.keep, h.q.congrK hr.iscr hr.keep,
    h.qi.congrK hr.iscr hr.keep, h.pbl, h.qbl, h.qil, h.pl1, ?_, h.ql1, ?_⟩
  · have := h.pl2; simp only [CrtPub.w]; omega
  · have := h.ql2; simp only [CrtPub.w]; omega

/-- The checks leak the same in runs that agree on the public data. -/
theorem checksS_ct (hC : ChecksCT) : RelCT isa (Two (Stage R2)) (seqs checks) (Two (Stage R3)) := by
  refine stage_step (hC.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    offQ p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : ChecksPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
      ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (checksPart_ok h hv hr) fun _ ⟨mp', mq', h'⟩ =>
      ⟨minv, mp', mq', h'⟩
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega
  refine ⟨minv, hr.n.nv, ?_⟩
  unfold ChecksPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, _, _, hr.n.good, by omega, by omega,
    show slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from le_refl _, by unfold offQ offP; omega, hZq, hwp2,
    wsWords_le (by have := h.pl2; omega) (by omega), hwq2, wsWords_le (by have := h.ql2; omega) (by omega),
    hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.n.nv.n, hr.n.msk, hr.pv, hr.qv, hr.qiv, hodd⟩

/-- `q`'s phase leaks the same in runs that agree on the public data. -/
theorem qS_ct (M : Mont) (hQ : QPhaseCT M) : RelCT isa (Two (Stage R3)) (seqs (qPhase M.mm)) (Two (Stage R4)) := by
  refine stage_step (hQ.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offQ p.w p.pl,
    wsWords p.ql, p.dqp, p.ql⟩ : PhasePub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h)
      fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (qPart_ok M h hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨-, -, hQ'⟩ := mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hql2 := h.ql2
  have hql1 := h.ql1
  have hZq := h.z
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  unfold QPre
  dsimp only [CrtPub.w]
  exact ⟨mq, _, _, dqb, hr.good, by omega, by omega,
    by unfold offQ; omega, hZq, hwq2, wsWords_le (by omega) (by omega), hr.wsQ, hr.qws, hr.nv,
    hodd, hN1, hr.xm, hr.qxv, hQ'.1, hQ'.2, by rw [hh _ (by decide) (by decide)]; exact h.hDq,
    by rw [hh _ (by decide) (by decide), h.dql]; exact h.hQl, h.dql, by rw [h.dql]; omega,
    by rw [h.dql]; omega, h.dq.congrK hr.iscr hr.keep⟩

/-- `p`'s phase leaks the same in runs that agree on the public data. -/
theorem pS_ct (M : Mont) (hP : PPhaseCT M) : RelCT isa (Two (Stage R4)) (seqs (pPhase M.mm)) (Two (Stage R5)) := by
  refine stage_step (hP.mono (fun _ _ h => two_stage (fun p minv => (⟨⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    wsWords p.pl, p.dpp, p.pl⟩, offQ p.w p.pl, wsWords p.ql, p.qip⟩ : PPhasePub))
      (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (pPart_ok M h hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨hMk', hP', -⟩ := mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  unfold PPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, dpb, qib, p.mask xb pb qb qib, hr.good, by omega,
    by omega, show slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from le_refl _, by unfold offQ offP; omega, hZq, hwp2,
    wsWords_le (by omega) (by omega), by unfold wsWords; omega,
    wsWords_le (by omega) (by omega), hr.wsP, hr.pws, hr.wsQ, hr.qws, hr.nv, hodd, hN1, hr.xm,
    hr.pxv, hP'.1, hP'.2, hr.pmask, fun hm => ?_, by rw [hh _ (by decide) (by decide)]; exact h.hDp,
    by rw [hh _ (by decide) (by decide), h.dpl]; exact h.hPl, h.dpl, by rw [h.dpl]; omega, by rw [h.dpl]; omega,
    h.dp.congrK hr.iscr hr.keep, by rw [hh _ (by decide) (by decide)]; exact h.hQi, by rw [h.qil, h.dpl],
    h.qi.congrK hr.iscr hr.keep, by rw [h.qil]; unfold wsWords; omega, fun hm => ?_⟩
  · obtain ⟨_, hpq, _⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact ⟨_, hpq.symm⟩
  · obtain ⟨_, _, hqi⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact hqi

/-! ## The result -/

/-- The public data of the result, without `-n⁻¹`. -/
structure OPubW where
  B : Addr
  Z : Nat
  w : Nat
  k : Nat
  op : Addr

/-- `outPhase_ok`'s hypotheses, for some `-n⁻¹`. -/
def OPreW (p : OPubW) (s : State) : Prop := ∃ minv, OPre ⟨⟨p.B, p.Z, p.w, minv⟩, p.k, p.op⟩ s

/-- Before `storeBE`, from array `j`. -/
def O1Arr (j : Nat) (p : OPubW) (s : State) : Prop :=
  ∃ c : Bool, Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ p.w = (p.k + 7) / 8 ∧ slot p.w 8 ≤ p.Z ∧
    1 ≤ p.k ∧ p.k < 2 ^ 31 ∧ s.gpr .rbx = off p.B (slot p.w j) ∧ s.gpr .rsi = p.op ∧
    s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .r15 = mask c ∧
    (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 j))

/-- The result's store from array `j` (`out_ct`'s), given that the taint
analysis checks its loads. -/
theorem outArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rbx (.mem (hdr (sArr j))), .mov .rsi (.mem (hdr Public.sOut)),
      .mov .rcx (.mem (hdr Public.sK)), .mov .r15 (.mem (hdr Public.sMask))]) hc).isSome = true) :
    RelCT isa (Two OPreW) (seqs (outStepsArr j)) fun _ _ => True := by
  unfold outStepsArr
  refine RelCT.seq (two_piece (Ψ := O1Arr j) [.rdi] (fun p s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) hT ?_) ?_
  · rintro p s ⟨_, c, hg, hw, hZ, hk1, hk, hO, hK, hM, hout, hsep⟩
    dsimp only at hg hw hZ hk1 hk hO hK hM hout hsep
    have hn := hg.scr.nowrap
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi => hg.scr.ld (by omega)
    refine WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
        t.gpr .rbx = off p.B (slot p.w j) ∧ t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.k ∧
        t.gpr .r15 = mask c ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl Public.sOut (by decide),
        hl Public.sK (by decide), hl Public.sMask (by decide), hg.hdr.harr j hj, hO, hK, hM]) rfl)
      fun t ⟨⟨hbx, hsi, hcx, h15, hm⟩, k⟩ => ⟨c, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hw, hZ,
        hk1, hk, hbx, hsi, hcx, h15, fun j hj => by rw [k.2.2]; exact hout j hj, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = p.B) [.rbx, .rsi, .rcx]
    (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, a₁, b₁, c₁, _⟩ ⟨_, _, _, _, _, _, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hs, hdi, hw, hZ, hk1, hk, hbx, hsi, hcx, h15, hout, hsep⟩
    exact WP.mono (storeBE_ok hs hbx hsi hcx h15 hk1 hk hw
      (by have := slot_le (w := p.w) hj; omega) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr (by decide)).trans hdi
  exact two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

/-! ## `main` -/

/-- `main` leaks the same in runs that agree on the public data, given that
its parts do. -/
theorem crtMain_ct (M : Mont) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    RelCT isa (Two (Stage R0)) (Crt.main M.mm) fun _ _ => True := by
  rw [crtMain_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [qPhase]) (RelCT.seq (R := Two (Stage R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks])
      (RelCT.seq (R := Two (Stage R2)) ?_ (checksS_ct hC))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (RelCT.seq (R := Two (Stage R1)) ?_ (setupS_ct hS))
    exact stage_step (nSetup_ct M) fun p σ xb _ _ _ _ _ t h hv ht => by
      subst ht; exact WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (qS_ct M hQ) ?_)
  exact RelCT.seqs_append (by simp [pPhase]) (by simp [finish]) (RelCT.seq (pS_ct M hP) hF)

end VG.Proof.Bignum.X86_64
