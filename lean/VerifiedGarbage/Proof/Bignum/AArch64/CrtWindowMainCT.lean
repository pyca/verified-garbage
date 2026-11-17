module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPowCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain

/-! ### `Bignum.AArch64.CrtWindowSetupCT`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: constant time of the primes' setup

`WindowFive.primesSetup` is the code of `Crt.primesSetup`, and its
precondition is `SetupPre`'s (`offQ32` is `offQ`, `tabBytes32` is `wsTab`):
`setup_ct` is the 4-bit setup's.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive

def SetupPre (p : SetupPub) (s : State) : Prop :=
  ∃ pb qb ib : List Byte, Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ32 p.w p.pl + slot (wsWords p.ql) 8 + tabBytes32 (wsWords p.ql) ≤ p.Z ∧
    word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    word s.mem p.B (8 * sP) = p.pp ∧ word s.mem p.B (8 * sQ) = p.qp ∧ word s.mem p.B (8 * sQinv) = p.ip ∧
    Src s p.B p.Z p.pp pb ∧ Src s p.B p.Z p.qp qb ∧ Src s p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

/-- `primesSetup` is constant time. -/
def SetupCT : Prop := RelCT isa (Two SetupPre) (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) fun _ _ => True

theorem setup_ct : SetupCT := VG.Proof.Bignum.AArch64.setup_ct

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowQCT`, which only this module used -/

section

/-! Constant time for the q phase with the wider window. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

def QPreWide (p : PhasePub) (s : State) : Prop := QPre p s ∧ Wide (CrtCTQ.sp p).x

def Q1Wide (p : PhasePub) (s : State) : Prop := CrtCTQ.Q1 p s ∧ Wide (CrtCTQ.sp p).x

def QPhaseCT (W : Window) (M : Mont) (S : Selector) : Prop :=
  RelCT isa (Two QPreWide)
    (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) (fun _ _ => True)

theorem unit_q1_wide (M : Mont) {p : PhasePub} {s : State} (h : QPreWide p s) :
    WP isa (seqs (unitSteps M.mm sWsQ)) s (Q1Wide p) :=
  WP.mono (CrtCTQ.unit_q1 M h.1) fun _ ht => ⟨ht,h.2⟩

theorem mm_pwPre_wide (M : Mont) {p : PhasePub} {s : State} (h : Q1Wide p s) :
    WP isa (M.mm Public.aY Public.aXm Public.aY) s (PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p)) :=
  WP.mono (CrtCTQ.mm_pwPre M h.1) fun _ ht => ⟨ht,h.2⟩

theorem pow_q3_wide (W : Window) (M : Mont) (S : Selector) {p : PhasePub} {s : State}
    (h : PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p) s) :
    WP isa (seqs (powSteps W.code S.code M.mm sWsQ sDq sQlen)) s (CrtCTQ.Q3 p) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨_,mx,_,X,_,eb,hg,hw28,hlo,_,hwx2,hwx,hsl,hslv,hws,hX,hX1,hXodd,hnY,hyl,hyc,hsd,
    hsln,hep,hel,_,hL1,hL2,he⟩ := h
  exact WP.mono (powPhase_ok W M S hg hw28 hlo hwide hwx2 hwx hsl hslv hws hX hX1 hXodd hnY hyl hyc
    hsd hsln hep hel hL1 hL2 he) fun _ ⟨hc,hX',_⟩ =>
      ⟨mx,X,hc,hX',hX1,hwx2,(by omega_using [hw28, hwx] : (CrtCTQ.sp p).x.wx < 2 ^ 28)⟩

theorem qPhase_ct (W : Window) (M : Mont) (S : Selector) (hU : UnitCT M sWsQ)
    (hP : PowCT W M S sWsQ sDq sQlen) : QPhaseCT W M S := by
  unfold QPhaseCT
  rw [qPhase_eq]
  refine RelCT.seqs_append (by simp [unitSteps,gPow]) (by simp) (RelCT.seq
    (two_post (Ψ := Q1Wide) (two_map CrtCTQ.up (fun _ _ h => CrtCTQ.uPre h.1) hU)
      fun _ _ h => unit_q1_wide M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [powSteps]) (RelCT.seq
    (two_post (Ψ := fun p => PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p))
      (two_map (fun p : PhasePub => (⟨p.B,p.Z,p.w⟩ : Ws))
        (fun _ _ ⟨⟨_,_,_,hg,_,_,hlo,hhi,_⟩,_⟩ => ⟨_,hg,by dsimp only; omega_using [hlo, hhi]⟩)
        (M.ct (by unfold MmUse; decide))) fun _ _ h => mm_pwPre_wide M h) ?_)
  exact RelCT.seqs_append (by simp [powSteps]) (by simp) (RelCT.seq
    (two_post (Ψ := CrtCTQ.Q3) (two_map CrtCTQ.sp (fun _ _ h => h) hP)
      fun _ _ h => pow_q3_wide W M S h) (CrtCTQ.mmLeave_ct M))

end VG.Proof.Bignum.AArch64.WindowFive

end

end


/-!
# RSA with the CRT on AArch64: `main` in constant time

`main` leaks the same in runs that agree on the public data (`CrtPub`: the
working space, the pointers, the lengths and `n`), from the constant time of
its parts (`crtMain_ct`). Its states between the parts are those of a run
from a state `CrtPre` describes (`Stage`), where the correctness lemmas of
the parts (`nPart_ok`, `setupPart_ok`, …) give what each part's claim needs.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (offQ32 tabBytes32)
open VG.Proof.MlKem.AArch64 (Keep)

structure CrtPreWide (s : State) (B : Addr) (Z k : Nat) (op np ip pp qp dpp dqp qip : Addr)
    (pl ql : Nat) (nb xb pb qb dpb dqb qib : List Byte) : Prop
    extends CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib where
  wide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z

/-- What holds of a state of a run from a state `σ` that `CrtPre` describes
with the public data `p`, the input `xb` and the private key. -/
abbrev StageRel := CrtPub → State → List Byte → List Byte → List Byte → List Byte → List Byte → List Byte →
  State → Prop

/-- A state satisfying `R` from such a start. -/
def Stage (R : StageRel) (p : CrtPub) (t : State) : Prop :=
  ∃ (σ : State) (xb pb qb dpb dqb qib : List Byte),
    CrtPreWide σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ R p σ xb pb qb dpb dqb qib t

/-- A part constant time from a stage, with its correctness, goes to the
next stage. -/
theorem stage_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (Stage R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPreWide σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (Stage R)) c (Two (Stage R')) :=
  two_post hct fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩ =>
    WP.mono (hw p σ xb pb qb dpb dqb qib t h hv hr) fun _ h' => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h'⟩

theorem stage_forget {G : Nat → Nat → Nat → Prop} {R : StageRel} {p : CrtPub} {t : State}
    (h : Stage (RG G R) p t) : Stage R p t :=
  let ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, _, hr⟩ := h; ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩

theorem stage_true {R : StageRel} {p : CrtPub} {t : State} (h : Stage R p t) :
    Stage (RG (fun _ _ _ => True) R) p t :=
  let ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩ := h; ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, trivial, hr⟩

/-! ## The stages -/

def R0 : StageRel := fun _ σ _ _ _ _ _ _ t => t = σ

def R1 : StageRel := fun p σ xb _ _ _ _ _ t => ∃ minv, NReady σ t p.B p.Z p.w minv p.N (Spec.Rsa.os2ip xb)

def R2 : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, PReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)

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

/-! ## From the stages to the parts' claims -/

/-- Runs at a stage agree on what a part needs, with `-n⁻¹` (the same in both
runs) among its public data. -/
theorem two_stage {R : StageRel} {α : Type} {Φ : α → State → Prop} (f : CrtPub → BitVec 64 → α)
    (m : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPreWide σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      ∃ minv, NVals t p.B p.w minv p.N ∧ Φ (f p minv) t)
    {s₁ s₂ : State} (h : Two (Stage R) s₁ s₂) : Two Φ s₁ s₂ := by
  obtain ⟨p, ⟨σ₁, xb₁, pb₁, qb₁, dpb₁, dqb₁, qib₁, h₁, hv, r₁⟩, ⟨σ₂, xb₂, pb₂, qb₂, dpb₂, dqb₂, qib₂, h₂, hv₂, r₂⟩, hsp⟩ := h
  obtain ⟨m₁, n₁, φ₁⟩ := m p _ _ _ _ _ _ _ _ h₁ hv r₁
  obtain ⟨m₂, n₂, φ₂⟩ := m p _ _ _ _ _ _ _ _ h₂ hv₂ r₂
  obtain ⟨hodd, -, -⟩ := valid_facts hv h₁.k1
  have := h₁.k1
  obtain rfl := nv_minv n₁ n₂ hodd (show 1 ≤ p.w by simp only [CrtPub.w]; omega_arith)
  exact ⟨_, φ₁, φ₂, hsp⟩

/-- The primes' setup leaks the same in runs that agree on the public data. -/
theorem setupS_ct (G : Nat → Nat → Nat → Prop) (hS : SetupCT) :
    RelCT isa (Two (Stage (RG G R1))) (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) (Two (Stage (RG G R2))) := by
  refine stage_step (hS.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.pl, p.ql, p.pp, p.qp,
    p.qip⟩ : SetupPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨_, minv, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨hg, minv, hr⟩ => WP.mono (setupPart_ok h.toCrtPre h.wide hr)
      fun _ h' => ⟨hg, minv, h'⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, pb, qb, qib, hr.good, by simp only [CrtPub.w]; omega_arith, by simp only [CrtPub.w]; omega_arith, hZq,
    by rw [hh _ (by decide) (by decide)]; exact h.hPl, by rw [hh _ (by decide) (by decide)]; exact h.hQl,
    by rw [hh _ (by decide) (by decide)]; exact h.hP, by rw [hh _ (by decide) (by decide)]; exact h.hQ,
    by rw [hh _ (by decide) (by decide)]; exact h.hQi, h.p.congrK hr.iscr hr.keep, h.q.congrK hr.iscr hr.keep,
    h.qi.congrK hr.iscr hr.keep, h.pbl, h.qbl, h.qil, h.pl1, ?_, h.ql1, ?_⟩
  · have := h.pl2; simp only [CrtPub.w]; omega_arith
  · have := h.ql2; simp only [CrtPub.w]; omega_arith

/-- The checks `C` leak the same in runs that agree on the public data. -/
theorem checksS_ct {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksCTOf C) (hok : ChecksOk C G) :
    RelCT isa (Two (Stage (RG G R2))) (seqs C) (Two (Stage R3)) := by
  refine stage_step (hC.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    offQ32 p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : ChecksPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨_, minv, mp, mq, hr⟩ =>
      ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨hg, minv, mp, mq, hr⟩ =>
      WP.mono (checksPart_ok h.toCrtPre h.wide hv hr hok hg) fun _ ⟨mp', mq', h'⟩ => ⟨minv, mp', mq', h'⟩
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_arith
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega_arith
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega_arith
  refine ⟨minv, hr.n.nv, ?_⟩
  unfold ChecksPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, _, _, hr.n.good, by omega_arith, by omega_arith,
    show slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from Nat.le_refl _, by unfold offQ32 offP; omega_arith, by omega_arith, hwp2,
    wsWords_le (by have := h.pl2; omega_arith) (by omega_arith), hwq2, wsWords_le (by have := h.ql2; omega_arith) (by omega_arith),
    hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.n.nv.n, hr.n.msk, hr.pv, hr.qv, hr.qiv, hodd⟩

/-- `q`'s phase leaks the same in runs that agree on the public data. -/
theorem qS_ct (W : Window) (M : Mont) (S : Selector) (hQ : QPhaseCT W M S) : RelCT isa (Two (Stage R3)) (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) (Two (Stage R4)) := by
  refine stage_step (hQ.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offQ32 p.w p.pl,
    wsWords p.ql, p.dqp, p.ql⟩ : PhasePub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h)
      fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (qPart_ok W M S h.toCrtPre h.wide hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h.toCrtPre hv
  obtain ⟨-, -, hQ'⟩ := mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hql2 := h.ql2
  have hql1 := h.ql1
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_arith
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega_arith
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  refine ⟨?_,hZq⟩
  unfold QPre
  dsimp only [CrtPub.w]
  exact ⟨mq, _, _, dqb, hr.good, by omega_arith, by omega_arith,
    by unfold offQ32; omega_arith, by omega_arith, hwq2, wsWords_le (by omega_arith) (by omega_arith), hr.wsQ, hr.qws, hr.nv,
    hodd, hN1, hr.xm, hr.qxv, hQ'.1, hQ'.2, by rw [hh _ (by decide) (by decide)]; exact h.hDq,
    by rw [hh _ (by decide) (by decide), h.dql]; exact h.hQl, h.dql, by rw [h.dql]; omega_arith,
    by rw [h.dql]; omega_arith, h.dq.congrK hr.iscr hr.keep⟩

/-- `p`'s phase leaks the same in runs that agree on the public data. -/
theorem pS_ct (W : Window) (M : Mont) (S : Selector) (hP : PPhaseCT W M S) : RelCT isa (Two (Stage R4)) (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) (Two (Stage R5)) := by
  refine stage_step (hP.mono (fun _ _ h => two_stage (fun p minv => (⟨⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    wsWords p.pl, p.dpp, p.pl⟩, offQ32 p.w p.pl, wsWords p.ql, p.qip⟩ : PPhasePub))
      (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (pPart_ok W M S h.toCrtPre h.wide hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h.toCrtPre hv
  obtain ⟨hMk', hP', -⟩ := mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_arith
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega_arith
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  refine ⟨?_,?_⟩
  swap
  · change offP p.w + slot (wsWords p.pl) 8 + tabBytes32 (wsWords p.pl) ≤ p.Z
    unfold offQ32 at hZq
    dsimp only [CrtPub.w]
    unfold offP
    omega_arith
  unfold PPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, dpb, qib, p.mask xb pb qb qib, hr.good, by omega_arith,
    by omega_arith, show slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from Nat.le_refl _, by unfold offQ32 offP; omega_arith, by omega_arith, hwp2,
    wsWords_le (by omega_arith) (by omega_arith), by unfold wsWords; omega_arith,
    wsWords_le (by omega_arith) (by omega_arith), hr.wsP, hr.pws, hr.wsQ, hr.qws, hr.nv, hodd, hN1, hr.xm,
    hr.pxv, hP'.1, hP'.2, hr.pmask, fun hm => ?_, by rw [hh _ (by decide) (by decide)]; exact h.hDp,
    by rw [hh _ (by decide) (by decide), h.dpl]; exact h.hPl, h.dpl, by rw [h.dpl]; omega_arith, by rw [h.dpl]; omega_arith,
    h.dp.congrK hr.iscr hr.keep, by rw [hh _ (by decide) (by decide)]; exact h.hQi, by rw [h.qil, h.dpl],
    h.qi.congrK hr.iscr hr.keep, by rw [h.qil]; unfold wsWords; omega_arith, fun hm => ?_⟩
  · obtain ⟨_, hpq, _⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact ⟨_, hpq.symm⟩
  · obtain ⟨_, _, hqi⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact hqi

/-! ## `main` -/

/-- `main` leaks the same in runs that agree on the public data, given that
its parts do. -/
theorem crtMain_ct (W : Window) (M : Mont) (S : Selector) (hN : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True)
    {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop}
    (hS : SetupCT) (hC : ChecksCTOf C) (hok : ChecksOk C G) (hQ : QPhaseCT W M S) (hP : PPhaseCT W M S)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    RelCT isa (Two (Stage (RG G R0))) (VG.Impl.Rsa.AArch64.WindowFive.mainWith C W.code S.code M.mm) fun _ _ => True := by
  rw [crtMain_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (RelCT.seq (R := Two (Stage R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) hok.ne
      (RelCT.seq (R := Two (Stage (RG G R2))) ?_ (checksS_ct hC hok))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.primesSetup])
      (RelCT.seq (R := Two (Stage (RG G R1))) ?_ (setupS_ct G hS))
    exact stage_step (two_map id (fun _ _ h => stage_forget h) hN) fun p σ xb _ _ _ _ _ t h hv ⟨hg, ht⟩ => by
      subst ht; exact WP.mono (nPart_ok M h.toCrtPre hv) fun _ ⟨minv, hr⟩ => ⟨hg, minv, hr⟩
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (RelCT.seq (qS_ct W M S hQ) ?_)
  exact RelCT.seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (by simp [finish]) (RelCT.seq (pS_ct W M S hP) hF)

end VG.Proof.Bignum.AArch64.WindowFive
