module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseWitness
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundsCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.PolicyLoopCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.PolicyStep`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: public state after a policy iteration -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

def PolicyPublic.sample (d : PolicyPublic) : Option Nat := (Spec.Ffdh.drawWitness d.p.N d.bs).map Prod.fst

def PolicyAfter (d : PolicyPublic) (s : State) : Prop :=
  ∃ n, n ≤ d.bs.length ∧ DrawState d.p (off d.rp n) (d.used + n) (d.bs.drop n) s ∧
    word s.mem d.p.O (8 * oStatus) = BitVec.ofNat 64 (runStatus d.p d.i d.checks d.sample) ∧
    word s.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 (runIndex d.p d.i d.sample) ∧
    (∀ a rest, Spec.Ffdh.drawWitness d.p.N d.bs = some (a, rest) → rest = d.bs.drop n) ∧
    s.zf = some (decide (runStatus d.p d.i d.checks d.sample = 4)) ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ s.gpr .rsp = d.sp ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr ∧ RoundRoom d.p (off d.rp n) (d.bs.drop n) s

theorem policy_after (M : Mont) (K : Kernel) (d : PolicyPublic) (s : State) (h : PolicyBefore d s) :
    WP isa (roundBody M.mm K.run) s (PolicyAfter d) := by
  obtain ⟨hd, hroom, hsp, hi, hc, hi32, hc32⟩ := h
  refine WP.mono (roundBody_ok M K hd.1 hroom hi hc hi32 hc32)
    fun t ⟨n, hn, ht, hs, hidx, hrest, hz, hsave, _, k⟩ => ?_
  exact ⟨n, hn, ht, hs, hidx, hrest, hz,
    (hsave _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc,
    (k.gpr (by decide)).trans hsp, k.2.2.trans hd.2.1, hd.2.2, hroom.after_draw k (by decide) n⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of the uniform round policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64

private def policyInv (n : Nat) : State → State → Prop :=
  Two fun d s => d.i + n = d.checks ∧ PolicyBefore d s

private theorem checks_bound {d : PolicyPublic} {s : State} (h : PolicyBefore d s) : d.checks < 2 ^ 31 := by
  obtain ⟨_, _, _, _, _, _, hc⟩ := h
  exact hc

private theorem policy_step (M : Mont) (K : Kernel) (n : Nat) :
    RelCT isa (policyInv n) (roundBody M.mm K.run) fun s₁ s₂ =>
      isa.eval .e s₁ = isa.eval .e s₂ ∧ (isa.eval .e s₁ = some false → True) ∧
        (isa.eval .e s₁ = some true → ∃ m < n, policyInv m s₁ s₂) := by
  have hct : RelCT isa (policyInv n) (roundBody M.mm K.run)
      (Two fun d s => d.i + n = d.checks ∧ d.checks < 2 ^ 31 ∧ PolicyAfter d s) :=
    two_post (two_map (fun d : PolicyPublic => d) (fun _ _ h => h.2) (roundBody_ct M K))
      (fun d s h => WP.mono (policy_after M K d s h.2) fun _ ht => ⟨h.1, checks_bound h.2, ht⟩)
  refine hct.mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨d, ⟨hsize, hc32, h₁⟩, ⟨_, _, h₂⟩⟩
  obtain ⟨u₁, hu₁, ht₁, _, hi₁, hr₁, hz₁, hc₁, hsp₁, hw₁, hk₁, hroom₁⟩ := h₁
  obtain ⟨u₂, hu₂, ht₂, _, hi₂, hr₂, hz₂, hc₂, hsp₂, hw₂, hk₂, hroom₂⟩ := h₂
  refine ⟨by simp only [eval, hz₁, hz₂], fun _ => trivial, fun hgo => ?_⟩
  have hfour : runStatus d.p d.i d.checks d.sample = 4 := of_decide_eq_true (by
    simpa only [eval, hz₁, Option.some.injEq] using hgo)
  cases he : Spec.Ffdh.drawWitness d.p.N d.bs with
  | none => simp only [PolicyPublic.sample, he, Option.map_none, runStatus] at hfour; contradiction
  | some ar =>
    obtain ⟨a, rest⟩ := ar
    have hsample : d.sample = some a := by simp only [PolicyPublic.sample, he, Option.map_some]
    have hpass : Spec.Ffdh.mrRound d.p.N a = true ∧ d.i + 1 < d.checks := by
      by_cases hp : Spec.Ffdh.mrRound d.p.N a = true
      · by_cases hm : d.i + 1 < d.checks
        · exact ⟨hp, hm⟩
        · simp [runStatus, hsample, hp, passStatus, hm] at hfour
      · have hp' : Spec.Ffdh.mrRound d.p.N a = false := Bool.eq_false_iff.mpr hp
        simp [runStatus, hsample, hp'] at hfour
    have hrest₁ := hr₁ a rest he
    have hrest₂ := hr₂ a rest he
    have heq : u₁ = u₂ := by
      have hl₁ := congrArg List.length hrest₁
      have hl₂ := congrArg List.length hrest₂
      simp only [List.length_drop] at hl₁ hl₂
      omega_using [hl₁, hl₂, hu₁, hu₂]
    subst u₂
    let d' : PolicyPublic := { d with rp := off d.rp u₁, used := d.used + u₁, bs := d.bs.drop u₁, i := d.i + 1 }
    have hidx₁ : word s₁.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 (d.i + 1) := by
      simpa only [runIndex, hsample, hpass.1, ite_true] using hi₁
    have hidx₂ : word s₂.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 (d.i + 1) := by
      simpa only [runIndex, hsample, hpass.1, ite_true] using hi₂
    refine ⟨n - 1, by omega_using [hsize, hpass.2], d', ?_, ?_⟩
    · refine ⟨?_, ⟨⟨ht₁, hw₁, hk₁⟩, hroom₁, hsp₁, hidx₁, hc₁, ?_, hc32⟩⟩
      · change d.i + 1 + (n - 1) = d.checks
        omega_using [hsize, hpass.2]
      · change d.i + 1 < 2 ^ 31
        omega_using [hc32, hpass.2]
    · refine ⟨?_, ⟨⟨ht₂, hw₂, hk₂⟩, hroom₂, hsp₂, hidx₂, hc₂, ?_, hc32⟩⟩
      · change d.i + 1 + (n - 1) = d.checks
        omega_using [hsize, hpass.2]
      · change d.i + 1 < 2 ^ 31
        omega_using [hc32, hpass.2]

theorem policyLoop_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two fun d s => PolicyBefore d s ∧ d.i < d.checks)
      (.loop (roundBody M.mm K.run) .e) fun _ _ => True := by
  rintro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨d, h₁, h₂⟩ e₁ e₂
  exact RelCT.loop policyInv (policy_step M K) (d.checks - d.i) s₁ s₂ tr₁ tr₂ t₁ t₂
    ⟨d, ⟨by omega_using [h₁.2], h₁.1⟩, ⟨by omega_using [h₂.2], h₂.1⟩⟩ e₁ e₂

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of a complete primality policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

def RoundsBefore (d : PolicyPublic) (s : State) : Prop :=
  DrawBefore d.toDrawPublic s ∧ RoundRoom d.p d.rp d.bs s ∧ s.gpr .rsp = d.sp ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ 0 < d.checks ∧ d.checks < 2 ^ 31

private theorem init_policy (d : PolicyPublic) (s : State) (h : RoundsBefore d s) :
    WP isa (.block roundInit) s (fun t => PolicyBefore {d with i := 0} t ∧ 0 < d.checks) := by
  obtain ⟨hd, hroom, hsp, hc, hpos, hc32⟩ := h
  refine WP.mono (roundInit_ok hd.1) fun t ⟨hm, k⟩ => ?_
  have hf : Frm d.p.O [(8 * oIndex, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have ht := hd.1.outer_frame hf (by simp [oIndex]) (by simp [oIndex]) k
    ((k.gpr (by decide)).trans hd.1.ready.good.rdi)
  have hst : t.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨⟨ht, k.2.2.trans hd.2.1, hd.2.2⟩, hroom.congr hst, hst.trans hsp, ?_, ?_, by change 0 < 2 ^ 31; decide, hc32⟩, hpos⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hc

theorem rounds_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two RoundsBefore) (rounds M.mm K.run) fun _ _ => True := by
  unfold rounds
  refine RelCT.seq (two_post
    (two_map (fun d : PolicyPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.link) roundInit_ct)
    init_policy) ?_
  exact two_map (fun d : PolicyPublic => {d with i := 0}) (fun _ _ h => h) (policyLoop_ct M K)

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of the complete modulus policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaKeyGen.X86_64 (two_bind)

def PhasePrime (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q c d s ∧ d.p.phaseValue q % 2 = 1

def PhasePrepared (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) : Prop :=
  CandidateState d s ∧ d.p.phaseValue q % 2 = 1 ∧ ∃ mi,
    ModulusReady s (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi (d.p.phaseValue q) ∧ PhaseHeader d.p q c s

private theorem prepare_phase (M : Mont) (R : R2Impl M) (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) (h : PhasePrime q c d s) :
    WP isa (prepareModulus M.mm R.code) s (PhasePrepared q c d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.1.2
  exact WP.mono (prepareModulus_state_ok M R h.1.1.1 hg hp hn h.2)
    fun _ ⟨mi', ht, hr, hp', _, _, k⟩ => ⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, h.2, mi', hr, hp'⟩

private theorem prepared_rounds (q : Bool) (c : Checks) {s₁ s₂ : State} (h : Two (PhasePrepared q c) s₁ s₂) : Two RoundsBefore s₁ s₂ := by
  refine two_bind (fun d t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨mi₁, hr₁, hp₁⟩ := h₁.2.2
  obtain ⟨mi₂, hr₂, hp₂⟩ := h₂.2.2
  have hw : 1 ≤ d.p.phaseWords q := by omega_using [(h₁.1.1.base.phase_room q).1]
  have hi₁ := hr₁.inv
  have hi₂ := hr₂.inv
  have he₁ : (word t₁.mem (off d.p.B 256) (slot (d.p.phaseWords q) aN)).toNat = d.p.phaseValue q % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.p.phaseWords q) _ _ _ hw, hr₁.n]
  have he₂ : (word t₂.mem (off d.p.B 256) (slot (d.p.phaseWords q) aN)).toNat = d.p.phaseValue q % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.p.phaseWords q) _ _ _ hw, hr₂.n]
  rw [he₁] at hi₁
  rw [he₂] at hi₂
  have heq := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.2.1) hi₁ hi₂
  cases heq
  let wp := h₁.1.1.base.witnessParams q mi₁ h₁.2.1
  let dp : DrawPublic := ⟨wp, off d.p.rp d.used, d.used, d.p.rand.drop d.used, d.wr⟩
  let pp : PolicyPublic := ⟨dp, d.p.sp, 0, d.p.phaseChecks q c⟩
  have hchecks : 0 < pp.checks ∧ pp.checks < 2 ^ 31 := checksCount_pos c _
  refine ⟨pp, ?_, ?_⟩
  · exact ⟨⟨h₁.1.1.drawState hp₁ h₁.2.1 hr₁, h₁.1.2.1, h₁.1.2.2⟩,
      h₁.1.1.roundRoom h₁.2.1, h₁.1.1.base.sp, hp₁.checks, hchecks.1, hchecks.2⟩
  · exact ⟨⟨h₂.1.1.drawState hp₂ h₁.2.1 hr₂, h₂.1.2.1, h₂.1.2.2⟩,
      h₂.1.1.roundRoom h₁.2.1, h₂.1.1.base.sp, hp₂.checks, hchecks.1, hchecks.2⟩

theorem modulusPolicy_ct (M : Mont) (R : R2Impl M) (K : Kernel) (q : Bool) (c : Checks) :
    RelCT isa (Two (PhasePrime q c)) (modulusPolicy M.mm R.code K.run) fun _ _ => True := by
  unfold modulusPolicy
  exact RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => d.prep q) (fun _ _ h => h.1.prepare h.2) (prepareModulus_ct M R))
    (prepare_phase M R q c)) ((rounds_ct M K).mono (fun _ _ h => prepared_rounds q c h) (fun _ _ h => h))

end VG.Proof.Ffdh.X86_64.ParameterCandidate
