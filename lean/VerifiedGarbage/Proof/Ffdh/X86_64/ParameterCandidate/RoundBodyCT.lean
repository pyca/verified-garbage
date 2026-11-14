module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResultCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestoreCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawPrefix
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawBody
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRunCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
public import Mathlib.Algebra.Group.Nat.Defs

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawLoopCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawBodyCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawSampleCT`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: timing of one sampled witness -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def DrawAvailable (d : DrawPublic) (s : State) : Prop := DrawBefore d s ∧ d.p.len ≤ d.bs.length

theorem drawPrefix_ct : RelCT isa (Two DrawAvailable) drawPrefix fun _ _ => True := by
  unfold drawPrefix cutLoad
  refine RelCT.seq (two_post
    (two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.link) drawSetup_ct)
    (fun d s h => drawSetup_cut d s h.1 h.2)) ?_
  exact RelCT.seq (two_post cutRestore_ct cutRestore_inner)
    (two_map DrawPublic.inner (fun _ _ h => h) inner_loadWitness_ct)

def SampleLoaded (d : DrawPublic) (s : State) : Prop :=
  DrawState d.p (off d.rp d.p.len) (d.used + d.p.len) (d.bs.drop d.p.len) s ∧
    wv s.mem d.p.I (slot d.p.w aXm) d.p.w = Spec.Rsa.os2ip (d.bs.take d.p.len) % 2 ^ d.p.bits ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr

private theorem prefix_loaded (d : DrawPublic) (s : State) (h : DrawAvailable d s) :
    WP isa drawPrefix s (SampleLoaded d) :=
  WP.mono (drawPrefix_ok h.1.1 h.2) fun _ ⟨ht, hx, _, _, k⟩ => ⟨ht, hx, k.2.2.trans h.1.2.1, h.1.2.2⟩

private theorem loaded_range (d : DrawPublic) (s : State) (h : SampleLoaded d s) :
    WP isa witnessRange s (LinkHeader ⟨d.p.O, d.wr⟩) := by
  refine WP.mono (witnessRange_ok h.1.ready d.p.dims d.p.odd h.2.1)
    fun t ⟨_, _, ht, _, hf, k⟩ => ?_
  have hlo : ∀ r ∈ [(slot d.p.w aTmp, 8 * d.p.w), (8 * VG.Impl.Ffdh.X86_64.Domain.sF, 8)],
      136 ≤ r.1 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold slot VG.Impl.Bignum.hdrBytes aTmp; omega_using []
    · decide
  refine ⟨h.2.2.2, ht.good.rdi, k.2.2.trans h.2.2.1, ?_⟩
  intro e he
  simp only [List.mem_singleton] at he; subst e
  exact (inner_link hf hlo).trans h.1.link

theorem drawSample_ct : RelCT isa (Two DrawAvailable) drawSample fun _ _ => True := by
  unfold drawSample
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post drawPrefix_ct prefix_loaded) (RelCT.seq (two_post ?_ loaded_range) ?_)
  · refine two_map (fun d : DrawPublic => (⟨d.p.I, d.p.IZ, d.p.w⟩ : Ws)) (fun d _ h => ?_) witnessRange_ct
    exact ⟨⟨d.p.mi, h.1.ready.good, d.p.dims.z⟩,
      by change 1 ≤ d.p.w; omega_using [d.p.width_bounds.1],
      by change d.p.w < 2 ^ 31; omega_using [d.p.width_bounds.2.1]⟩
  · exact two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h) drawFinish_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of a rejection-sampling step -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def DrawHeadAfter (d : DrawPublic) (s : State) : Prop :=
  DrawBefore d s ∧ s.cf = some (decide (d.bs.length < d.p.len))

private theorem head_after (d : DrawPublic) (s : State) (h : DrawBefore d s) :
    WP isa (.block drawHead) s (DrawHeadAfter d) := by
  have houter : Scr s d.p.O 256 := by
    simpa [off] using h.1.scr.sub (o := 0) (n := 256) d.p.space_bounds.1 (by decide)
  refine WP.mono (drawHead_ok h.1.ready.good.scr d.p.space_bounds.2.1 houter h.1.ready.good.rdi
    h.1.link h.1.left h.1.len (by omega_using [h.1.countBound])
    (by omega_using [d.p.width_bounds.2.2.2.1])) fun t ⟨hcf, hm, k⟩ => ?_
  exact ⟨⟨h.1.same_mem hm k ((k.gpr (by decide)).trans h.1.ready.good.rdi),
    k.2.2.trans h.2.1, h.2.2⟩, hcf⟩

theorem drawBody_ct : RelCT isa (Two DrawBefore) drawBody fun _ _ => True := by
  unfold drawBody
  refine RelCT.seq (two_post
    (two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.link) drawHead_ct)
    head_after) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.link) drawShort_ct
  · refine two_map (fun d : DrawPublic => d) (fun d s h => ?_) drawSample_ct
    refine ⟨h.1.1, ?_⟩
    have hx : decide (d.bs.length < d.p.len) = false := by simpa only [eval, h.1.2, Option.some.injEq] using h.2
    omega_using [of_decide_eq_false hx]

def DrawAfter (d : DrawPublic) (s : State) : Prop :=
  (if d.p.len ≤ d.bs.length then
    DrawState d.p (off d.rp d.p.len) (d.used + d.p.len) (d.bs.drop d.p.len) s ∧
      s.zf = some (!decide (2 ≤ drawValue d.p d.bs ∧ drawValue d.p d.bs < d.p.N - 1))
   else DrawState d.p d.rp d.used d.bs s ∧ s.zf = some false) ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr

theorem drawBody_after (d : DrawPublic) (s : State) (h : DrawBefore d s) :
    WP isa drawBody s (DrawAfter d) := by
  refine WP.mono (drawBody_ok h.1) fun t ⟨hstep, _, _, k⟩ => ?_
  refine ⟨?_, k.2.2.trans h.2.1, h.2.2⟩
  by_cases ha : d.p.len ≤ d.bs.length
  · simp only [ite_eq_left ha] at hstep ⊢
    exact ⟨hstep.1, hstep.2.2.1⟩
  · simp only [ite_eq_right ha] at hstep ⊢
    exact ⟨hstep.1, hstep.2.1⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of uniform rejection sampling -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

private def drawInv (n : Nat) : State → State → Prop :=
  Two fun d s => d.bs.length = n ∧ DrawBefore d s

private theorem draw_step (n : Nat) : RelCT isa (drawInv n) drawBody fun s₁ s₂ =>
    isa.eval .e s₁ = isa.eval .e s₂ ∧ (isa.eval .e s₁ = some false → True) ∧
      (isa.eval .e s₁ = some true → ∃ m < n, drawInv m s₁ s₂) := by
  have hc : RelCT isa (drawInv n) drawBody
      (Two fun d s => d.bs.length = n ∧ DrawAfter d s) :=
    two_post (two_map (fun d : DrawPublic => d) (fun _ _ h => h.2) drawBody_ct)
      (fun d s h => WP.mono (drawBody_after d s h.2) fun _ ht => ⟨h.1, ht⟩)
  refine hc.mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨d, ⟨hsize, h₁⟩, ⟨_, h₂⟩⟩
  by_cases ha : d.p.len ≤ d.bs.length
  · simp only [DrawAfter, ite_eq_left ha] at h₁ h₂
    refine ⟨by simp only [eval, h₁.1.2, h₂.1.2], fun _ => trivial, fun _ => ?_⟩
    let d' : DrawPublic := { d with rp := off d.rp d.p.len, used := d.used + d.p.len, bs := d.bs.drop d.p.len }
    refine ⟨d'.bs.length, ?_, d', ⟨rfl, ⟨h₁.1.1, h₁.2⟩⟩, ⟨rfl, ⟨h₂.1.1, h₂.2⟩⟩⟩
    change (d.bs.drop d.p.len).length < n
    rw [List.length_drop]
    omega_using [ha, hsize, d.p.width_bounds.2.2.1]
  · simp only [DrawAfter, ite_eq_right ha] at h₁ h₂
    refine ⟨by simp only [eval, h₁.1.2, h₂.1.2], fun _ => trivial, ?_⟩
    intro he
    simp only [eval, h₁.1.2, Option.some.injEq, Bool.false_eq_true] at he

theorem drawWitness_ct : RelCT isa (Two DrawBefore) drawWitness fun _ _ => True := by
  rintro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨d, h₁, h₂⟩ e₁ e₂
  exact RelCT.loop drawInv draw_step d.bs.length s₁ s₂ tr₁ tr₂ t₁ t₂
    ⟨d, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩ e₁ e₂

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of a complete policy iteration -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

structure PolicyPublic extends DrawPublic where
  sp : Addr
  i : Nat
  checks : Nat

def PolicyBefore (d : PolicyPublic) (s : State) : Prop :=
  DrawBefore d.toDrawPublic s ∧ RoundRoom d.p d.rp d.bs s ∧ s.gpr .rsp = d.sp ∧
    word s.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 d.i ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ d.i < 2 ^ 31 ∧ d.checks < 2 ^ 31

def PolicyPublic.run (d : PolicyPublic) : RunPublic :=
  ⟨d.p, d.wr, d.sp, (Spec.Ffdh.drawWitness d.p.N d.bs).map Prod.fst, d.i, d.checks⟩

private theorem witness_run (d : PolicyPublic) (s : State) (h : PolicyBefore d s) :
    WP isa drawWitness s (RunBefore d.run) := by
  obtain ⟨hd, hroom, hsp, hi, hc, hi32, hc32⟩ := h
  refine WP.mono (drawWitness_ok hd.1) fun t ⟨n, _, ht, hresult, _, hsaved, _, k⟩ => ?_
  refine ⟨⟨off d.rp n, d.used + n, d.bs.drop n, ht,
    hroom.after_draw k (by decide) n, (k.gpr (by decide)).trans hsp,
    k.2.2.trans hd.2.1, hd.2.2,
    (hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi,
    (hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc,
    hi32, hc32⟩, ?_⟩
  cases he : Spec.Ffdh.drawWitness d.p.N d.bs with
  | none => simpa only [SampleAt, PolicyPublic.run, he, Option.map_none] using hresult
  | some ar =>
    obtain ⟨a, rest⟩ := ar
    simp only [he] at hresult
    simpa only [SampleAt, PolicyPublic.run, he, Option.map_some] using And.intro hresult.1 hresult.2.2

theorem roundBody_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two PolicyBefore) (roundBody M.mm K.run) fun _ _ => True := by
  unfold roundBody
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map PolicyPublic.toDrawPublic (fun _ _ h => h.1) drawWitness_ct) witness_run) ?_
  refine RelCT.seq (two_map PolicyPublic.run (fun _ _ h => h) (roundRun_ct M K)) ?_
  exact two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h) statusMore_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate
