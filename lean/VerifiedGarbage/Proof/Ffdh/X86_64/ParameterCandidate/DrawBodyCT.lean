module

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSampleCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawBody
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawCTData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead

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
