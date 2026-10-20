module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestoreCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawPrefix

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
    · unfold slot VG.Impl.Bignum.hdrBytes aTmp; omega
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
