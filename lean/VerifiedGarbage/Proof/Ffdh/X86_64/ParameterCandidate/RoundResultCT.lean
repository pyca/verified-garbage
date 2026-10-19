module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of a known round result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.RsaKeyGen.X86_64.Candidate (kFlag)
open VG.Proof.MlKem.X86_64

structure RunPublic where
  p : WitnessParams
  wr : List Region
  sp : Addr
  sample : Option Nat
  i : Nat
  checks : Nat

def RunContext (d : RunPublic) (s : State) : Prop :=
  ∃ rp used bs, DrawState d.p rp used bs s ∧ RoundRoom d.p rp bs s ∧ s.gpr .rsp = d.sp ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr ∧
    word s.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 d.i ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ d.i < 2 ^ 31 ∧ d.checks < 2 ^ 31

theorem RunContext.link {d : RunPublic} {s : State} (h : RunContext d s) :
    LinkHeader ⟨d.p.O, d.wr⟩ s := by
  obtain ⟨_, _, _, ht, _, _, hw, hk, _⟩ := h
  exact ⟨hk, ht.ready.good.rdi, hw, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact ht.link⟩

def FlagBefore (d : RunPublic) (s : State) : Prop := RunContext d s ∧
  word s.mem d.p.I (8 * kFlag) = mask (Spec.Ffdh.mrRound d.p.N (d.sample.getD 0))

def FlagAfter (d : RunPublic) (s : State) : Prop := LinkHeader ⟨d.p.O, d.wr⟩ s ∧
  s.zf = some (!(Spec.Ffdh.mrRound d.p.N (d.sample.getD 0)))

private theorem flag_after (d : RunPublic) (s : State) (h : FlagBefore d s) :
    WP isa (.block [.mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)]) s (FlagAfter d) := by
  obtain ⟨rp, used, bs, ht, _, _, hw, hk, _⟩ := h.1
  refine WP.mono (roundFlag_ok ht.ready.good.scr (by
    have hz := d.p.dims.z; unfold slot VG.Impl.Bignum.hdrBytes at hz; omega_using [hz])
    ht.ready.good.rdi h.2) fun t ⟨hz, hm, k⟩ => ?_
  refine ⟨⟨hk, (k.gpr (by decide)).trans ht.ready.good.rdi, k.2.2.trans hw, ?_⟩, hz⟩
  intro e he
  simp only [List.mem_singleton] at he; subst e
  rw [hm]; exact ht.link

theorem roundResult_ct : RelCT isa (Two FlagBefore) roundResult fun _ _ => True := by
  unfold roundResult
  refine RelCT.seq (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact h₁.1.choose_spec.choose_spec.choose_spec.1.ready.good.rdi.trans
      h₂.1.choose_spec.choose_spec.choose_spec.1.ready.good.rdi.symm)
    (by taint_decide) flag_after) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1) roundFail_ct
  · exact two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1) roundPass_ct

theorem roundResult_link (d : RunPublic) (s : State) (h : FlagBefore d s) :
    WP isa roundResult s (LinkHeader ⟨d.p.O, d.wr⟩) := by
  obtain ⟨rp, used, bs, ht, _, _, hw, hk, hi, hc, hi32, hc32⟩ := h.1
  refine WP.mono (roundResult_ok ht h.2 hi hc hi32 hc32)
    fun t ⟨ht', _, _, _, _, k⟩ => ?_
  exact ⟨hk, ht'.ready.good.rdi, k.2.2.trans hw, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact ht'.link⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
