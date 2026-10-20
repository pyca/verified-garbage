module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResultCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRunCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
import VerifiedGarbage.Proof.Framework.Omega

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
