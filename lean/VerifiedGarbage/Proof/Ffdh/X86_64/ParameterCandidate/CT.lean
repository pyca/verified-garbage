module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.OuterCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.BodyCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Body
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyCT
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # FFDH parameter generation on x86-64: constant time under the public tape contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def finishPublic (p : CandidateP) : OuterPublic :=
  ⟨p.B, candidateWr p, p.op, p.k, p.up, p.bits,
    Proof.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand), p.rp⟩

private theorem body_finish (M : Mont) (R : R2Impl M) (K : Kernel) (p : CandidateP) (s : State) (h : CR p s) :
    WP isa (body M.mm R.code K.run) s (FinishHeader (finishPublic p)) := by
  have hk := pc_kw h.1
  have hw := pc_wr h.1
  cases h.2
  refine WP.mono (body_ok M R K (pcCtx_of h.1)) fun t ⟨used, ht, hd, hr, _, _, k⟩ => ?_
  refine ⟨hk.kw, hd, k.2.2.trans hw, ?_⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · simp only [finishPublic, outerSlots, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    all_goals exact ht.base.hdr _ (by simp [CandidateP.headers])
  · simp only [List.mem_singleton] at he; subst e
    exact hr.1

theorem code_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.ParameterCandidate.code
  exact RelCT.seq (two_post (body_ct M R K) (body_finish M R K))
    (two_map finishPublic (fun _ _ h => h) finish_ct)

theorem pc_constantTime (M : Mont) (R : R2Impl M) (K : Kernel) :
    ConstantTime isa pcContract.pre pcContract.pub
      (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) := by
  refine RelCT.constantTime ((code_ct M R K).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨candidateOfState s₁, ⟨h₁, rfl⟩, h₂, ?_⟩) fun _ _ h => h)
  obtain ⟨hsp, hbytes, r0, r1, r2, r3, r4, r5, a1, a2⟩ := hp
  have hrand := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hbytes)
  simp only [candidateOfState, r0, r1, r2, r3, r4, r5, a2, hsp, hrand]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
