module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateLoadState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateLoadState

/-! # Constant time of complete candidate and generator-exponent arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem candidateFirst_ct : RelCT isa (Two CandidateInput)
    (seqs (loadA 0 16 17)) (Two CandidateFirst) :=
  two_post (two_map CandidatePublic.xLoad (fun _ _ h => h.x)
    (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateFirst_state h)

theorem candidateSecond_ct : RelCT isa (Two CandidateFirst)
    (seqs (loadA 2 18 19)) (Two CandidateLoaded) :=
  two_post (two_map CandidatePublic.qLoad (fun _ _ h => h.q)
    (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateSecond_state h)

theorem candidateDouble_ct : RelCT isa (Two CandidateLoaded)
    (Impl.Dsa.X86_64.Generation.doubleArray 2)
    (Two fun (p : CandidatePublic) s => ReductionStart p.reduction s) :=
  doubleArray_ct CandidatePublic.B CandidatePublic.Z CandidatePublic.w
    (fun _ _ h => h.ws) 2 (by taint_decide) (fun _ _ h => candidateDouble_state h)

theorem candidateArithmetic_ct : RelCT isa (Two CandidateInput)
    Impl.Dsa.X86_64.Generation.candidateArithmetic (fun _ _ => True) :=
  RelCT.seq candidateFirst_ct (RelCT.seq candidateSecond_ct (RelCT.seq candidateDouble_ct
    (two_map CandidatePublic.reduction (fun _ _ h => h) reduceExponent_ct)))

end VG.Proof.Dsa.X86_64.Generation
