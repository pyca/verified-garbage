module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareR2CT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareConstantsCT

/-! # FFDH parameter generation on x86-64: timing of complete modulus preparation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

theorem prepareModulus_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two PrepareBefore) (prepareModulus M.mm R.code) fun _ _ => True := by
  unfold prepareModulus
  exact RelCT.seq (two_post (prepareR2_ct M R) (prepareR2_ready M R))
    (RelCT.seq (two_post (prepareConstants_ct M) (prepareConstants_header M))
      (two_map PreparePublic.inner (fun _ _ h => h.header) inner_expSetup_ct))

end VG.Proof.Ffdh.X86_64.ParameterCandidate
