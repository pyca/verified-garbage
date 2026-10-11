import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIOCT

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64

/-- The computation leaks the same in runs with the same public data, given
that the last multiplication does (`hfinal`). -/
theorem rest_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    RelCT isa (Two DRel) (Folded.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp [wordIn]) (by simp [phases]) (RelCT.seq wordSetup_ct ?_)
  refine RelCT.seqs_append (by simp [phases]) (by simp [wordOutStepsArr])
    (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (RelCT.seq pdExp_ct (pdFinal_ct hfinal))
  · exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub))
      (fun _ _ h => dd_wordOPre h) wordOut_ct

end VG.Proof.Bignum.X86_64.FoldedPublic
