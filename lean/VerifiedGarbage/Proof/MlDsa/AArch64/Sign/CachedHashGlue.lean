import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashPre

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg glue)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Proof.MlKem.AArch64 (Only wp_nil)

/-- The nonce lives in x9, which these seven argument moves preserve. -/
theorem hashGlue_ok (p : Params) (s : State) :
    WP isa (.block (glue (hashArgs p))) s (Args (hashArgs p) s) := by
  simp only [hashArgs,glue,Arg.instrs]
  refine lea_ok (by decide) 0 fun s0 h0 e0 => ?_
  refine lea_ok (by decide) oW1 fun s1 h1 e1 => ?_
  refine lea_ok (by decide) oCT fun s2 h2 e2 => ?_
  refine lea_ok (by decide) t1P.2 fun s3 h3 e3 => ?_
  refine lea_ok (by decide) oMS fun s4 h4 e4 => ?_
  refine lea_ok (by decide) 0 fun s5 h5 e5 => ?_
  refine lea_ok (by decide) t4P.2 fun s6 h6 e6 => ?_
  have h := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6
  apply wp_nil
  refine ⟨⟨?_,h.mem⟩,h.keep.mono (by decide)⟩
  simp only [List.mem_cons,List.not_mem_nil,forall_eq_or_imp,false_implies,implies_true,and_true,
    Arg.val,pa]
  and_intros
  · rw [h6.get .x0 (by decide),h5.get .x0 (by decide),h4.get .x0 (by decide),
      h3.get .x0 (by decide),h2.get .x0 (by decide),h1.get .x0 (by decide),e0]
  · rw [h6.get .x1 (by decide),h5.get .x1 (by decide),h4.get .x1 (by decide),
      h3.get .x1 (by decide),h2.get .x1 (by decide),e1,h0.get .x28 (by decide)]
  · rw [h6.get .x2 (by decide),h5.get .x2 (by decide),h4.get .x2 (by decide),
      h3.get .x2 (by decide),e2,h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x3 (by decide),h5.get .x3 (by decide),h4.get .x3 (by decide),e3,
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x4 (by decide),h5.get .x4 (by decide),e4,h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x5 (by decide),e5,h4.get .x9 (by decide),h3.get .x9 (by decide),
      h2.get .x9 (by decide),h1.get .x9 (by decide),h0.get .x9 (by decide)]
  · rw [e6,h5.get .x28 (by decide),h4.get .x28 (by decide),h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]

end VG.Proof.MlDsa.AArch64.Sign.Cached
