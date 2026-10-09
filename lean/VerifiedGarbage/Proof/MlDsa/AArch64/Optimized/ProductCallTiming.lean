import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductCall

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse

/-- Product coefficient values remain secret across the complete call. -/
theorem productAt_tr {S : Nat}
    {nm : String} {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → ProductCallReady out a b scratch x ∧ ProductCallReady out a b scratch y ∧
      pa x out=pa y out ∧ pa x a=pa y a ∧ pa x b=pa y b ∧ pa x scratch=pa y scratch ∧
      x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (callAt nm (staticCode true) (productArgs out a b scratch)) fun _ _ => True := by
  refine callAtSyms_tr (productRaw_callee S) (productArgs_ok ho ha hb hs) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,eo,ea,eb,es,esp,et⟩ := hQ x y hp
  refine ⟨[outputRegion (pa x a),outputRegion (pa x b),
    tableRegion (x.syms "VG_MLDSA_INV_FOLDED")],[outputRegion (pa x out),outputRegion (pa x scratch)],
    productAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb,es,et]
    exact productAt_pre ry h2 hy2
  · sig_pub [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,eo,ea,eb,es⟩
  · rw [eo,ea,eb,es,et]; exact ry.readable
  · rw [eo,es]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
