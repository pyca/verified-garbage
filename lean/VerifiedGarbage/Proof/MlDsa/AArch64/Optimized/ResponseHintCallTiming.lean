import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCall

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem hintNormAt_tr {S : Nat} {nm : String} {low ct high : Ptr} {g : Nat}
    (hl : (Arg.ptr low).Ok) (hc : (Arg.ptr ct).Ok) (hh : (Arg.ptr high).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → HintNormReady low ct high g x ∧ HintNormReady low ct high g y ∧
      pa x low=pa y low ∧ pa x ct=pa y ct ∧ pa x high=pa y high ∧ x.sp=y.sp) :
    RelCT isa Q (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.hintNorm
      (hintNormArgs low ct high g)) fun _ _=>True := by
  refine callAt_tr (hintNorm_callee S) (hintNormArgs_ok hl hc hh) (by simp)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨rx,ry,ew,ec,el,esp⟩ := hQ x y hp
  refine ⟨[polyRegion (pa x ct),polyRegion (pa x high)],[polyRegion (pa x low)],hintNormAt_pre rx h1,?_,?_,
    rx.readable,rx.writable,?_,?_⟩
  · rw [ew,ec,el]; exact hintNormAt_pre ry h2
  · sig_pub [hintNormContract,hintNormSig,abi,argRegs]
    rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,
      Args.r0 h2,Args.r1 h2,Args.r2 h2,Args.r3 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,ew,ec,el,rfl⟩
  · rw [ew,ec,el]; exact ry.readable
  · rw [ew]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Response
