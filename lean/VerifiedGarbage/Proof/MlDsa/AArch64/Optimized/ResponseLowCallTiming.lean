import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCall

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem subLowNormAt_tr {S : Nat} {nm : String} {w cs low : Ptr} {g B : Nat}
    (hw : (Arg.ptr w).Ok) (hc : (Arg.ptr cs).Ok) (hl : (Arg.ptr low).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → SubLowNormReady w cs low g B x ∧ SubLowNormReady w cs low g B y ∧
      pa x w=pa y w ∧ pa x cs=pa y cs ∧ pa x low=pa y low ∧ x.sp=y.sp) :
    RelCT isa Q (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
      (subLowNormArgs w cs low g B)) fun _ _=>True := by
  refine callAt_tr (subLowNorm_callee S) (subLowNormArgs_ok hw hc hl) (by simp)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨rx,ry,ew,ec,el,esp⟩ := hQ x y hp
  refine ⟨[polyRegion (pa x cs)],[polyRegion (pa x w),polyRegion (pa x low)],subLowNormAt_pre rx h1,?_,?_,
    rx.readable,rx.writable,?_,?_⟩
  · rw [ew,ec,el]; exact subLowNormAt_pre ry h2
  · sig_pub [subLowNormContract,subLowNormSig,abi,argRegs]
    rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,
      Args.r0 h2,Args.r1 h2,Args.r2 h2,Args.r3 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,ew,ec,el,rfl⟩
  · rw [ew,ec,el]; exact ry.readable
  · rw [ew,el]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Response
