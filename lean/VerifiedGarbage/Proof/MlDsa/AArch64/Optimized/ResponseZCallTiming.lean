import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZCall

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem addNormAt_tr {S : Nat} {nm : String} {y cs : Ptr} {B : Nat}
    (hy : (Arg.ptr y).Ok) (hc : (Arg.ptr cs).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → AddNormReady y cs B x ∧ AddNormReady y cs B z ∧
      pa x y=pa z y ∧ pa x cs=pa z cs ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      (addNormArgs y cs B)) fun _ _=>True := by
  refine callAtSyms_tr (addNorm_callee S) (addNormArgs_ok hy hc) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,ey,ec,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x cs)],[polyRegion (pa x y)],addNormAt_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ey,ec]; exact addNormAt_pre rz h2
  · sig_pub [addNormContract,addNormSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,ey,ec,rfl⟩
  · rw [ey,ec]; exact rz.readable
  · rw [ey]; exact rz.writable

end VG.Proof.MlDsa.AArch64.Optimized.Response
