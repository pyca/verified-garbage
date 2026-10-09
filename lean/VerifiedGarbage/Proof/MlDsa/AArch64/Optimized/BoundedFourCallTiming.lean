import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCall

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)

theorem samplerAt_tr {S : Nat} (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {nm : String} {seed out work : Ptr}
    (hs : (Arg.ptr seed).Ok) (ho : (Arg.ptr out).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State→State→Prop}
    (hQ : ∀s t,Q s t→CallReady seed out work s ∧ CallReady seed out work t ∧
      pa s seed=pa t seed ∧ pa s out=pa t out ∧ pa s work=pa t work ∧ s.sp=t.sp ∧
      rejBoundedFourLeak η s.mem (pa s seed)=rejBoundedFourLeak η t.mem (pa t seed)) :
    RelCT isa Q (callAt nm (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (samplerArgs seed out work)) (fun _ _=>True) := by
  refine callAtSyms_tr (sampler_callee S sha3 hη) (samplerArgs_ok hs ho hw) (by simp)
    fun s t s1 t1 hp h1 h2 _ _=>?_
  obtain ⟨rs,rt,es,eo,ew,esp,el⟩:=hQ s t hp
  refine ⟨[⟨pa s seed,264⟩],[⟨pa s out,4096⟩,⟨pa s work,8192⟩],
    samplerAt_pre hη rs h1,?_,?_,rs.readable,rs.writable,?_,?_⟩
  · rw [es,eo,ew]; exact samplerAt_pre hη rt h2
  · sig_pub [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.sp h1,Args.sp h2,Args.mem h1,Args.mem h2]
    exact ⟨esp,el,es,eo,ew⟩
  · rw [es,eo,ew]; exact rt.readable
  · rw [eo,ew]; exact rt.writable

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
