import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductCall

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem at_tr {S : Nat} {nm : String} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → Ready out a b x ∧ Ready out a b z ∧
      pa x out=pa z out ∧ pa x a=pa z a ∧ pa x b=pa z b ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm code (args out a b)) fun _ _=>True := by
  refine callAtSyms_tr (callee S) (args_ok ho ha hb) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,eo,ea,eb,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x a),polyRegion (pa x b)],[polyRegion (pa x out)],
    at_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb]; exact at_pre rz h2
  · sig_pub [montProductContract,montProductSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,eo,ea,eb⟩
  · rw [eo,ea,eb]; exact rz.readable
  · rw [eo]; exact rz.writable
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct
