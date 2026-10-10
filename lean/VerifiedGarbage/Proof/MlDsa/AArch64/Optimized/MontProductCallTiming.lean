import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

/-! ## From `MontProductCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) : CalleeOk S code (montProductContract abi) :=
  ⟨verified.1,verified.2.1,Nat.zero_le _⟩

abbrev args (out a b : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b)]

structure Ready (out a b : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  outA : (polyRegion (pa s out)).Disjoint (polyRegion (pa s a))
  outB : (polyRegion (pa s out)).Disjoint (polyRegion (pa s b))
  positiveA : PositiveReduced s.mem (pa s a)
  positiveB : PositiveReduced s.mem (pa s b)
  readable : Covers [polyRegion (pa s a),polyRegion (pa s b),polyRegion (pa s out)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s out)] s.wr

theorem at_pre {s s1 : State} {out a b : Ptr}
    (h : Ready out a b s) (h1 : Args (args out a b) s s1) :
    (montProductContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s a),polyRegion (pa s b)] [polyRegion (pa s out)]) := by
  sig_pre [montProductContract,montProductSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  exact ⟨trivial,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,h.positiveA,h.positiveB⟩

theorem args_ok {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : Ready out a b s) :
    WP isa (callAt nm code (args out a b)) s fun t =>
      Post S s t [polyRegion (pa s out)] ∧
      PolyIs t.mem (pa s out) (montgomeryMultiplyNTT (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b))) := by
  refine WP.mono (callAtSyms_ok hS (callee S) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [montProductContract,montProductSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

/-! ## From `MontProductCallTiming.lean` -/

section

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

end
