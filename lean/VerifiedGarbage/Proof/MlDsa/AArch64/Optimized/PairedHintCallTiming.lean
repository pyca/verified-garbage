import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintCall

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHintAt_tr {S : Nat} {nm : String} {c secret out high work : Ptr} {gamma : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hu : (Arg.ptr high).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → PairedHintReady c secret out high work gamma x ∧ PairedHintReady c secret out high work gamma y ∧
      pa x c=pa y c ∧ pa x secret=pa y secret ∧ pa x out=pa y out ∧ pa x high=pa y high ∧
      pa x work=pa y work ∧ x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR") :
    RelCT isa Q (callAt nm (selected .h) (pairedHintArgs c secret out high work gamma)) fun _ _ => True := by
  refine callAtSyms_tr (pairedHint_callee S) (pairedHintArgs_ok hc hs ho hu hw) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ec,es,eo,eu,ew,esp,et⟩ := hQ x y hp
  refine ⟨[⟨pa x c,1024⟩,⟨pa x secret,2048⟩,⟨pa x high,2048⟩,⟨x.syms "VG_MLDSA_INV_PAIR",4096⟩],
    [⟨pa x out,2048⟩,⟨pa x work,2176⟩],pairedHintAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ec,es,eo,eu,ew,et]
    exact pairedHintAt_pre ry h2 hy2
  · sig_pub [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.r4 h1,Args.r4 h2,Args.sp h1,Args.sp h2]
    have h5x : x1.gpr .x5=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
    have h5y : y1.gpr .x5=BitVec.ofNat 64 gamma := h2.imm (by simp [pairedHintArgs])
    rw [h5x,h5y]
    exact ⟨esp,et,ec,es,eo,eu,ew,rfl⟩
  · rw [ec,es,eo,eu,ew,et]; exact ry.readable
  · rw [eo,ew]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Paired
