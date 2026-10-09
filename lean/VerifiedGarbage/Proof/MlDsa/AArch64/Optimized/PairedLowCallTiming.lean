import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCall

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLowAt_tr {S : Nat} {nm : String} {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → PairedLowReady c secret out low work g B x ∧ PairedLowReady c secret out low work g B y ∧
      pa x c=pa y c ∧ pa x secret=pa y secret ∧ pa x out=pa y out ∧ pa x low=pa y low ∧
      pa x work=pa y work ∧ x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR") :
    RelCT isa Q (callAt nm (selected .r0) (pairedLowArgs c secret out low work g B)) fun _ _=>True := by
  refine callAtSyms_tr (pairedLow_callee S) (pairedLowArgs_ok hc hs ho hl hw) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ec,es,eo,el,ew,esp,et⟩ := hQ x y hp
  refine ⟨[⟨pa x c,1024⟩,⟨pa x secret,2048⟩,⟨x.syms "VG_MLDSA_INV_PAIR",4096⟩],
    [⟨pa x out,2048⟩,⟨pa x low,2048⟩,⟨pa x work,2176⟩],
    pairedLowAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ec,es,eo,el,ew,et]
    exact pairedLowAt_pre ry h2 hy2
  · sig_pub [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
    have h5x : x1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
    have h5y : y1.gpr .x5=BitVec.ofNat 64 g := h2.imm (by simp [pairedLowArgs])
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.r4 h1,Args.r4 h2,h5x,h5y,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,ec,es,eo,el,ew,rfl⟩
  · rw [ec,es,eo,el,ew,et]; exact ry.readable
  · rw [eo,el,ew]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Paired
