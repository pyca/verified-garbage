import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_callee (S : Nat) :
    CalleeOk S (selected .z) (pairedZContract (abi.withConsts pairedConsts)) := by
  refine ⟨pairedZ_verified.1,pairedZ_verified.2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

abbrev pairedZArgs (c secret y unused work : Ptr) (gamma bound : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr c),(.x1,.ptr secret),(.x2,.ptr y),(.x3,.ptr unused),(.x4,.ptr work),
    (.x5,.imm gamma),(.x6,.imm bound)]

structure PairedZReady (c secret y work : Ptr) (bound : Nat) (s : State) : Prop where
  cFit : (pa s c).toNat+1024≤2^64
  secretFit : (pa s secret).toNat+2048≤2^64
  yFit : (pa s y).toNat+2048≤2^64
  workFit : (pa s work).toNat+2176≤2^64
  held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64
  tableApart : ∀r∈[⟨pa s y,2048⟩,⟨pa s work,2176⟩],
    (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  cY : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s y,2048⟩
  cWork : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s work,2176⟩
  secretY : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s y,2048⟩
  secretWork : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  yWork : (⟨pa s y,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  products : pairedProductsReduced s.mem (pa s c) (pa s secret)
  data : ∀j<2,Reduced s.mem (pairPolyPtr (pa s y) j)
  boundLow : 1≤bound
  boundHigh : bound≤524288
  readable : Covers ([⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]++
    [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) (s.rd++s.wr)
  writable : Covers [⟨pa s y,2048⟩,⟨pa s work,2176⟩] s.wr

theorem pairedZAt_pre {s s1 : State} {c secret y unused work : Ptr} {gamma bound : Nat}
    (h : PairedZReady c secret y work bound s)
    (h1 : Args (pairedZArgs c secret y unused work gamma bound) s s1) (hy : s1.syms=s.syms) :
    (pairedZContract (abi.withConsts pairedConsts)).pre
      (s1.callEntry.withRegions [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
        [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) := by
  have hb : s1.gpr .x6=BitVec.ofNat 64 bound := h1.imm (by simp [pairedZArgs])
  have hb32 := imm32 (v:=bound) (by have := h.boundHigh; omega)
  sig_pre [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r4 h1,Args.mem h1,Arg.val,hb,hb32]
  exact ⟨True.intro,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),True.intro,True.intro,h.cY,h.cWork,h.secretY,h.secretWork,
    h.yWork,h.cFit,h.secretFit,h.yFit,h.workFit,h.products,h.data,h.boundLow,h.boundHigh⟩

theorem pairedZArgs_ok {c secret y unused work : Ptr} {gamma bound : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr unused).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈pairedZArgs c secret y unused work gamma bound,x.2.Ok ∧ x.1∈argRegs := by
  simp only [pairedZArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hc,by simp⟩
  · exact ⟨hs,by simp⟩
  · exact ⟨hy,by simp⟩
  · exact ⟨hu,by simp⟩
  · exact ⟨hw,by simp⟩
  · exact ⟨True.intro,by simp⟩
  · exact ⟨True.intro,by simp⟩

theorem pairedZAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State}
    {c secret y unused work : Ptr} {gamma bound : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr unused).Ok) (hw : (Arg.ptr work).Ok)
    (h : PairedZReady c secret y work bound s) :
    WP isa (callAt nm (selected .z) (pairedZArgs c secret y unused work gamma bound)) s fun t =>
      Post S s t [⟨pa s y,2048⟩,⟨pa s work,2176⟩] ∧
      (∀j<2,CenteredReduced t.mem (pairPolyPtr (pa s y) j) ∧
        signedPolyAt t.mem (pairPolyPtr (pa s y) j)=add (polyAt s.mem (pairPolyPtr (pa s y) j))
          (pairedProduct s.mem (pa s c) (pa s secret) j)) ∧
      (t.gpr .x0).setWidth 32=if normRq ((List.range 2).map fun j =>
        add (polyAt s.mem (pairPolyPtr (pa s y) j)) (pairedProduct s.mem (pa s c) (pa s secret) j))<bound then 1 else 0 := by
  refine WP.mono (callAtSyms_ok hS (pairedZ_callee S) (pairedZArgs_ok hc hs hy hu hw) (by simp)
    (fun s1 h1 hy => pairedZAt_pre h h1 hy) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  have hb : s1.gpr .x6=BitVec.ofNat 64 bound := h1.imm (by simp [pairedZArgs])
  have hb32 := imm32 (v:=bound) (by have := h.boundHigh; omega)
  sig_post [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,hb,hb32] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired
