import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_callee (S : Nat) :
    CalleeOk S (selected .h) (pairedHintContract (abi.withConsts pairedConsts)) := by
  refine ⟨pairedHint_verified.1,pairedHint_verified.2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

abbrev pairedHintArgs (c secret y high work : Ptr) (gamma : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr c),(.x1,.ptr secret),(.x2,.ptr y),(.x3,.ptr high),(.x4,.ptr work),
    (.x5,.imm gamma),(.x6,.imm gamma)]

structure PairedHintReady (c secret y high work : Ptr) (gamma : Nat) (s : State) : Prop where
  cFit : (pa s c).toNat+1024≤2^64
  secretFit : (pa s secret).toNat+2048≤2^64
  yFit : (pa s y).toNat+2048≤2^64
  highFit : (pa s high).toNat+2048≤2^64
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
  yHigh : (⟨pa s y,2048⟩:Region).Disjoint ⟨pa s high,2048⟩
  highWork : (⟨pa s high,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  products : pairedProductsReduced s.mem (pa s c) (pa s secret)
  gammaOk : gamma∈gamma2s
  data : ∀j<2,ResponseDecomposed s.mem (pairPolyPtr (pa s y) j) (pairPolyPtr (pa s high) j) gamma
  readable : Covers ([⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨pa s high,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]++
    [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) (s.rd++s.wr)
  writable : Covers [⟨pa s y,2048⟩,⟨pa s work,2176⟩] s.wr

theorem pairedHintAt_pre {s s1 : State} {c secret y high work : Ptr} {gamma : Nat}
    (h : PairedHintReady c secret y high work gamma s)
    (h1 : Args (pairedHintArgs c secret y high work gamma) s s1) (hy : s1.syms=s.syms) :
    (pairedHintContract (abi.withConsts pairedConsts)).pre
      (s1.callEntry.withRegions [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨pa s high,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
        [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) := by
  have hg : s1.gpr .x5=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
  have hb : s1.gpr .x6=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
  have hg32 := imm32 (v:=gamma) (by have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gammaOk; rcases hg with rfl|rfl <;> decide)
  sig_pre [pairedHintContract,pairedHintSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.mem h1,Arg.val,hg,hb,hg32]
  exact ⟨True.intro,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),True.intro,True.intro,h.cY,h.cWork,h.secretY,h.secretWork,
    h.yHigh,h.yWork,h.highWork,h.cFit,h.secretFit,h.yFit,h.highFit,h.workFit,h.products,h.gammaOk,True.intro,h.data⟩

theorem pairedHintArgs_ok {c secret y high work : Ptr} {gamma : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr high).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈pairedHintArgs c secret y high work gamma,x.2.Ok ∧ x.1∈argRegs := by
  simp only [pairedHintArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hc,by simp⟩
  · exact ⟨hs,by simp⟩
  · exact ⟨hy,by simp⟩
  · exact ⟨hu,by simp⟩
  · exact ⟨hw,by simp⟩
  · exact ⟨True.intro,by simp⟩
  · exact ⟨True.intro,by simp⟩

theorem pairedHintAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State}
    {c secret y high work : Ptr} {gamma : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr high).Ok) (hw : (Arg.ptr work).Ok)
    (h : PairedHintReady c secret y high work gamma s) :
    WP isa (callAt nm (selected .h) (pairedHintArgs c secret y high work gamma)) s fun t =>
      Post S s t [⟨pa s y,2048⟩,⟨pa s work,2176⟩] ∧
      HintIs t.mem (pa s y) 2 ((List.range 2).map fun j => pairedHintPoly s.mem (pa s c) (pa s secret) (pa s y) (pa s high) gamma j) ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j => pairedHintPoly s.mem (pa s c) (pa s secret) (pa s y) (pa s high) gamma j)+
        if normRq ((List.range 2).map fun j => pairedProduct s.mem (pa s c) (pa s secret) j)<gamma then 4294967296 else 0) := by
  refine WP.mono (callAtSyms_ok hS (pairedHint_callee S) (pairedHintArgs_ok hc hs hy hu hw) (by simp)
    (fun s1 h1 hy => pairedHintAt_pre h h1 hy) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  have hg : s1.gpr .x5=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
  have hg32 := imm32 (v:=gamma) (by have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gammaOk; rcases hg with rfl|rfl <;> decide)
  sig_post [pairedHintContract,pairedHintSig,abi,argRegs,pairedConsts_eq,Abi.withConsts] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1,hg,hg32] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired
