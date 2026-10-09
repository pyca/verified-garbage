import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_callee (S : Nat) : CalleeOk S (selected .r0)
    (pairedLowContract (abi.withConsts pairedConsts)) :=
  ⟨pairedLow_verified.1,pairedLow_verified.2.1,Nat.zero_le _⟩

abbrev pairedLowArgs (c secret out low work : Ptr) (g B : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr c),(.x1,.ptr secret),(.x2,.ptr out),(.x3,.ptr low),(.x4,.ptr work),(.x5,.imm g),(.x6,.imm B)]

structure PairedLowReady (c secret out low work : Ptr) (g B : Nat) (s : State) : Prop where
  cFit : (pa s c).toNat+1024≤2^64
  secretFit : (pa s secret).toNat+2048≤2^64
  outFit : (pa s out).toNat+2048≤2^64
  lowFit : (pa s low).toNat+2048≤2^64
  workFit : (pa s work).toNat+2176≤2^64
  held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64
  tableApart : ∀r∈[⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩],
    (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  cOut : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s out,2048⟩
  cLow : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s low,2048⟩
  cWork : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s work,2176⟩
  secretOut : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s out,2048⟩
  secretLow : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s low,2048⟩
  secretWork : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  outLow : (⟨pa s out,2048⟩:Region).Disjoint ⟨pa s low,2048⟩
  outWork : (⟨pa s out,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  lowWork : (⟨pa s low,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  products : pairedProductsReduced s.mem (pa s c) (pa s secret)
  canonical : ∀j<2,Reduced s.mem (pairPolyPtr (pa s out) j)
  gamma : g∈gamma2s
  boundPos : 1≤B
  boundMax : B≤524288
  readable : Covers [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩,
    ⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] (s.rd++s.wr)
  writable : Covers [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] s.wr

theorem PairedLowReady.gamma_lt {c secret out low work : Ptr} {g B : Nat} {s : State}
    (h : PairedLowReady c secret out low work g B s) : g<2^32 := by
  have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gamma
  rcases hg with rfl|rfl <;> decide

theorem pairedLowAt_pre {s s1 : State} {c secret out low work : Ptr} {g B : Nat}
    (h : PairedLowReady c secret out low work g B s)
    (h1 : Args (pairedLowArgs c secret out low work g B) s s1) (hy : s1.syms=s.syms) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre
      (s1.callEntry.withRegions [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
        [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩]) := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  have h5 : s1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
  have h6 : s1.gpr .x6=BitVec.ofNat 64 B := h1.imm (by simp [pairedLowArgs])
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,h5,h6,
    Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  rw [hg,hB]
  exact ⟨trivial,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableApart _ (by simp),
    trivial,trivial,h.cOut,h.cLow,h.cWork,h.secretOut,h.secretLow,h.secretWork,h.outLow,h.outWork,h.lowWork,
    h.cFit,h.secretFit,h.outFit,h.lowFit,h.workFit,h.products,h.canonical,h.gamma,h.boundPos,h.boundMax⟩

theorem pairedLowArgs_ok {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈pairedLowArgs c secret out low work g B,x.2.Ok ∧ x.1∈argRegs := by
  simp only [pairedLowArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨hc,by simp⟩
  · exact ⟨hs,by simp⟩
  · exact ⟨ho,by simp⟩
  · exact ⟨hl,by simp⟩
  · exact ⟨hw,by simp⟩
  · exact ⟨trivial,by simp⟩
  · exact ⟨trivial,by simp⟩

def PairedLowPost (g B : Nat) (m m' : Mem) (c secret out low : Addr) (r : BitVec 32) : Prop :=
  (∀j<2,∀i<n,
    (coeffAt m' (pairPolyPtr out j) i).toNat=(highBits g (pairedDifference m c secret out j)[i]!).toNat ∧
    (coeffAt m' (pairPolyPtr low j) i).toInt=lowBits g (pairedDifference m c secret out j)[i]!) ∧
  r=if normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m c secret out j))<B then 1 else 0

theorem pairedLowAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State}
    {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok)
    (h : PairedLowReady c secret out low work g B s) :
    WP isa (callAt nm (selected .r0) (pairedLowArgs c secret out low work g B)) s fun t =>
      Post S s t [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] ∧
      PairedLowPost g B s.mem t.mem (pa s c) (pa s secret) (pa s out) (pa s low) ((t.gpr .x0).setWidth 32) := by
  refine WP.mono (callAtSyms_ok hS (pairedLow_callee S)
    (pairedLowArgs_ok hc hs ho hl hw) (by simp)
    (fun s1 h1 hy => pairedLowAt_pre h h1 hy) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at hq
  have h5 : s1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
  have h6 : s1.gpr .x6=BitVec.ofNat 64 B := h1.imm (by simp [pairedLowArgs])
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,h5,h6,Args.mem h1] at hq
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  simpa only [PairedLowPost,Arg.val,hg,hB] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired
