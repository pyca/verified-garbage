import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRoots

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open Message.Optimized (rootRegions)

structure VPre (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [rKey s p.pkLen, rMsg s, rCtx s, ⟨s.gpr .x5, p.sigLen⟩] ++ rootRegions s
  wr : s.wr = [⟨s.gpr .x6, mScrLen p⟩]
  pkScr : (rKey s p.pkLen).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  msgScr : (rMsg s).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  ctxScr : (rCtx s).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  sigScr : Region.Disjoint ⟨s.gpr .x5, p.sigLen⟩ ⟨s.gpr .x6, mScrLen p⟩
  stkPk : (rStk s).Disjoint (rKey s p.pkLen)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkSig : (rStk s).Disjoint ⟨s.gpr .x5, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨s.gpr .x6, mScrLen p⟩
  nPk : (s.gpr .x0).toNat + p.pkLen ≤ 2 ^ 64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  nSig : (s.gpr .x5).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (s.gpr .x6).toNat + mScrLen p ≤ 2 ^ 64
  roots : StaticRoots 16 s

theorem vPre_of {p : Params} {s : State}
    (h : (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre s) : VPre p s := by
  sig_pre [verifyMessageContract,verifyMessageSig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow,
    List.range,List.range.loop] at h
  obtain ⟨hsp,hd,hf,hi,hff,hfw,hfs,hif,hiw,his,ht,hw,d1,d2,d3,d4,
    k1,k2,k3,k4,k5,n1,n2,n3,n4,n5⟩ := h
  have hrd : s.rd=[rKey s p.pkLen,rMsg s,rCtx s,⟨s.gpr .x5,p.sigLen⟩]++rootRegions s := by
    rw [← List.take_append_drop (s.rd.length-2) s.rd,ht,hd]
  refine ⟨hsp,hrd,hw,d1,d2,d3,d4,k1,k2,k3,k4,k5,n1,n2,n3,n4,n5,
    ⟨⟨hf,hff,?_,hfw,hfs⟩,⟨hi,hif,?_,hiw,his⟩⟩⟩
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]; simp [rootRegions]
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]; simp [rootRegions]

theorem vlay_ok {p : Params} (hp : p ∈ params) {s : State} (h : VPre p s) (h8 : (s.gpr .x4).toNat < 256) :
    (vlay p s).Ok := by
  have hX := vlay_X p s
  have hXs := hX.sub
  have hE := oE_lt hp
  refine ⟨h8, hE, pkLen_ge hp, h.sp, toNat_X (e := oE p) h.nScr (by rw [mScr_eq]),
    ⟨_, by simp [vlay, h.wr], hX⟩, by simp [vlay, h.rd], by simp [vlay, h.rd], by simp [vlay, h.rd],
    h.pkScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs, h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs,
    h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx, ?_⟩
  intro R hR
  simp only [vlay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
  have := h.nScr
  subst hR; simp only; omega

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
