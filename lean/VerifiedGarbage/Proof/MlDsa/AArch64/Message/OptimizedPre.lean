import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry

namespace VG.Proof.MlDsa.AArch64.Message.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message

abbrev rootRegions (s : State) : List Region :=
  [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩]

structure SPre (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [rKey s p.skLen, rMsg s, rCtx s, ⟨s.gpr .x5, 32⟩] ++ rootRegions s
  wr : s.wr = [⟨s.gpr .x6, p.sigLen⟩, ⟨s.gpr .x7, mScrLen p⟩]
  skSig : (rKey s p.skLen).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  skScr : (rKey s p.skLen).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  msgSig : (rMsg s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  msgScr : (rMsg s).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  ctxSig : (rCtx s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  ctxScr : (rCtx s).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  rndSig : Region.Disjoint ⟨s.gpr .x5, 32⟩ ⟨s.gpr .x6, p.sigLen⟩
  rndScr : Region.Disjoint ⟨s.gpr .x5, 32⟩ ⟨s.gpr .x7, mScrLen p⟩
  sigScr : Region.Disjoint ⟨s.gpr .x6, p.sigLen⟩ ⟨s.gpr .x7, mScrLen p⟩
  stkSk : (rStk s).Disjoint (rKey s p.skLen)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkRnd : (rStk s).Disjoint ⟨s.gpr .x5, 32⟩
  stkSig : (rStk s).Disjoint ⟨s.gpr .x6, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨s.gpr .x7, mScrLen p⟩
  nSk : (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64
  nMsg : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  nRnd : (s.gpr .x5).toNat + 32 ≤ 2 ^ 64
  nSig : (s.gpr .x6).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (s.gpr .x7).toNat + mScrLen p ≤ 2 ^ 64

  roots : StaticRoots 16 s

 theorem sPre_of {p : Params} {s : State}
    (h : (signMessageContract p (abi.withConsts signRootConsts) 16).pre s) : SPre p s := by
  sig_pre [signMessageContract,signMessageSig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow,
    List.range,List.range.loop] at h
  obtain ⟨hsp,hd,hf,hi,hff,hfw,hfs,hif,hiw,his,ht,hw,d1,d2,d3,d4,d5,d6,d7,d8,d9,
    k1,k2,k3,k4,k5,k6,n1,n2,n3,n4,n5,n6⟩ := h
  have hrd : s.rd=[rKey s p.skLen,rMsg s,rCtx s,⟨s.gpr .x5,32⟩]++rootRegions s := by
    rw [← List.take_append_drop (s.rd.length-2) s.rd,ht,hd]
  refine ⟨hsp,hrd,hw,d1,d2,d3,d4,d5,d6,d7,d8,d9,k1,k2,k3,k4,k5,k6,
    n1,n2,n3,n4,n5,n6,⟨⟨hf,hff,?_,hfw,hfs⟩,⟨hi,hif,?_,hiw,his⟩⟩⟩
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]; simp [rootRegions]
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,?_,Region.contains_self _ _⟩
    rw [hrd]; simp [rootRegions]

theorem slay_ok {p : Params} (hp : p ∈ params) {s : State} (h : SPre p s) (h8 : (s.gpr .x4).toNat < 256) :
    (slay p s).Ok := by
  have hX := slay_X p s
  have hXs := hX.sub
  have hE := oE_lt hp
  refine ⟨h8, hE, skLen_ge hp, h.sp, toNat_X (e := oE p) h.nScr (by rw [mScr_eq]),
    ⟨_, by simp [slay, h.wr], hX⟩, by simp [slay, h.rd], by simp [slay, h.rd], by simp [slay, h.rd],
    h.skScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs, h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs,
    h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx, ?_⟩
  intro R hR
  simp only [slay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
  have := h.nSig; have := h.nScr
  rcases hR with rfl | rfl <;> simp only <;> omega

end VG.Proof.MlDsa.AArch64.Message.Optimized
