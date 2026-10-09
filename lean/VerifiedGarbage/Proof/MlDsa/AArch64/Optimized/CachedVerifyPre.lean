import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Pre
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The precondition of `verifyMessageCachedContract p AArch64.abi 16`. -/
structure CachedPre (p : Params) (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  rd : s.rd = [rKey s p.pkLen, rMsg s, rCtx s, ⟨s.gpr .x5, p.sigLen⟩, ⟨s.gpr .x7, 64⟩]
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
  trScr : Region.Disjoint ⟨s.gpr .x7, 64⟩ ⟨s.gpr .x6, mScrLen p⟩
  stkTr : (rStk s).Disjoint ⟨s.gpr .x7, 64⟩
  nTr : (s.gpr .x7).toNat + 64 ≤ 2 ^ 64
  digest : bytesAt s.mem (s.gpr .x7) 64 = pkTr (bytesAt s.mem (s.gpr .x0) p.pkLen)

theorem cachedPre_of {p : Params} {s : State}
    (h : (verifyMessageCachedContract p AArch64.abi 16).pre s) : CachedPre p s := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, AArch64.abi,
    AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a9, a10, a11, a12, a13,
    a15, a16, a17, a18, a19, a8.symm, a14, a20, a21⟩

/-- The cached verifier layout: the cached digest pointer occupies the otherwise unused randomness slot. -/
def cachedLay (p : Params) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .x0
  keyLen := p.pkLen
  msg := s.gpr .x1
  len := s.gpr .x2
  ctx := s.gpr .x3
  ctxLen := s.gpr .x4
  rnd := s.gpr .x7
  sig := s.gpr .x5
  scr := s.gpr .x6
  E := oE p
  rd := s.rd
  wr := s.wr

theorem cachedLay_X (p : Params) (s : State) : Within (cachedLay p s).XS ⟨s.gpr .x6, mScrLen p⟩ :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem cachedLay_ok {p : Params} (hp : p ∈ params) {s : State} (h : CachedPre p s) (h8 : (s.gpr .x4).toNat < 256) :
    (cachedLay p s).Ok := by
  have hX := cachedLay_X p s
  have hXs := hX.sub
  have hE := oE_lt hp
  refine ⟨h8, hE, pkLen_ge hp, h.sp, toNat_X (e := oE p) h.nScr (by rw [mScr_eq]),
    ⟨_, by simp [cachedLay, h.wr], hX⟩, by simp [cachedLay, h.rd], by simp [cachedLay, h.rd], by simp [cachedLay, h.rd],
    h.pkScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs, h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs,
    h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx, ?_⟩
  intro R hR
  simp only [cachedLay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
  have := h.nScr
  subst hR; simp only; omega

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
