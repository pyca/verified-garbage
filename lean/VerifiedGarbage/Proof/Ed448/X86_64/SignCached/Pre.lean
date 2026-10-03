import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Layout
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# Ed448 signing with a cached public key on x86-64: the precondition and the layout

The precondition of `signCachedContract X86_64.abi 464`, spelled out
(`SPre`), and the layout of a run from a state satisfying it (`slay`, `Ok` by
`slay_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64

section
variable (s : State)

abbrev sOut : Region := ⟨s.gpr .rdi, 114⟩
abbrev sSeed : Region := ⟨s.gpr .rsi, 57⟩
abbrev sPk : Region := ⟨s.gpr .rdx, 57⟩
abbrev sCtx : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev sMsg : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
abbrev sArgs : Region := ⟨stackArgAddr s 0, 16⟩
abbrev sScr : Region := ⟨stackArg s 1, 8192⟩
abbrev sRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev sStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 464, 464⟩

end

/-- The precondition of `signCachedContract X86_64.abi 464`. -/
structure SPre (s : State) : Prop where
  sp : 464 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [sSeed s, sPk s, sCtx s, sMsg s, sArgs s]
  wr : s.wr = [sOut s, sScr s]
  outSeed : (sOut s).Disjoint (sSeed s)
  outPk : (sOut s).Disjoint (sPk s)
  outCtx : (sOut s).Disjoint (sCtx s)
  outMsg : (sOut s).Disjoint (sMsg s)
  outScr : (sOut s).Disjoint (sScr s)
  outArgs : (sOut s).Disjoint (sArgs s)
  seedScr : (sSeed s).Disjoint (sScr s)
  pkScr : (sPk s).Disjoint (sScr s)
  ctxScr : (sCtx s).Disjoint (sScr s)
  msgScr : (sMsg s).Disjoint (sScr s)
  scrArgs : (sScr s).Disjoint (sArgs s)
  retOut : (sRet s).Disjoint (sOut s)
  retSeed : (sRet s).Disjoint (sSeed s)
  retPk : (sRet s).Disjoint (sPk s)
  retCtx : (sRet s).Disjoint (sCtx s)
  retMsg : (sRet s).Disjoint (sMsg s)
  retScr : (sRet s).Disjoint (sScr s)
  retArgs : (sRet s).Disjoint (sArgs s)
  stkOut : (sStk s).Disjoint (sOut s)
  stkSeed : (sStk s).Disjoint (sSeed s)
  stkPk : (sStk s).Disjoint (sPk s)
  stkCtx : (sStk s).Disjoint (sCtx s)
  stkMsg : (sStk s).Disjoint (sMsg s)
  stkScr : (sStk s).Disjoint (sScr s)
  stkArgs : (sStk s).Disjoint (sArgs s)
  nOut : (s.gpr .rdi).toNat + 114 ≤ 2 ^ 64
  nSeed : (s.gpr .rsi).toNat + 57 ≤ 2 ^ 64
  nPk : (s.gpr .rdx).toNat + 57 ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nMsg : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  nScr : (stackArg s 1).toNat + 8192 ≤ 2 ^ 64
  pk : Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 57)
  ctxLe : (s.gpr .r8).toNat ≤ 255

theorem sPre_of {s : State} (h : (Spec.Ed448.signCachedContract X86_64.abi 464).pre s) : SPre s := by
  sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
    X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩

/-- The layout of a run of `signCached` from `s`. -/
def slay (s : State) : Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 464
  out := s.gpr .rdi
  seed := s.gpr .rsi
  pk := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  msg := s.gpr .r9
  len := stackArg s 0
  scr := stackArg s 1
  rd := s.rd
  wr := s.wr

theorem slay_B (s : State) : (slay s).B + BitVec.ofNat 64 464 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem slay_ok {s : State} (h : SPre s) : (slay s).Ok := by
  have eR : (slay s).RET = sRet s := by
    show (⟨(slay s).B + BitVec.ofNat 64 464, 8⟩ : Region) = _
    rw [slay_B]
  refine ⟨by have := h.ctxLe; simp only [slay]; omega, ?_, h.wr, by simp [slay, h.rd], by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.seedScr.symm, h.pkScr.symm, h.ctxScr.symm, h.msgScr.symm,
    h.outScr.symm, h.outSeed, h.outPk, h.outCtx, h.outMsg, h.stkScr, h.stkOut, h.stkSeed, h.stkPk, h.stkCtx,
    h.stkMsg, by rw [eR]; exact h.retScr, by rw [eR]; exact h.retOut, h.nOut, h.nSeed, h.nPk, h.nCtx, h.nMsg,
    h.nScr⟩
  have := h.sp; have := h.sp2
  simp only [slay, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end VG.Proof.Ed448.X86_64.SignCached
