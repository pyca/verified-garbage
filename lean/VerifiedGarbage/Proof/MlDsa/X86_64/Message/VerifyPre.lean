module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignPre
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Bitslice.Anf
import VerifiedGarbage.Proof.Sha3.X86_64.Permute

/-!
# ML-DSA on x86-64, `verify_message_cached`: the precondition and the layout

Untrusted: everything here is checked by Lean. The precondition of
`verifyMessageCachedContract p X86_64.abi 112`, spelled out (`VPre`), and
the layout of a run from a state satisfying it (`vlay`): the key is `pk`,
`scratch` and `tr` are the arguments on the stack, and the slot of `rnd`
holds `tr`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The length of the public key: the encoded key, or a prepared key (`prep`). -/
abbrev keyLenV (p : Params) (prep : Bool) : Nat := if prep then preparedPublicKeyBytes p else p.pkLen

section
variable (p : Params) (prep : Bool) (s : State)

abbrev vPk : Region := ⟨s.gpr .rdi, keyLenV p prep⟩
abbrev vSigR : Region := ⟨s.gpr .r9, p.sigLen⟩
abbrev vArgs : Region := ⟨stackArgAddr s 0, 16⟩
abbrev vScr : Region := ⟨stackArg s 0, mScrLen p⟩
abbrev vTr : Region := ⟨stackArg s 1, 64⟩

end

/-- The precondition of `verifyMessageCachedContract p X86_64.abi 112` (`prep = false`) or of
`preparedVerifyMessageContract p X86_64.abi 112` (`prep = true`). -/
structure VPre (p : Params) (prep : Bool) (s : State) : Prop where
  sp : 112 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [vPk p prep s, rMsg s, rCtx s, vSigR p s, vTr s, vArgs s]
  wr : s.wr = [vScr p s]
  pkScr : (vPk p prep s).Disjoint (vScr p s)
  msgScr : (rMsg s).Disjoint (vScr p s)
  ctxScr : (rCtx s).Disjoint (vScr p s)
  sigScr : (vSigR p s).Disjoint (vScr p s)
  scrTr : (vScr p s).Disjoint (vTr s)
  scrArgs : (vScr p s).Disjoint (vArgs s)
  retPk : (rRet s).Disjoint (vPk p prep s)
  retMsg : (rRet s).Disjoint (rMsg s)
  retCtx : (rRet s).Disjoint (rCtx s)
  retSig : (rRet s).Disjoint (vSigR p s)
  retScr : (rRet s).Disjoint (vScr p s)
  retTr : (rRet s).Disjoint (vTr s)
  retArgs : (rRet s).Disjoint (vArgs s)
  stkPk : (rStk s).Disjoint (vPk p prep s)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkSig : (rStk s).Disjoint (vSigR p s)
  stkScr : (rStk s).Disjoint (vScr p s)
  stkTr : (rStk s).Disjoint (vTr s)
  stkArgs : (rStk s).Disjoint (vArgs s)
  nPk : (s.gpr .rdi).toNat + keyLenV p prep ≤ 2 ^ 64
  nMsg : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nSig : (s.gpr .r9).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (stackArg s 0).toNat + mScrLen p ≤ 2 ^ 64
  nTr : (stackArg s 1).toNat + 64 ≤ 2 ^ 64
  tr : bytesAt s.mem (stackArg s 1) 64 = pkTr (bytesAt s.mem (s.gpr .rdi) p.pkLen)
  prepK : prep = true → PreparedPublicKey p s.mem (s.gpr .rdi)

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageCachedContract p X86_64.abi 112).pre s) :
    VPre p false s := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, X86_64.abi, X86_64.argRegs, List.range,
    List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrTr, scrArgs, retPk, retMsg, retCtx, retSig,
    retScr, retTr, retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkTr, stkArgs, nPk, nMsg, nCtx, nSig,
    nScr, nTr, tr⟩ := h
  exact ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrTr, scrArgs, retPk, retMsg, retCtx, retSig,
    retScr, retTr, retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkTr, stkArgs, nPk, nMsg, nCtx, nSig,
    nScr, nTr, tr, fun h => absurd h (by decide)⟩

theorem vPreP_of {p : Params} {s : State} (h : (preparedVerifyMessageContract p X86_64.abi 112).pre s) :
    VPre p true s := by
  sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
    List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrTr, scrArgs, retPk, retMsg, retCtx, retSig,
    retScr, retTr, retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkTr, stkArgs, nPk, nMsg, nCtx, nSig,
    nScr, nTr, hk, tr⟩ := h
  exact ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrTr, scrArgs, retPk, retMsg, retCtx, retSig,
    retScr, retTr, retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkTr, stkArgs, nPk, nMsg, nCtx, nSig,
    nScr, nTr, tr, fun _ => hk⟩

theorem keyLenV_ge {p : Params} (hp : p ∈ params) (prep : Bool) :
    128 ≤ keyLenV p prep ∧ keyLenV p prep < 2 ^ 31 ∧ p.pkLen ≤ keyLenV p prep := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> cases prep <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 31 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The layout of a run of `verify_message` from `s`. -/
def vlay (p : Params) (prep : Bool) (s : State) : Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 112
  key := s.gpr .rdi
  keyLen := keyLenV p prep
  msg := s.gpr .rsi
  len := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  rnd := stackArg s 1
  sig := s.gpr .r9
  scr := stackArg s 0
  E := oE p
  rd := s.rd
  wr := s.wr

theorem vlay_B (p : Params) (prep : Bool) (s : State) :
    (vlay p prep s).B + BitVec.ofNat 64 112 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem vlay_X (p : Params) (prep : Bool) (s : State) : Within (vlay p prep s).XS (vScr p s) :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem vlay_ok {p : Params} {prep : Bool} (hp : p ∈ params) {s : State} (h : VPre p prep s)
    (h8 : (s.gpr .r8).toNat < 256) : (vlay p prep s).Ok := by
  have hX := vlay_X p prep s
  have hXs := hX.sub
  refine ⟨h8, oE_lt hp, ⟨(keyLenV_ge hp prep).1, (keyLenV_ge hp prep).2.1⟩, ?_, ⟨vScr p s, by simp [vlay, h.wr], hX⟩, by simp [vlay, h.rd],
    by simp [vlay, h.rd], by simp [vlay, h.rd], h.pkScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs,
    h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs, h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx, ?_⟩
  · have := h.sp; have := (s.gpr .rsp).isLt
    simp only [vlay, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · intro R hR
    simp only [vlay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
    have := h.nScr
    subst hR; simp only; omega

end VG.Proof.MlDsa.X86_64.Message
