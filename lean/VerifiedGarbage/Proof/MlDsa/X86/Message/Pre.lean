module

public import VerifiedGarbage.Impl.MlDsa.X86.Message
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Layout
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86.Piece
import VerifiedGarbage.Proof.MlKem.X86.Leaf

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The preconditions of
`signMessageContract p X86.abi 136` and `verifyMessageCachedContract p X86.abi
132`, spelled out (`SPre`, `CPre`, which extends `VPre`), and the layouts of
runs from states satisfying them (`slay`, `vlay`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.MlDsa

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

theorem mScr_eq (p : Params) : mScrLen p = oE p + 1024 := by
  simp only [mScrLen, messageScratchWords, oE]; omega

theorem skLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

section
variable (s : State)

/-- Argument `i`, a pointer to `n` bytes. -/
abbrev aR (i n : Nat) : Region := ⟨(arg s i).setWidth 64, n⟩
abbrev msgRg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
abbrev ctxRg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
/-- The `n` bytes of arguments. -/
abbrev sArgs (n : Nat) : Region := ⟨argAddr s 0, n⟩
/-- The return address. -/
abbrev sRet : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
/-- The `n` bytes of stack the contract gives. -/
abbrev sStk (n : Nat) : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩

end

theorem stk_eq {s : State} {n : Nat} (h : n ≤ (s.gpr .esp).toNat) : sStk s n = below (s.gpr .esp) n := by
  simp only [sStk, below]; rw [Taint.sub_setWidth h]

/-! ## Signing -/

/-- The precondition of `signMessageContract p X86.abi 136`. -/
structure SPre (p : Params) (s : State) : Prop where
  sp : 136 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 32 ≤ 2 ^ 32
  rd : s.rd = [aR s 0 p.skLen, msgRg s, ctxRg s, aR s 5 32]
  wr : s.wr = [aR s 6 p.sigLen, aR s 7 (mScrLen p), sArgs s 32]
  skSig : (aR s 0 p.skLen).Disjoint (aR s 6 p.sigLen)
  skScr : (aR s 0 p.skLen).Disjoint (aR s 7 (mScrLen p))
  skArgs : (aR s 0 p.skLen).Disjoint (sArgs s 32)
  msgSig : (msgRg s).Disjoint (aR s 6 p.sigLen)
  msgScr : (msgRg s).Disjoint (aR s 7 (mScrLen p))
  msgArgs : (msgRg s).Disjoint (sArgs s 32)
  ctxSig : (ctxRg s).Disjoint (aR s 6 p.sigLen)
  ctxScr : (ctxRg s).Disjoint (aR s 7 (mScrLen p))
  ctxArgs : (ctxRg s).Disjoint (sArgs s 32)
  rndSig : (aR s 5 32).Disjoint (aR s 6 p.sigLen)
  rndScr : (aR s 5 32).Disjoint (aR s 7 (mScrLen p))
  rndArgs : (aR s 5 32).Disjoint (sArgs s 32)
  sigScr : (aR s 6 p.sigLen).Disjoint (aR s 7 (mScrLen p))
  sigArgs : (aR s 6 p.sigLen).Disjoint (sArgs s 32)
  scrArgs : (aR s 7 (mScrLen p)).Disjoint (sArgs s 32)
  rSk : (sRet s).Disjoint (aR s 0 p.skLen)
  rMsg : (sRet s).Disjoint (msgRg s)
  rCtx : (sRet s).Disjoint (ctxRg s)
  rRnd : (sRet s).Disjoint (aR s 5 32)
  rSig : (sRet s).Disjoint (aR s 6 p.sigLen)
  rScr : (sRet s).Disjoint (aR s 7 (mScrLen p))
  rArgs : (sRet s).Disjoint (sArgs s 32)
  kSk : (sStk s 136).Disjoint (aR s 0 p.skLen)
  kMsg : (sStk s 136).Disjoint (msgRg s)
  kCtx : (sStk s 136).Disjoint (ctxRg s)
  kRnd : (sStk s 136).Disjoint (aR s 5 32)
  kSig : (sStk s 136).Disjoint (aR s 6 p.sigLen)
  kScr : (sStk s 136).Disjoint (aR s 7 (mScrLen p))
  kArgs : (sStk s 136).Disjoint (sArgs s 32)
  nSk : (arg s 0).toNat + p.skLen ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nRnd : (arg s 5).toNat + 32 ≤ 2 ^ 32
  nSig : (arg s 6).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 7).toNat + mScrLen p ≤ 2 ^ 32

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p X86.abi 136).pre s) : SPre p s := by
  sig_pre [signMessageContract, signMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39⟩

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : Lay where
  SP := s.gpr .esp
  N := 136
  nA := 8
  key := arg s 0
  keyLen := p.skLen
  msg := arg s 1
  len := arg s 2
  ctx := arg s 3
  ctxLen := arg s 4
  rnd := arg s 5
  sig := arg s 6
  scr := arg s 7
  scrLen := mScrLen p
  E := oE p
  argv := [arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6, arg s 7]
  rd := s.rd
  wr := s.wr

theorem slay_ok {p : Params} (hp : p ∈ params) {s : State} (h : SPre p s) (h8 : (arg s 4).toNat < 256) :
    (slay p s).Ok := by
  have hk := stk_eq (s := s) (n := 136) h.sp
  refine ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], skLen_ge hp, by show 56 ≤ 136; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * 8 ≤ _; have := h.spA; omega, h.nScr, by simp [slay, h.wr], by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.skScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    rfl, by show 8 ≤ 8; decide, by show 5 ≤ 8; decide, rfl, rfl, rfl, rfl, rfl, h.nSk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 136).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kSk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

/-! ## Verification -/

/-- Most of the precondition of `verifyMessageCachedContract p X86.abi 132`
(`n = 8`, `T` the cached `tr`): `n` arguments, and the read-only regions
`T s` after the others. -/
structure VPre (p : Params) (n : Nat) (T : State → List Region) (s : State) : Prop where
  sp : 132 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  rd : s.rd = [aR s 0 p.pkLen, msgRg s, ctxRg s, aR s 5 p.sigLen] ++ T s
  wr : s.wr = [aR s 6 (mScrLen p), sArgs s (4 * n)]
  pkScr : (aR s 0 p.pkLen).Disjoint (aR s 6 (mScrLen p))
  pkArgs : (aR s 0 p.pkLen).Disjoint (sArgs s (4 * n))
  msgScr : (msgRg s).Disjoint (aR s 6 (mScrLen p))
  msgArgs : (msgRg s).Disjoint (sArgs s (4 * n))
  ctxScr : (ctxRg s).Disjoint (aR s 6 (mScrLen p))
  ctxArgs : (ctxRg s).Disjoint (sArgs s (4 * n))
  sigScr : (aR s 5 p.sigLen).Disjoint (aR s 6 (mScrLen p))
  sigArgs : (aR s 5 p.sigLen).Disjoint (sArgs s (4 * n))
  scrArgs : (aR s 6 (mScrLen p)).Disjoint (sArgs s (4 * n))
  rPk : (sRet s).Disjoint (aR s 0 p.pkLen)
  rMsg : (sRet s).Disjoint (msgRg s)
  rCtx : (sRet s).Disjoint (ctxRg s)
  rSig : (sRet s).Disjoint (aR s 5 p.sigLen)
  rScr : (sRet s).Disjoint (aR s 6 (mScrLen p))
  rArgs : (sRet s).Disjoint (sArgs s (4 * n))
  kPk : (sStk s 132).Disjoint (aR s 0 p.pkLen)
  kMsg : (sStk s 132).Disjoint (msgRg s)
  kCtx : (sStk s 132).Disjoint (ctxRg s)
  kSig : (sStk s 132).Disjoint (aR s 5 p.sigLen)
  kScr : (sStk s 132).Disjoint (aR s 6 (mScrLen p))
  kArgs : (sStk s 132).Disjoint (sArgs s (4 * n))
  nPk : (arg s 0).toNat + p.pkLen ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nSig : (arg s 5).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 6).toNat + mScrLen p ≤ 2 ^ 32
  hn : n = 7 ∨ n = 8

/-- The cached `tr`. -/
abbrev trRg (s : State) : List Region := [aR s 7 64]

/-- The precondition of `verifyMessageCachedContract p X86.abi 132`. -/
structure CPre (p : Params) (s : State) : Prop extends VPre p 8 trRg s where
  scrTr : (aR s 6 (mScrLen p)).Disjoint (aR s 7 64)
  trArgs : (aR s 7 64).Disjoint (sArgs s 32)
  rTr : (sRet s).Disjoint (aR s 7 64)
  kTr : (sStk s 132).Disjoint (aR s 7 64)
  nTr : (arg s 7).toNat + 64 ≤ 2 ^ 32
  tr : Spec.Sha3.bytesAt s.mem ((arg s 7).setWidth 64) 64 =
    pkTr (Spec.Sha3.bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen)

theorem cPre_of {p : Params} {s : State} (h : (verifyMessageCachedContract p X86.abi 132).pre s) : CPre p s := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14, a16, a17, a18, a19, a20, a22, a23, a24, a25,
    a26, a27, a29, a30, a31, a32, a33, a34, .inr rfl⟩, a13, a15, a21, a28, a35, a36⟩

/-- The layout of a run of `verify_message_cached` (`n = 8`) from `s` (`sig`
in the place of `rnd` too). -/
def vlay (p : Params) (n : Nat) (s : State) : Lay where
  SP := s.gpr .esp
  N := 132
  nA := n
  key := arg s 0
  keyLen := p.pkLen
  msg := arg s 1
  len := arg s 2
  ctx := arg s 3
  ctxLen := arg s 4
  rnd := arg s 5
  sig := arg s 5
  scr := arg s 6
  scrLen := mScrLen p
  E := oE p
  argv := [arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6] ++
    (List.range (n - 7)).map fun i => arg s (7 + i)
  rd := s.rd
  wr := s.wr

theorem vlay_ok {p : Params} (hp : p ∈ params) {n : Nat} {T : State → List Region} {s : State} (h : VPre p n T s)
    (h8 : (arg s 4).toNat < 256) : (vlay p n s).Ok := by
  have hk := stk_eq (s := s) (n := 132) h.sp
  have hn := h.hn
  refine ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], pkLen_ge hp, by show 56 ≤ 132; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * n ≤ _; have := h.spA; omega, h.nScr, by simp [vlay, h.wr], by simp [vlay, h.rd],
    by simp [vlay, h.rd], by simp [vlay, h.rd], h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),
    by simp only [vlay, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]; omega,
    by show n ≤ 8; omega, by show 5 ≤ n; omega, rfl, rfl, rfl, rfl, rfl, h.nPk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 132).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kPk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

end VG.Proof.MlDsa.X86.Message
