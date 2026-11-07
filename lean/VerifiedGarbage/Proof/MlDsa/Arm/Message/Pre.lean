module

public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Layout
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message_cached`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The preconditions of
`signMessageContract p Arm.abi 52` and `verifyMessageCachedContract p Arm.abi
52`, spelled out (`SPre`, `CPre`), and the layouts of runs from states
satisfying them (`slay`, `clay`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
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

theorem secretKeyLen_bounds {p : Params} (hp : p ∈ params) (prepared : Bool) :
    128 ≤ secretKeyLen p prepared ∧ secretKeyLen p prepared < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> cases prepared <;> decide

theorem publicKeyLen_bounds {p : Params} (hp : p ∈ params) (prepared : Bool) :
    128 ≤ publicKeyLen p prepared ∧ publicKeyLen p prepared < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> cases prepared <;> decide

theorem skLen_le {p : Params} (prepared : Bool) : p.skLen ≤ secretKeyLen p prepared := by
  cases prepared <;> simp [secretKeyLen, preparedSecretKeyBytes]

theorem pkLen_le {p : Params} (prepared : Bool) : p.pkLen ≤ publicKeyLen p prepared := by
  cases prepared <;> simp [publicKeyLen, preparedPublicKeyBytes]

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

section
variable (s : State)

abbrev rKey (n : Nat) : Region := ⟨State.addr (s.gpr .r0), n⟩
abbrev rMsg : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
abbrev rCtx : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
/-- The `n` bytes below the stack pointer the calls use. -/
abbrev rStk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 52, 52⟩
/-- The arguments on the stack. -/
abbrev rArgs (n : Nat) : Region := ⟨stackArgAddr s 0, n⟩
/-- The `j`-th argument on the stack, as an address. -/
abbrev sArg (j : Nat) : Addr := State.addr (stackArg s j)

end

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

/-! ## Signing -/

/-- The precondition of `signMessageContract p Arm.abi 52` (`prepared` false) and of
`preparedSignMessageContract p Arm.abi 52` (`prepared` true). -/
structure SPre (p : Params) (prepared : Bool) (s : State) : Prop where
  sp : 52 ≤ s.sp.toNat
  spA : s.sp.toNat + 16 ≤ 2 ^ 32
  rd : s.rd = [rKey s (secretKeyLen p prepared), rMsg s, rCtx s, ⟨sArg s 1, 32⟩, rArgs s 16]
  wr : s.wr = [⟨sArg s 2, p.sigLen⟩, ⟨sArg s 3, mScrLen p⟩]
  skSig : (rKey s (secretKeyLen p prepared)).Disjoint ⟨sArg s 2, p.sigLen⟩
  skScr : (rKey s (secretKeyLen p prepared)).Disjoint ⟨sArg s 3, mScrLen p⟩
  msgSig : (rMsg s).Disjoint ⟨sArg s 2, p.sigLen⟩
  msgScr : (rMsg s).Disjoint ⟨sArg s 3, mScrLen p⟩
  ctxSig : (rCtx s).Disjoint ⟨sArg s 2, p.sigLen⟩
  ctxScr : (rCtx s).Disjoint ⟨sArg s 3, mScrLen p⟩
  rndSig : Region.Disjoint ⟨sArg s 1, 32⟩ ⟨sArg s 2, p.sigLen⟩
  rndScr : Region.Disjoint ⟨sArg s 1, 32⟩ ⟨sArg s 3, mScrLen p⟩
  sigScr : Region.Disjoint ⟨sArg s 2, p.sigLen⟩ ⟨sArg s 3, mScrLen p⟩
  sigArgs : Region.Disjoint ⟨sArg s 2, p.sigLen⟩ (rArgs s 16)
  scrArgs : Region.Disjoint ⟨sArg s 3, mScrLen p⟩ (rArgs s 16)
  stkSk : (rStk s).Disjoint (rKey s (secretKeyLen p prepared))
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkRnd : (rStk s).Disjoint ⟨sArg s 1, 32⟩
  stkSig : (rStk s).Disjoint ⟨sArg s 2, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨sArg s 3, mScrLen p⟩
  stkArgs : (rStk s).Disjoint (rArgs s 16)
  nSk : (s.gpr .r0).toNat + secretKeyLen p prepared ≤ 2 ^ 32
  nMsg : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  nCtx : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nRnd : (stackArg s 1).toNat + 32 ≤ 2 ^ 32
  nSig : (stackArg s 2).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (stackArg s 3).toNat + mScrLen p ≤ 2 ^ 32
  key : SecretKeyOk p prepared s.mem (State.addr (s.gpr .r0))

theorem sPre_of {p : Params} {s : State} (h : (signMessageContract p Arm.abi 52).pre s) : SPre p false s := by
  sig_pre [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24, a25, h⟩ := h
  obtain ⟨a26, a27, a28⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, fun h => absurd h (by decide)⟩

theorem sPre_of_prepared {p : Params} {s : State} (h : (preparedSignMessageContract p Arm.abi 52).pre s) :
    SPre p true s := by
  sig_pre [preparedSignMessageContract, preparedSignMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24, a25, h⟩ := h
  obtain ⟨a26, a27, a28, a29⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, fun _ => a29⟩

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (prepared : Bool) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .r0
  keyLen := secretKeyLen p prepared
  msg := s.gpr .r1
  len := s.gpr .r2
  ctx := s.gpr .r3
  ctxLen := stackArg s 0
  rnd := stackArg s 1
  sig := stackArg s 2
  scr := stackArg s 3
  scrLen := mScrLen p
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_ok {p : Params} {prepared : Bool} (hp : p ∈ params) {s : State} (h : SPre p prepared s)
    (h8 : (stackArg s 0).toNat < 256) : (slay p prepared s).Ok :=
  ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], secretKeyLen_bounds hp prepared, h.sp, h.nScr, by simp [slay, h.wr], by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.skScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr,
    h.stkSk, h.stkMsg, h.stkCtx, h.nSk, h.nMsg, h.nCtx⟩

/-! ## Verification with a cached `tr` -/

/-- The precondition of `verifyMessageCachedContract p Arm.abi 52` (`prepared` false) and of
`preparedVerifyMessageContract p Arm.abi 52` (`prepared` true). -/
structure CPre (p : Params) (prepared : Bool) (s : State) : Prop where
  sp : 52 ≤ s.sp.toNat
  spA : s.sp.toNat + 16 ≤ 2 ^ 32
  rd : s.rd = [rKey s (publicKeyLen p prepared), rMsg s, rCtx s, ⟨sArg s 1, p.sigLen⟩, ⟨sArg s 3, 64⟩, rArgs s 16]
  wr : s.wr = [⟨sArg s 2, mScrLen p⟩]
  pkScr : (rKey s (publicKeyLen p prepared)).Disjoint ⟨sArg s 2, mScrLen p⟩
  msgScr : (rMsg s).Disjoint ⟨sArg s 2, mScrLen p⟩
  ctxScr : (rCtx s).Disjoint ⟨sArg s 2, mScrLen p⟩
  sigScr : Region.Disjoint ⟨sArg s 1, p.sigLen⟩ ⟨sArg s 2, mScrLen p⟩
  scrTr : Region.Disjoint ⟨sArg s 2, mScrLen p⟩ ⟨sArg s 3, 64⟩
  scrArgs : Region.Disjoint ⟨sArg s 2, mScrLen p⟩ (rArgs s 16)
  stkPk : (rStk s).Disjoint (rKey s (publicKeyLen p prepared))
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkSig : (rStk s).Disjoint ⟨sArg s 1, p.sigLen⟩
  stkScr : (rStk s).Disjoint ⟨sArg s 2, mScrLen p⟩
  stkTr : (rStk s).Disjoint ⟨sArg s 3, 64⟩
  stkArgs : (rStk s).Disjoint (rArgs s 16)
  nPk : (s.gpr .r0).toNat + publicKeyLen p prepared ≤ 2 ^ 32
  nMsg : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  nCtx : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nSig : (stackArg s 1).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (stackArg s 2).toNat + mScrLen p ≤ 2 ^ 32
  nTr : (stackArg s 3).toNat + 64 ≤ 2 ^ 32
  tr : Spec.Sha3.bytesAt s.mem (sArg s 3) 64 = pkTr (Spec.Sha3.bytesAt s.mem (State.addr (s.gpr .r0)) p.pkLen)
  key : PublicKeyOk p prepared s.mem (State.addr (s.gpr .r0))

theorem cPre_of {p : Params} {s : State} (h : (verifyMessageCachedContract p Arm.abi 52).pre s) :
    CPre p false s := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, fun h => absurd h (by decide)⟩

theorem cPre_of_prepared {p : Params} {s : State} (h : (preparedVerifyMessageContract p Arm.abi 52).pre s) :
    CPre p true s := by
  sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨a1, a2, a3, a4, a5, h⟩ := h
  obtain ⟨a6, a7, a8, a9, a10, h⟩ := h
  obtain ⟨a11, a12, a13, a14, a15, h⟩ := h
  obtain ⟨a16, a17, a18, a19, a20, h⟩ := h
  obtain ⟨a21, a22, a23, a24, a25⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a25, fun _ => a24⟩

/-- The layout of a run of `verify_message_cached` from `s` (`tr` in the slot of `rnd`). -/
def clay (p : Params) (prepared : Bool) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .r0
  keyLen := publicKeyLen p prepared
  msg := s.gpr .r1
  len := s.gpr .r2
  ctx := s.gpr .r3
  ctxLen := stackArg s 0
  rnd := stackArg s 3
  sig := stackArg s 1
  scr := stackArg s 2
  scrLen := mScrLen p
  E := oE p
  rd := s.rd
  wr := s.wr

theorem clay_ok {p : Params} {prepared : Bool} (hp : p ∈ params) {s : State} (h : CPre p prepared s)
    (h8 : (stackArg s 0).toNat < 256) : (clay p prepared s).Ok :=
  ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], publicKeyLen_bounds hp prepared, h.sp, h.nScr, by simp [clay, h.wr], by simp [clay, h.rd],
    by simp [clay, h.rd], by simp [clay, h.rd], h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, h.stkScr,
    h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx⟩

end VG.Proof.MlDsa.Arm.Message
