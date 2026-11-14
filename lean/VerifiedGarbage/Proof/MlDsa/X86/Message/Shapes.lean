module

public import VerifiedGarbage.Proof.MlDsa.X86.Message.Entry
public import VerifiedGarbage.Impl.MlDsa.X86.Message
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Layout
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86.Piece
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.X86.Message.Pre`, which only this module used -/

section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The functions on messages
take their key as a `KeyArg`: its length, and what their contracts require
of it (nothing of an encoded key; of a prepared one, that it is one), and
call a function on `μ` that takes the same key (`signKContract`,
`verifyKContract`). `signMessageKContract` and `verifyMessageKContract` are
the contracts of both kinds (`signMessageContract_eq`, …). Their
preconditions, with 176 and 172 bytes of stack, are spelled out (`SPre`,
`CPre`, which extends `VPre`), and so are the layouts of runs from states
satisfying them (`slay`, `vlay`).
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
  simp only [mScrLen, messageScratchWords, oE]; omega_using []

theorem skLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-! ## The key -/

/-- The key a function on messages takes, at argument 0: `len` bytes, and
what its contract requires of them. -/
structure KeyArg where
  len : Nat
  pre : Mem → Addr → Prop

/-- An encoded key of `len` bytes, of which the contract requires nothing. -/
abbrev plainKey (len : Nat) : KeyArg := ⟨len, fun _ _ => True⟩

/-- A key that begins with an encoded key of `enc` bytes, and whose
precondition only its own bytes decide. -/
structure KeyArg.Ok (K : KeyArg) (enc : Nat) : Prop where
  ge : 128 ≤ enc
  le : enc ≤ K.len
  lt : K.len < 2 ^ 16
  congr : ∀ {m m' : Mem} {a : Addr}, Spec.Sha3.bytesAt m' a K.len = Spec.Sha3.bytesAt m a K.len →
    K.pre m a → K.pre m' a

theorem plainKey_ok {enc : Nat} (h : 128 ≤ enc ∧ enc < 2 ^ 16) : (plainKey enc).Ok enc :=
  ⟨h.1, Nat.le_refl _, h.2, fun _ h => h⟩

/-! ## The contracts, for a key -/

/-- `signSig`, with a key of `kl` bytes. -/
def signKSig (p : Params) (kl : Nat) : Sig where
  params := [("sk", .array false .u8 kl), ("mu", .array false .u8 64),
    ("rnd", .array false .u8 32), ("sig", .array true .u8 p.sigLen),
    ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- `signContract`, with the key `K`. -/
def signKContract (p : Params) (K : KeyArg) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signKSig p K.len).contract A
    (pre := fun sk _mu _rnd _sig _scratch m => K.pre m sk)
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m mu 64)
        (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeak p (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m mu 64) (Spec.Sha3.bytesAt m rnd 32))

theorem signContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    signContract p A stack = signKContract p (plainKey p.skLen) A stack := rfl

/-- `verifySig`, with a key of `kl` bytes. -/
def verifyKSig (p : Params) (kl : Nat) : Sig where
  params := [("pk", .array false .u8 kl), ("mu", .array false .u8 64),
    ("sig", .array false .u8 p.sigLen), ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- `verifyContract`, with the key `K`. -/
def verifyKContract (p : Params) (K : KeyArg) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifyKSig p K.len).contract A
    (pre := fun pk _mu _sig _scratch m => K.pre m pk)
    (post := fun pk mu sig _scratch m _m' r =>
      let v := fun b => verifyMu p b (Spec.Sha3.bytesAt m pk p.pkLen) (Spec.Sha3.bytesAt m mu 64)
        (Spec.Sha3.bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk mu sig _scratch m =>
      leakBytes (Spec.Sha3.bytesAt m pk p.pkLen ++ Spec.Sha3.bytesAt m mu 64 ++ Spec.Sha3.bytesAt m sig p.sigLen))

theorem verifyContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    verifyContract p A stack = verifyKContract p (plainKey p.pkLen) A stack := rfl

/-- `signMessageSig`, with a key of `kl` bytes. -/
def signMessageKSig (p : Params) (kl : Nat) : Sig where
  params := [("sk", .array false .u8 kl), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("rnd", .array false .u8 32),
    ("sig", .array true .u8 p.sigLen), ("scratch", .array true .u64 (messageScratchWords p))]
  ret := some .u32

/-- `signMessageContract`, with the key `K`. -/
def signMessageKContract (p : Params) (K : KeyArg) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signMessageKSig p K.len).contract A
    (pre := fun sk _msg _msgLen _ctx _ctxLen _rnd _sig _scratch m => K.pre m sk)
    (post := fun sk msg msgLen ctx ctxLen rnd sig _scratch m m' r =>
      match formatMessage (Spec.Sha3.bytesAt m ctx ctxLen.toNat) (Spec.Sha3.bytesAt m msg msgLen.toNat) with
      | none => r = 2
      | some M' =>
        Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M' (Spec.Sha3.bytesAt m rnd 32)) r
          (Spec.Sha3.bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk msg msgLen ctx ctxLen rnd _sig _scratch m =>
      signMessageLeak p (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m msg msgLen.toNat)
        (Spec.Sha3.bytesAt m ctx ctxLen.toNat) (Spec.Sha3.bytesAt m rnd 32))

theorem signMessageContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    signMessageContract p A stack = signMessageKContract p (plainKey p.skLen) A stack := rfl

/-- `verifyMessageCachedSig`, with a key of `kl` bytes. -/
def verifyMessageKSig (p : Params) (kl : Nat) : Sig where
  params := [("pk", .array false .u8 kl), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("sig", .array false .u8 p.sigLen),
    ("scratch", .array true .u64 (messageScratchWords p)), ("tr", .array false .u8 64)]
  ret := some .u32

/-- `verifyMessageCachedContract`, with a key of `kl` bytes, of which and of
`tr` it requires `VP`. -/
def verifyMessageKContract (p : Params) (kl : Nat) (VP : Mem → Addr → Addr → Prop) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (verifyMessageKSig p kl).contract A
    (pre := fun pk _msg _msgLen _ctx _ctxLen _sig _scratch tr m => VP m pk tr)
    (post := fun pk msg msgLen ctx ctxLen sig _scratch _tr m _m' r =>
      match formatMessage (Spec.Sha3.bytesAt m ctx ctxLen.toNat) (Spec.Sha3.bytesAt m msg msgLen.toNat) with
      | none => r = 2
      | some M' =>
        let v := fun b => verifyInternal p b (Spec.Sha3.bytesAt m pk p.pkLen) M' (Spec.Sha3.bytesAt m sig p.sigLen)
        (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk msg msgLen ctx ctxLen sig _scratch _tr m =>
      leakBytes (Spec.Sha3.bytesAt m pk p.pkLen ++ Spec.Sha3.bytesAt m msg msgLen.toNat ++
        Spec.Sha3.bytesAt m ctx ctxLen.toNat ++ Spec.Sha3.bytesAt m sig p.sigLen))

/-- What `verifyMessageCachedContract` requires of `pk` and `tr`. -/
abbrev plainTr (p : Params) (m : Mem) (pk tr : Addr) : Prop :=
  Spec.Sha3.bytesAt m tr 64 = pkTr (Spec.Sha3.bytesAt m pk p.pkLen)

theorem verifyMessageCachedContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    verifyMessageCachedContract p A stack = verifyMessageKContract p p.pkLen (plainTr p) A stack := rfl

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

/-- The precondition of `signMessageKContract p K X86.abi 176`. -/
structure SPre (p : Params) (K : KeyArg) (s : State) : Prop where
  sp : 176 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 32 ≤ 2 ^ 32
  rd : s.rd = [aR s 0 K.len, msgRg s, ctxRg s, aR s 5 32]
  wr : s.wr = [aR s 6 p.sigLen, aR s 7 (mScrLen p), sArgs s 32]
  skSig : (aR s 0 K.len).Disjoint (aR s 6 p.sigLen)
  skScr : (aR s 0 K.len).Disjoint (aR s 7 (mScrLen p))
  skArgs : (aR s 0 K.len).Disjoint (sArgs s 32)
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
  rSk : (sRet s).Disjoint (aR s 0 K.len)
  rMsg : (sRet s).Disjoint (msgRg s)
  rCtx : (sRet s).Disjoint (ctxRg s)
  rRnd : (sRet s).Disjoint (aR s 5 32)
  rSig : (sRet s).Disjoint (aR s 6 p.sigLen)
  rScr : (sRet s).Disjoint (aR s 7 (mScrLen p))
  rArgs : (sRet s).Disjoint (sArgs s 32)
  kSk : (sStk s 176).Disjoint (aR s 0 K.len)
  kMsg : (sStk s 176).Disjoint (msgRg s)
  kCtx : (sStk s 176).Disjoint (ctxRg s)
  kRnd : (sStk s 176).Disjoint (aR s 5 32)
  kSig : (sStk s 176).Disjoint (aR s 6 p.sigLen)
  kScr : (sStk s 176).Disjoint (aR s 7 (mScrLen p))
  kArgs : (sStk s 176).Disjoint (sArgs s 32)
  nSk : (arg s 0).toNat + K.len ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nRnd : (arg s 5).toNat + 32 ≤ 2 ^ 32
  nSig : (arg s 6).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 7).toNat + mScrLen p ≤ 2 ^ 32
  kp : K.pre s.mem ((arg s 0).setWidth 64)

theorem sPre_of {p : Params} {K : KeyArg} {s : State} (h : (signMessageKContract p K X86.abi 176).pre s) : SPre p K s := by
  sig_pre [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40⟩

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (K : KeyArg) (s : State) : Lay where
  SP := s.gpr .esp
  N := 176
  nA := 8
  key := arg s 0
  keyLen := K.len
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

theorem slay_ok {p : Params} {K : KeyArg} (hK : K.Ok p.skLen) {s : State} (h : SPre p K s) (h8 : (arg s 4).toNat < 256) :
    (slay p K s).Ok := by
  have hk := stk_eq (s := s) (n := 176) h.sp
  refine ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], ⟨show 128 ≤ K.len by have := hK.ge; have := hK.le; omega_arith, hK.lt⟩, by show 56 ≤ 176; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * 8 ≤ _; have := h.spA; omega_using [this], h.nScr, by simp [slay, h.wr], by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.skScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    rfl, by show 8 ≤ 8; decide, by show 5 ≤ 8; decide, rfl, rfl, rfl, rfl, rfl, h.nSk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 176).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kSk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

/-! ## Verification -/

/-- Most of the precondition of `verifyMessageKContract p K.len VP X86.abi 172`
(`n = 8`, `T` the cached `tr`): `n` arguments, and the read-only regions
`T s` after the others. -/
structure VPre (p : Params) (K : KeyArg) (n : Nat) (T : State → List Region) (s : State) : Prop where
  sp : 172 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  rd : s.rd = [aR s 0 K.len, msgRg s, ctxRg s, aR s 5 p.sigLen] ++ T s
  wr : s.wr = [aR s 6 (mScrLen p), sArgs s (4 * n)]
  pkScr : (aR s 0 K.len).Disjoint (aR s 6 (mScrLen p))
  pkArgs : (aR s 0 K.len).Disjoint (sArgs s (4 * n))
  msgScr : (msgRg s).Disjoint (aR s 6 (mScrLen p))
  msgArgs : (msgRg s).Disjoint (sArgs s (4 * n))
  ctxScr : (ctxRg s).Disjoint (aR s 6 (mScrLen p))
  ctxArgs : (ctxRg s).Disjoint (sArgs s (4 * n))
  sigScr : (aR s 5 p.sigLen).Disjoint (aR s 6 (mScrLen p))
  sigArgs : (aR s 5 p.sigLen).Disjoint (sArgs s (4 * n))
  scrArgs : (aR s 6 (mScrLen p)).Disjoint (sArgs s (4 * n))
  rPk : (sRet s).Disjoint (aR s 0 K.len)
  rMsg : (sRet s).Disjoint (msgRg s)
  rCtx : (sRet s).Disjoint (ctxRg s)
  rSig : (sRet s).Disjoint (aR s 5 p.sigLen)
  rScr : (sRet s).Disjoint (aR s 6 (mScrLen p))
  rArgs : (sRet s).Disjoint (sArgs s (4 * n))
  kPk : (sStk s 172).Disjoint (aR s 0 K.len)
  kMsg : (sStk s 172).Disjoint (msgRg s)
  kCtx : (sStk s 172).Disjoint (ctxRg s)
  kSig : (sStk s 172).Disjoint (aR s 5 p.sigLen)
  kScr : (sStk s 172).Disjoint (aR s 6 (mScrLen p))
  kArgs : (sStk s 172).Disjoint (sArgs s (4 * n))
  nPk : (arg s 0).toNat + K.len ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nSig : (arg s 5).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 6).toNat + mScrLen p ≤ 2 ^ 32
  hn : n = 7 ∨ n = 8
  kp : K.pre s.mem ((arg s 0).setWidth 64)

/-- The cached `tr`. -/
abbrev trRg (s : State) : List Region := [aR s 7 64]

/-- The precondition of `verifyMessageKContract p K.len VP X86.abi 172`, for a `VP` that gives `K.pre` and
`tr = H(pk, 64)` (`cPre_of`). -/
structure CPre (p : Params) (K : KeyArg) (s : State) : Prop extends VPre p K 8 trRg s where
  scrTr : (aR s 6 (mScrLen p)).Disjoint (aR s 7 64)
  trArgs : (aR s 7 64).Disjoint (sArgs s 32)
  rTr : (sRet s).Disjoint (aR s 7 64)
  kTr : (sStk s 172).Disjoint (aR s 7 64)
  nTr : (arg s 7).toNat + 64 ≤ 2 ^ 32
  tr : Spec.Sha3.bytesAt s.mem ((arg s 7).setWidth 64) 64 =
    pkTr (Spec.Sha3.bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen)

theorem cPre_of {p : Params} {K : KeyArg} {VP : Mem → Addr → Addr → Prop}
    (hV : ∀ {m pk tr}, VP m pk tr → K.pre m pk ∧ Spec.Sha3.bytesAt m tr 64 = pkTr (Spec.Sha3.bytesAt m pk p.pkLen))
    {s : State} (h : (verifyMessageKContract p K.len VP X86.abi 172).pre s) : CPre p K s := by
  sig_pre [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14, a16, a17, a18, a19, a20, a22, a23, a24, a25,
    a26, a27, a29, a30, a31, a32, a33, a34, .inr rfl, (hV a36).1⟩, a13, a15, a21, a28, a35, (hV a36).2⟩

/-- The layout of a run of `verify_message_cached` (`n = 8`) from `s` (`sig`
in the place of `rnd` too). -/
def vlay (p : Params) (K : KeyArg) (n : Nat) (s : State) : Lay where
  SP := s.gpr .esp
  N := 172
  nA := n
  key := arg s 0
  keyLen := K.len
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

theorem vlay_ok {p : Params} {K : KeyArg} (hK : K.Ok p.pkLen) {n : Nat} {T : State → List Region} {s : State}
    (h : VPre p K n T s) (h8 : (arg s 4).toNat < 256) : (vlay p K n s).Ok := by
  have hk := stk_eq (s := s) (n := 172) h.sp
  have hn := h.hn
  refine ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], ⟨show 128 ≤ K.len by have := hK.ge; have := hK.le; omega_arith, hK.lt⟩, by show 56 ≤ 172; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * n ≤ _; have := h.spA; omega_using [this], h.nScr, by simp [vlay, h.wr], by simp [vlay, h.rd],
    by simp [vlay, h.rd], by simp [vlay, h.rd], h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),
    by simp only [vlay, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]; omega_using [hn],
    by show n ≤ 8; omega_using [hn], by show 5 ≤ n; omega_using [hn], rfl, rfl, rfl, rfl, rfl, h.nPk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 172).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kPk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

end VG.Proof.MlDsa.X86.Message

end

end


/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: the layouts' shapes

Untrusted: everything here is checked by Lean. The contracts' public data,
spelled out (`SPub`, `VPub`), and the layouts of `sign_message` and
`verify_message_cached` (`slay`, `vlay`) meet what the
proofs of the check, the entry and the hashes need (`sShape`, `vShape`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- The public data of `signMessageKContract p K X86.abi 176`. -/
structure SPub (p : Params) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : signMessageLeak p (bytesAt s.mem ((arg s 0).setWidth 64) p.skLen)
      (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
      (bytesAt s.mem ((arg s 5).setWidth 64) 32) =
    signMessageLeak p (bytesAt s'.mem ((arg s' 0).setWidth 64) p.skLen)
      (bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat)
      (bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat) (bytesAt s'.mem ((arg s' 5).setWidth 64) 32)
  args : ∀ i < 8, arg s i = arg s' i

theorem spub_of {p : Params} {K : KeyArg} {s s' : State} (h : (signMessageKContract p K X86.abi 176).pub s s') :
    SPub p s s' := by
  sig_pub [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The public data of `verifyMessageKContract p kl VP X86.abi 172` (`n = 8`,
`cpub_of`). -/
structure VPub (p : Params) (n : Nat) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : leakBytes (bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen ++
      bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat ++
      bytesAt s.mem ((arg s 5).setWidth 64) p.sigLen) =
    leakBytes (bytesAt s'.mem ((arg s' 0).setWidth 64) p.pkLen ++
      bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat ++
      bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat ++ bytesAt s'.mem ((arg s' 5).setWidth 64) p.sigLen)
  args : ∀ i < n, arg s i = arg s' i

theorem cpub_of {p : Params} {kl : Nat} {VP : Mem → Addr → Addr → Prop} {s s' : State}
    (h : (verifyMessageKContract p kl VP X86.abi 172).pub s s') : VPub p 8 s s' := by
  sig_pub [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The leaf's frame, below the stack pointer on entry. -/
theorem frame_eq {s : State} (h : 16 ≤ (s.gpr .esp).toNat) :
    (⟨(E0 s).setWidth 64 - 16#64, 16⟩ : Region) = below (s.gpr .esp) 16 := by
  simp only [below]; rw [Taint.sub_setWidth h]

theorem sShape {p : Params} {K : KeyArg} (hK : K.Ok p.skLen) : Shape (SPre p K) (SPub p) (slay p K) 7 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ _ i hi := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ _ := by show 7 < 8; decide
  E _ _ := rfl
  ok _ h₀ h8 := slay_ok hK h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega_using [this],
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega_using [this]⟩
  fit _ h₀ := by show _ + 4 + 4 * 8 ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega_using [this])]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega_using []) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  n5 _ _ := by show 5 ≤ 8; decide
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ _ _ hq := ⟨hq.args 4 (by decide), hq.args 7 (by decide)⟩
  pubL _ _ _ _ hq := ⟨hq.esp, by simp only [slay, hq.args 0 (by decide), hq.args 1 (by decide),
      hq.args 2 (by decide), hq.args 3 (by decide), hq.args 4 (by decide), hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)], by simp only [Lay.X32, slay, hq.args 7 (by decide)], rfl,
    hq.args 0 (by decide), hq.args 1 (by decide), hq.args 2 (by decide), hq.args 3 (by decide),
    hq.args 4 (by decide)⟩

theorem vlay_argv {p : Params} {K : KeyArg} {n : Nat} (hn : n = 7 ∨ n = 8) (s : State) :
    ∀ i < n, (vlay p K n s).argv.getD i 0 = arg s i := by
  rcases hn with rfl | rfl <;> intro i hi
  · match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
  · match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl

theorem vShape {p : Params} {K : KeyArg} (hK : K.Ok p.pkLen) {n : Nat} {T : State → List Region} :
    Shape (VPre p K n T) (VPub p n) (vlay p K n) 6 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ h₀ := vlay_argv h₀.hn s₀
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ h₀ := by show 6 < n; have := h₀.hn; omega_using [this]
  E _ _ := rfl
  ok _ h₀ h8 := vlay_ok hK h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega_using [this],
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega_using [this]⟩
  fit _ h₀ := by show _ + 4 + 4 * n ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega_using [this])]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega_using []) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  n5 _ h₀ := by show 5 ≤ n; have := h₀.hn; omega_using [this]
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ h₀ _ hq := ⟨hq.args 4 (by have := h₀.hn; omega_using [this]), hq.args 6 (by have := h₀.hn; omega_using [this])⟩
  pubL s₀ s₀' h₀ _ hq := by
    have hn := h₀.hn
    have e : ((List.range (n - 7)).map fun i => arg s₀ (7 + i)) = (List.range (n - 7)).map fun i => arg s₀' (7 + i) :=
      List.map_congr_left fun i hi => hq.args _ (by rw [List.mem_range] at hi; omega_using [hi])
    exact ⟨hq.esp, by simp only [vlay, hq.args 0 (by omega_using [hn]), hq.args 1 (by omega_using [hn]),
      hq.args 2 (by omega_using [hn]), hq.args 3 (by omega_using [hn]), hq.args 4 (by omega_using [hn]), hq.args 5 (by omega_using [hn]),
      hq.args 6 (by omega_using [hn]), e], by simp only [Lay.X32, vlay, hq.args 6 (by omega_using [hn])], rfl,
    hq.args 0 (by omega_using [hn]), hq.args 1 (by omega_using [hn]), hq.args 2 (by omega_using [hn]), hq.args 3 (by omega_using [hn]),
    hq.args 4 (by omega_using [hn])⟩

/-- A shape, for a stronger precondition. -/
theorem Shape.pre_mono {Pre Pre' : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {si : Nat}
    {p : Params} (hS : Shape Pre Pub lay si p) (h : ∀ s, Pre' s → Pre s) : Shape Pre' Pub lay si p where
  sp s₀ h₀ := hS.sp s₀ (h _ h₀)
  rd s₀ h₀ := hS.rd s₀ (h _ h₀)
  wr s₀ h₀ := hS.wr s₀ (h _ h₀)
  argv s₀ h₀ := hS.argv s₀ (h _ h₀)
  ctxLen s₀ h₀ := hS.ctxLen s₀ (h _ h₀)
  scr s₀ h₀ := hS.scr s₀ (h _ h₀)
  siLt s₀ h₀ := hS.siLt s₀ (h _ h₀)
  E s₀ h₀ := hS.E s₀ (h _ h₀)
  ok s₀ h₀ := hS.ok s₀ (h _ h₀)
  e16 s₀ h₀ := hS.e16 s₀ (h _ h₀)
  fit s₀ h₀ := hS.fit s₀ (h _ h₀)
  fd s₀ h₀ := hS.fd s₀ (h _ h₀)
  ain s₀ h₀ := hS.ain s₀ (h _ h₀)
  n5 s₀ h₀ := hS.n5 s₀ (h _ h₀)
  pubE s₀ s₀' h₀ h₀' := hS.pubE s₀ s₀' (h _ h₀) (h _ h₀')
  pubA s₀ s₀' h₀ h₀' := hS.pubA s₀ s₀' (h _ h₀) (h _ h₀')
  pubL s₀ s₀' h₀ h₀' := hS.pubL s₀ s₀' (h _ h₀) (h _ h₀')

end VG.Proof.MlDsa.X86.Message
