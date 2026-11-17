module

public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Layout
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Lost
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
public import VerifiedGarbage.Proof.MlKem.Arm.CallF
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Args
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Sha512.Arm.Rounds
public import VerifiedGarbage.Proof.MlKem.Arm.Keccak
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Hash

/-! ### `MlDsa.Arm.Message.Pre`, which only this module used -/

section

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
  simp only [mScrLen, messageScratchWords, oE]; omega_using []

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

end

end

/-! ### `MlDsa.Arm.Message.Entry`, which only this module used -/

section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message_cached`: entry and exit

Untrusted: everything here is checked by Lean. Stores of registers at
distinct offsets that are multiples of 4 from a base (`strs_ok`), and loads
of words on the stack into distinct registers (`lds_ok`). The entry: the
caller's `r7` kept in the first word of `scratch`, the address of `X` in
`r7`, the caller's `r7` and `lr` saved at `X + 904` and `X + 908`, the
arguments at `X + 912 + 4j` and `0 ‖ ctx_len` at `X + 944`, give `Ctx`
(`enter_ok`). The exit restores `lr` and `r7` (`leave_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

/-- Registers, permissions and stack pointer unchanged. -/
structure Same (t t' : State) : Prop where
  gpr : t'.gpr = t.gpr
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp

theorem Same.refl (t : State) : Same t t := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Same.of_memTo {a b : State} {m : Mem} (h : MemTo a b m) : Same a b := ⟨h.gpr, h.rd, h.wr, h.sp⟩

/-- Stores of registers at distinct offsets, multiples of 4, from `B` in `b`. -/
theorem strs_ok (b : Reg) (B : BitVec 32) (XB : Addr)
    (hB : ∀ o, o + 4 ≤ 1024 → State.addr (B + BitVec.ofNat 32 o) = XB + BitVec.ofNat 64 o) :
    ∀ (as : List (Reg × Nat)) (t : State), t.gpr b = B →
    (∀ a ∈ as, a.2 % 4 = 0 ∧ a.2 + 4 ≤ 1024 ∧ InRegions t.wr (XB + BitVec.ofNat 64 a.2) 4) →
    (as.map (·.2)).Nodup →
    WP isa (.block (as.map fun a => .str a.1 b a.2)) t fun t' => Same t t' ∧
      (∀ a ∈ as, t'.mem.readW (XB + BitVec.ofNat 64 a.2) 32 = t.gpr a.1) ∧
      Frame (as.map fun a => ⟨XB + BitVec.ofNat 64 a.2, 4⟩) t.mem t'.mem
  | [], t, _, _, _ => wp_nil ⟨Same.refl t, fun _ h => by simp at h, Frame.refl _ _⟩
  | (r, f) :: as, t, hb, ha, hn => by
    obtain h0 := ha (r, f) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    obtain ea : State.addr (t.gpr b + BitVec.ofNat 32 f) = XB + BitVec.ofNat 64 f := by rw [hb]; exact hB f h0.2.1
    refine wp_str (by omega) (by rw [ea]; exact h0.2.2) fun s1 m1 => ?_
    obtain hs1 := Same.of_memTo m1
    refine WP.mono (strs_ok b B XB hB as s1 (by rw [hs1.gpr, hb]) (fun a h => by
      rw [hs1.wr]; exact ha a (List.mem_cons_of_mem _ h)) hn.2) fun t' ⟨hs, hr, hf⟩ => ⟨hs1.trans hs, ?_, ?_⟩
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [hf.readW (r := ⟨XB + BitVec.ofNat 64 f, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
            simp only [List.mem_map] at hr'
            obtain ⟨a', ha', rfl⟩ := hr'
            have := ha a' (List.mem_cons_of_mem _ ha')
            obtain hne : f ≠ a'.2 := fun e => hn.1 ⟨a', ha', e.symm⟩
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
          m1.mem, ea, Mem.readW_writeW_self32]
      · rw [hr a h, hs1.gpr]
    · have f1 : Frame [⟨XB + BitVec.ofNat 64 f, 4⟩] t.mem s1.mem := by
        rw [m1.mem, ea]
        exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine (f1.mono fun r h => ?_).trans (hf.mono fun r h => ?_)
      · simp only [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ h

/-- Loads of words on the stack into distinct registers. -/
theorem lds_ok : ∀ (ss : List (Reg × Nat)) (t : State), (ss.map (·.1)).Nodup →
    (∀ a ∈ ss, a.2 < 4096 ∧ InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 a.2)) 4) →
    WP isa (.block (ss.map fun a => .ldrSp a.1 a.2)) t fun t' => Only (ss.map (·.1)) t t' ∧
      ∀ a ∈ ss, t'.gpr a.1 = t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 a.2)) 32
  | [], t, _, _ => wp_nil ⟨Only.refl _ _, fun _ h => by simp at h⟩
  | (r, o) :: ss, t, hn, ha => by
    obtain h0 := ha (r, o) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine wp_ldrSp h0.1 h0.2 fun s1 o1 e1 => ?_
    refine WP.mono (lds_ok ss s1 hn.2 fun a h => by
      rw [o1.rd, o1.wr, o1.sp]; exact ha a (List.mem_cons_of_mem _ h)) fun t' ⟨o, hv⟩ => ⟨?_, ?_⟩
    · exact (o1.mono fun x hx => by simp only [List.mem_singleton] at hx; simp [hx]).trans
        (o.mono fun x hx => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hx)
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · rw [o.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact hn.1 ⟨x, hx', hx''⟩), e1]
      · rw [hv a h, o1.mem, o1.sp]

theorem movi_val (v : Nat) :
    (BitVec.ofNat 16 (v / 65536) ++ ((BitVec.ofNat 16 v).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  obtain e1 : BitVec.ofNat 16 (v / 65536) = (BitVec.ofNat 32 v).extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using []
  obtain e2 : BitVec.ofNat 16 v = (BitVec.ofNat 32 v).extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega_using []
  rw [e1, e2]; exact movw_movt _

theorem regSaves_ok : ∀ a ∈ regSaves, a.2 % 4 = 0 ∧ 904 ≤ a.2 ∧ a.2 + 4 ≤ 928 := by decide
theorem stkSaves_ok : ∀ a ∈ stkSaves, a.2 % 4 = 0 ∧ 928 ≤ a.2 ∧ a.2 + 4 ≤ 944 := by decide

/-- The entry, from a state whose registers and stack hold the layout's values. -/
theorem enter_ok {L : Lay} (hL : L.Ok) {p : Spec.MlDsa.Params} (hE : oE p = L.E) {so nA : Nat}
    {ss : List (Reg × Nat)} (hss : ss.map (·.1) = [.r0, .r1, .r2, .r3]) (hnA : nA ≤ 16) {s : State}
    (hsp : s.sp = L.SP) (hrd : s.rd = L.rd) (hwr : s.wr = L.wr)
    (h0 : s.gpr .r0 = L.key) (h1 : s.gpr .r1 = L.msg) (h2 : s.gpr .r2 = L.len) (h3 : s.gpr .r3 = L.ctx)
    (hA : ∀ o, o + 4 ≤ nA → InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4)
    (hfA : s.sp.toNat + nA ≤ 2 ^ 32) (hdA : L.SC.Disjoint ⟨State.addr s.sp, nA⟩)
    (hso : so + 4 ≤ nA) (hscr : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 so)) 32 = L.scr)
    (hsa : ∀ a ∈ ss, a.2 + 4 ≤ nA)
    (hv : ∀ j (hj : j < ss.length), s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (ss[j]'hj).2)) 32 =
      L.vals.getD (4 + j) 0) :
    WP isa (.block (enter so p ss)) s fun t => Ctx L s.gpr s.mem t := by
  obtain hlen : ss.length = 4 := by rw [← List.length_map (f := (·.1)), hss]; rfl
  have hscL := hL.hE
  -- Words on the stack: in the arguments' region, apart from `scratch`.
  obtain estk : ∀ o, o + 4 ≤ nA → State.addr (s.sp + BitVec.ofNat 32 o) = State.addr s.sp + BitVec.ofNat 64 o :=
    fun o ho => addr_add (by omega_arith)
  obtain dstk : ∀ o, o + 4 ≤ nA → L.SC.Disjoint ⟨State.addr (s.sp + BitVec.ofNat 32 o), 4⟩ := fun o ho => by
    rw [estk o ho]; exact hdA.sub_right (Offset.sub_base _ ho)
  obtain sc0 : State.addr (L.scr + BitVec.ofNat 32 0) = State.addr L.scr := by rw [BitVec.add_zero]
  obtain hsc4 : Region.Sub ⟨State.addr L.scr, 4⟩ L.SC := by
    have := Offset.sub_base (State.addr L.scr) (d := 0) (n := 4) (k := L.scrLen) (by omega_arith)
    simpa only [BitVec.add_zero] using this
  obtain csc : L.SC.Contains (State.addr L.scr) 4 := by
    simpa using (Offset.contains_base (State.addr L.scr) (d := 0) (n := 4) (k := L.scrLen) (by omega_arith) (by omega_arith))
  obtain isc : InRegions L.wr (State.addr L.scr) 4 := ⟨L.SC, hL.inSC, csc⟩
  unfold enter
  simp only [List.append_assoc]
  -- `scratch` in `r12`, the caller's `r7` in its first word.
  refine wp_ldrSp (by omega_arith) (hA so hso) fun s1 o1 e1 => ?_
  rw [hscr] at e1
  refine wp_str (by decide) (by rw [e1, sc0, o1.wr, hwr]; exact isc) fun s2 m2 => ?_
  obtain q2 := Same.of_memTo m2
  -- `X` in `r7`.
  refine wp_movw fun s3 o3 e3 => wp_movt fun s4 o4 e4 => wp_addReg fun s5 o5 e5 => ?_
  rw [o4.get .r12, o3.get .r12, q2.gpr, e1, e4, e3, movi_val, hE] at e5
  -- The caller's `r7` back in `r12`.
  obtain m5 : s5.mem = s1.mem.writeW (State.addr L.scr) (s.gpr .r7) := by
    rw [o5.mem, o4.mem, o3.mem, m2.mem, e1, sc0, o1.get .r7]
  obtain r12_5 : s5.gpr .r12 = L.scr := by rw [o5.get .r12, o4.get .r12, o3.get .r12, q2.gpr, e1]
  refine wp_ldr (by decide) (by
      rw [r12_5, sc0, o5.rd, o5.wr, o4.rd, o4.wr, o3.rd, o3.wr, q2.rd, q2.wr, o1.rd, o1.wr, hrd, hwr]
      exact ⟨L.SC, List.mem_append_right _ hL.inSC, csc⟩) fun s6 o6 e6 => ?_
  rw [r12_5, sc0, m5, Mem.readW_writeW_self32] at e6
  obtain e76 : s6.gpr .r7 = L.X32 := by rw [o6.get .r7, e5]
  obtain hw6 : s6.wr = L.wr := by rw [o6.wr, o5.wr, o4.wr, o3.wr, q2.wr, o1.wr, hwr]
  -- The registers.
  obtain g6 : ∀ r, r ≠ .r7 → r ≠ .r12 → s6.gpr r = s.gpr r := fun r h7 h12 => by
    rw [o6.get r (by simpa using h12), o5.get r (by simpa using h7), o4.get r (by simpa using h7),
      o3.get r (by simpa using h7), q2.gpr, o1.get r (by simpa using h12)]
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  obtain hxo : ∀ o, o + 4 ≤ 1024 → State.addr (L.X32 + BitVec.ofNat 32 o) = L.X + BitVec.ofNat 64 o :=
    fun o ho => hL.xo (by omega_arith)
  refine WP.mono (strs_ok .r7 L.X32 L.X hxo regSaves s6 e76 (fun a ha => by
    have := regSaves_ok a ha; exact ⟨this.1, by omega_arith, by rw [hw6]; exact hL.inW (by omega_arith)⟩) (by decide))
    fun s7 ⟨q7, r7, f7⟩ => ?_
  rw [WP.block_append_iff]
  -- The arguments on the stack, unchanged since the entry.
  obtain m7 : ∀ o, o + 4 ≤ nA → s7.mem.readW (State.addr (s7.sp + BitVec.ofNat 32 o)) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun o ho => by
    obtain hs7 : s7.sp = s.sp := by rw [q7.sp, o6.sp, o5.sp, o4.sp, o3.sp, q2.sp, o1.sp]
    rw [hs7, f7.readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 o), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := regSaves_ok a ha
      exact ((dstk o ho).sub_left (hL.sub_sc (e := a.2) (k := 4) (by omega_arith))).symm) (by decide), o6.mem, m5,
      Mem.readW_writeW_sep (fun x h1 h2 => (dstk o ho).symm x h1 (hsc4 x h2)) (by decide), o1.mem]
  refine WP.mono (lds_ok ss s7 (by rw [hss]; decide) fun a ha => ⟨by have := hsa a ha; omega_arith, by
    rw [q7.rd, q7.wr, q7.sp, o6.rd, o6.wr, o6.sp, o5.rd, o5.wr, o5.sp, o4.rd, o4.wr, o4.sp, o3.rd, o3.wr, o3.sp,
      q2.rd, q2.wr, q2.sp, o1.rd, o1.wr, o1.sp]; exact hA _ (hsa a ha)⟩) fun s8 ⟨o8, v8⟩ => ?_
  rw [hss] at o8
  -- The values loaded.
  obtain hl8 : ∀ j (hj : j < ss.length), s8.gpr (ss[j]'hj).1 = L.vals.getD (4 + j) 0 := fun j hj => by
    rw [v8 _ (List.getElem_mem hj), m7 _ (hsa _ (List.getElem_mem hj)), hv j hj]
  obtain hreg : ∀ j (hj : j < ss.length), (ss[j]'hj).1 = [Reg.r0, .r1, .r2, .r3].getD j .r0 := fun j hj => by
    have := congrArg (·[j]?) hss
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at this
    rw [List.getD_eq_getElem?_getD, ← this, Option.getD_some]
  obtain l8 : ∀ j < 4, s8.gpr ([Reg.r0, .r1, .r2, .r3].getD j .r0) = L.vals.getD (4 + j) 0 := fun j hj => by
    rw [← hreg j (by omega_arith)]; exact hl8 j (by omega_arith)
  obtain hw8 : s8.wr = L.wr := by rw [o8.wr, q7.wr, hw6]
  obtain e78 : s8.gpr .r7 = L.X32 := by rw [o8.get .r7, q7.gpr, e76]
  rw [WP.block_append_iff]
  refine WP.mono (strs_ok .r7 L.X32 L.X hxo stkSaves s8 e78 (fun a ha => by
    have := stkSaves_ok a ha; exact ⟨this.1, by omega_arith, by rw [hw8]; exact hL.inW (by omega_arith)⟩) (by decide))
    fun s9 ⟨q9, r9, f9⟩ => ?_
  -- `0 ‖ ctx_len`.
  obtain e79 : s9.gpr .r7 = L.X32 := by rw [q9.gpr, e78]
  simp only [oHdr, Nat.reduceAdd]
  refine wp_movImm (d := .r12) (v := 0) (by decide) fun s10 o10 e10 => ?_
  refine wp_strb (by decide) (by rw [o10.get .r7, e79, hxo 944 (by omega_arith), o10.wr, q9.wr, hw8]; exact hL.inW (by omega_arith))
    fun s11 m11 => ?_
  obtain q11 := Same.of_memTo m11
  refine wp_strb (by decide)
    (by rw [q11.gpr, o10.get .r7, e79, hxo 945 (by omega_arith), q11.wr, o10.wr, q9.wr, hw8]; exact hL.inW (by omega_arith))
    fun s12 m12 => wp_nil ?_
  obtain q12 := Same.of_memTo m12
  obtain x0_12 : s11.gpr .r0 = L.ctxLen := by
    rw [q11.gpr, o10.get .r0, q9.gpr]
    have := l8 0 (by omega_arith); simpa [Lay.vals] using this
  obtain m12e : s12.mem = (s9.mem.writeW (L.X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW
      (L.X + BitVec.ofNat 64 945) (L.ctxLen.setWidth 8) := by
    rw [m12.mem, m11.mem, o10.mem, q11.gpr, o10.get .r7, e79, e10, hxo 944 (by omega_arith), hxo 945 (by omega_arith),
      ← q11.gpr, x0_12]
  -- Reads of the saves.
  obtain hdr2 : ∀ d, d + 4 ≤ 40 → s12.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      s9.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd => by
    rw [m12e, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
  obtain r9' : ∀ d, d + 4 ≤ 24 → s9.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      s7.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd => by
    rw [f9.readW (r := ⟨L.X + BitVec.ofNat 64 (904 + d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := stkSaves_ok a ha
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), o8.mem]
  have hX := hL.x_toNat
  refine ⟨by rw [q12.rd, q11.rd, o10.rd, q9.rd, o8.rd, q7.rd, o6.rd, o5.rd, o4.rd, o3.rd, q2.rd, o1.rd, hrd],
    by rw [q12.wr, q11.wr, o10.wr, q9.wr, hw8],
    by rw [q12.sp, q11.sp, o10.sp, q9.sp, o8.sp, q7.sp, o6.sp, o5.sp, o4.sp, o3.sp, q2.sp, o1.sp, hsp],
    by rw [q12.gpr, q11.gpr, o10.get .r7, e79], fun r hr h7 hl => ?_, ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · have hn : r ∉ [Reg.r0, .r1, .r2, .r3, .r12] := fun hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> revert hr <;> decide
    rw [q12.gpr, q11.gpr, o10.get r (by simp at hn ⊢; exact hn.2.2.2.2), q9.gpr,
      o8.get r (by simp at hn ⊢; exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩), q7.gpr,
      g6 r h7 (by simp at hn; exact hn.2.2.2.2)]
  · rw [hdr2 0 (by omega_arith), r9' 0 (by omega_arith)]; exact (r7 (.r12, oR7) (by decide)).trans e6
  · rw [hdr2 4 (by omega_arith), r9' 4 (by omega_arith)]
    exact (r7 (.lr, oLR) (by decide)).trans (g6 .lr (by decide) (by decide))
  · rw [hdr2 _ (by omega_arith)]
    rcases (by omega_arith : j < 4 ∨ 4 ≤ j) with hj4 | hj4
    · rw [r9' _ (by omega_arith)]
      rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · refine (r7 (.r0, fKey) (by decide)).trans ?_; rw [g6 .r0 (by decide) (by decide), h0]; rfl
      · refine (r7 (.r1, fMsg) (by decide)).trans ?_; rw [g6 .r1 (by decide) (by decide), h1]; rfl
      · refine (r7 (.r2, fLen) (by decide)).trans ?_; rw [g6 .r2 (by decide) (by decide), h2]; rfl
      · refine (r7 (.r3, fCtx) (by decide)).trans ?_; rw [g6 .r3 (by decide) (by decide), h3]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, j = 4 + k := ⟨j - 4, by omega_arith⟩
      obtain hk : k < 4 := by omega_arith
      rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · exact (r9 (.r0, fCtxLen) (by decide)).trans (l8 0 (by omega_arith))
      · exact (r9 (.r1, fRnd) (by decide)).trans (l8 1 (by omega_arith))
      · exact (r9 (.r2, fSig) (by decide)).trans (l8 2 (by omega_arith))
      · exact (r9 (.r3, fScr) (by decide)).trans (l8 3 (by omega_arith))
  · have n45 : L.X + BitVec.ofNat 64 944 ≠ L.X + BitVec.ofNat 64 945 :=
      Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [show 904 + 40 = 944 from rfl, m12e]
    generalize L.X = X at n45 ⊢
    simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
    rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
    refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · -- Memory changed only in `scratch`.
    obtain a2 : Frame [L.SC, L.STK] s.mem s5.mem := by
      rw [m5, o1.mem]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ csc
    obtain a7 : Frame [L.SC, L.STK] s6.mem s7.mem := Frame.sub f7 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := regSaves_ok a ha
      exact ⟨L.SC, by simp, hL.sub_sc (by omega_arith)⟩
    obtain a9 : Frame [L.SC, L.STK] s8.mem s9.mem := Frame.sub f9 fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have := stkSaves_ok a ha
      exact ⟨L.SC, by simp, hL.sub_sc (by omega_arith)⟩
    obtain a12 : Frame [L.SC, L.STK] s9.mem s12.mem := by
      rw [m12e]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hL.sub_sc (e := 944) (k := 1) (by omega_arith) _
          (Region.contains_self _ _))).writeW
        (List.mem_cons_self ..) _ (hL.sub_sc (e := 945) (k := 1) (by omega_arith) _ (Region.contains_self _ _))
    rw [o6.mem] at a7
    rw [o8.mem] at a9
    exact a2.trans (a7.trans (a9.trans a12))

/-- What the exit needs: `r7` pointing at `X`, the callee-saved registers
but `r7` and `lr`, and the saves of those two. -/
structure Fin (L : Lay) (g : Reg → BitVec 32) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  r7 : t.gpr .r7 = L.X32
  cs : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → t.gpr r = g r
  s7 : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 0)) 32 = g .r7
  sLR : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 4)) 32 = g .lr

/-- The exit: `lr`, then `r7`, from the saves. -/
theorem leave_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {t : State} (hc : Fin L g t) :
    WP isa (.block leave) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = L.SP ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = t.gpr .r0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain hx : ∀ f, f + 4 ≤ 1024 → InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 f) 4 := fun f hf => by
    obtain ⟨R, hR, hc'⟩ := hL.inW (e := f) (k := 4) hf
    exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩
  refine wp_ldr (by decide) (by rw [hc.r7, hL.xo (by decide)]; exact hx 908 (by omega_using [])) fun t1 o1 e1 => ?_
  refine wp_ldr (by decide) (by rw [o1.get .r7, hc.r7, hL.xo (by decide), o1.rd, o1.wr]; exact hx 904 (by omega_using []))
    fun t2 o2 e2 => wp_nil ?_
  rw [hc.r7, hL.xo (by decide)] at e1
  rw [o1.get .r7, hc.r7, hL.xo (by decide), o1.mem] at e2
  refine ⟨fun r hr => ?_, by rw [o2.sp, o1.sp, hc.sp], by rw [o2.mem, o1.mem], by rw [o2.get .r0, o1.get .r0],
    by rw [o2.rd, o1.rd], by rw [o2.wr, o1.wr]⟩
  by_cases e7 : r = .r7
  · subst e7; rw [e2]; exact hc.s7
  · by_cases el : r = .lr
    · subst el; rw [o2.get .lr, e1]; exact hc.sLR
    · rw [o2.get r (by simpa using e7), o1.get r (by simpa using el), hc.cs r hr e7 el]

end VG.Proof.MlDsa.Arm.Message

end

end


/-!
# ML-DSA on ARMv7, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. A call of verified code with
frames of its own, in a frame that pushes its fifth argument (`r12`) and
`lr` (`frameCall_ok`, as `callS_ok` of the signing function on `μ`, after
the moves of the arguments). Any code verified against `signContract p
Arm.abi 44` whose frames use at most 44 bytes of stack (`SignFn`): its call
on the key, `μ` at `X + 840`, `rnd`, `sig` and the first `scratchWords p`
words of `scratch` (`signCall_ok`), after which the saves are intact
(`Fin`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (push2_frame push2_arg addr_sub view_gpr below)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (prepared : Bool) (c : Prog isa) : Prop where
  ok : ∀ s, (Sign.signE p prepared 44).pre s → ∃ t s', Exec isa c s t s' ∧ Arm.target.abiPreserved s s' ∧
    (Sign.signE p prepared 44).post s s'
  ct : ConstantTime isa (Sign.signE p prepared 44).pre (Sign.signE p prepared 44).pub c
  su : stackUse c ≤ 44

/-- The size of the working space of the functions on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The argument on the stack of a call in a frame: the word at the stack
pointer of the callee. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 4⟩

theorem frame8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩ : Region) =
      belowA s.sp 8 := by
  simp only [belowA, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  rw [addr_sub hsp]

theorem ne12_pres : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r12 := by decide

theorem sp_sub8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : (sp - BitVec.ofNat 32 8).toNat = sp.toNat - 8 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith

/-- A call of verified code in a frame that pushes `r12` (its fifth
argument) and `lr`, from the state after the moves of its arguments. -/
theorem frameCall_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : 8 + stackUse c ≤ D) {s : State} (hsp : D ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed [.r12, .lr] s).callEntry.withRegions (rd ++ [argR s]) wr))
    (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) s fun s' =>
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (wr ++ [belowA s.sp D]) s.mem s'.mem ∧
      ∃ s₂ : State, Frame [belowA s.sp D] s₂.mem s'.mem ∧ (∀ r, r ≠ .r12 → s₂.gpr r = s'.gpr r) ∧
        k.post ((pushed [.r12, .lr] s).callEntry.withRegions (rd ++ [argR s]) wr)
          (s₂.withRegions (rd ++ [argR s]) wr) := by
  obtain h8 : 8 ≤ s.sp.toNat := by omega_arith
  refine WP.frameLost (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8) (by decide) ?_
  obtain hwp : (pushed [.r12, .lr] s).wr = belowA s.sp 8 :: s.wr := by rw [VG.Arm.pushed_wr, frame8 h8]
  refine WP.callF hv hpre (fun x m hx => ?_) (fun x m hx => ?_) ?_ fun s₂ hrd hwr hsp₂ hf hcs hpost mL uL hfl => ?_
  · rw [VG.Arm.pushed_rd, hwp]
    rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      simp only [Region.Contains, belowA] at hcr ⊢; omega_arith
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · rw [hwp]
    obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [VG.Arm.pushed_sp, show BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 from rfl,
      sp_sub8 h8]; omega_arith
  · have hsp₂' : s₂.sp = s.sp - BitVec.ofNat 32 8 := by rw [hsp₂, VG.Arm.pushed_sp]; rfl
    obtain f₁ := push2_frame h8
    obtain hsu' : 8 + stackUse c ≤ s.sp.toNat := by omega_arith
    rw [frame8 h8] at hfl
    have hflD : Frame [belowA s.sp D] s₂.mem mL := hfl.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact belowA_sub (show 8 ≤ D by omega_arith)⟩
    refine ⟨by simp only [popped_rd, hrd, VG.Arm.pushed_rd], by simp only [popped_wr, hwr, hwp, List.tail_cons],
      by rw [popped_sp, hsp₂']; exact BitVec.sub_add_cancel _ _,
      fun r hr hl => by rw [popped_gpr (ne12_pres r hr hl), hcs r hr hl, VG.Arm.pushed_gpr], ?_,
      s₂, hflD, fun r hr => (popped_gpr hr 8 s₂).symm, hpost⟩
    dsimp only
    refine Frame.trans ?_ (hflD.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
    rw [VG.Arm.pushed_sp] at hf
    refine (f₁.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      exact belowA_sub (show 8 ≤ D by omega_arith)
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun x h => belowA_sub (show 8 + stackUse c ≤ D by omega_arith) x (belowA_push hsu' x h)⟩

/-- The regions a callee in a frame of `r12` and `lr` is given, within the
state after the push. -/
theorem cov_pushed {t1 : State} (h8 : 8 ≤ t1.sp.toNat) {rd wr : List Region}
    (hr : ∀ r ∈ rd, ∃ R ∈ t1.rd ++ t1.wr, Within r R) (hw : ∀ r ∈ wr, ∃ R ∈ t1.wr, Within r R) :
    Covers ((rd ++ [argR t1]) ++ wr) ((pushed [.r12, .lr] t1).rd ++ (pushed [.r12, .lr] t1).wr) ∧
      Covers wr (pushed [.r12, .lr] t1).wr := by
  obtain hwp : (pushed [.r12, .lr] t1).wr = belowA t1.sp 8 :: t1.wr := by rw [VG.Arm.pushed_wr, frame8 h8]
  obtain cW : Covers wr (pushed [.r12, .lr] t1).wr := by
    rw [hwp]
    exact covers_of_within fun r h => let ⟨R, hR, w⟩ := hw r h; ⟨R, List.mem_cons_of_mem _ hR, w⟩
  refine ⟨fun x m ⟨r, hr', hc⟩ => ?_, cW⟩
  rcases List.mem_append.mp hr' with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨R, hR, w⟩ := hr r h
      obtain hR' : R ∈ (pushed [.r12, .lr] t1).rd ++ (pushed [.r12, .lr] t1).wr := by
        rw [VG.Arm.pushed_rd, hwp]
        rcases List.mem_append.mp hR with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
      exact covers_of_within (rs := [r]) (fun r' h' => by
        simp only [List.mem_singleton] at h'; subst h'; exact ⟨R, hR', w⟩) x m ⟨r, List.mem_singleton_self _, hc⟩
    · simp only [List.mem_singleton] at h; subst h
      refine ⟨belowA t1.sp 8, by rw [hwp]; simp, ?_⟩
      simp only [Region.Contains, belowA] at hc ⊢; omega_arith
  · obtain ⟨R, hR, c⟩ := cW x m ⟨r, h, hc⟩
    exact ⟨R, List.mem_append_right _ hR, c⟩

/-- The bytes of a region apart from the 8 the push writes, after the push. -/
theorem storeWords_bytes {t : State} (h8 : 8 ≤ t.sp.toNat) {a : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨a, n⟩ (below t 8)) (hn : n ≤ 2 ^ 64) :
    bytesAt (storeWords t.mem (t.sp - 8#32) [t.gpr .r12, t.gpr .lr]) a n = bytesAt t.mem a n :=
  Proof.MlKem.bytesAt_frame (push2_frame h8) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd) hn

/-- The precondition of `Sign.signE p prepared 44`, from its facts. -/
theorem signC_pre {p : Params} {prepared : Bool} {E : State} (sp : 44 ≤ E.sp.toNat) (sp4 : E.sp.toNat + 4 ≤ 2 ^ 32)
    (rd : E.rd = [⟨State.addr (E.gpr .r0), secretKeyLen p prepared⟩, ⟨State.addr (E.gpr .r1), 64⟩, ⟨State.addr (E.gpr .r2), 32⟩,
      ⟨stackArgAddr E 0, 4⟩])
    (wr : E.wr = [⟨State.addr (E.gpr .r3), p.sigLen⟩, ⟨State.addr (stackArg E 0), sScr p⟩])
    (d03 : Region.Disjoint ⟨State.addr (E.gpr .r0), secretKeyLen p prepared⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d0s : Region.Disjoint ⟨State.addr (E.gpr .r0), secretKeyLen p prepared⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d13 : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d1s : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d23 : Region.Disjoint ⟨State.addr (E.gpr .r2), 32⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d2s : Region.Disjoint ⟨State.addr (E.gpr .r2), 32⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d3s : Region.Disjoint ⟨State.addr (E.gpr .r3), p.sigLen⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d3a : Region.Disjoint ⟨State.addr (E.gpr .r3), p.sigLen⟩ ⟨stackArgAddr E 0, 4⟩)
    (dsa : Region.Disjoint ⟨State.addr (stackArg E 0), sScr p⟩ ⟨stackArgAddr E 0, 4⟩)
    (k0 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 44, 44⟩ ⟨State.addr (E.gpr .r0), secretKeyLen p prepared⟩)
    (k1 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 44, 44⟩ ⟨State.addr (E.gpr .r1), 64⟩)
    (k2 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 44, 44⟩ ⟨State.addr (E.gpr .r2), 32⟩)
    (k3 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 44, 44⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (ks : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 44, 44⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (_ka : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 44, 44⟩ ⟨stackArgAddr E 0, 4⟩)
    (n0 : (E.gpr .r0).toNat + secretKeyLen p prepared ≤ 2 ^ 32) (n1 : (E.gpr .r1).toNat + 64 ≤ 2 ^ 32)
    (n2 : (E.gpr .r2).toNat + 32 ≤ 2 ^ 32) (n3 : (E.gpr .r3).toNat + p.sigLen ≤ 2 ^ 32)
    (ns : (stackArg E 0).toNat + sScr p ≤ 2 ^ 32)
    (hk : SecretKeyOk p prepared E.mem (State.addr (E.gpr .r0))) :
    (Sign.signE p prepared 44).pre E := by
  obtain e : sScr p = Sign.scrLen p := Nat.mul_comm _ _
  rw [e] at wr d0s d1s d2s d3s dsa ks ns
  exact ⟨rd, wr, d03, d0s, d13, d1s, d23, d2s, d3s, d3a, dsa, k0, k1, k2, k3, ks, n0, n1, n2, n3, ns, sp, sp4, hk⟩

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × Arg) := [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fRnd), (.r3, .slot fSig),
  (.r12, .slot fScr)]

section
variable {p : Params} {prepared : Bool} {s : State}

/-- The working space of the functions on `μ`: the start of `scratch`. -/
theorem sScr_sub (p : Params) (b : Addr) : Region.Sub ⟨b, sScr p⟩ ⟨b, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [sScr, oE]; omega_arith)

/-- What lies in the 1 KiB is apart from it. -/
theorem x_sScr {L : Lay} (hL : L.Ok) (hE : L.E = oE p) {d n : Nat} (hd : d + n ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 d, n⟩ ⟨State.addr L.scr, sScr p⟩ := by
  rw [hL.x_eq, add_add, hE]
  have := hL.hE; have := hL.nScr
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega_arith) (by omega_arith)

theorem mu_within {L : Lay} (hL : L.Ok) : Within ⟨L.MU, 64⟩ L.SC :=
  (within_off L.X (d := 840) (n := 64) (k := 1024) (by omega_arith)).trans hL.xs_sc

/-- The stack below the callee's stack pointer, in `STK`. -/
theorem stkE_sub {L : Lay} (hL : L.Ok) :
    Region.Sub ⟨State.addr (L.SP - BitVec.ofNat 32 8) - BitVec.ofNat 64 44, 44⟩ L.STK := by
  rw [addr_sub (by have := hL.nSP; omega_arith), BitVec.sub_sub, BitVec.ofNat_add_ofNat]
  exact Offset.sub_below _ (by omega_arith) (by omega_arith)

theorem argR_sub {L : Lay} {t : State} (ht : t.sp = L.SP) : Region.Sub (argR t) L.STK := by
  simp only [argR, ht]; exact Offset.sub_below _ (by omega_arith) (by omega_arith)

/-- The regions the signing function on `μ` reads and writes. -/
abbrev signRd (p : Params) (prepared : Bool) (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), secretKeyLen p prepared⟩, ⟨(slay p prepared s).MU, 64⟩, ⟨State.addr (stackArg s 1), 32⟩]
abbrev signWr (p : Params) (s : State) : List Region :=
  [⟨State.addr (stackArg s 2), p.sigLen⟩, ⟨State.addr (stackArg s 3), sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem signRegs_of (hL : (slay p prepared s).Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (slay p prepared s) g m₀ t) (hm : (∀ da ∈ signArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .r0 = s.gpr .r0 ∧ t1.gpr .r1 = (slay p prepared s).X32 + BitVec.ofNat 32 840 ∧ t1.gpr .r2 = stackArg s 1 ∧
      t1.gpr .r3 = stackArg s 2 ∧ t1.gpr .r12 = stackArg s 3 := by
  obtain e0 := hm (.r0, .slot fKey) (by simp)
  obtain e1 := hm (.r1, .off oMU) (by simp)
  obtain e2 := hm (.r2, .slot fRnd) (by simp)
  obtain e3 := hm (.r3, .slot fSig) (by simp)
  obtain e4 := hm (.r12, .slot fScr) (by simp)
  rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega_arith)] at e0
  rw [hc.off] at e1
  rw [hc.slotV hL (f := fRnd) (j := 5) rfl (by omega_arith)] at e2
  rw [hc.slotV hL (f := fSig) (j := 6) rfl (by omega_arith)] at e3
  rw [hc.slotV hL (f := fScr) (j := 7) rfl (by omega_arith)] at e4
  simp only [Lay.vals, slay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3 e4
  exact ⟨e0, e1, e2, e3, e4⟩

/-- The precondition of the signing function on `μ`, on entry to it. -/
theorem signK_pre (hp : p ∈ params) (h : SPre p prepared s) (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 : State} (hc : Ctx (slay p prepared s) g m₀ t)
    (hA : ∀ da ∈ signArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) (hm1 : t1.mem = t.mem)
    (hk : SecretKeyOk p prepared t.mem (State.addr (s.gpr .r0))) :
    (Sign.signE p prepared 44).pre
      ((pushed [.r12, .lr] t1).callEntry.withRegions (signRd p prepared s ++ [argR t1]) (signWr p s)) := by
  obtain hL := slay_ok hp h h8
  obtain ⟨e0, e1, e2, e3, e4⟩ := signRegs_of hL hc hA
  obtain h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := h.sp; omega_arith
  obtain ⟨a0, a1, -⟩ := push2_arg (t := (pushed [.r12, .lr] t1).callEntry.withRegions (signRd p prepared s ++ [argR t1])
    (signWr p s)) h8' rfl rfl
  obtain hmu := mu_eq hL
  obtain hsub := sScr_sub p (State.addr (stackArg s 3))
  obtain hmuS : Region.Sub ⟨(slay p prepared s).MU, 64⟩ ⟨State.addr (stackArg s 3), mScrLen p⟩ := (mu_within hL).sub
  obtain eSP : ((pushed [.r12, .lr] t1).callEntry.withRegions (signRd p prepared s ++ [argR t1]) (signWr p s)).sp =
      s.sp - BitVec.ofNat 32 8 := by
    simp only [State.withRegions_sp, State.callEntry_sp, VG.Arm.pushed_sp, hsp1]; rfl
  obtain kE := stkE_sub (L := slay p prepared s) hL
  obtain kA := argR_sub (L := slay p prepared s) (t := t1) hsp1
  simp only [slay] at kE kA
  obtain hstk : ∀ {r : Region}, (rStk s).Disjoint r → Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 8) -
      BitVec.ofNat 64 44, 44⟩ r := fun hr => hr.sub_left kE
  refine signC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs),
      view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs),
      e0, e1, e2, e3, a0, a1, e4, eSP, hmu, State.withRegions_rd, State.withRegions_wr]
  · rw [sp_sub8 (by have := h.sp; omega_arith)]; have := h.sp; omega_arith
  · rw [sp_sub8 (by have := h.sp; omega_arith)]; have := h.spA; omega_arith
  · simp only [argR, hsp1, List.cons_append, List.nil_append]
  · exact h.skSig
  · exact h.skScr.sub_right hsub
  · exact h.sigScr.symm.sub_left hmuS
  · exact (x_sScr hL rfl (by omega_arith) : Region.Disjoint ⟨(slay p prepared s).X + BitVec.ofNat 64 840, 64⟩ _)
  · exact h.rndSig
  · exact h.rndScr.sub_right hsub
  · exact h.sigScr.sub_right hsub
  · exact (h.stkSig.sub_left kA).symm
  · exact ((h.stkScr.sub_left kA).sub_right hsub).symm
  · exact hstk h.stkSk
  · exact (k_mu hL).sub_left kE
  · exact hstk h.stkRnd
  · exact hstk h.stkSig
  · exact hstk (h.stkScr.sub_right hsub)
  · rw [hsp1, addr_sub (by have := h.sp; omega_arith)]
    exact (Offset.base_disjoint_below _ (by omega_arith)).symm
  · exact h.nSk
  · have := hL.x32_lt
    rw [x32_toNat hL (by omega_arith)]; omega_arith
  · exact h.nRnd
  · exact h.nSig
  · have := h.nScr; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega_arith
  · intro hp'
    subst hp'
    obtain bk : Region.Sub (below t1 8) (slay p true s).STK := below_stk hsp1
    have e : secretKeyLen p true = preparedSecretKeyBytes p := rfl
    obtain dk := h.stkSk.symm.sub_right bk
    have nk := h.nSk
    rw [e] at dk nk
    refine VG.Proof.MlDsa.PreparedKey.preparedSecretKey_of_bytes ?_ (hk rfl)
    show bytesAt (storeWords t1.mem (t1.sp - 8#32) [t1.gpr .r12, t1.gpr .lr]) _ _ = _
    rw [storeWords_bytes h8' dk (by omega_using [nk]), hm1]

/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : SignFn p prepared c) (hp : p ∈ params) (h : SPre p prepared s)
    (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx (slay p prepared s) g m₀ t) (hk : SecretKeyOk p prepared t.mem (State.addr (s.gpr .r0))) :
    WP isa (.seq (.block (setArgs signArgs)) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8))) t fun s' =>
      Fin (slay p prepared s) g s' ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (State.addr (s.gpr .r0)) p.skLen) (bytesAt t.mem (slay p prepared s).MU 64)
          (bytesAt t.mem (State.addr (stackArg s 1)) 32)) (s'.gpr .r0)
        (bytesAt s'.mem (State.addr (stackArg s 2)) p.sigLen) := by
  obtain hL := slay_ok hp h h8
  refine WP.seq (WP.mono (setArgs_ok signArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  obtain hc1 : Ctx (slay p prepared s) g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl =>
    o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  obtain ⟨e0, e1, e2, e3, _⟩ := signRegs_of hL hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  obtain hpre := signK_pre hp h h8 hc hA hsp1 o.mem hk
  obtain hsub := sScr_sub p (State.addr (stackArg s 3))
  obtain hmuS : Region.Sub ⟨(slay p prepared s).MU, 64⟩ ⟨State.addr (stackArg s 3), mScrLen p⟩ := (mu_within hL).sub
  refine WP.mono (frameCall_ok (D := 52) hS.ok (by have := hS.su; omega_arith) (by rw [hsp1]; exact h.sp) hpre ?_ ?_)
    fun s' ⟨hrd, hwr, hsp, hcs, hf, s₂, hm₂, hg₂, hpost⟩ => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp [slay, h.rd], within_self _⟩
    · exact ⟨_, by simp [slay, h.wr], mu_within hL⟩
    · exact ⟨_, by simp [slay, h.rd], within_self _⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [slay, h.wr], within_self _⟩
    · exact ⟨⟨State.addr (stackArg s 3), mScrLen p⟩, by simp [slay, h.wr],
        within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega_arith)⟩
  -- After the call.
  obtain hsv : ∀ d, d + 4 ≤ 120 → s'.mem.readW ((slay p prepared s).X + BitVec.ofNat 64 (904 + d)) 32 =
      t1.mem.readW ((slay p prepared s).X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.sigScr.symm.sub_left ((within_off (slay p prepared s).X (d := 904 + d) (n := 4) (k := 1024)
          (by omega_arith)).trans hL.xs_sc).sub
      · exact x_sScr hL rfl (by omega_arith)
      · rw [hsp1]
        exact hL.sv_disj (r := belowA s.sp 52) (.inr fun _ h => h) hd') (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .r7 (by decide) (by decide)).trans hc1.r7,
    fun r hr h7 hl => (hcs r hr hl).trans (hc1.cs r hr h7 hl),
    (hsv 0 (by omega_arith)).trans hc1.s7, (hsv 4 (by omega_arith)).trans hc1.sLR⟩, ?_⟩
  obtain h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := h.sp; omega_arith
  obtain kA := argR_sub (L := slay p prepared s) (t := t1) hsp1
  obtain bk : Region.Sub (below t1 8) (slay p prepared s).STK := below_stk hsp1
  have hpm : (pushed [.r12, .lr] t1).mem = storeWords t1.mem (t1.sp - 8#32) [t1.gpr .r12, t1.gpr .lr] := rfl
  simp only [Sign.signE, Sign.signK, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, hpm,
    view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs),
    view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs)] at hpost
  obtain pm : ∀ (x : BitVec 32) (n : Nat), Region.Disjoint ⟨State.addr x, n⟩ (below t1 8) → n ≤ 2 ^ 64 →
      bytesAt (storeWords t1.mem (t1.sp - 8#32) [t1.gpr .r12, t1.gpr .lr]) (State.addr x) n =
        bytesAt t1.mem (State.addr x) n := fun x n hd hn => storeWords_bytes h8' hd hn
  rw [e0, e1, e2, e3, pm _ _ ((h.stkSk.sub_right (Region.sub_prefix (skLen_le prepared))).symm.sub_right bk)
      (by have := h.nSk; have := skLen_le (p := p) prepared; omega_arith),
    pm _ _ (by rw [mu_eq hL]; exact (k_mu hL).symm.sub_right bk) (by decide),
    pm _ _ (h.stkRnd.symm.sub_right bk) (by decide), mu_eq hL,
    hg₂ .r0 (by decide), o.mem] at hpost
  -- The signature is apart from the released frame.
  rw [Proof.MlKem.bytesAt_frame hm₂ (fun r hr => by rw [List.mem_singleton.mp hr, hsp1]; exact h.stkSig.symm)
    (by have := h.nSig; omega_arith)]
  exact hpost

end

end VG.Proof.MlDsa.Arm.Message
