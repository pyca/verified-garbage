import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Impl.AesCcm.AArch64
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Frame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Contract`. -/
section

/-!
# AES-CCM on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). A call (`bl`) stores nothing in memory, so no
stack is used; `seal` and `open` read their last three arguments from the
stack, which they may only read.
-/

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The three arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = x0, rounds = x1, nonce = x2, nonce_len = x3,
aad = x4, aad_len = x5, data = x6, len = x7, tag = [sp], tag_len = [sp + 8],
work = [sp + 16])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesCcm.AArch64.args s) ∧ work.Disjoint (VG.Proof.AesCcm.AArch64.args s) ∧
    (s.gpr .x0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 24 ≤ 2 ^ 64 ∧ VG.Proof.AesCcm.AArch64.rounds (s.gpr .x1) ∧
    valid (stackArg s 1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat = true

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, VG.Proof.AesCcm.AArch64.args s] ∧ s.wr = [data, tag, work] ∧ VG.Proof.AesCcm.AArch64.oneLay s

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .x0, 240⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, tag, VG.Proof.AesCcm.AArch64.args s] ∧ s.wr = [data, work] ∧ VG.Proof.AesCcm.AArch64.oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ccm_seal`. -/
def sealAArch64 : Contract isa where
  pre := VG.Proof.AesCcm.AArch64.sealPre
  post s s' :=
    VG.Spec.Ccm.encryptWith (VG.Spec.Ccm.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (stackArg s 1).toNat
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, VG.Spec.Aes.bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := VG.Proof.AesCcm.AArch64.onePub

/-- What `vg_aes_ccm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  VG.Spec.Ccm.decryptWith (VG.Spec.Ccm.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (stackArg s 1).toNat
    (VG.Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (VG.Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (VG.Spec.Aes.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- The result of `vg_aes_ccm_open`: `x0` and the `n` bytes of `out` for the
result `r` of the decryption-verification. -/
def openOut (r : Option (List Byte)) (x0 : BitVec 64) (out : List Byte) (n : Nat) : Prop :=
  match r with
  | some pt => x0.setWidth 32 = 1 ∧ out = pt
  | none => x0.setWidth 32 = 0 ∧ out = VG.Spec.Ccm.zeros n

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesCcm.AArch64.rounds (s.gpr .x1) then [] else [if (VG.Proof.AesCcm.AArch64.openRes s).isSome = true then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openAArch64 : Contract isa where
  pre := VG.Proof.AesCcm.AArch64.openPre
  post s s' := VG.Proof.AesCcm.AArch64.openOut (VG.Proof.AesCcm.AArch64.openRes s) (s'.gpr .x0) (VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat) (s.gpr .x7).toNat
  pub s₁ s₂ := VG.Proof.AesCcm.AArch64.onePub s₁ s₂ ∧ VG.Proof.AesCcm.AArch64.openLeak s₁ = VG.Proof.AesCcm.AArch64.openLeak s₂

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Env`. -/
section

/-!
# AES-CCM on AArch64: where everything is

Untrusted: everything here is checked by Lean. The public values of a call
(`Cx`): the key schedule (240 bytes at `K`), the working space (2560 bytes at
`W`), the data (`n` bytes at `D`), the associated data (`al` bytes at `A`),
the tag (`tl` bytes at `T`), the rounds, the tag length and the nonce length,
and the stack pointer; what
the precondition says of them (`Lay`); what a state may access (`Perm`); the
registers holding them (`Env`); and the values the entry keeps in `W`
(`Slots`). The pieces write only the parts of `W` in `mutR` and the data, so
the slots, our caller's registers saved in `W`, the key schedule and the
associated data stay as the entry left them. `carun` runs a block
symbolically.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (in_off covers_off covers_left in_left)

/-- A `movz` of a 16-bit literal. -/
theorem imm_lit (k : Nat) : (BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< 0 : BitVec 64) = BitVec.ofNat 64 (k % 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte stored from a register. -/
theorem setWidth_8_32 (x : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

/-- Runs a block of the instructions the AES-CCM code uses. -/
macro "carun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self, BitVec.add_zero,
    mov, ptr, imm, zero16, bO, c0O, c1O, ksO, uO, aadO, alenO, nlenO, vO, rO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff,
    Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, and_true, true_and,
    eq_self_iff_true, imm_lit, setWidth_8_32, $ts,*]) <;> try rfl)

/-! ## Reassociating sequences -/

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => VG.Proof.AesCcm.AArch64.seq_assoc3 h)

theorem seq_assoc5 {a b c d e f : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c (.seq d e)))) f) s Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e f))))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => VG.Proof.AesCcm.AArch64.seq_assoc4 h)

/-! ## The public values -/

/-- The public values of a call of `seal` or `open`. -/
structure Cx where
  K : Addr
  W : Addr
  D : Addr
  A : Addr
  R : Nat
  tl : Nat
  n : Nat
  al : Nat
  nl : Nat
  SP : Addr
  T : Addr

/-- What the precondition says of the public values. -/
structure Lay (c : VG.Proof.AesCcm.AArch64.Cx) : Prop where
  kw : c.K.toNat + 240 ≤ 2 ^ 64
  ww : c.W.toNat + 2560 ≤ 2 ^ 64
  dw : c.D.toNat + c.n ≤ 2 ^ 64
  aw : c.A.toNat + c.al ≤ 2 ^ 64
  k_w : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W, 2560⟩
  k_d : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D, c.n⟩
  d_w : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W, 2560⟩
  a_w : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W, 2560⟩
  a_d : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.D, c.n⟩
  rounds : c.R = 10 ∨ c.R = 12 ∨ c.R = 14
  n_lt : c.n < 2 ^ 64
  al_lt : c.al < 2 ^ 64
  t4 : 4 ≤ c.tl
  t16 : c.tl ≤ 16
  te : c.tl % 2 = 0
  h7 : 7 ≤ c.nl
  h13 : c.nl ≤ 13
  hn : c.n < 256 ^ (15 - c.nl)
  tw : c.T.toNat + c.tl ≤ 2 ^ 64
  t_w : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.W, 2560⟩
  t_d : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.D, c.n⟩

/-- What a state may access. -/
structure Perm (c : VG.Proof.AesCcm.AArch64.Cx) (s : State) : Prop where
  k : Covers [⟨c.K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨c.W, 2560⟩] s.wr
  d : Covers [⟨c.D, c.n⟩] s.wr
  a : Covers [⟨c.A, c.al⟩] (s.rd ++ s.wr)
  t : Covers [⟨c.T, c.tl⟩] (s.rd ++ s.wr)

/-- The registers holding the public values throughout, the stack pointer,
and what the state may access. -/
structure Env (c : VG.Proof.AesCcm.AArch64.Cx) (s : State) : Prop where
  x19 : s.gpr .x19 = c.W
  x20 : s.gpr .x20 = BitVec.ofNat 64 c.tl
  x21 : s.gpr .x21 = c.K
  x22 : s.gpr .x22 = BitVec.ofNat 64 c.R
  x27 : s.gpr .x27 = c.D
  x28 : s.gpr .x28 = BitVec.ofNat 64 c.n
  sp : s.sp = c.SP
  perm : VG.Proof.AesCcm.AArch64.Perm c s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.x19, .x20, .x21, .x22, .x27, .x28]

theorem Perm.of_eq {c : VG.Proof.AesCcm.AArch64.Cx} {s s' : State} (h : VG.Proof.AesCcm.AArch64.Perm c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesCcm.AArch64.Perm c s' :=
  ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w, by rw [hwr]; exact h.d, by rw [hrd, hwr]; exact h.a,
    by rw [hrd, hwr]; exact h.t⟩

/-- An environment, after code that keeps its registers, the stack pointer
and the permissions. -/
theorem Env.keep {c : VG.Proof.AesCcm.AArch64.Cx} {s s' : State} (h : VG.Proof.AesCcm.AArch64.Env c s) (hg : ∀ r ∈ VG.Proof.AesCcm.AArch64.envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.AArch64.Env c s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hg _ (by simp), h.x22], by rw [hg _ (by simp), h.x27], by rw [hg _ (by simp), h.x28],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after code that writes only registers outside `envRegs`. -/
theorem Env.others {c : VG.Proof.AesCcm.AArch64.Cx} {s s' : State} (h : VG.Proof.AesCcm.AArch64.Env c s) {rs : List Reg}
    (hg : ∀ r, r ∉ rs → s'.gpr r = s.gpr r) (hd : ∀ r ∈ VG.Proof.AesCcm.AArch64.envRegs, r ∉ rs := by decide)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.AArch64.Env c s' :=
  h.keep (fun r hr => hg r (hd r hr)) hsp hrd hwr

/-- An environment, after a call. -/
theorem Env.of_saved {c : VG.Proof.AesCcm.AArch64.Cx} {s s' : State} (h : VG.Proof.AesCcm.AArch64.Env c s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.AArch64.Env c s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨c.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

/-- `W` and a part of it. -/
theorem w0_w {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 2560) :
    (⟨c.W, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ := by
  simpa using L.w_w (a := 0) (n := n) (.inl (by omega)) (by omega) hd

theorem k_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (VG.Proof.AesCcm.AArch64.Lay.wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (VG.Proof.AesCcm.AArch64.Lay.wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (VG.Proof.AesCcm.AArch64.Lay.wSub hd)

theorem wrapW {d : Nat} (hd : d < 2560) : (c.W + BitVec.ofNat 64 d).toNat = c.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rb : 16 * (c.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (P : VG.Proof.AesCcm.AArch64.Perm c s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (c.K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (c.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (c.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

end Perm

/-! ## Buffers -/

/-- A buffer of `len` bytes at `P` that the code may read, apart from `W`. -/
structure Buf (c : VG.Proof.AesCcm.AArch64.Cx) (s : State) (P : Addr) (len : Nat) : Prop where
  rd : Covers [⟨P, len⟩] (s.rd ++ s.wr)
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  w : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 2560⟩

namespace Buf

variable {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} {P : Addr} {len : Nat} (h : VG.Proof.AesCcm.AArch64.Buf c s P len)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.AArch64.Buf c s' P len :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ len) : VG.Proof.AesCcm.AArch64.Buf c s (P + BitVec.ofNat 64 k) (len - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (P.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base P (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ len) : VG.Proof.AesCcm.AArch64.Buf c s P k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ len) : VG.Proof.AesCcm.AArch64.Buf c s (P + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

theorem wd {d k : Nat} (hd : d + k ≤ 2560) : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  h.w.sub_right (Lay.wSub hd)

end Buf

/-- The associated data as a buffer. -/
theorem Lay.bufA {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (P : VG.Proof.AesCcm.AArch64.Perm c s) : VG.Proof.AesCcm.AArch64.Buf c s c.A c.al :=
  ⟨P.a, L.al_lt, L.aw, L.a_w⟩

/-- The data as a buffer. -/
theorem Lay.bufD {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (P : VG.Proof.AesCcm.AArch64.Perm c s) : VG.Proof.AesCcm.AArch64.Buf c s c.D c.n :=
  ⟨covers_left P.d, L.n_lt, L.dw, L.d_w⟩

/-- Data for a call: `len` bytes at `P`, which the code may read, apart from
the working space of the functions called. -/
structure Src (c : VG.Proof.AesCcm.AArch64.Cx) (s : State) (P : Addr) (len : Nat) : Prop where
  rd : Covers [⟨P, len⟩] (s.rd ++ s.wr)
  wrap : P.toNat + len ≤ 2 ^ 64
  qs : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 384, 2176⟩

theorem Buf.src {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} {P : Addr} {len : Nat} (h : VG.Proof.AesCcm.AArch64.Buf c s P len) : VG.Proof.AesCcm.AArch64.Src c s P len :=
  ⟨h.rd, h.wrap, h.wd (by decide)⟩

/-- Bytes of `W` below 384 as data. -/
theorem Lay.srcW {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (P : VG.Proof.AesCcm.AArch64.Perm c s) {t k : Nat} (hk : t + k ≤ 384) :
    VG.Proof.AesCcm.AArch64.Src c s (c.W + BitVec.ofNat 64 t) k :=
  ⟨P.wCR (by omega), by rw [L.wrapW (by omega)]; have := L.ww; omega, L.w_w (.inl (by omega)) (by omega) (by decide)⟩

/-! ## The slots -/

/-- The values the entry keeps in `W`: the address and length of the
associated data, the length of the nonce and the address of the tag. -/
structure Slots (c : VG.Proof.AesCcm.AArch64.Cx) (m : Mem) : Prop where
  aad : m.readW (c.W + BitVec.ofNat 64 216) 64 = c.A
  alen : m.readW (c.W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 c.al
  nlen : m.readW (c.W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 c.nl
  tag : m.readW (c.W + BitVec.ofNat 64 240) 64 = c.T

/-- The parts of `W` the pieces write: `[0, 112)` and `[256, 2560)`. -/
abbrev wLo (W : Addr) : Region := ⟨W, 112⟩
abbrev wHi (W : Addr) : Region := ⟨W + BitVec.ofNat 64 256, 2304⟩

/-- What the pieces may change: those parts of `W` and the data. -/
abbrev mutR (c : VG.Proof.AesCcm.AArch64.Cx) : List Region := [VG.Proof.AesCcm.AArch64.wLo c.W, VG.Proof.AesCcm.AArch64.wHi c.W, ⟨c.D, c.n⟩]

/-- A part of `W` the pieces write, within `mutR`. -/
theorem sub_lo {c : VG.Proof.AesCcm.AArch64.Cx} {d k : Nat} (h : d + k ≤ 112) :
    ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨VG.Proof.AesCcm.AArch64.wLo c.W, by simp, Offset.sub_base _ h⟩

theorem sub_hi {c : VG.Proof.AesCcm.AArch64.Cx} {d k : Nat} (h₁ : 256 ≤ d) (h₂ : d + k ≤ 2560) :
    ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨VG.Proof.AesCcm.AArch64.wHi c.W, by simp, Offset.sub _ h₁ (by omega)⟩

theorem sub_data {c : VG.Proof.AesCcm.AArch64.Cx} : ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub ⟨c.D, c.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {d k : Nat} (hd : 112 ≤ d ∧ d + k ≤ 256) :
    ∀ r ∈ VG.Proof.AesCcm.AArch64.mutR c, (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.w0_w (n := 112) (d := d) (k := k) hd.1 (by omega)).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.d_w' (by omega)).symm

theorem k_mut {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) : ∀ r ∈ VG.Proof.AesCcm.AArch64.mutR c, (⟨c.K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w' (by decide)
  · exact L.k_d

theorem a_mut {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) : ∀ r ∈ VG.Proof.AesCcm.AArch64.mutR c, (⟨c.A, c.al⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.a_w.sub_right (Region.sub_prefix (by decide))
  · exact L.a_w' (by decide)
  · exact L.a_d

/-- A frame within what the pieces write. -/
theorem frame_mut {c : VG.Proof.AesCcm.AArch64.Cx} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub r r') : Frame (VG.Proof.AesCcm.AArch64.mutR c) m m' := hf.sub hs

section
variable {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.AArch64.mutR c) m m')
include L hf

theorem Slots.mut (S : VG.Proof.AesCcm.AArch64.Slots c m) : VG.Proof.AesCcm.AArch64.Slots c m' := by
  have k : ∀ d, 216 ≤ d → d + 8 ≤ 248 →
      m'.readW (c.W + BitVec.ofNat 64 d) 64 = m.readW (c.W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (r := ⟨c.W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _)
      (VG.Proof.AesCcm.AArch64.kept_mut L ⟨by omega, by omega⟩) (by decide)
  exact ⟨by rw [k 216 (by decide) (by decide)]; exact S.aad, by rw [k 224 (by decide) (by decide)]; exact S.alen,
    by rw [k 232 (by decide) (by decide)]; exact S.nlen, by rw [k 240 (by decide) (by decide)]; exact S.tag⟩

theorem saved_mut {s₀ : State} (S : Proof.AesGcm.AArch64.SavedAt m c.W s₀) :
    Proof.AesGcm.AArch64.SavedAt m' c.W s₀ :=
  S.frame hf (fun r hr => VG.Proof.AesCcm.AArch64.kept_mut L (d := 128) (k := 88) ⟨by decide, by decide⟩ r hr)

theorem ciph_mut : Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (VG.Proof.AesCcm.AArch64.k_mut L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

theorem aad_mut : bytesAt m' c.A c.al = bytesAt m c.A c.al :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (VG.Proof.AesCcm.AArch64.a_mut L) (by have := L.al_lt; omega)

theorem tag_mut (ht : c.tl ≤ 16) : bytesAt m' c.T c.tl = bytesAt m c.T c.tl :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.t_w.sub_right (Region.sub_prefix (by decide))
    · exact L.t_w.sub_right (Lay.wSub (by decide))
    · exact L.t_d) (by omega)

end

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Callee`. -/
section

/-!
# AES-CCM on AArch64: the functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` are those of streaming AES-CMAC
(`Proof.CmacAes.Stream.AArch64.upd_call`), and those of `vg_aes_ctr32` those
of AES-GCM (`Proof.AesGcm.AArch64.ctr_call`); `uargs` and `cargs` build their
arguments from the environment: the key schedule, a block of `W` as the
state or the counter block, the data or blocks of `W` as the data, and the
working space at `W + 384`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs)
open VG.Proof.AesGcm.AArch64 (CtrCall covers_cons covers_nil covers_append covers_left)

/-- The arguments of `vg_cmac_aes_update`: the key schedule, the state at
`W + y`, `k` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : VG.Proof.AesCcm.AArch64.Src c s Q (16 * k)) (hqy : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩)
    (hk : 16 * k < 2 ^ 64) (x0 : s.gpr .x0 = c.K) (x1 : s.gpr .x1 = BitVec.ofNat 64 c.R)
    (x2 : s.gpr .x2 = c.W + BitVec.ofNat 64 y) (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 k)
    (x5 : s.gpr .x5 = c.W + BitVec.ofNat 64 384) :
    UArgs s c.K (c.W + BitVec.ofNat 64 y) Q (c.W + BitVec.ofNat 64 384) c.R k where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := L.rounds
  hn := hk
  wc := L.k_w' (by omega)
  ws := L.k_w' (by decide)
  dc := hqy
  ds := hq.qs
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  wrapC := by rw [L.wrapW (by omega)]; have := L.ww; omega
  wrapD := hq.wrap
  wrapS := by rw [L.wrapW (by decide)]; have := L.ww; omega
  reads := covers_append (covers_cons E.perm.k (covers_cons hq.rd covers_nil))
    (covers_cons (E.perm.wCR (by omega)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- The arguments of `vg_aes_ctr32`: the key schedule, the counter block at
`W + o`, `k` blocks at `Q`, which it may write, and the working space at
`W + 384`. -/
theorem cargs {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {o : Nat} (ho : o + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : VG.Proof.AesCcm.AArch64.Src c s Q (16 * k)) (hqo : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 o, 16⟩)
    (hqk : (⟨c.K, 240⟩ : Region).Disjoint ⟨Q, 16 * k⟩) (hqw : Covers [⟨Q, 16 * k⟩] s.wr) (hk : k < 2 ^ 64)
    (x0 : s.gpr .x0 = c.K) (x1 : s.gpr .x1 = BitVec.ofNat 64 c.R) (x2 : s.gpr .x2 = c.W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 k) (x5 : s.gpr .x5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s c.K (c.W + BitVec.ofNat 64 o) Q (c.W + BitVec.ofNat 64 384) c.R k where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := L.rounds
  wrap := hq.wrap
  n_lt := hk
  kc := L.k_w' (by omega)
  kd := hqk
  ks := L.k_w' (by decide)
  cd := hqo.symm
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  ds := hq.qs.sub_right (Region.sub_prefix (by decide))
  reads := covers_append (covers_cons E.perm.k covers_nil)
    (covers_cons (E.perm.wCR (by omega)) (covers_cons hq.rd (covers_cons (E.perm.wCR (by decide)) covers_nil)))
  writes := covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))

/-- A block of `W` below 384 as the data of a call of `vg_aes_ctr32`. -/
theorem cargsW {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {o : Nat} (ho : o + 16 ≤ 384) {d : Nat}
    (hd : d + 16 ≤ 384) (hod : o + 16 ≤ d ∨ d + 16 ≤ o)
    (x0 : s.gpr .x0 = c.K) (x1 : s.gpr .x1 = BitVec.ofNat 64 c.R) (x2 : s.gpr .x2 = c.W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = c.W + BitVec.ofNat 64 d) (x4 : s.gpr .x4 = BitVec.ofNat 64 1)
    (x5 : s.gpr .x5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s c.K (c.W + BitVec.ofNat 64 o) (c.W + BitVec.ofNat 64 d) (c.W + BitVec.ofNat 64 384) c.R 1 :=
  VG.Proof.AesCcm.AArch64.cargs L E ho (L.srcW E.perm (k := 16 * 1) hd) (L.w_w (by omega) (by omega) (by omega)) (L.k_w' (by omega))
    (E.perm.wC (by omega)) (by decide) x0 x1 x2 x3 x4 x5

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Entry`. -/
section

/-!
# AES-CCM on AArch64: the arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work`, the tag length and
`tag` from the stack, saves our caller's registers at `W + 128` and keeps the
arguments in registers and in `W` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm save saved)
open VG.Proof.AesGcm.AArch64 (savedMem savedR SavedAt save_ok readW_writeW_other savedMem_slot savedMem_frame
  covers_of_mem covers_left in_off)

/-- The public values of the arguments of `s`. -/
def cxOf (s : State) : VG.Proof.AesCcm.AArch64.Cx where
  K := s.gpr .x0
  W := stackArg s 2
  D := s.gpr .x6
  A := s.gpr .x4
  R := (s.gpr .x1).toNat
  tl := (stackArg s 1).toNat
  n := (s.gpr .x7).toNat
  al := (s.gpr .x5).toNat
  nl := (s.gpr .x3).toNat
  SP := s.sp
  T := stackArg s 0

/-- What `seal` and `open` are given: the public values `c`, and the nonce at
`N`. -/
structure Args (c : VG.Proof.AesCcm.AArch64.Cx) (N : Addr) (s : State) : Prop where
  lay : VG.Proof.AesCcm.AArch64.Lay c
  x0 : s.gpr .x0 = c.K
  x1 : s.gpr .x1 = BitVec.ofNat 64 c.R
  x2 : s.gpr .x2 = N
  x3 : s.gpr .x3 = BitVec.ofNat 64 c.nl
  x4 : s.gpr .x4 = c.A
  x5 : s.gpr .x5 = BitVec.ofNat 64 c.al
  x6 : s.gpr .x6 = c.D
  x7 : s.gpr .x7 = BitVec.ofNat 64 c.n
  sp : s.sp = c.SP
  w : stackArg s 2 = c.W
  tl : stackArg s 1 = BitVec.ofNat 64 c.tl
  t : stackArg s 0 = c.T
  perm : VG.Proof.AesCcm.AArch64.Perm c s
  nonce : VG.Proof.AesCcm.AArch64.Buf c s N c.nl
  nd : (⟨N, c.nl⟩ : Region).Disjoint ⟨c.D, c.n⟩
  argsC : Covers [VG.Proof.AesCcm.AArch64.args s] (s.rd ++ s.wr)
  argsW : (VG.Proof.AesCcm.AArch64.args s).Disjoint ⟨c.W, 2560⟩
  argsD : (VG.Proof.AesCcm.AArch64.args s).Disjoint ⟨c.D, c.n⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : VG.Proof.AesCcm.AArch64.oneLay s)
    (hk : Covers [⟨s.gpr .x0, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [VG.Proof.AesCcm.AArch64.args s] (s.rd ++ s.wr))
    (hT : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 2, 2560⟩] s.wr) :
    VG.Proof.AesCcm.AArch64.Args (VG.Proof.AesCcm.AArch64.cxOf s) (s.gpr .x2) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, b1, b2, b3, b4, b5, b6, _, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact {
    lay := ⟨b1, b6, b4, b3, d2, d1, d9, d6, d5, hR, BitVec.isLt _, BitVec.isLt _, ht4, ht16, hte, hn7, hn13, hp,
      b5, d8, d7⟩
    x0 := rfl
    x1 := (VG.Proof.AesCcm.AArch64.ofNat_toNat64 _).symm
    x2 := rfl
    x3 := (VG.Proof.AesCcm.AArch64.ofNat_toNat64 _).symm
    x4 := rfl
    x5 := (VG.Proof.AesCcm.AArch64.ofNat_toNat64 _).symm
    x6 := rfl
    x7 := (VG.Proof.AesCcm.AArch64.ofNat_toNat64 _).symm
    sp := rfl
    w := rfl
    tl := (VG.Proof.AesCcm.AArch64.ofNat_toNat64 _).symm
    t := rfl
    perm := ⟨hk, hW, hD, hA, hT⟩
    nonce := ⟨hN, BitVec.isLt _, b2, d4⟩
    nd := d3
    argsC := ha
    argsW := d11.symm
    argsD := d10.symm }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : VG.Proof.AesCcm.AArch64.sealPre s) :
    VG.Proof.AesCcm.AArch64.Args (VG.Proof.AesCcm.AArch64.cxOf s) (s.gpr .x2) s ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] s.wr := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      VG.Proof.AesCcm.AArch64.args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
      ⟨stackArg s 2, 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesCcm.AArch64.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (covers_left (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with its received tag, to read. -/
theorem args_of_open {s : State} (h : VG.Proof.AesCcm.AArch64.openPre s) : VG.Proof.AesCcm.AArch64.Args (VG.Proof.AesCcm.AArch64.cxOf s) (s.gpr .x2) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, VG.Proof.AesCcm.AArch64.args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region), ⟨stackArg s 2, 2560⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact VG.Proof.AesCcm.AArch64.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## The entry -/

/-- The memory after the entry: the registers saved and the arguments kept. -/
def entryMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((savedMem m W g).writeW (W + BitVec.ofNat 64 216) (g .x4)).writeW (W + BitVec.ofNat 64 224) (g .x5)).writeW
    (W + BitVec.ofNat 64 232) (g .x3)).writeW (W + BitVec.ofNat 64 240) (g .x11)

/-- What the entry writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 120⟩

theorem entry_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 248) :
    (VG.Proof.AesCcm.AArch64.entryR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem entryMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [VG.Proof.AesCcm.AArch64.entryR W] m (VG.Proof.AesCcm.AArch64.entryMem m W g) := by
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 248) := VG.Proof.AesCcm.AArch64.entry_contains W h₁ h₂
  exact (((((savedMem_frame m W g).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
    (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem entryMem_saved (m : Mem) (W : Addr) {g : Reg → BitVec 64} {s₀ : State}
    (hg : ∀ p ∈ saved, g p.1 = s₀.gpr p.1) : SavedAt (VG.Proof.AesCcm.AArch64.entryMem m W g) W s₀ := by
  have h₀ : SavedAt (savedMem m W g) W s₀ := fun p hp => (savedMem_slot m W g p hp).trans (hg p hp)
  refine h₀.frame (rs := [⟨W + BitVec.ofNat 64 216, 32⟩]) ?_ ?_
  · have c (d : Nat) (h₁ : 216 ≤ d) (h₂ : d + 8 ≤ 248) :
        (⟨W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := by
      rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 216) + BitVec.ofNat 64 (d - 216) from
        (Offset.add_add_eq W (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem entryMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) :
    (VG.Proof.AesCcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 216) 64 = g .x4 ∧
    (VG.Proof.AesCcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 224) 64 = g .x5 ∧
    (VG.Proof.AesCcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 232) 64 = g .x3 ∧
    (VG.Proof.AesCcm.AArch64.entryMem m W g).readW (W + BitVec.ofNat 64 240) 64 = g .x11 := by
  simp only [VG.Proof.AesCcm.AArch64.entryMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

/-- What the entry leaves. -/
structure Entered (c : VG.Proof.AesCcm.AArch64.Cx) (N : Addr) (s s₁ : State) : Prop where
  env : VG.Proof.AesCcm.AArch64.Env c s₁
  slots : VG.Proof.AesCcm.AArch64.Slots c s₁.mem
  saved : SavedAt s₁.mem c.W s
  frame : Frame [VG.Proof.AesCcm.AArch64.entryR c.W] s.mem s₁.mem
  x2 : s₁.gpr .x2 = N
  x3 : s₁.gpr .x3 = BitVec.ofNat 64 c.nl
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The loads of `work`, the tag length and `tag`. -/
theorem ldr_ok {c : VG.Proof.AesCcm.AArch64.Cx} {N : Addr} {s : State} (Ar : VG.Proof.AesCcm.AArch64.Args c N s) :
    WP isa (.block [.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0]) s fun s₀ => s₀.gpr .x9 = c.W ∧
      s₀.gpr .x10 = BitVec.ofNat 64 c.tl ∧ s₀.gpr .x11 = c.T ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₀.gpr r = s.gpr r) ∧ s₀.sp = s.sp ∧
      s₀.mem = s.mem ∧ s₀.rd = s.rd ∧ s₀.wr = s.wr := by
  have hA : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr) := by
    have := Ar.argsC
    simpa [VG.Proof.AesCcm.AArch64.args, stackArgAddr] using this
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  have a₈ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 :=
    in_off (d := 8) (n := 8) hA (by decide) (by decide)
  have a₁₆ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 :=
    in_off (d := 16) (n := 8) hA (by decide) (by decide)
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [a₀, a₈, a₁₆], rfl⟩ fun s₀ hs₀ => ?_
  subst hs₀
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl, rfl, rfl⟩
  · rw [← Ar.w]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]
  · rw [← Ar.tl]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]
  · rw [← Ar.t]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]

/-- After the entry. -/
theorem entry_ok {c : VG.Proof.AesCcm.AArch64.Cx} {N : Addr} {s : State} (Ar : VG.Proof.AesCcm.AArch64.Args c N s) :
    WP isa (.block entry) s (VG.Proof.AesCcm.AArch64.Entered c N s) := by
  refine WP.block_append (WP.block_append (WP.mono (VG.Proof.AesCcm.AArch64.ldr_ok Ar) fun s₀ ⟨x9₀, x10₀, x11₀, g₀, sp₀, m₀, rd₀, wr₀⟩ => ?_))
  have hperm₀ : VG.Proof.AesCcm.AArch64.Perm c s₀ := Ar.perm.of_eq rd₀ wr₀
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := VG.Proof.AesGcm.AArch64.save_ok s₀ .x9 x9₀ hperm₀.w
  have w (d : Nat) (h : d + 8 ≤ 2560) := in_off hperm₀.w h (by decide)
  rw [← wr₁] at w
  have gx : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₁.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by rw [g₁, g₀ r h₁ h₂ h₃]
  have x9₁ : s₁.gpr .x9 = c.W := by rw [g₁, x9₀]
  have x10₁ : s₁.gpr .x10 = BitVec.ofNat 64 c.tl := by rw [g₁, x10₀]
  have w₁ := w 216 (by decide)
  have w₂ := w 224 (by decide)
  have w₃ := w 232 (by decide)
  have w₄ := w 240 (by decide)
  obtain ⟨s₂, run₂, m₂, y19, y20, y21, y22, y27, y28, y2, y3, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, mov .x20 .x10, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
        .str .x .x5 .x19 alenO, .str .x .x3 .x19 nlenO, .str .x .x11 .x19 tagO, mov .x27 .x6, mov .x28 .x7] s₁ =
        some s₂ ∧
      s₂.mem = (((s₁.mem.writeW (c.W + BitVec.ofNat 64 216) (s₁.gpr .x4)).writeW (c.W + BitVec.ofNat 64 224)
        (s₁.gpr .x5)).writeW (c.W + BitVec.ofNat 64 232) (s₁.gpr .x3)).writeW (c.W + BitVec.ofNat 64 240)
        (s₁.gpr .x11) ∧
      s₂.gpr .x19 = s₁.gpr .x9 ∧ s₂.gpr .x20 = s₁.gpr .x10 ∧ s₂.gpr .x21 = s₁.gpr .x0 ∧
      s₂.gpr .x22 = s₁.gpr .x1 ∧ s₂.gpr .x27 = s₁.gpr .x6 ∧ s₂.gpr .x28 = s₁.gpr .x7 ∧
      s₂.gpr .x2 = s₁.gpr .x2 ∧ s₂.gpr .x3 = s₁.gpr .x3 ∧
      s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by carun [tagO, x9₁, w₁, w₂, w₃, w₄], ?_⟩
    simp only [Mem.writeW, gpr_write, mem_write, sp_write, rd_write, wr_write, ite_true, ite_false, reduceCtorEq,
      x9₁, and_self, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq, true_and]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have hm : s₂.mem = VG.Proof.AesCcm.AArch64.entryMem s.mem c.W s₀.gpr := by
    rw [m₂, m₁, m₀, VG.Proof.AesCcm.AArch64.entryMem, g₁]
  obtain ⟨e₁, e₂, e₃, e₄⟩ := VG.Proof.AesCcm.AArch64.entryMem_slot s.mem c.W s₀.gpr
  rw [g₀ .x4 (by decide) (by decide) (by decide)] at e₁
  rw [g₀ .x5 (by decide) (by decide) (by decide)] at e₂
  rw [g₀ .x3 (by decide) (by decide) (by decide)] at e₃
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [y19, x9₁]
  · rw [y20, x10₁]
  · rw [y21, gx .x0 (by decide) (by decide) (by decide), Ar.x0]
  · rw [y22, gx .x1 (by decide) (by decide) (by decide), Ar.x1]
  · rw [y27, gx .x6 (by decide) (by decide) (by decide), Ar.x6]
  · rw [y28, gx .x7 (by decide) (by decide) (by decide), Ar.x7]
  · rw [sp₂, sp₁, sp₀, Ar.sp]
  · exact Ar.perm.of_eq (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀])
  · rw [hm, e₁, Ar.x4]
  · rw [hm, e₂, Ar.x5]
  · rw [hm, e₃, Ar.x3]
  · rw [hm, e₄, x11₀]
  · rw [hm]
    exact VG.Proof.AesCcm.AArch64.entryMem_saved s.mem c.W fun p hp => by
      have h9 : p.1 ≠ .x9 ∧ p.1 ≠ .x10 ∧ p.1 ≠ .x11 := by
        revert hp; revert p; decide
      exact g₀ p.1 h9.1 h9.2.1 h9.2.2
  · rw [hm]; exact VG.Proof.AesCcm.AArch64.entryMem_frame _ _ _
  · rw [y2, gx .x2 (by decide) (by decide) (by decide), Ar.x2]
  · rw [y3, gx .x3 (by decide) (by decide) (by decide), Ar.x3]
  · rw [rd₂, rd₁, rd₀]
  · rw [wr₂, wr₁, wr₀]

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Blocks`. -/
section

/-!
# AES-CCM on AArch64: `Ctr₀`, counter blocks and chaining a block

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte and copies the nonce
after it: `Ctr₀` (`ctrs_ok`). `ctrAt` makes `Ctrᵢ` at `W + 64` from `Ctr₀`
(`ctrAt_ok`); `updBlock y` chains the block `B` at `W + 32` into the MAC
state at `W + y` (`updBlock_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok loopRegs Others add_ofNat_assoc)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_base ctrBlock_take8 ctr_or be_zero
  sub_low_byte)

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

/-! ## `Ctr₀` -/

/-- `Ctr₀`, from the nonce `N` of `nl` bytes. -/
theorem ctrs_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {N : Addr} (hN : VG.Proof.AesCcm.AArch64.Buf c s N c.nl)
    (h2 : s.gpr .x2 = N) (h3 : s.gpr .x3 = BitVec.ofNat 64 c.nl) :
    WP isa ctrs s fun s' => VG.Proof.AesCcm.AArch64.Env c s' ∧ Frame [⟨c.W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h7 := L.h7
  have h13 := L.h13
  have w₁ := E.perm.wW (show 48 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 56 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 48 + 1 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, x11₁, x12₁, x13₁, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa ctrsSeg s = some s₁ ∧
      s₁.mem = ((s.mem.writeW (c.W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 56)
        (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 48) (BitVec.ofNat 8 (15 - c.nl - 1)) ∧
      s₁.gpr .x11 = c.W + BitVec.ofNat 64 49 ∧ s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 c.nl ∧
      Others [.x9, .x11, .x12, .x13] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [ctrsSeg, E.x19, w₁, w₂, w₃], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · have z : (BitVec.setWidth 64 0#16 <<< 0 : BitVec 64) = 0 := by decide
      have f : (BitVec.setWidth 64 14#16 <<< 0 : BitVec 64) = BitVec.ofNat 64 14 := by decide
      simp only [mem_write, z, f, h3, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide),
        sub_low_byte (show c.nl ≤ 14 by omega)]
      rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h2]
    · simp [gpr_write, h3]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  have dNW : (⟨N, c.nl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 49, c.nl⟩ := hN.wd (by omega)
  have lp : LoopPre s₁ N (c.W + BitVec.ofNat 64 49) c.nl :=
    ⟨by omega, by rw [rd₁, wr₁]; exact hN.rd, E₁.perm.wC (by omega), dNW⟩
  refine WP.mono (copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega) lp) fun s₂ ⟨hm₂, _, _, hg₂, sp₂, rd₂, wr₂⟩ => ?_
  have hfz : Frame [⟨c.W + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 48) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 56) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 48) (n := 1) (e := 48) (k := 16) (by decide) (by decide) (by decide))
  have hNs : bytesAt s₁.mem N c.nl = bytesAt s.mem N c.nl :=
    Proof.AesGcm.AArch64.bytesAt_frame hfz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hN.wd (by decide)) (by omega)
  refine ⟨E₁.others hg₂ (by decide) sp₂ rd₂ wr₂, ?_, ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · refine hfz.trans ?_
    rw [hm₂]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains c.W (d := 49) (n := c.nl) (e := 48) (k := 16) (by decide) (by omega) (by decide))
  · -- The bytes of the block.
    have e56 : c.W + BitVec.ofNat 64 56 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
    have hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 48) 16 = BitVec.ofNat 8 (15 - c.nl - 1) :: Spec.Ccm.zeros 15 := by
      rw [hm₁, bytesAt_writeW8_base _ _ _ (by decide) (by decide), e56, Proof.Cmac.bytesAt_store2,
        Proof.Cmac.le8_zero]
      rfl
    have hl := length_bytesAt s.mem N c.nl
    rw [hm₂, show c.W + BitVec.ofNat 64 49 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 by rw [add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hz, hNs,
      Spec.Ccm.ctrBlock, hl, be_zero, show 1 + c.nl = c.nl + 1 by omega]
    simp only [Spec.Ccm.zeros, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_replicate,
      List.cons_append, List.nil_append]

/-! ## `ctrAt` -/

/-- `Ctrᵢ` at `W + 64`, for `i` in `x9`. -/
theorem ctrAt_ok {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (h13 : nonce.length ≤ 13) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) (h9 : s.gpr .x9 = BitVec.ofNat 64 i) :
    WP isa (.block ctrAt) s fun s' => Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      Others [.x9, .x10, .x11] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₁ := E.perm.wW (show 64 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 56 + 8 ≤ 2560 by decide)
  obtain ⟨s', run, hm, hg, sp', rd', wr'⟩ : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 64) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
        (c.W + BitVec.ofNat 64 72) (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 i)) ∧
      Others [.x9, .x10, .x11] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by carun [ctrAt, E.x19, w₁, w₂, r₁, r₂], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h9]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have e72 : c.W + BitVec.ofNat 64 72 = c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have e56 : c.W + BitVec.ofNat 64 56 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  refine WP.of_runBlock ⟨s', run, ?_, ?_, hg, sp', rd', wr'⟩
  · rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 64) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains c.W (d := 72) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))
  · have h8 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 8 = (bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16).take 8 := by
      rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hlo : le8 (s.mem.readW (c.W + BitVec.ofNat 64 48) 64) = (Spec.Ccm.ctrBlock nonce i).take 8 := by
      rw [Proof.Cmac.le8_readW, h8, hc0, ctrBlock_take8 h7, ctrBlock_take8 h7]
    have hhi : le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    rw [hm, e72, Proof.Cmac.bytesAt_store2, hlo, ctr_or h7 h13 hhi hi, List.take_append_drop]

/-! ## Chaining `B` -/

/-- What a call of `vg_cmac_aes_update` keeps of the pieces' registers. -/
abbrev pieceRegs : List Reg := [.x23, .x24, .x25, .x26]

/-- The arguments of the call chaining `B` into the MAC state at `W + y`. -/
theorem updArgs_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (updArgs y ++ ([ptr .x3 .x19 bO, imm .x4 1] : List Instr))) s fun s₁ => VG.Proof.AesCcm.AArch64.Env c s₁ ∧
      Proof.CmacAes.Stream.AArch64.UArgs s₁ c.K (c.W + BitVec.ofNat 64 y) (c.W + BitVec.ofNat 64 32)
        (c.W + BitVec.ofNat 64 384) c.R 1 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ [ptr .x3 .x19 bO, imm .x4 1]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .x0 = c.K ∧ s₁.gpr .x1 = BitVec.ofNat 64 c.R ∧ s₁.gpr .x2 = c.W + BitVec.ofNat 64 y ∧
      s₁.gpr .x3 = c.W + BitVec.ofNat 64 32 ∧ s₁.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₁.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hy' : y < 4096 := by omega
    refine ⟨_, by carun [updArgs, hy'], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x22]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, E.x19]
    · simp [gpr_write]
    · simp [gpr_write, E.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  refine WP.of_runBlock ⟨s₁, run₁, E₁, ?_, hg₁, hm₁, rd₁, wr₁⟩
  have hq := L.srcW (s := s₁) E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨c.W + BitVec.ofNat 64 32, 16 * 1⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  exact VG.Proof.AesCcm.AArch64.uargs L E₁ (by omega) hq hqy (by decide) x0 x1 x2 x3 x4 x5

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock v.callee y) s fun s' => VG.Proof.AesCcm.AArch64.Env c s' ∧ (∀ r ∈ VG.Proof.AesCcm.AArch64.pieceRegs, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 y, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
          [bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16] := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.updArgs_ok L E hy) fun s₁ ⟨E₁, A₁, hg₁, hm₁, rd₁, wr₁⟩ => ?_)
  refine WP.mono (upd_call v v.callee.name A₁)
    fun s₂ h => ⟨E₁.of_saved h.saved h.sp h.rd h.wr, fun r hr => ?_, by rw [h.rd, rd₁], by rw [h.wr, wr₁],
      by rw [← hm₁]; exact h.frame, ?_⟩
  · have hr' : r = .x23 ∨ r = .x24 ∨ r = .x25 ∨ r = .x26 := by simpa using hr
    rcases hr' with rfl | rfl | rfl | rfl <;> rw [h.saved _ (by decide) (by decide), hg₁ _ (by decide)]
  · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
      (Proof.Cmac.bytesAt_length _ _ _), hm₁]
    rfl

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.B0`. -/
section

/-!
# AES-CCM on AArch64: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `flagsSeg` computes the flags
`4 (t − 2) + q − 1 + 64 [a > 0]` (which is A.2.1's for an even `t`,
`flags_ok`); `b0Seg y` writes `B₀` to `W + 32` from `Ctr₀` and zeroes the MAC
state at `W + y` (`b0Seg_ok`); `b0 y` then chains `B₀` into it (`b0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (Others add_ofNat_assoc eval_zero ofNat_sub)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeW64_at bytesAt_writeW8_base bytesAt_writeW64_base
  ctrBlock_take8 ctrBlock_drop8 ctr_or flags_val)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B` and the
working space of the functions called. -/
abbrev macR (W : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩]

theorem macR_mut {c : VG.Proof.AesCcm.AArch64.Cx} {y : Nat} (hy : y = 0 ∨ y = 96) : ∀ r ∈ VG.Proof.AesCcm.AArch64.macR c.W y, ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesCcm.AArch64.sub_lo (by omega)
  · exact VG.Proof.AesCcm.AArch64.sub_lo (by decide)
  · exact VG.Proof.AesCcm.AArch64.sub_hi (by decide) (by decide)

/-- The flags, from the tag length, the nonce length in its slot and the
length of the associated data in `x24`. -/
theorem flags_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) (S : VG.Proof.AesCcm.AArch64.Slots c s.mem)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) :
    WP isa flagsSeg s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64) ∧
      Others [.x9, .x10, .x11] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have rn := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have ht4 := L.t4
  have ht16 := L.t16
  have h13 := L.h13
  obtain ⟨s₁, run₁, x9₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.subImm .x .x9 .x20 2, .lsl .x .x9 .x9 2, .ldr .x .x10 .x19 nlenO, imm .x11 14,
        .sub .x .x11 .x11 .x10, .add .x .x9 .x9 .x11] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl)) ∧ Others [.x9, .x10, .x11] s s₁ ∧
      s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, rn], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
    · have hn : s.mem.read (c.W + 232#64) 8 = BitVec.ofNat 64 c.nl := S.nlen
      simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E.x20, hn]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft,
        BitVec.toNat_ofNat, Nat.shiftLeft_eq, Size.bits]
      have := L.h7
      omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 c.al := by rw [hg₁ _ (by decide), h24]
  refine WP.ite (decide (c.al = 0)) (eval_zero h24₁ L.al_lt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    exact WP.block_nil ⟨by rw [x9₁, h0]; rfl, hg₁, hm₁, sp₁, rd₁, wr₁⟩
  · have h0 : c.al ≠ 0 := of_decide_eq_false hf
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₂ hs₂ => ?_
    subst hs₂
    refine ⟨?_, fun r hr => ?_, hm₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, x9₁, h0, ite_false]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Size.bits]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hg₁ r (by simp [hr.1, hr.2.1, hr.2.2])]

/-- `B₀` in `B`, and the MAC state at `W + y` zeroed. -/
theorem b0Seg_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64))
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (b0Seg y)) s fun s' => VG.Proof.AesCcm.AArch64.Env c s' ∧ (∀ r ∈ VG.Proof.AesCcm.AArch64.pieceRegs, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
  have h7 := L.h7
  have h13 := L.h13
  have c₁ := E.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have c₂ := E.perm.wR (show 56 + 8 ≤ 2560 by decide)
  have b₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have b₂ := E.perm.wW (show 32 + 1 ≤ 2560 by decide)
  have b₃ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have y₁ := E.perm.wW (show y + 8 ≤ 2560 by omega)
  have y₂ := E.perm.wW (show y + 8 + 8 ≤ 2560 by omega)
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((s.mem.writeW (c.W + BitVec.ofNat 64 32) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
      (c.W + BitVec.ofNat 64 32) ((s.gpr .x9).setWidth 8 : Byte)).writeW (c.W + BitVec.ofNat 64 40)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 c.n)) := ⟨_, rfl⟩
  obtain ⟨s₃, run₃, hm₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa (b0Seg y) s = some s₃ ∧
      s₃.mem = (mB.writeW (c.W + BitVec.ofNat 64 y) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 (y + 8))
        (0 : BitVec 64) ∧
      Others [.x9, .x10, .x11, .x12] s s₃ ∧ s₃.sp = s.sp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
    have ya : y % 8 = 0 ∧ y < 32768 := by omega
    have yb : (y + 8) % 8 = 0 ∧ y + 8 < 32768 := by omega
    refine ⟨_, by carun [b0Seg, E.x19, c₁, c₂, b₁, b₂, b₃, y₁, y₂, ya, yb], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
    · rw [hmB]
      simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, E.x28]
      rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨s₃, run₃, E.others hg₃ (by decide) sp₃ rd₃ wr₃, fun r hr => hg₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> decide),
    rd₃, wr₃, ?_⟩
  -- What the block wrote.
  have e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have ey8 : c.W + BitVec.ofNat 64 (y + 8) = c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by decide)
  have cY : ∀ d k, y ≤ d → d + k ≤ y + 16 →
      (⟨c.W + BitVec.ofNat 64 y, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by omega)
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem mB := by
    rw [hmB]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))
  have fY : Frame [⟨c.W + BitVec.ofNat 64 y, 16⟩] mB s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cY y 8 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (cY (y + 8) 8 (by omega) (by omega))
  have dYB : (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨(fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
    (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩), ?_, ?_⟩
  · -- The state was zeroed.
    rw [hm₃, ey8, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · -- `B₀`.
    have hB₁ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 = bytesAt mB (c.W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.AArch64.bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB)
        (by decide)
    have hlo : le8 (s.mem.readW (c.W + BitVec.ofNat 64 48) 64) =
        BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
      have h8 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 8 =
          (bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16).take 8 := by
        rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rw [Proof.Cmac.le8_readW, h8, hc0, ctrBlock_take8 (by omega)]
    have hhi : le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      have e56 : c.W + BitVec.ofNat 64 56 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
      rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hb : ((s.gpr .x9).setWidth 8 : Byte) = Spec.Ccm.flags c.tl (15 - nonce.length) c.al := by
      rw [h9, hnl, flags_val L.t4 L.t16 L.te h7 h13]
    have hB : bytesAt mB (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
      rw [hmB, e40, bytesAt_writeW64_at _ _ _ (by decide) (by decide), bytesAt_writeW8_base _ _ _ (by decide)
        (by decide), bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hb,
        ctr_or (by omega) (by omega) hhi (by rw [hnl]; exact L.hn), ctrBlock_drop8 (by omega)]
      simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons]
      have hX : (Spec.Ccm.flags c.tl (15 - nonce.length) c.al ::
          (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16))).length ≤ 8 + 8 := by
        simp [length_bytesAt]; omega
      rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega),
        List.drop_eq_nil_of_le hX, List.append_nil, ← List.append_assoc, List.take_append_drop]
    rw [hB₁, hB]

/-- What a piece of the MAC leaves: the environment, what it writes, the MAC
state `Y` at `W + y`, and the permissions. -/
structure MacStep (c : VG.Proof.AesCcm.AArch64.Cx) (y : Nat) (s : State) (Y : List Byte) (s' : State) : Prop where
  env : VG.Proof.AesCcm.AArch64.Env c s'
  frame : Frame (VG.Proof.AesCcm.AArch64.macR c.W y) s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem k_macR {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {y : Nat} (hy : y + 16 ≤ 2560) :
    ∀ r ∈ VG.Proof.AesCcm.AArch64.macR c.W y, (⟨c.K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w' hy
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)

theorem ciph_macR {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {y : Nat} (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.AArch64.macR c.W y) m m') :
    Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (VG.Proof.AesCcm.AArch64.k_macR L hy r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

/-- A buffer missing `W` keeps its bytes. -/
theorem buf_macR {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.AArch64.Buf c s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.AArch64.macR c.W y) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.wd hy
    · exact hP.wd (by decide)
    · exact hP.wd (by decide)) (by have := hP.lt; omega)

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    (S : VG.Proof.AesCcm.AArch64.Slots c s.mem) (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee y) s fun s' => VG.Proof.AesCcm.AArch64.MacStep c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 c.tl nonce c.al c.n]) s' ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.flags_ok L E S h24) fun s₁ ⟨x9₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.b0Seg_ok L E₁ hnl (by rw [hm₁]; exact hc0) x9₁ hy)
    fun s₃ ⟨E₃, g₃, rd₃, wr₃, f₃, hz, hB⟩ => ?_)
  refine WP.mono (VG.Proof.AesCcm.AArch64.updBlock_ok v L E₃ hy) fun s₄ ⟨E₄, g₄, rd₄, wr₄, f₄, h₄⟩ =>
    ⟨⟨E₄, ?_, ?_, by rw [rd₄, rd₃, rd₁], by rw [wr₄, wr₃, wr₁]⟩, ?_, ?_⟩
  · rw [← hm₁]
    refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₄, hz, hB, ← hm₁, VG.Proof.AesCcm.AArch64.ciph_macR L (y := y) (by omega) (f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩)]
  · rw [g₄ _ (by simp), g₃ _ (by simp), hg₁ _ (by decide)]
  · rw [g₄ _ (by simp), g₃ _ (by simp), hg₁ _ (by decide)]

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Absorb`. -/
section

/-!
# AES-CCM on AArch64: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`, on none if
there are none (`absWhole_ok`), then its last `len mod 16` bytes copied into
the zeroed block `B` (`absTail_ok`); together, the blocks of the padded
string (`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok loopRegs Others add_ofNat_assoc eval_zero ofNat_sub lsr_ofNat
  lsl4_ofNat and15 toNat_ofNat_of_lt)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeBytes_base bytesAt_prefix bytesAt_suffix)

/-- The arguments of the call for the whole blocks. -/
theorem absArgs_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr}
    {len : Nat} (hP : VG.Proof.AesCcm.AArch64.Buf c s P len) (h23 : s.gpr .x23 = P) (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) s fun s₁ =>
      Proof.CmacAes.Stream.AArch64.UArgs s₁ c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R
        (len / 16) ∧ VG.Proof.AesCcm.AArch64.Env c s₁ ∧ Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hl := hP.lt
  obtain ⟨s₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ [mov .x3 .x23, .lsr .x .x4 .x24 4]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .x0 = c.K ∧ s₁.gpr .x1 = BitVec.ofNat 64 c.R ∧ s₁.gpr .x2 = c.W + BitVec.ofNat 64 y ∧
      s₁.gpr .x3 = P ∧ s₁.gpr .x4 = BitVec.ofNat 64 (len / 16) ∧ s₁.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hy' : y < 4096 := by omega
    refine ⟨_, by carun [updArgs, hy'], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x22]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h23]
    · simp [gpr_write, h24, lsr_ofNat len 4 hl]
    · simp [gpr_write, E.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hq := ((hP.take hb).of_eq (s' := s₁) rd₁ wr₁).src
  have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ :=
    (hP.take hb).wd (by omega)
  exact WP.of_runBlock ⟨s₁, run₁, VG.Proof.AesCcm.AArch64.uargs L E₁ (by omega) hq hqy (by omega) x0 x1 x2 x3 x4 x5, E₁, hg₁, hm₁,
    rd₁, wr₁⟩

/-- What `absorbPad`'s pieces leave. -/
structure Absorbed (c : VG.Proof.AesCcm.AArch64.Cx) (y : Nat) (P : Addr) (len : Nat) (s : State) (Y : List Byte) (s' : State) :
    Prop where
  env : VG.Proof.AesCcm.AArch64.Env c s'
  x23 : s'.gpr .x23 = P
  x24 : s'.gpr .x24 = BitVec.ofNat 64 len
  frame : Frame (VG.Proof.AesCcm.AArch64.macR c.W y) s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The whole blocks of the string. -/
theorem absWhole_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.AArch64.Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.seq (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) (callUpdate v.callee)) s
      (VG.Proof.AesCcm.AArch64.Absorbed c y P len s
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16)))))) := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.absArgs_ok L E hy hP h23 h24) fun s₁ ⟨U, E₁, hg₁, hm₁, rd₁, wr₁⟩ => ?_)
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  refine WP.mono (upd_call v v.callee.name U) fun s₂ h =>
    ⟨E₁.of_saved h.saved h.sp h.rd h.wr, ?_, ?_, ?_, ?_, by rw [h.rd, rd₁], by rw [h.wr, wr₁]⟩
  · rw [h.saved _ (by decide) (by decide), hg₁ _ (by decide), h23]
  · rw [h.saved _ (by decide) (by decide), hg₁ _ (by decide), h24]
  · rw [← hm₁]
    exact h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, hm₁, ← bytesAt_prefix _ _ hb]
    rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- The last `len mod 16` (not 0) bytes, padded with zeros in `B`. -/
theorem absTailPre_ok {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.AArch64.Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) (h13 : s.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h0 : len % 16 ≠ 0) :
    WP isa (.seq (.block (zero16 bO ++ ([.lsr .x .x10 .x24 4, .lsl .x .x10 .x10 4, .add .x .x12 .x23 .x10,
        ptr .x11 .x19 bO] : List Instr))) copyLoop) s fun s₃ =>
      VG.Proof.AesCcm.AArch64.Env c s₃ ∧ s₃.gpr .x23 = P ∧ s₃.gpr .x24 = BitVec.ofNat 64 len ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
  have hl := hP.lt
  have hxl := length_bytesAt s.mem P len
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, x11₂, x12₂, x13₂, hg₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      (zero16 bO ++ [.lsr .x .x10 .x24 4, .lsl .x .x10 .x10 4, .add .x .x12 .x23 .x10, ptr .x11 .x19 bO]) s =
        some s₂ ∧
      s₂.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧
      s₂.gpr .x11 = c.W + BitVec.ofNat 64 32 ∧ s₂.gpr .x12 = P + BitVec.ofNat 64 (16 * (len / 16)) ∧
      s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧
      Others [.x9, .x10, .x11, .x12] s s₂ ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h23, h24, lsr_ofNat len 4 hl, lsl4_ofNat]
    · simp [gpr_write, h13]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesCcm.AArch64.Env c s₂ := E.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hb : 16 * (len / 16) + len % 16 = len := by omega
  have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega)).of_eq (s' := s₂) rd₂ wr₂
  have dTB : (⟨P + BitVec.ofNat 64 (16 * (len / 16)), len % 16⟩ : Region).Disjoint
      ⟨c.W + BitVec.ofNat 64 32, len % 16⟩ := hT.wd (by omega)
  have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (c.W + BitVec.ofNat 64 32) (len % 16) :=
    ⟨by omega, hT.rd, E₂.perm.wC (by omega), dTB⟩
  refine WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ (by omega) lp) fun s₃ ⟨hm₃, _, _, hg₃, sp₃, rd₃, wr₃⟩ => ?_
  have E₃ : VG.Proof.AesCcm.AArch64.Env c s₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  -- What was written.
  have e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have fZ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 32) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 40) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))
  have fC : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s₂.mem s₃.mem := by
    rw [hm₃]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains c.W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide))
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem := fZ.trans fC
  have hB₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 =
      (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
    have hs₁ : bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
        (bytesAt s.mem P len).drop (16 * (len / 16)) := by
      rw [Proof.AesGcm.AArch64.bytesAt_frame fZ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hT.wd (by decide)) (by omega),
        show len % 16 = len - 16 * (len / 16) by omega, bytesAt_suffix _ _ (by omega)]
    have hz : bytesAt s₂.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      rw [hm₂, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
    rw [hm₃, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega) (by decide), hs₁, hz,
      List.length_drop, hxl]
    congr 1
    simp only [Spec.Cmac.zeros, Spec.Ccm.zeros, List.drop_replicate]
    congr 1
    omega
  refine ⟨E₃, by rw [hg₃ _ (by decide), hg₂ _ (by decide), h23], by rw [hg₃ _ (by decide), hg₂ _ (by decide), h24],
    by rw [rd₃, rd₂], by rw [wr₃, wr₂], fB, hB₃⟩

/-- The last `len mod 16` (not 0) bytes, padded with zeros in `B`, chained. -/
theorem absTail_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.AArch64.Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) (h13 : s.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h0 : len % 16 ≠ 0) :
    WP isa (absTail v.callee y) s (VG.Proof.AesCcm.AArch64.Absorbed c y P len s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (VG.Proof.AesCcm.AArch64.tailBlocks (bytesAt s.mem P len)))) := by
  have hxl := length_bytesAt s.mem P len
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.absTailPre_ok E hP h23 h24 h13 h0)
    fun s₃ ⟨E₃, x23₃, x24₃, rd₃, wr₃, fB, hB₃⟩ => ?_))
  have hY₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  refine WP.mono (VG.Proof.AesCcm.AArch64.updBlock_ok v L E₃ hy) fun s₄ ⟨E₄, g₄, hr₄, hw₄, f₄, h₄⟩ =>
    ⟨E₄, ?_, ?_, ?_, ?_, by rw [hr₄, rd₃], by rw [hw₄, wr₃]⟩
  · rw [g₄ _ (by simp), x23₃]
  · rw [g₄ _ (by simp), x24₃]
  · refine ((fB.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₄, hY₃, hB₃, VG.Proof.AesCcm.AArch64.ciph_macR L (y := y) (by omega) (fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)]
    simp only [VG.Proof.AesCcm.AArch64.tailBlocks, hxl, h0, ↓reduceIte]

/-- The length of the last bytes, `len mod 16`. -/
theorem absMask_ok {s : State} {len : Nat} (hl : len < 2 ^ 64)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.block [imm .x9 15, .logic .and .x .x13 .x24 .x9]) s fun s₂ =>
      s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧ Others [.x9, .x13] s s₂ ∧ s₂.mem = s.mem ∧
      s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain ⟨s₂, run₂, x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [imm .x9 15, .logic .and .x .x13 .x24 .x9]
      s = some s₂ ∧ s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧ Others [.x9, .x13] s s₂ ∧ s₂.mem = s.mem ∧
      s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h24]
      rw [and15, toNat_ofNat_of_lt hl]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  exact WP.of_runBlock ⟨s₂, run₂, x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.AArch64.Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (absorbPad v.callee y) s (VG.Proof.AesCcm.AArch64.Absorbed c y P len s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  have hl := hP.lt
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.absWhole_ok v L E hy hP h23 h24) fun s₁ A₁ => ?_))
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.absMask_ok hl A₁.x24) fun s₂ ⟨x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesCcm.AArch64.Env c s₂ := A₁.env.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hb := Proof.AesCcm.blocks_pad16 (bytesAt s.mem P len)
  rw [length_bytesAt] at hb
  have hRb := L.rb
  refine WP.ite (decide (len % 16 = 0)) (eval_zero x13₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E₂, by rw [hg₂ _ (by decide), A₁.x23], by rw [hg₂ _ (by decide), A₁.x24],
      by rw [hm₂]; exact A₁.frame, ?_, by rw [rd₂, A₁.rd], by rw [wr₂, A₁.wr]⟩
    rw [hm₂, A₁.out, hb]
    simp only [h0, ↓reduceIte, List.append_nil]
  · have h0 : len % 16 ≠ 0 := of_decide_eq_false hf
    refine WP.mono (VG.Proof.AesCcm.AArch64.absTail_ok v L E₂ hy (hP.of_eq (by rw [rd₂, A₁.rd]) (by rw [wr₂, A₁.wr]))
      (by rw [hg₂ _ (by decide), A₁.x23]) (by rw [hg₂ _ (by decide), A₁.x24]) x13₂ h0) fun s₃ A₃ =>
      ⟨A₃.env, A₃.x23, A₃.x24, A₁.frame.trans (by rw [← hm₂]; exact A₃.frame), ?_,
        by rw [A₃.rd, rd₂, A₁.rd], by rw [A₃.wr, wr₂, A₁.wr]⟩
    rw [A₃.out, hm₂, A₁.out, VG.Proof.AesCcm.AArch64.buf_macR hP (by omega) A₁.frame, VG.Proof.AesCcm.AArch64.ciph_macR L (by omega) A₁.frame,
      ← Proof.Cmac.chain_append, hb, VG.Proof.AesCcm.AArch64.tailBlocks, length_bytesAt]

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Header`. -/
section

/-!
# AES-CCM on AArch64: the first block of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a > 0` (A.2.2) at its start: `[a]₁₆`,
`0xff ‖ 0xfe ‖ [a]₃₂` or `0xff ‖ 0xff ‖ [a]₆₄`, by byte-reversing and
shifting `a` (`header_ok`); its length is in `x25`. `aadHead y` copies the
first `min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok minK_ok loopRegs minRegs Others add_ofNat_assoc eval_zero
  ofNat_sub lsr_ofNat toNat_ofNat_of_lt ofNat_add_ofNat)
open VG.Proof.AesCcm (hdrLen headLen length_bytesAt bytesAt_writeW64_at bytesAt_writeW64_base
  bytesAt_writeBytes_at bytesAt_prefix enc_lo enc_mid enc_hi)

/-- The sign of a difference of two numbers below `2⁶³`: whether the first
is the smaller. -/
theorem sign63 {x k : Nat} (hx : x < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if x < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega),
    Nat.shiftRight_eq_div_pow]
  split
  · rw [toNat_ofNat_of_lt (by decide)]; omega
  · rw [toNat_ofNat_of_lt (by decide)]; omega

theorem movz_lit (k : Nat) (hk : k < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< (16 * 0) = BitVec.ofNat 64 k :=
  Proof.AesGcm.AArch64.movz_ofNat hk

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`x24`) at its start, and its length in `x25`. -/
theorem header_ok {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 64)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 a) :
    WP isa header s fun s' => VG.Proof.AesCcm.AArch64.Env c s' ∧ s'.gpr .x25 = BitVec.ofNat 64 (hdrLen a) ∧
      Others [.x9, .x10, .x25] s s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 34 + 8 ≤ 2560 by decide)
  have e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have e34 : c.W + BitVec.ofNat 64 34 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2 := by rw [add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by decide)
  -- `B` zeroed; `a >> 32`.
  obtain ⟨s₁, run₁, hm₁, x9₁, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (zero16 bO ++ [.lsr .x .x9 .x24 32]) s =
      some s₁ ∧
      s₁.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧ s₁.gpr .x9 = BitVec.ofNat 64 (a / 2 ^ 32) ∧
      Others [.x9] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, h24, lsr_ofNat a 32 ha]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [hm₁, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  have fz : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64) (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (cB 40 8 (by decide) (by decide))
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others hg₁ (by decide) sp₁ rd₁ wr₁
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₁ _ (by decide), h24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (a / 2 ^ 32 = 0)) (eval_zero x9₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h₂ : a < 2 ^ 32 := by have := of_decide_eq_true ht; omega
    obtain ⟨s₂, run₂, x9₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
        [.lsr .x .x9 .x24 8, .subImm .x .x9 .x9 255, .lsr .x .x9 .x9 63] s₁ = some s₂ ∧
        s₂.gpr .x9 = BitVec.ofNat 64 (if a / 256 < 255 then 1 else 0) ∧ Others [.x9] s₁ s₂ ∧
        s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by carun [], ?_⟩
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · simp only [gpr_write, BitVec.setWidth_eq, ite_true, h24₁, lsr_ofNat a 8 ha]
        exact VG.Proof.AesCcm.AArch64.sign63 (by omega) (by decide)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, hr]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : VG.Proof.AesCcm.AArch64.Env c s₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
    have h24₂ : s₂.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₂ _ (by decide), h24₁]
    have w₁' := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
    refine WP.ite (decide ((if a / 256 < 255 then 1 else 0) = 0)) (eval_zero x9₂ (by split <;> decide))
      (fun ht => ?_) (fun hf => ?_)
    · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
      have h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_true ht; split at this <;> simp_all <;> omega
      have kf : (BitVec.setWidth 64 (0xfeff : BitVec 16) <<< 0 : BitVec 64) = BitVec.ofNat 64 0xfeff := by decide
      obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
          [.rev .x9 .x24, .lsr .x .x9 .x9 16, .movz .x .x10 0xfeff 0, .logic .orr .x .x9 .x9 .x10,
            .str .x .x9 .x19 bO, imm .x25 6] s₂ = some s₃ ∧
          s₃.mem = s₂.mem.writeW (c.W + BitVec.ofNat 64 32)
            (byteRev64 (BitVec.ofNat 64 a) >>> 16 ||| BitVec.ofNat 64 0xfeff) ∧
          s₃.gpr .x25 = BitVec.ofNat 64 6 ∧ Others [.x9, .x10, .x25] s₂ s₃ ∧
          s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
        refine ⟨_, by carun [E₂.x19, w₁', kf], ?_⟩
        refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
        · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₂]; rfl
        · simp [gpr_write]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [gpr_write, hr]
      refine WP.of_runBlock ⟨s₃, run₃, E₂.others hg₃ (by decide) sp₃ rd₃ wr₃,
        by rw [x25₃, Proof.AesCcm.hdrLen_mid h₁ h₂], fun r hr => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
        ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₂ r (by simp [hr.1]), hg₁ r (by simp [hr.1])]
      · rw [hm₃, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
      · rw [hm₃, bytesAt_writeW64_base _ _ _ (by decide) (by decide), hm₂, hz]
        exact enc_mid h₁ h₂ _ rfl
    · -- `[a]₁₆`.
      have h₁ : a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_false hf; split at this <;> simp_all <;> omega
      obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
          [.rev .x9 .x24, .lsr .x .x9 .x9 48, .str .x .x9 .x19 bO, imm .x25 2] s₂ = some s₃ ∧
          s₃.mem = s₂.mem.writeW (c.W + BitVec.ofNat 64 32) (byteRev64 (BitVec.ofNat 64 a) >>> 48) ∧
          s₃.gpr .x25 = BitVec.ofNat 64 2 ∧ Others [.x9, .x10, .x25] s₂ s₃ ∧
          s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
        refine ⟨_, by carun [E₂.x19, w₁'], ?_⟩
        refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
        · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₂]; rfl
        · simp [gpr_write]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [gpr_write, hr]
      refine WP.of_runBlock ⟨s₃, run₃, E₂.others hg₃ (by decide) sp₃ rd₃ wr₃,
        by rw [x25₃, Proof.AesCcm.hdrLen_lo h₁], fun r hr => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
        ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₂ r (by simp [hr.1]), hg₁ r (by simp [hr.1])]
      · rw [hm₃, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
      · rw [hm₃, bytesAt_writeW64_base _ _ _ (by decide) (by decide), hm₂, hz]
        exact enc_lo h₁ _ rfl
  · -- `0xff ‖ 0xff ‖ [a]₆₄`.
    have h₂ : ¬ a < 2 ^ 32 := by have := of_decide_eq_false hf; omega
    have h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by omega
    have w₁' := E₁.perm.wW (show 32 + 8 ≤ 2560 by decide)
    have w₃' := E₁.perm.wW (show 34 + 8 ≤ 2560 by decide)
    have kf : (BitVec.setWidth 64 (0xffff : BitVec 16) <<< 0 : BitVec 64) = BitVec.ofNat 64 0xffff := by decide
    obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
        [.movz .x .x9 0xffff 0, .str .x .x9 .x19 bO, .rev .x9 .x24, ptr .x10 .x19 (bO + 2),
          .str .x .x9 .x10 0, imm .x25 10] s₁ = some s₃ ∧
        s₃.mem = (s₁.mem.writeW (c.W + BitVec.ofNat 64 32) (BitVec.ofNat 64 0xffff)).writeW
          (c.W + BitVec.ofNat 64 34) (byteRev64 (BitVec.ofNat 64 a)) ∧
        s₃.gpr .x25 = BitVec.ofNat 64 10 ∧ Others [.x9, .x10, .x25] s₁ s₃ ∧
        s₃.sp = s₁.sp ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
      refine ⟨_, by carun [E₁.x19, w₁', w₃', kf], ?_⟩
      refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
      · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₁]; rfl
      · simp [gpr_write]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, hr]
    refine WP.of_runBlock ⟨s₃, run₃, E₁.others hg₃ (by decide) sp₃ rd₃ wr₃,
      by rw [x25₃, Proof.AesCcm.hdrLen_hi h₁ h₂], fun r hr => ?_, by rw [rd₃, rd₁], by rw [wr₃, wr₁], ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₁ r (by simp [hr.1])]
    · rw [hm₃]
      exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (cB 34 8 (by decide) (by decide))
    · rw [hm₃, e34, bytesAt_writeW64_at _ _ _ (by decide) (by decide),
        bytesAt_writeW64_base _ _ _ (by decide) (by decide), hz]
      exact enc_hi h₁ h₂ ha

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Mac`. -/
section

/-!
# AES-CCM on AArch64: the MAC (`aadHead y`, `mac y`)

Untrusted: everything here is checked by Lean. `aadHead y` writes the
encoding of the length `a` of the associated data to `B`, copies its first
`min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`);
the associated data is that block and the rest of it, padded, if there is
any (`aadPart_ok`): the blocks `Proof.AesCcm.adataBlocks`. `mac y` chains
`B₀`, the associated data and the payload padded (`mac_ok`): the blocks of
`Spec.Ccm.format`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok minK_ok loopRegs minRegs Others add_ofNat_assoc eval_zero
  ofNat_sub toNat_ofNat_of_lt ofNat_add_ofNat)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks length_bytesAt bytesAt_writeBytes_at bytesAt_prefix
  bytesAt_suffix)

/-- The encoding of the length of the associated data, its first bytes and
the arguments of the chaining: what `aadHead` does before its call. -/
theorem aadHeadPre_ok {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {A : Addr} {a : Nat} (hA : VG.Proof.AesCcm.AArch64.Buf c s A a)
    (ha0 : 0 < a) (h23 : s.gpr .x23 = A) (h24 : s.gpr .x24 = BitVec.ofNat 64 a) :
    WP isa (.seq header (.seq minK (.seq (.block [.add .x .x11 .x19 .x25, ptr .x11 .x11 bO, mov .x12 .x23,
        mov .x13 .x10]) (.seq copyLoop (.block [.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10]))))) s fun s₅ =>
      VG.Proof.AesCcm.AArch64.Env c s₅ ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr ∧ Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₅.mem ∧
      s₅.gpr .x23 = A + BitVec.ofNat 64 (VG.Proof.AesCcm.headLen a) ∧ s₅.gpr .x24 = BitVec.ofNat 64 (a - VG.Proof.AesCcm.headLen a) ∧
      bytesAt s₅.mem (c.W + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (VG.Proof.AesCcm.headLen a)) := by
  have ha := hA.lt
  have hh := Proof.AesCcm.hdrLen_le a
  have hh2 : 2 ≤ hdrLen a := by unfold hdrLen; split <;> [omega; split <;> omega]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.header_ok E ha0 ha h24) fun s₁ ⟨E₁, x25₁, hg₁, rd₁, wr₁, f₁, hB₁⟩ => ?_)
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₁ _ (by decide), h24]
  have h23₁ : s₁.gpr .x23 = A := by rw [hg₁ _ (by decide), h23]
  refine WP.seq (WP.mono (minK_ok s₁ x25₁ h24₁ (by omega) ha) fun s₂ ⟨x10₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = VG.Proof.AesCcm.headLen a := by unfold VG.Proof.AesCcm.headLen; omega
  rw [hn1] at x10₂
  have hn1' : 1 ≤ VG.Proof.AesCcm.headLen a ∧ VG.Proof.AesCcm.headLen a ≤ a ∧ hdrLen a + VG.Proof.AesCcm.headLen a ≤ 16 := by unfold VG.Proof.AesCcm.headLen; omega
  have E₂ : VG.Proof.AesCcm.AArch64.Env c s₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  obtain ⟨s₃, run₃, x11₃, x12₃, x13₃, hg₃, hm₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
      [.add .x .x11 .x19 .x25, ptr .x11 .x11 bO, mov .x12 .x23, mov .x13 .x10] s₂ = some s₃ ∧
      s₃.gpr .x11 = c.W + BitVec.ofNat 64 (32 + hdrLen a) ∧ s₃.gpr .x12 = A ∧
      s₃.gpr .x13 = BitVec.ofNat 64 (VG.Proof.AesCcm.headLen a) ∧ Others [.x11, .x12, .x13] s₂ s₃ ∧
      s₃.mem = s₂.mem ∧ s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have x25₂ : s₂.gpr .x25 = BitVec.ofNat 64 (hdrLen a) := by rw [hg₂ _ (by decide), x25₁]
    have x23₂ : s₂.gpr .x23 = A := by rw [hg₂ _ (by decide), h23₁]
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E₂.x19, x25₂, BitVec.setWidth_eq]
      rw [BitVec.add_assoc, ofNat_add_ofNat, Nat.add_comm (hdrLen a) 32]
    · simp [gpr_write, x23₂]
    · simp [gpr_write, x10₂]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.AArch64.Env c s₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  have hA₃ := hA.of_eq (s' := s₃) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
  have dAB : (⟨A, VG.Proof.AesCcm.headLen a⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 (32 + hdrLen a), VG.Proof.AesCcm.headLen a⟩ :=
    (hA.take hn1'.2.1).wd (by omega)
  have lp : LoopPre s₃ A (c.W + BitVec.ofNat 64 (32 + hdrLen a)) (VG.Proof.AesCcm.headLen a) :=
    ⟨by omega, (hA₃.take hn1'.2.1).rd, E₃.perm.wC (by omega), dAB⟩
  refine WP.seq (WP.mono (copyLoop_ok s₃ x12₃ x11₃ x13₃ hn1'.1 lp) fun s₄ ⟨hm₄, _, _, hg₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ : VG.Proof.AesCcm.AArch64.Env c s₄ := E₃.others hg₄ (by decide) sp₄ rd₄ wr₄
  have x23₄ : s₄.gpr .x23 = A := by
    rw [hg₄ _ (by decide), hg₃ _ (by decide), hg₂ _ (by decide), h23₁]
  have x24₄ : s₄.gpr .x24 = BitVec.ofNat 64 a := by
    rw [hg₄ _ (by decide), hg₃ _ (by decide), hg₂ _ (by decide), h24₁]
  have x10₄ : s₄.gpr .x10 = BitVec.ofNat 64 (VG.Proof.AesCcm.headLen a) := by
    rw [hg₄ _ (by decide), hg₃ _ (by decide), x10₂]
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₅ hs₅ => ?_
  subst hs₅
  -- What was written.
  have fC : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains c.W (d := 32 + hdrLen a) (n := VG.Proof.AesCcm.headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← hm₂] at f₁; rw [← hm₃] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem A (VG.Proof.AesCcm.headLen a) = (bytesAt s.mem A a).take (VG.Proof.AesCcm.headLen a) := by
    rw [hm₃, hm₂, Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hA.take hn1'.2.1).wd (by decide)) (by omega),
      bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (VG.Proof.AesCcm.headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem A a).take (VG.Proof.AesCcm.headLen a)).length = VG.Proof.AesCcm.headLen a := by
      rw [List.length_take, length_bytesAt]; omega
    rw [hm₄, show c.W + BitVec.ofNat 64 (32 + hdrLen a) = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by
        rw [add_ofNat_assoc], bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide),
      length_bytesAt, hAk, hm₃, hm₂, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (VG.Proof.AesCcm.headLen a))
      (by rw [List.length_append, hl, htl]; omega) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + VG.Proof.AesCcm.headLen a - hdrLen a) = 16 - (hdrLen a + VG.Proof.AesCcm.headLen a) by omega]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega)
  refine ⟨E₄.others (rs := [.x23, .x24]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]) (by decide)
      rfl rfl rfl, by simp only [rd_write]; rw [rd₄, rd₃, rd₂, rd₁], by simp only [wr_write]; rw [wr₄, wr₃, wr₂, wr₁],
      fB, ?_, ?_, hB₄⟩
  · simp [gpr_write, x23₄, x10₄]
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, x24₄, x10₄]
    exact ofNat_sub hn1'.2.1 ha

/-- The first block of the associated data. -/
theorem aadHead_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : Addr} {a : Nat} (hA : VG.Proof.AesCcm.AArch64.Buf c s A a) (ha0 : 0 < a)
    (h23 : s.gpr .x23 = A) (h24 : s.gpr .x24 = BitVec.ofNat 64 a) :
    WP isa (aadHead v.callee y) s (VG.Proof.AesCcm.AArch64.Absorbed c y (A + BitVec.ofNat 64 (VG.Proof.AesCcm.headLen a)) (a - VG.Proof.AesCcm.headLen a) s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (VG.Proof.AesCcm.headLen a))])) := by
  refine VG.Proof.AesCcm.AArch64.seq_assoc5 (WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.aadHeadPre_ok E hA ha0 h23 h24)
    fun s₅ ⟨E₅, rd₅, wr₅, fB, x23₅, x24₅, hB⟩ => ?_))
  have hY₅ : bytesAt s₅.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  refine WP.mono (VG.Proof.AesCcm.AArch64.updBlock_ok v L E₅ hy) fun s₆ ⟨E₆, g₆, rd₆, wr₆, f₆, h₆⟩ =>
    ⟨E₆, by rw [g₆ _ (by simp), x23₅], by rw [g₆ _ (by simp), x24₅],
      (fB.sub fun r hr => ?_).trans (f₆.sub fun r hr => ?_), ?_, by rw [rd₆, rd₅], by rw [wr₆, wr₅]⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₆, hY₅, hB, VG.Proof.AesCcm.AArch64.ciph_macR L (y := y) (by omega) (fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)]

/-- The associated data, formatted and chained, if there is any. -/
theorem aadPart_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) (h23 : s.gpr .x23 = c.A) (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) :
    WP isa (.ite (.zero .x .x24) (.block []) (.seq (aadHead v.callee y) (absorbPad v.callee y))) s
      (VG.Proof.AesCcm.AArch64.MacStep c y s (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem c.A c.al)))) := by
  have ha := L.al_lt
  have hA := L.bufA E.perm
  refine WP.ite (decide (c.al = 0)) (eval_zero h24 ha) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E, Frame.refl _ _, ?_, rfl, rfl⟩
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : c.al ≠ 0 := of_decide_eq_false hf
    refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.aadHead_ok v L E hy hA (by omega) h23 h24) fun s₂ A₂ => ?_)
    have hn1 : VG.Proof.AesCcm.headLen c.al ≤ c.al := by unfold VG.Proof.AesCcm.headLen; omega
    have hT := (hA.drop hn1).of_eq (s' := s₂) A₂.rd A₂.wr
    refine WP.mono (VG.Proof.AesCcm.AArch64.absorbPad_ok v L A₂.env hy hT A₂.x23 A₂.x24) fun s₃ A₃ =>
      ⟨A₃.env, A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd], by rw [A₃.wr, A₂.wr]⟩
    rw [A₃.out, A₂.out, VG.Proof.AesCcm.AArch64.buf_macR hT (by omega) A₂.frame, VG.Proof.AesCcm.AArch64.ciph_macR L (by omega) A₂.frame,
      bytesAt_suffix _ _ hn1, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

/-- The addresses of the associated data, from their slots. -/
theorem aadLd_ok {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) (S : VG.Proof.AesCcm.AArch64.Slots c s.mem) :
    WP isa (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO]) s fun s₁ =>
      s₁.gpr .x23 = c.A ∧ s₁.gpr .x24 = BitVec.ofNat 64 c.al ∧ Others [.x23, .x24] s s₁ ∧ s₁.mem = s.mem ∧
        s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := E.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have q₂ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [E.x19, q₁, q₂], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq]; rw [← S.aad]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq]; rw [← S.alen]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]

/-- The data as the string to absorb. -/
theorem dataArgs_ok {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) :
    WP isa (.block [mov .x23 .x27, mov .x24 .x28]) s fun s₁ =>
      s₁.gpr .x23 = c.D ∧ s₁.gpr .x24 = BitVec.ofNat 64 c.n ∧ Others [.x23, .x24] s s₁ ∧ s₁.mem = s.mem ∧
        s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨by simp [gpr_write, E.x27], by simp [gpr_write, E.x28], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s)
    (S : VG.Proof.AesCcm.AArch64.Slots c s.mem) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (mac v.callee y) s (VG.Proof.AesCcm.AArch64.MacStep c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format c.tl nonce (bytesAt s.mem c.A c.al) (bytesAt s.mem c.D c.n)))) := by
  have hy16 : y + 16 ≤ 2560 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.aadLd_ok E S) fun s₁ ⟨x23₁, x24₁, og₁, hm₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others og₁ (by decide) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.b0_ok v L E₁ (by rw [hm₁]; exact S) x24₁ hnl (by rw [hm₁]; exact hc0) hy)
    fun s₂ ⟨M₂, x23₂, x24₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.aadPart_ok v L M₂.env hy (by rw [x23₂, x23₁]) (by rw [x24₂, x24₁])) fun s₃ M₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.dataArgs_ok M₃.env) fun s₄ ⟨x23₄, x24₄, og₄, hm₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ : VG.Proof.AesCcm.AArch64.Env c s₄ := M₃.env.others og₄ (by decide) sp₄ rd₄ wr₄
  refine WP.mono (VG.Proof.AesCcm.AArch64.absorbPad_ok v L E₄ hy (L.bufD E₄.perm) x23₄ x24₄) fun s₅ A₅ => ?_
  have f₃ : Frame (VG.Proof.AesCcm.AArch64.macR c.W y) s.mem s₃.mem := by rw [← hm₁]; exact M₂.frame.trans M₃.frame
  refine ⟨A₅.env, f₃.trans (by rw [← hm₄]; exact A₅.frame), ?_, by rw [A₅.rd, rd₄, M₃.rd, M₂.rd, rd₁],
    by rw [A₅.wr, wr₄, M₃.wr, M₂.wr, wr₁]⟩
  have hl : nonce.length ≤ 15 := by rw [hnl]; have := L.h13; omega
  have f₂ : Frame (VG.Proof.AesCcm.AArch64.macR c.W y) s.mem s₂.mem := by rw [← hm₁]; exact M₂.frame
  rw [A₅.out, hm₄, M₃.out, M₂.out, VG.Proof.AesCcm.AArch64.ciph_macR L hy16 f₃, VG.Proof.AesCcm.AArch64.ciph_macR L hy16 f₂, hm₁, VG.Proof.AesCcm.AArch64.buf_macR (L.bufD E.perm) hy16 f₃,
    VG.Proof.AesCcm.AArch64.buf_macR (L.bufA E.perm) hy16 f₂, Proof.AesCcm.format_eq c.tl hl, length_bytesAt, length_bytesAt,
    Proof.Cmac.chain_append, Proof.Cmac.chain_append]

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Tag`. -/
section

/-!
# AES-CCM on AArch64: the MAC encrypted (`tag y`)

Untrusted: everything here is checked by Lean. `tag y` copies `Ctr₀` to
`W + 64` (`tagArgs_ok`) and calls `vg_aes_ctr32` on the MAC at `W + y`: it
XORs in `CIPH_K(Ctr₀)`, CCM's keystream from `Ctr₀` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (CtrCall ctr_call Others)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesCcm (xorFrom)

/-- The arguments of the call: `Ctr₀` at `W + 64`. -/
theorem tagArgs_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (([imm .x9 0] : List Instr) ++ ctrAt ++ ctrArgs ++ ([ptr .x3 .x19 y, imm .x4 1] : List Instr))) s
      fun s₃ => VG.Proof.AesCcm.AArch64.Env c s₃ ∧
        CtrCall s₃ c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 y) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
        Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] s s₃ ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
        Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
        bytesAt s₃.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  have h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  have h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  have E₁ : VG.Proof.AesCcm.AArch64.Env c t₁ := E.others (rs := [.x9]) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]) (by decide)
    (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  have h9 : t₁.gpr .x9 = BitVec.ofNat 64 0 := by rw [← ht₁]; simp [gpr_write]
  have hm₁ : t₁.mem = s.mem := by rw [← ht₁]; rfl
  have hg₁ : Others [.x9] s t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  refine WP.block_append (WP.mono (VG.Proof.AesCcm.AArch64.ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := 0) (Nat.pow_pos (by decide))
    h9) fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesCcm.AArch64.Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hy' : y < 4096 := by omega
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [ctrArgs, hy'], rfl⟩ fun t₃ ht₃ => ?_
  have hg₃ : Others [.x0, .x1, .x2, .x3, .x4, .x5] t₂ t₃ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; rw [← ht₃]; simp [gpr_write, hr]
  have E₃ : VG.Proof.AesCcm.AArch64.Env c t₃ := E₂.others hg₃ (by decide) (by rw [← ht₃]; rfl) (by rw [← ht₃]; rfl) (by rw [← ht₃]; rfl)
  have hm₃ : t₃.mem = t₂.mem := by rw [← ht₃]; rfl
  refine ⟨E₃, VG.Proof.AesCcm.AArch64.cargsW L E₃ (o := 64) (d := y) (by decide) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_, ?_,
    by rw [← ht₃]; simp only [rd_write]; rw [rd₂, ← ht₁]; rfl,
    by rw [← ht₃]; simp only [wr_write]; rw [wr₂, ← ht₁]; rfl,
    by rw [hm₃, ← hm₁]; exact f₂, by rw [hm₃]; exact hc₂⟩
  · rw [← ht₃]; simp [gpr_write, E₂.x21]
  · rw [← ht₃]; simp [gpr_write, E₂.x22]
  · rw [← ht₃]; simp [gpr_write, E₂.x19]
  · rw [← ht₃]; simp [gpr_write, E₂.x19]
  · rw [← ht₃]; simp [gpr_write]
  · rw [← ht₃]; simp [gpr_write, E₂.x19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
      hg₂ r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      hg₁ r (by simp [hr.2.2.2.2.2.2.1])]

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`. -/
theorem tag_ok (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (tag v.callee y) s fun s' => VG.Proof.AesCcm.AArch64.Env c s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩]
        s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 0 (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16) := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.tagArgs_ok L E hnl hc0 hy) fun t₃ ⟨E₃, C₃, _, rd₃, wr₃, f₃, hc₃⟩ => ?_)
  refine WP.mono (ctr_call v C₃) fun t₄ h => ⟨E₃.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, rd₃],
    by rw [h.wr, wr₃], ?_, ?_⟩
  · refine (f₃.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 0) (by rw [hnl]; have := L.h13; omega) (fun i hi => by
      rw [show i = 0 by omega, Nat.add_zero]
      show Spec.Gcm.ofBytes _ = _
      rw [hc₃]) h.out
    rw [Nat.mul_one] at hx
    have hK : Spec.Ccm.ctxCiph t₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
      unfold Spec.Ccm.ctxCiph
      rw [Proof.AesGcm.AArch64.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega)]
    have hY : bytesAt t₃.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
      Proof.AesGcm.AArch64.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    rw [hx, hK, hY]

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Chunk`. -/
section

/-!
# AES-CCM on AArch64: a chunk of counter mode (`ctrChunk`)

Untrusted: everything here is checked by Lean. After `b` whole blocks
(`CtrInv`), `ctrChunk` encrypts `k = min (n/16 − b, 2³² − (1 + b) mod 2³²)`
more by `vg_aes_ctr32` from `Ctr₁₊ᵦ`, whose counters do not wrap around in
their low 32 bits, so that they are CCM's (`chunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call Others add_ofNat_assoc eval_zero eval_nonzero ofNat_sub
  toNat_ofNat_of_lt ofNat_add_ofNat lsl4_ofNat covers_off)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesCcm (xorFrom xorFrom_append repeat_inc32_ctrBlock ctr32_ccm length_bytesAt bytesAt_prefix
  bytesAt_suffix)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `W + 64`, the
working space of the functions called and the data. -/
abbrev ctrR (c : VG.Proof.AesCcm.AArch64.Cx) : List Region :=
  [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩, ⟨c.D, c.n⟩]

theorem ctrR_mut (c : VG.Proof.AesCcm.AArch64.Cx) : ∀ r ∈ VG.Proof.AesCcm.AArch64.ctrR c, ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesCcm.AArch64.sub_lo (by decide)
  · exact VG.Proof.AesCcm.AArch64.sub_hi (by decide) (by decide)
  · exact VG.Proof.AesCcm.AArch64.sub_data

/-- The parts of `W` that `ctr` does not write. -/
theorem ctrR_disj {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {d k : Nat} (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 384)) :
    ∀ r ∈ VG.Proof.AesCcm.AArch64.ctrR c, (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (by omega) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.d_w' (by omega)).symm

theorem ctrR_k {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) : ∀ r ∈ VG.Proof.AesCcm.AArch64.ctrR c, (⟨c.K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.k_d

theorem ciph_ctrR {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.AArch64.ctrR c) m m') :
    Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (VG.Proof.AesCcm.AArch64.ctrR_k L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

/-- The state of `ctr` after `b` whole blocks, from the state `s` it
started from: those encrypted, the rest of the data as it was. -/
structure CtrInv (c : VG.Proof.AesCcm.AArch64.Cx) (nonce : List Byte) (s : State) (b : Nat) (t : State) : Prop where
  env : VG.Proof.AesCcm.AArch64.Env c t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  x23 : t.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b)
  x24 : t.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b)
  le : b ≤ c.n / 16
  frame : Frame (VG.Proof.AesCcm.AArch64.ctrR c) s.mem t.mem
  done : bytesAt t.mem c.D (16 * b) = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D (16 * b))
  rest : bytesAt t.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.n - 16 * b) =
    bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.n - 16 * b)

theorem low32 (x : Nat) : (BitVec.ofNat 64 x).setWidth 32 + BitVec.ofNat 32 0 = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `k = min (m, 2³² − (1 + b) mod 2³²)` in `x26`, for `m` blocks left. -/
theorem kSel_ok {b m : Nat} {t : State} (h24 : t.gpr .x24 = BitVec.ofNat 64 m)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b)) (hm : m < 2 ^ 60) :
    WP isa (.seq (.block [.addImm .w .x9 .x25 0, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9, .sub .x .x11 .x24 .x10,
        .lsr .x .x11 .x11 63]) (.ite (.zero .x .x11) (.block [mov .x26 .x10]) (.block [mov .x26 .x24]))) t
      fun t₂ => t₂.gpr .x26 = BitVec.ofNat 64 (min m (2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
        Others [.x9, .x10, .x11, .x26] t t₂ ∧ t₂.mem = t.mem ∧ t₂.sp = t.sp ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  have hj := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide)
  obtain ⟨t₁, run₁, x10₁, x11₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.addImm .w .x9 .x25 0, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9, .sub .x .x11 .x24 .x10,
        .lsr .x .x11 .x11 63] t = some t₁ ∧
      t₁.gpr .x10 = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) ∧
      t₁.gpr .x11 = BitVec.ofNat 64 (if m < 2 ^ 32 - (1 + b) % 2 ^ 32 then 1 else 0) ∧
      Others [.x9, .x10, .x11] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    have k1 : (BitVec.setWidth 64 (1 : BitVec 16) <<< 32 : BitVec 64) = BitVec.ofNat 64 (2 ^ 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rfl
    have hx10 : BitVec.ofNat 64 (2 ^ 32) - BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (1 + b))) =
        BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat]
      omega
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h25, k1, hx10]
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h25, h24, k1, hx10]
      exact VG.Proof.AesCcm.AArch64.sign63 (by omega) (by omega)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x11₁ (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
  · have h : ¬ m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by
      have := of_decide_eq_true ht; split at this <;> simp_all
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₂ ht₂ => ?_
    subst ht₂
    refine ⟨?_, fun r hr => ?_, hm₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, x10₁]; rw [Nat.min_eq_right (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.2.2.2, hg₁ r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  · have h : m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by
      have := of_decide_eq_false hf; split at this <;> simp_all
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₂ ht₂ => ?_
    subst ht₂
    refine ⟨?_, fun r hr => ?_, hm₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, hg₁ .x24 (by decide), h24]; rw [Nat.min_eq_left (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.2.2.2, hg₁ r (by simp [hr.1, hr.2.1, hr.2.2.1])]


/-- The arguments of `vg_aes_ctr32` for a chunk, and `Ctr₁₊ᵦ`. -/
theorem setup_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {b k : Nat}
    (hb : b + k ≤ c.n / 16) (hk : 1 ≤ k) {t : State} (E : VG.Proof.AesCcm.AArch64.Env c t)
    (hc0 : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (h23 : t.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b)) (h25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b))
    (h26 : t.gpr .x26 = BitVec.ofNat 64 k) :
    WP isa (.block (([mov .x9 .x25] : List Instr) ++ ctrAt ++ ctrArgs ++ ([mov .x3 .x23, mov .x4 .x26] : List Instr))) t
      fun t₅ => VG.Proof.AesCcm.AArch64.Env c t₅ ∧
        CtrCall t₅ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k ∧
        Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] t.mem t₅.mem ∧
        bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b) ∧
        Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] t t₅ ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
  have h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  have h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  have hq16 : c.n / 16 < 256 ^ (15 - nonce.length) := by
    rw [hnl]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) L.hn
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  have hg₁ : Others [.x9] t t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  have E₁ : VG.Proof.AesCcm.AArch64.Env c t₁ := E.others hg₁ (by decide) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  have h9 : t₁.gpr .x9 = BitVec.ofNat 64 (1 + b) := by rw [← ht₁]; simp [gpr_write, h25]
  have hm₁ : t₁.mem = t.mem := by rw [← ht₁]; rfl
  refine WP.block_append (WP.mono (VG.Proof.AesCcm.AArch64.ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := 1 + b) (by omega) h9)
    fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesCcm.AArch64.Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [ctrArgs], rfl⟩ fun t₅ ht₅ => ?_
  have hg₅ : Others [.x0, .x1, .x2, .x3, .x4, .x5] t₂ t₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; rw [← ht₅]; simp [gpr_write, hr]
  have E₅ : VG.Proof.AesCcm.AArch64.Env c t₅ := E₂.others hg₅ (by decide) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl)
  have hm₅ : t₅.mem = t₂.mem := by rw [← ht₅]; rfl
  have g₂ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → t₂.gpr r = t.gpr r := fun r a b' c' => by
    rw [hg₂ r (by simp [a, b', c']), hg₁ r (by simp [a])]
  have hS := (L.bufD E₂.perm).slice (a := 16 * b) (k := 16 * k) (by omega)
  have hqo : (⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 64, 16⟩ :=
    hS.wd (by decide)
  have hqk : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩ :=
    L.k_d.sub_right (Offset.sub_base c.D (by omega))
  have hqw : Covers [⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩] t₅.wr :=
    covers_off E₅.perm.d (by omega) L.n_lt
  have hS₅ := hS.of_eq (s' := t₅) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl)
  refine ⟨E₅, ?_, by rw [hm₅, ← hm₁]; exact f₂, by rw [hm₅]; exact hc₂, ?_, by rw [← ht₅]; simp only [rd_write]; rw [rd₂, ← ht₁]; rfl,
    by rw [← ht₅]; simp only [wr_write]; rw [wr₂, ← ht₁]; rfl⟩
  · refine VG.Proof.AesCcm.AArch64.cargs L E₅ (o := 64) (by decide) hS₅.src hqo hqk hqw (by have := L.n_lt; omega) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← ht₅]; simp [gpr_write, E₂.x21]
    · rw [← ht₅]; simp [gpr_write, E₂.x22]
    · rw [← ht₅]; simp [gpr_write, E₂.x19]
    · rw [← ht₅]; simp [gpr_write, g₂ .x23 (by decide) (by decide) (by decide), h23]
    · rw [← ht₅]; simp [gpr_write, g₂ .x26 (by decide) (by decide) (by decide), h26]
    · rw [← ht₅]; simp [gpr_write, E₂.x19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₅ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
      g₂ r hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2]

/-- What follows the call: `k` blocks past them. -/
theorem step_ok {c : VG.Proof.AesCcm.AArch64.Cx} {t : State} {b k : Nat} (h23 : t.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b))
    (h24 : t.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b)) (h25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b))
    (h26 : t.gpr .x26 = BitVec.ofNat 64 k) (hkb : b + k ≤ c.n / 16) (hn : c.n < 2 ^ 64) :
    WP isa (.block [.sub .x .x24 .x24 .x26, .add .x .x25 .x25 .x26, .lsl .x .x9 .x26 4, .add .x .x23 .x23 .x9]) t
      fun t' => t'.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - (b + k)) ∧
        t'.gpr .x25 = BitVec.ofNat 64 (1 + (b + k)) ∧ t'.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (b + k)) ∧
        Others [.x9, .x23, .x24, .x25] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t' ht' => ?_
  subst ht'
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h24, h26]
    rw [show c.n / 16 - (b + k) = c.n / 16 - b - k by omega]
    exact ofNat_sub (by omega) (by omega)
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h25, h26]
    rw [ofNat_add_ofNat, Nat.add_assoc]
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h23, h26, lsl4_ofNat]
    rw [BitVec.add_assoc, ofNat_add_ofNat, Nat.mul_add]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr]

/-- The state after a chunk of `k` blocks. -/
theorem chunk_inv {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} {b k : Nat}
    {t : State} (I : VG.Proof.AesCcm.AArch64.CtrInv c nonce s b t) (hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32) (hkb : b + k ≤ c.n / 16)
    {t₅ t₆ t₇ : State} (f₅ : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] t.mem t₅.mem)
    (hc₅ : bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b))
    (h : CtrPost t₅ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k t₆)
    (hm₇ : t₇.mem = t₆.mem) :
    Frame (VG.Proof.AesCcm.AArch64.ctrR c) s.mem t₇.mem ∧
      bytesAt t₇.mem c.D (16 * (b + k)) =
        xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D (16 * (b + k))) ∧
      bytesAt t₇.mem (c.D + BitVec.ofNat 64 (16 * (b + k))) (c.n - 16 * (b + k)) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (b + k))) (c.n - 16 * (b + k)) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  have hDn := L.dw
  have cR : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩, ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₇.mem := by
    rw [hm₇]
    refine (f₅.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have toR : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], ∃ r' ∈ VG.Proof.AesCcm.AArch64.ctrR c, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega)⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  -- Separation of the data from what the chunk wrote.
  have sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ c.n →
      ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
        ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint c.D (by omega) (by omega) (by omega)
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  have hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    have h₁ : bytesAt t₇.mem c.D (16 * b) = bytesAt t.mem c.D (16 * b) := by
      have := Proof.AesGcm.AArch64.bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega)) (by omega))
        (by omega)
      rwa [BitVec.add_zero] at this
    have hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (c.W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock (by rw [hnl]; exact L.h7) (by rw [hnl]; exact L.h13) hk32
        (by rw [hnl]; have := Nat.lt_of_le_of_lt (Nat.div_le_self c.n 16) L.hn; omega) i hi
    have hx := ctr32_ccm (by rw [hnl]; have := L.h13; omega) hinc h.out
    have f₅' : Frame (VG.Proof.AesCcm.AArch64.ctrR c) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    have hx₅ : bytesAt t₅.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      rw [bytesAt_prefix t₅.mem _ (show 16 * k ≤ c.n - 16 * b by omega),
        bytesAt_prefix s.mem _ (show 16 * k ≤ c.n - 16 * b by omega), ← I.rest,
        Proof.AesGcm.AArch64.bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (L.d_w.sub_left (Offset.sub_base c.D (by omega))).sub_right (Lay.wSub (by decide))) (by omega)]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      VG.Proof.AesCcm.AArch64.ciph_ctrR L f₅', xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    have hR' := Proof.AesGcm.AArch64.bytesAt_frame cR
      (sep (a := 16 * (b + k)) (l := c.n - 16 * (b + k)) (.inr (Nat.le_refl _)) (by omega)) (by omega)
    rw [hR', show c.D + BitVec.ofNat 64 (16 * (b + k)) = c.D + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (16 * k) by
        rw [add_ofNat_assoc, hbk],
      show c.n - 16 * (b + k) = c.n - 16 * b - 16 * k by omega, bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega),
      bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega), I.rest]

/-- One chunk. -/
theorem chunk_ok (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl)
    {s : State} (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {b : Nat}
    {t : State} (I : VG.Proof.AesCcm.AArch64.CtrInv c nonce s b t) (hb : b < c.n / 16) :
    WP isa (ctrChunk v.callee) t fun t' => ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ∧ 1 ≤ k ∧
      b + k ≤ c.n / 16 ∧ VG.Proof.AesCcm.AArch64.CtrInv c nonce s (b + k) t' := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.kSel_ok (b := b) I.x24 I.x25 (by omega))
    fun t₂ ⟨x26₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ => ?_))
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at x26₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega
  have hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have E₂ : VG.Proof.AesCcm.AArch64.Env c t₂ := I.env.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hc0t : bytesAt t₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₂, Proof.AesGcm.AArch64.bytesAt_frame I.frame (VG.Proof.AesCcm.AArch64.ctrR_disj L (.inl (by decide))) (by decide), hc0]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.setup_ok L hnl hkb hk1 E₂ hc0t (by rw [hg₂ _ (by decide), I.x23])
    (by rw [hg₂ _ (by decide), I.x25]) x26₂) fun t₅ ⟨E₅, C₅, f₅, hc₅, hg₅, rd₅, wr₅⟩ => ?_)
  refine WP.seq (WP.mono (ctr_call v C₅) fun t₆ h => ?_)
  have E₆ : VG.Proof.AesCcm.AArch64.Env c t₆ := E₅.of_saved h.saved h.sp h.rd h.wr
  have sv : ∀ r ∈ [Reg.x23, .x24, .x25, .x26], t₆.gpr r = t₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      hg₅ r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine WP.mono (VG.Proof.AesCcm.AArch64.step_ok (c := c) (b := b) (k := k) (by rw [sv .x23 (by simp), hg₂ _ (by decide), I.x23])
    (by rw [sv .x24 (by simp), hg₂ _ (by decide), I.x24]) (by rw [sv .x25 (by simp), hg₂ _ (by decide), I.x25])
    (by rw [sv .x26 (by simp), x26₂]) hkb hn64) fun t₇ ⟨x24₇, x25₇, x23₇, hg₇, hm₇, sp₇, rd₇, wr₇⟩ => ?_
  obtain ⟨fr, dn, rs⟩ := VG.Proof.AesCcm.AArch64.chunk_inv L hnl I hk32 hkb (by rw [← hm₂]; exact f₅) hc₅ h hm₇
  exact ⟨k, hk, hk1, hkb, ⟨E₆.others hg₇ (by decide) sp₇ rd₇ wr₇, by rw [rd₇, h.rd, rd₅, rd₂, I.rd],
    by rw [wr₇, h.wr, wr₅, wr₂, I.wr], x23₇, x24₇, x25₇, hkb, fr, dn, rs⟩⟩

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Cmp`. -/
section

/-!
# AES-CCM on AArch64: checking a received tag (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` pads the `tl` bytes of
the received tag at `T` (in `x12`) and of the computed one at `W + 96` with
zeros, and
leaves 0 in `x10` if they are equal, 1 if not (`cmp_ok`), as AES-GCM's
`cmpSeg` does; `mask` ANDs every byte of the data with `x10 − 1`: it keeps
the data if the tags are equal, and overwrites it with zeros if not
(`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok loopRegs Others add_ofNat_assoc eval_zero eval_nonzero
  words_eq pad_bytes carry_val in_of_covers succ_ofNat bytesAt_succ read_one writeBytes_frame' in_left)
open VG.Proof.AesCcm (length_bytesAt)

/-- `cmp`: 0 in `x10` iff the first `tl` bytes of the tag at `W + 96` are
those at `T`, in `x12`. -/
theorem cmp_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) (hx12 : s.gpr .x12 = c.T) :
    WP isa cmp s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64
        (if bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem c.T c.tl then 0 else 1) ∧
      VG.Proof.AesCcm.AArch64.Env c s' ∧ Others [.x9, .x10, .x11, .x12, .x13, .x14, .x15] s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem := by
  have ht4 := L.t4
  have ht16 := L.t16
  have w (d : Nat) (h : d + 8 ≤ 2560) := E.perm.wW h
  obtain ⟨s₁, run₁, hm₁, x11₁, x12₁, x13₁, og₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [imm .x9 0,
      .str .x .x9 .x19 vO, .str .x .x9 .x19 (vO + 8), .str .x .x9 .x19 rO, .str .x .x9 .x19 (rO + 8),
      ptr .x11 .x19 rO, mov .x13 .x20] s = some s₁ ∧
      s₁.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 264)
        (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 280)
          (0 : BitVec 64) ∧
      s₁.gpr .x11 = c.W + BitVec.ofNat 64 272 ∧ s₁.gpr .x12 = c.T ∧ s₁.gpr .x13 = BitVec.ofNat 64 c.tl ∧
      Others [.x9, .x11, .x13] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w 256 (by decide), w 264 (by decide), w 272 (by decide), w 280 (by decide)], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, hx12]
    · simp [gpr_write, E.x20]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq ?_
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others og₁ (by decide) sp₁ rd₁ wr₁
  have dW : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 272, c.tl⟩ :=
    L.t_w.sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₁ c.T (c.W + BitVec.ofNat 64 272) c.tl :=
    ⟨by omega, E₁.perm.t, E₁.perm.wC (by omega), dW⟩
  refine WP.mono (copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega) lp) fun s₂ ⟨hm₂, _, _, og₂, sp₂, rd₂, wr₂⟩ => ?_
  have E₂ : VG.Proof.AesCcm.AArch64.Env c s₂ := E₁.others og₂ (by decide) sp₂ rd₂ wr₂
  refine WP.seq ?_
  obtain ⟨s₃, run₃, hm₃, x11₃, x12₃, x13₃, og₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [ptr .x11 .x19 vO,
      ptr .x12 .x19 uO, mov .x13 .x20] s₂ = some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x11 = c.W + BitVec.ofNat 64 256 ∧ s₃.gpr .x12 = c.W + BitVec.ofNat 64 96 ∧
      s₃.gpr .x13 = BitVec.ofNat 64 c.tl ∧
      Others [.x11, .x12, .x13] s₂ s₃ ∧ s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by carun [E₂.x19], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, E₂.x20]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have E₃ : VG.Proof.AesCcm.AArch64.Env c s₃ := E₂.others og₃ (by decide) sp₃ rd₃ wr₃
  have dU : (⟨c.W + BitVec.ofNat 64 96, c.tl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 256, c.tl⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by omega)
  have lp₃ : LoopPre s₃ (c.W + BitVec.ofNat 64 96) (c.W + BitVec.ofNat 64 256) c.tl :=
    ⟨by omega, E₃.perm.wCR (by omega), E₃.perm.wC (by omega), dU⟩
  refine WP.seq (WP.mono (copyLoop_ok s₃ x12₃ x11₃ x13₃ (by omega) lp₃)
    fun s₄ ⟨hm₄, _, _, og₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ : VG.Proof.AesCcm.AArch64.Env c s₄ := E₃.others og₄ (by decide) sp₄ rd₄ wr₄
  have r (d : Nat) (h : d + 8 ≤ 2560) := E₄.perm.wR h
  obtain ⟨s₅, run₅, x10₅, og₅, sp₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x9 .x19 vO, .ldr .x .x10 .x19 rO,
      .logic .eor .x .x9 .x9 .x10, .ldr .x .x10 .x19 (vO + 8), .ldr .x .x11 .x19 (rO + 8),
      .logic .eor .x .x10 .x10 .x11, .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1,
      .adds .x .x9 .x9 .x12, .adcs .x .x10 .x11 .x11] s₄ = some s₅ ∧
      s₅.gpr .x10 = BitVec.ofNat 64 (if (s₄.mem.readW (c.W + BitVec.ofNat 64 256) 64 ^^^
        s₄.mem.readW (c.W + BitVec.ofNat 64 272) 64) ||| (s₄.mem.readW (c.W + BitVec.ofNat 64 264) 64 ^^^
        s₄.mem.readW (c.W + BitVec.ofNat 64 280) 64) = 0 then 0 else 1) ∧
      Others [.x9, .x10, .x11, .x12] s₄ s₅ ∧ s₅.sp = s₄.sp ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by carun [E₄.x19, r 256 (by decide), r 264 (by decide), r 272 (by decide), r 280 (by decide),
      gpr_addWithCarry, c_addWithCarry, mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry,
      c_write], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, Size.bits, Nat.reduceAdd,
        show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv, Nat.reduceMul]
      exact carry_val _
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, gpr_addWithCarry, hr]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have e8 (a : Nat) : c.W + BitVec.ofNat 64 (a + 8) = c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc c.W a 8).symm
  have hm₁' : s₁.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272)
        (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [hm₁, ← e8, ← e8]
  have fa := Proof.Cmac.frame_store2 (m := s.mem) (c.W + BitVec.ofNat 64 256) 0 0
  have fb := Proof.Cmac.frame_store2 (m := (s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) (c.W + BitVec.ofNat 64 272) 0 0
  have sR (d n : Nat) (h₁ : 256 ≤ d) (h₂ : d + n ≤ 288) :
      ∃ r' ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], Region.Sub ⟨c.W + BitVec.ofNat 64 d, n⟩ r' :=
    ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₁.mem := by
    rw [hm₁']
    refine (fa.sub fun r hr => ?_).trans (fb.sub fun r hr => ?_) <;>
      (simp only [List.mem_singleton] at hr; subst hr)
    · exact sR 256 16 (by decide) (by decide)
    · exact sR 272 16 (by decide) (by decide)
  have z₁ : bytesAt s₁.mem (c.W + BitVec.ofNat 64 272) 16 = zeros 16 := by
    rw [hm₁', Proof.Cmac.bytesAt_store2]; rfl
  have z₀ : bytesAt s₁.mem (c.W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [hm₁', Proof.AesGcm.AArch64.bytesAt_frame fb (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), Proof.Cmac.bytesAt_store2]; rfl
  have f₂ : Frame [⟨c.W + BitVec.ofNat 64 272, c.tl⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have f₄ : Frame [⟨c.W + BitVec.ofNat 64 256, c.tl⟩] s₂.mem s₄.mem := by
    rw [hm₄, hm₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have f₁₂ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₂.mem :=
    f₁.trans (f₂.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 272 c.tl (by decide) (by omega))
  have f₁₄ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₄.mem :=
    f₁₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 256 c.tl (by decide) (by omega))
  have hA : bytesAt s₁.mem c.T c.tl = bytesAt s.mem c.T c.tl :=
    Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.t_w.sub_right (Lay.wSub (by decide))) (by omega)
  have hB : bytesAt s₂.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl :=
    Proof.AesGcm.AArch64.bytesAt_frame f₁₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by omega)) (by omega) (by decide)) (by omega)
  have p₁ : bytesAt s₂.mem (c.W + BitVec.ofNat 64 272) 16 = bytesAt s.mem c.T c.tl ++ zeros (16 - c.tl) := by
    rw [hm₂, pad_bytes z₁ _ (by rw [length_bytesAt]; omega), length_bytesAt, hA]
    rfl
  have z₀' : bytesAt s₂.mem (c.W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by omega))
      (by decide), z₀]
  have p₀ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 256) 16 =
      bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl ++ zeros (16 - c.tl) := by
    rw [hm₄, hm₃, pad_bytes z₀' _ (by rw [length_bytesAt]; omega), length_bytesAt, hB]
    rfl
  have q₁ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 272) 16 = bytesAt s₂.mem (c.W + BitVec.ofNat 64 272) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by decide) (by omega))
      (by decide)
  have key : ((s₄.mem.readW (c.W + BitVec.ofNat 64 256) 64 ^^^ s₄.mem.readW (c.W + BitVec.ofNat 64 272) 64) |||
      (s₄.mem.readW (c.W + BitVec.ofNat 64 264) 64 ^^^ s₄.mem.readW (c.W + BitVec.ofNat 64 280) 64) = 0) ↔
      bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem c.T c.tl := by
    rw [show (264 : Nat) = 256 + 8 from rfl, show (280 : Nat) = 272 + 8 from rfl, e8 256, e8 272, words_eq, p₀,
      q₁, p₁]
    exact ⟨List.append_cancel_right, fun h => by rw [h]⟩
  have og : Others [.x9, .x10, .x11, .x12, .x13, .x14, .x15] s s₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h10, h11, h12, h13, h14, h15⟩ := hr
    have hl : r ∉ loopRegs := by simp [loopRegs, h11, h12, h13, h14, h15]
    rw [og₅ r (by simp [h9, h10, h11, h12]), og₄ r hl, og₃ r (by simp [h11, h12, h13]), og₂ r hl,
      og₁ r (by simp [h9, h11, h13])]
  refine ⟨by rw [x10₅]; simp only [key], E₄.others og₅ (by decide) sp₅ rd₅ wr₅, og, ?_⟩
  rw [m₅]; exact f₁₄

/-- The bytes at `D`, each ANDed with `b`. -/
def maskBytes (m : Mem) (D : Addr) (b : Byte) (n : Nat) : List Byte := (bytesAt m D n).map (· &&& b)

theorem length_maskBytes (m : Mem) (D : Addr) (b : Byte) (n : Nat) : (VG.Proof.AesCcm.AArch64.maskBytes m D b n).length = n := by
  simp [VG.Proof.AesCcm.AArch64.maskBytes, length_bytesAt]

theorem maskBytes_succ (m : Mem) (D : Addr) (b : Byte) (i : Nat) :
    VG.Proof.AesCcm.AArch64.maskBytes m D b (i + 1) = VG.Proof.AesCcm.AArch64.maskBytes m D b i ++ [m (D + BitVec.ofNat 64 i) &&& b] := by
  simp [VG.Proof.AesCcm.AArch64.maskBytes, bytesAt_succ]

theorem byte_and (a : BitVec (8 * 1)) (x : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) &&& BitVec.setWidth 32 x))) =
      a &&& x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 64 by omega, show i < 32 by omega,
    hi, decide_true, Bool.true_and]

/-- A byte at `D + i`, not yet written by a write of `i` bytes at `D`. -/
theorem writeBytes_at_len (m : Mem) (D : Addr) (xs : List Byte) {i : Nat} (hxs : xs.length = i)
    (hi : i < 2 ^ 64) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.lt_irrefl, ite_false]

abbrev maskRegs : List Reg := [.x12, .x13, .x14]

theorem maskStep_ok (s : State) {A : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A)
    (w : InRegions s.wr A 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧ s'.mem = s.mem.writeW A (s.mem A &&& (s.gpr .x11).setWidth 8) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      (∀ r, r ∉ VG.Proof.AesCcm.AArch64.maskRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wa := in_left (rd := s.rd) w
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, ha, w, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, VG.Proof.AesCcm.AArch64.byte_and, VG.Proof.AesGcm.AArch64.read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
    done
  · simp only [VG.Proof.AesCcm.AArch64.maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    simp [gpr_write, h₁, h₂, h₃]

/-- The loop: the `n` (at least 1) bytes at `D` (`x12`) ANDed with the low
byte of `x11`. -/
theorem maskLoop_ok (s : State) {D : Addr} {n : Nat} (hD : s.gpr .x12 = D) (hn : s.gpr .x13 = BitVec.ofNat 64 n)
    (hpos : 0 < n) (hlt : n < 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block maskBody) (.nonzero .x .x13)) s fun s' =>
      s'.mem = writeBytes s.mem D (VG.Proof.AesCcm.AArch64.maskBytes s.mem D ((s.gpr .x11).setWidth 8) n) ∧
      (∀ r, r ∉ VG.Proof.AesCcm.AArch64.maskRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = D + BitVec.ofNat 64 i ∧
      t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (VG.Proof.AesCcm.AArch64.maskBytes s.mem D ((s.gpr .x11).setWidth 8) i) ∧
      (∀ r, r ∉ VG.Proof.AesCcm.AArch64.maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hpos, by rw [hD]; simp, by rw [hn, Nat.sub_zero],
      by simp [VG.Proof.AesCcm.AArch64.maskBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x13', g', sp', rd', wr'⟩ := VG.Proof.AesCcm.AArch64.maskStep_ok t
    (A := D + BitVec.ofNat 64 i) (by rw [x12, BitVec.add_zero])
    (by rw [wr]; exact in_of_covers hw hi hlt)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := VG.Proof.AesCcm.AArch64.length_maskBytes s.mem D ((s.gpr .x11).setWidth 8) i
  have x11t : t.gpr .x11 = s.gpr .x11 := g .x11 (by decide)
  have hmem : t'.mem = writeBytes s.mem D (VG.Proof.AesCcm.AArch64.maskBytes s.mem D ((s.gpr .x11).setWidth 8) (i + 1)) := by
    rw [mem', mem, VG.Proof.AesCcm.AArch64.writeBytes_at_len _ _ _ hlen (by omega), x11t, VG.Proof.AesCcm.AArch64.maskBytes_succ,
      writeBytes_snoc s.mem D _ _ (by rw [hlen]; omega), hlen]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := VG.Proof.AesGcm.AArch64.eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega)
  have gg : ∀ r, r ∉ VG.Proof.AesCcm.AArch64.maskRegs → t'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, BitVec.add_assoc, VG.Proof.AesGcm.AArch64.succ_ofNat], x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩

theorem mask_byte {ok : Bool} :
    ((BitVec.ofNat 64 (if ok then 0 else 1) - 1 : BitVec 64).setWidth 8 : Byte) = if ok then 0xff else 0 := by
  cases ok <;> decide

/-- `mask`: the data kept if `x10` is 0, zeros if it is 1. -/
theorem mask_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {ok : Bool}
    (h10 : s.gpr .x10 = BitVec.ofNat 64 (if ok then 0 else 1)) :
    WP isa mask s fun s' =>
      bytesAt s'.mem c.D c.n = (if ok then bytesAt s.mem c.D c.n else zeros c.n) ∧
      VG.Proof.AesCcm.AArch64.Env c s' ∧ Others [.x11, .x12, .x13, .x14] s s' ∧ Frame [⟨c.D, c.n⟩] s.mem s'.mem := by
  have hn := L.n_lt
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, og₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.subImm .x .x11 .x10 1, mov .x12 .x27, mov .x13 .x28] s = some s₁ ∧
      s₁.gpr .x11 = BitVec.ofNat 64 (if ok then 0 else 1) - 1 ∧ s₁.gpr .x12 = c.D ∧
      s₁.gpr .x13 = BitVec.ofNat 64 c.n ∧ Others [.x11, .x12, .x13] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, h10]
    · simp [gpr_write, E.x27]
    · simp [gpr_write, E.x28]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others og₁ (by decide) sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hmb : ((s₁.gpr .x11).setWidth 8 : Byte) = if ok then 0xff else 0 := by rw [x11₁, VG.Proof.AesCcm.AArch64.mask_byte]
  have hres : ∀ m : Mem, (if ok then bytesAt m c.D c.n else zeros c.n) =
      VG.Proof.AesCcm.AArch64.maskBytes m c.D (if ok then 0xff else 0) c.n := fun m => by
    cases ok
    · simp only [VG.Proof.AesCcm.AArch64.maskBytes, Bool.false_eq_true, ite_false]
      apply List.ext_getElem (by simp [length_bytesAt, zeros])
      intro i h₁ h₂; simp [zeros]
    · simp only [VG.Proof.AesCcm.AArch64.maskBytes, ite_true]
      apply List.ext_getElem (by simp [length_bytesAt])
      intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_zipWith]
      generalize (bytesAt m c.D c.n)[i] = x
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (255 : BitVec 8).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt x.isLt]
  refine WP.ite (decide (c.n = 0)) (VG.Proof.AesGcm.AArch64.eval_zero x13₁ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n = 0 := by simpa using ht
    refine WP.block_nil ⟨?_, E₁, fun r hr => og₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.1, hr.2.1, hr.2.2.1⟩),
      by rw [hm₁]; exact Frame.refl _ _⟩
    rw [hm₁, h0]; cases ok <;> rfl
  · have h0 : c.n ≠ 0 := by simpa using hf
    refine WP.mono (VG.Proof.AesCcm.AArch64.maskLoop_ok s₁ x12₁ x13₁ (by omega) hn E₁.perm.d) fun s' ⟨hm, g, sp', rd', wr'⟩ => ?_
    refine ⟨?_, E₁.others g (by decide) sp' rd' wr', fun r hr => ?_, ?_⟩
    · rw [hm, hmb, Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesCcm.AArch64.length_maskBytes]) hn,
        VG.Proof.AesCcm.AArch64.length_maskBytes, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil, hm₁, hres]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [VG.Proof.AesCcm.AArch64.maskRegs, hr.2.1, hr.2.2.1, hr.2.2.2]), og₁ r (by simp [hr.1, hr.2.1, hr.2.2.1])]
    · rw [hm, ← hm₁]
      exact writeBytes_frame' _ (VG.Proof.AesCcm.AArch64.length_maskBytes _ _ _ _)

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Crypt`. -/
section

/-!
# AES-CCM on AArch64: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_ok`, by `chunk_ok`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_ok`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_ok`), which is its encryption (`Proof.AesCcm.crypt_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm xorLoop)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call Others add_ofNat_assoc eval_zero eval_nonzero
  LoopPre xorLoop_ok xorBytes loopRegs lsr_ofNat and15 toNat_ofNat_of_lt covers_off covers_left)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesCcm (xorFrom xorFrom_append xorFrom_tail xorFrom_zeros ctr32_ccm length_bytesAt
  bytesAt_prefix bytesAt_writeBytes_at BlockCipher)

/-- `x23`, `x24` and `x25` for the first chunk. -/
theorem ctrHeadBlk_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {nonce : List Byte} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) :
    WP isa (.block [mov .x23 .x27, .lsr .x .x24 .x28 4, imm .x25 1]) s (VG.Proof.AesCcm.AArch64.CtrInv c nonce s 0) := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨E.others (rs := [.x23, .x24, .x25]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]) (by decide)
      rfl rfl rfl, rfl, rfl, ?_, ?_, ?_, Nat.zero_le _, Frame.refl _ _, rfl, by simp [mem_write]⟩
  · simp [gpr_write, E.x27]
  · simp [gpr_write, E.x28, lsr_ofNat c.n 4 L.n_lt]
  · simp [gpr_write]

/-- The whole blocks, in chunks. -/
theorem ctrHead_ok (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl)
    {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (.seq (.block [mov .x23 .x27, .lsr .x .x24 .x28 4, imm .x25 1])
      (.ite (.zero .x .x24) (.block []) (.loop (ctrChunk v.callee) (.nonzero .x .x24)))) s
      (VG.Proof.AesCcm.AArch64.CtrInv c nonce s (c.n / 16)) := by
  have hn64 := L.n_lt
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.ctrHeadBlk_ok L (nonce := nonce) E) fun s₁ I₀ => ?_)
  refine WP.ite (decide (c.n / 16 = 0)) (eval_zero (a := c.n / 16) (by rw [I₀.x24, Nat.sub_zero]) (by omega))
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n / 16 = 0 := of_decide_eq_true ht
    exact WP.block_nil (by rw [h0]; exact I₀)
  · have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = c.n / 16 - b ∧ b < c.n / 16 ∧ VG.Proof.AesCcm.AArch64.CtrInv c nonce s b t) ?_
      (c.n / 16 - 0) s₁ ⟨0, rfl, by omega, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (VG.Proof.AesCcm.AArch64.chunk_ok v L hnl hc0 I hb) fun t' ⟨k, _, hk1, hkb, I'⟩ => ?_
    have ev := eval_nonzero (r := .x24) (a := c.n / 16 - (b + k)) I'.x24 (by omega)
    by_cases he : b + k = c.n / 16
    · left; exact ⟨by rw [ev]; simp [he], by rw [← he]; exact I'⟩
    · right; exact ⟨by rw [ev]; simp; omega, c.n / 16 - (b + k), by omega, b + k, rfl, by omega, I'⟩

/-- The arguments of the call for the last bytes: `Ctrⱼ` and a zero block at
`W + 80`. -/
theorem tailSetup_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {t : State}
    (E : VG.Proof.AesCcm.AArch64.Env c t) (hc0 : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {j : Nat}
    (hj : j < 256 ^ (15 - c.nl)) (h25 : t.gpr .x25 = BitVec.ofNat 64 j) :
    WP isa (.block (([mov .x9 .x25] : List Instr) ++ ctrAt ++ zero16 ksO ++ ctrArgs ++
        ([ptr .x3 .x19 ksO, imm .x4 1] : List Instr))) t fun t' =>
      VG.Proof.AesCcm.AArch64.Env c t' ∧ CtrCall t' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
      Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce j ∧
      bytesAt t'.mem (c.W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] t t' ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  have h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  have hg₁ : Others [.x9] t t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  have E₁ : VG.Proof.AesCcm.AArch64.Env c t₁ := E.others hg₁ (by decide) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  have h9 : t₁.gpr .x9 = BitVec.ofNat 64 j := by rw [← ht₁]; simp [gpr_write, h25]
  have hm₁ : t₁.mem = t.mem := by rw [← ht₁]; rfl
  refine WP.block_append (WP.mono (VG.Proof.AesCcm.AArch64.ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := j) (by rw [hnl]; exact hj) h9)
    fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesCcm.AArch64.Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  have w₁ := E₂.perm.wW (show 80 + 8 ≤ 2560 by decide)
  have w₂ := E₂.perm.wW (show 88 + 8 ≤ 2560 by decide)
  obtain ⟨t₃, run₃, hm₃, x0, x1, x2, x3, x4, x5, hg₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      (zero16 ksO ++ ctrArgs ++ [ptr .x3 .x19 ksO, imm .x4 1]) t₂ = some t₃ ∧
      t₃.mem = (t₂.mem.writeW (c.W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 88)
        (0 : BitVec 64) ∧
      t₃.gpr .x0 = c.K ∧ t₃.gpr .x1 = BitVec.ofNat 64 c.R ∧ t₃.gpr .x2 = c.W + BitVec.ofNat 64 64 ∧
      t₃.gpr .x3 = c.W + BitVec.ofNat 64 80 ∧ t₃.gpr .x4 = BitVec.ofNat 64 1 ∧
      t₃.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9] t₂ t₃ ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by carun [ctrArgs, E₂.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E₂.x21]
    · simp [gpr_write, E₂.x22]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write]
    · simp [gpr_write, E₂.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨t₃, by simpa only [List.append_assoc] using run₃, ?_⟩
  have E₃ : VG.Proof.AesCcm.AArch64.Env c t₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  have e88 : c.W + BitVec.ofNat 64 88 = c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have c80 : ∀ d, 80 ≤ d → d + 8 ≤ 96 →
      (⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => Offset.contains c.W (by omega) (by omega) (by decide)
  have fz : Frame [⟨c.W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))
  refine ⟨E₃, VG.Proof.AesCcm.AArch64.cargsW L E₃ (o := 64) (d := 80) (by decide) (by decide) (by decide) x0 x1 x2 x3 x4 x5, ?_, ?_, ?_,
    fun r hr => ?_, by rw [rd₃, rd₂, ← ht₁]; rfl, by rw [wr₃, wr₂, ← ht₁]; rfl⟩
  · rw [hm₃, ← hm₁]
    exact ((f₂.sub fun r hr => ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 80 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 88 (by decide) (by decide))
  · rw [Proof.AesGcm.AArch64.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c.W (.inl (by decide)) (by decide) (by decide)) (by decide), hc₂]
  · rw [hm₃, e88, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      hg₂ r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
    exact hg₁ r (by simp [hr.2.2.2.2.2.2.1])

/-- The last `n mod 16` bytes, after the whole blocks. -/
theorem tail_ok (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State}
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {t t₀ : State}
    (I : VG.Proof.AesCcm.AArch64.CtrInv c nonce s (c.n / 16) t) (E₀ : VG.Proof.AesCcm.AArch64.Env c t₀) (hm₀ : t₀.mem = t.mem)
    (h23 : t₀.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h25 : t₀.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16)) (h26 : t₀.gpr .x26 = BitVec.ofNat 64 (c.n % 16))
    (hrd₀ : t₀.rd = t.rd) (hwr₀ : t₀.wr = t.wr) (h0 : c.n % 16 ≠ 0) :
    WP isa (ctrTail v.callee) t₀ fun t' => VG.Proof.AesCcm.AArch64.Env c t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (VG.Proof.AesCcm.AArch64.ctrR c) s.mem t'.mem ∧
      bytesAt t'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  have hq16 : c.n / 16 < 256 ^ (15 - c.nl) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) L.hn
  have hc0₀ : bytesAt t₀.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₀, Proof.AesGcm.AArch64.bytesAt_frame I.frame (VG.Proof.AesCcm.AArch64.ctrR_disj L (.inl (by decide))) (by decide), hc0]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.tailSetup_ok L hnl E₀ hc0₀ (j := 1 + c.n / 16) (by have := L.hn; omega) h25)
    fun t₁ ⟨E₁, C₁, f₁, hc₁, hz₁, hg₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (ctr_call v C₁) fun t₂ h => ?_)
  have E₂ : VG.Proof.AesCcm.AArch64.Env c t₂ := E₁.of_saved h.saved h.sp h.rd h.wr
  have sv : ∀ r ∈ [Reg.x23, .x26], t₂.gpr r = t₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl <;> decide) (by rcases hr with rfl | rfl <;> decide),
      hg₁ r (by rcases hr with rfl | rfl <;> decide)]
  obtain ⟨t₃, run₃, x11₃, x12₃, x13₃, hg₃, hm₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      [ptr .x11 .x19 ksO, mov .x12 .x23, mov .x13 .x26] t₂ = some t₃ ∧
      t₃.gpr .x11 = c.W + BitVec.ofNat 64 80 ∧ t₃.gpr .x12 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
      t₃.gpr .x13 = BitVec.ofNat 64 (c.n % 16) ∧ Others [.x11, .x12, .x13] t₂ t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, sv .x23 (by simp), h23]
    · simp [gpr_write, sv .x26 (by simp), h26]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.AArch64.Env c t₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  have rd₃' : t₃.rd = s.rd := by rw [rd₃, h.rd, rd₁, hrd₀, I.rd]
  have wr₃' : t₃.wr = s.wr := by rw [wr₃, h.wr, wr₁, hwr₀, I.wr]
  have hS := (L.bufD E₃.perm).slice (a := 16 * (c.n / 16)) (k := c.n % 16) (by omega)
  have lp : LoopPre t₃ (c.W + BitVec.ofNat 64 80) (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) :=
    ⟨by omega, E₃.perm.wCR (by omega), covers_off E₃.perm.d (by omega) hn64, (hS.wd (by omega)).symm⟩
  refine WP.mono (xorLoop_ok t₃ x11₃ x12₃ x13₃ (by omega) lp) fun t₄ ⟨hm₄, hg₄, sp₄, rd₄, wr₄⟩ => ?_
  -- What the tail wrote.
  have cT : Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₃.mem := by
    rw [hm₃, ← hm₀]
    refine (f₁.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub c.W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  have sep : ∀ {a l : Nat}, a + l ≤ c.n → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes t₃.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
      (c.W + BitVec.ofNat 64 80) (c.n % 16) := ⟨_, rfl⟩
  rw [← hxs] at hm₄
  have hxl : xs.length = c.n % 16 := by simp [hxs, xorBytes, length_bytesAt]
  have fw : Frame [⟨c.D + BitVec.ofNat 64 (16 * (c.n / 16)), c.n % 16⟩] t₃.mem t₄.mem := by
    rw [hm₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨E₃.others hg₄ (by decide) sp₄ rd₄ wr₄, by rw [rd₄, rd₃'], by rw [wr₄, wr₃'], ?_, ?_⟩
  · refine I.frame.trans ((cT.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega)⟩
  · -- The bytes.
    have h₁ : bytesAt t₃.mem c.D (16 * (c.n / 16)) = bytesAt t.mem c.D (16 * (c.n / 16)) := by
      have := Proof.AesGcm.AArch64.bytesAt_frame cT (sep (a := 0) (l := 16 * (c.n / 16)) (by omega)) (by omega)
      rwa [BitVec.add_zero] at this
    have h₂ : bytesAt t₃.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) := by
      rw [Proof.AesGcm.AArch64.bytesAt_frame cT (sep (by omega)) (by omega),
        show c.n % 16 = c.n - 16 * (c.n / 16) by omega, I.rest]
    have f₁' : Frame (VG.Proof.AesCcm.AArch64.ctrR c) s.mem t₁.mem := I.frame.trans (by
      rw [← hm₀]; exact f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩)
    have hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem c.K c.R) := fun x => Proof.Cmac.aesWith_length _ _ x
    have hks : bytesAt t₃.mem (c.W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem c.K c.R (Spec.Ccm.ctrBlock nonce (1 + c.n / 16)) := by
      have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + c.n / 16) (by rw [hnl]; have := L.h13; omega)
        (fun i hi => by
          rw [show i = 0 by omega, Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [hc₁]) h.out
      rw [Nat.mul_one] at hx
      rw [hm₃, hx, hz₁, VG.Proof.AesCcm.AArch64.ciph_ctrR L f₁', xorFrom_zeros hBC]
    have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem c.K c.R) nonce (1 + c.n / 16)
      (d := bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16)) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt, hBC] at ht
    have ht' := ht.resolve_right (by omega)
    rw [hm₄, bytesAt_writeBytes_at t₃.mem c.D xs (by rw [hxl]; omega) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega), List.append_nil,
      ← bytesAt_prefix t₃.mem c.D (show 16 * (c.n / 16) ≤ c.n by omega), h₁, I.done, hxs, xorBytes, h₂,
      bytesAt_prefix t₃.mem (c.W + BitVec.ofNat 64 80) (show c.n % 16 ≤ 16 by omega), hks, ht']
    conv => rhs; rw [show c.n = 16 * (c.n / 16) + c.n % 16 from (Nat.div_add_mod c.n 16).symm]
    rw [Proof.Cmac.Stream.bytesAt_append, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 (c.n / 16)]

/-- `x26 = n mod 16`. -/
theorem lastLen_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {t : State} (E : VG.Proof.AesCcm.AArch64.Env c t) :
    WP isa (.block [imm .x9 15, .logic .and .x .x26 .x28 .x9]) t fun t₀ =>
      t₀.gpr .x26 = BitVec.ofNat 64 (c.n % 16) ∧ Others [.x9, .x26] t t₀ ∧ t₀.mem = t.mem ∧ t₀.sp = t.sp ∧
        t₀.rd = t.rd ∧ t₀.wr = t.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₀ ht₀ => ?_
  subst ht₀
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E.x28]
    rw [and15, toNat_ofNat_of_lt L.n_lt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (ctr v.callee) s fun s' => VG.Proof.AesCcm.AArch64.Env c s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame (VG.Proof.AesCcm.AArch64.ctrR c) s.mem s'.mem ∧
      bytesAt s'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 := L.n_lt
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.ctrHead_ok v L hnl E hc0) fun t I => ?_))
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.lastLen_ok L I.env) fun t₀ ⟨x26₀, hg₀, hm₀, sp₀, rd₀, wr₀⟩ => ?_)
  have E₀ : VG.Proof.AesCcm.AArch64.Env c t₀ := I.env.others hg₀ (by decide) sp₀ rd₀ wr₀
  refine WP.ite (decide (c.n % 16 = 0)) (eval_zero x26₀ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E₀, by rw [rd₀, I.rd], by rw [wr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (c.n / 16) = c.n by omega] at hd
    rw [hm₀, hd]
  · exact VG.Proof.AesCcm.AArch64.tail_ok v L hnl hc0 I E₀ hm₀ (by rw [hg₀ _ (by decide), I.x23]) (by rw [hg₀ _ (by decide), I.x25]) x26₀
      rd₀ wr₀ (of_decide_eq_false hf)

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Seal`. -/
section

/-!
# AES-CCM on AArch64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is `entry`, `Ctr₀`
(`ctrs`), the MAC of the payload (`mac 0`), encrypted at `W` (`tag 0`),
counter mode over the data (`ctr`), the tag copied to `tag`, whose address
the entry keeps in `W` (`loadTag_ok`, `tagOut_ok`), and `restore`
(`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (SavedAt exit_ok covers_left LoopPre copyLoop_ok loopRegs Others)
open VG.Impl.AesGcm.AArch64 (mov copyLoop)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher)

/-- The entry keeps a buffer missing `W`. -/
theorem entry_buf {c : VG.Proof.AesCcm.AArch64.Cx} {s s₁ : State} (hf : Frame [VG.Proof.AesCcm.AArch64.entryR c.W] s.mem s₁.mem) {P : Addr} {len : Nat}
    (hP : VG.Proof.AesCcm.AArch64.Buf c s P len) : bytesAt s₁.mem P len = bytesAt s.mem P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega)

theorem entry_ciph {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s s₁ : State} (hf : Frame [VG.Proof.AesCcm.AArch64.entryR c.W] s.mem s₁.mem) :
    Spec.Ccm.ctxCiph s₁.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega)]

theorem frame_ctrs_mut (c : VG.Proof.AesCcm.AArch64.Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region)], ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.AArch64.sub_lo (by decide)

theorem tagR_mut (c : VG.Proof.AesCcm.AArch64.Cx) {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.W + BitVec.ofNat 64 y, 16⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesCcm.AArch64.sub_lo (by decide)
  · exact VG.Proof.AesCcm.AArch64.sub_lo (by omega)
  · exact VG.Proof.AesCcm.AArch64.sub_hi (by decide) (by decide)

/-- The bytes of `W` below 48, kept by `ctrs`. -/
theorem ctrs_keeps {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {d k : Nat} (h : d + k ≤ 48 ∨ (64 ≤ d ∧ d + k ≤ 2560)) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region)], (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  rcases h with h | h
  · exact L.w_w (.inl h) (by omega) (by decide)
  · exact L.w_w (.inr h.1) (by omega) (by decide)

/-- `Ctr₀` is kept by the MAC's pieces. -/
theorem macR_c0 {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∀ r ∈ VG.Proof.AesCcm.AArch64.macR c.W y, (⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- `Ctr₀` is kept by `tag`. -/
theorem tagR_c0 {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.W + BitVec.ofNat 64 y, 16⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- The data, kept by the pieces before `ctr`. -/
theorem d_lo {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {rs : List Region} (hs : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.AesCcm.AArch64.wLo c.W, VG.Proof.AesCcm.AArch64.wHi c.W], Region.Sub r r') :
    ∀ r ∈ rs, (⟨c.D, c.n⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨r', hr', hsub⟩ := hs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact (L.d_w.sub_right (Region.sub_prefix (by decide))).sub_right hsub
  · exact (L.d_w' (by decide)).sub_right hsub

/-- The address of the tag loaded from its slot into `r`. -/
theorem loadTag_ok {c : VG.Proof.AesCcm.AArch64.Cx} {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) (S : VG.Proof.AesCcm.AArch64.Slots c s.mem) (r : Reg) :
    WP isa (.block [.ldr .x r .x19 tagO]) s fun s₁ =>
      s₁.gpr r = c.T ∧ Others [r] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q := E.perm.wR (show 240 + 8 ≤ 2560 by decide)
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [tagO, E.x19, q], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true]; rw [← S.tag]; rfl
  · simp only [List.mem_singleton] at hr'; simp [gpr_write, hr']

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, in `x11`. -/
theorem tagOut_ok {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {s : State} (E : VG.Proof.AesCcm.AArch64.Env c s) (hx11 : s.gpr .x11 = c.T)
    (hTw : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa tagOut s fun s' => VG.Proof.AesCcm.AArch64.Env c s' ∧ s'.mem = writeBytes s.mem c.T (bytesAt s.mem c.W c.tl) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x12₁, x13₁, og₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [mov .x12 .x19, mov .x13 .x20] s =
      some s₁ ∧ s₁.gpr .x12 = c.W ∧ s₁.gpr .x13 = BitVec.ofNat 64 c.tl ∧ Others [.x12, .x13] s s₁ ∧
      s₁.sp = s.sp ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x19]
    · simp [gpr_write, E.x20]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.AArch64.Env c s₁ := E.others og₁ (by decide) sp₁ rd₁ wr₁
  have x11₁ : s₁.gpr .x11 = c.T := by rw [og₁ .x11 (by decide), hx11]
  have lp : LoopPre s₁ c.W c.T c.tl :=
    ⟨by have := L.t16; omega, by simpa using E₁.perm.wCR (d := 0) (n := c.tl) (by have := L.t16; omega),
      by rw [wr₁]; exact hTw, (L.t_w.sub_right (Region.sub_prefix (by have := L.t16; omega))).symm⟩
  refine WP.mono (copyLoop_ok s₁ x12₁ x11₁ x13₁ (by have := L.t4; omega) lp)
    fun s₂ ⟨hm₂, _, _, og₂, sp₂, rd₂, wr₂⟩ => ⟨E₁.others og₂ (by decide) sp₂ rd₂ wr₂, by rw [hm₂, m₁],
      by rw [sp₂, sp₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} {N : Addr} {s : State} (Ar : VG.Proof.AesCcm.AArch64.Args c N s)
    (hTw : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n)
        (bytesAt s.mem c.A c.al) = (bytesAt s'.mem c.D c.n, bytesAt s'.mem c.T c.tl) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.entry_ok Ar) fun s₁ En => ?_)
  have hN₁ : VG.Proof.AesCcm.AArch64.Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.ctrs_ok L En.env hN₁ En.x2 En.x3) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [VG.Proof.AesCcm.AArch64.entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₂.mem := f₂.sub (VG.Proof.AesCcm.AArch64.frame_ctrs_mut c)
  have S₂ := En.slots.mut L f₂'
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.mac_ok v L E₂ S₂ hnl c₂ (.inl rfl)) fun s₃ M => ?_)
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame M.frame (VG.Proof.AesCcm.AArch64.macR_c0 L (.inl rfl)) (by decide), c₂]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.tag_ok v.ctr L M.env hnl c₃ (.inl rfl)) fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₄ (VG.Proof.AesCcm.AArch64.tagR_c0 L (.inl rfl)) (by decide), c₃]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.ctr_ok v.ctr L E₄ hnl c₄) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₁₃ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₃.mem := f₂'.trans (M.frame.sub (VG.Proof.AesCcm.AArch64.macR_mut (.inl rfl)))
  have f₁₄ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₄.mem := f₁₃.trans (f₄.sub (VG.Proof.AesCcm.AArch64.tagR_mut c (.inl rfl)))
  have f₁₅ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (VG.Proof.AesCcm.AArch64.ctrR_mut c))
  have sv₅ : SavedAt s₅.mem c.W s := VG.Proof.AesCcm.AArch64.saved_mut L f₁₅ En.saved
  -- The tag copied to `T`.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.loadTag_ok E₅ (En.slots.mut L f₁₅) .x11) fun s₆ ⟨x11₆, og₆, m₆, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ : VG.Proof.AesCcm.AArch64.Env c s₆ := E₅.others og₆ (by decide) sp₆ rd₆ wr₆
  have rw₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, M.wr, wr₂, En.wr]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.tagOut_ok L E₆ x11₆ (by rw [rw₆]; exact hTw)) fun s₇ ⟨E₇, m₇, sp₇, rd₇, wr₇⟩ => ?_)
  have hx : (bytesAt s₆.mem c.W c.tl).length = c.tl := length_bytesAt _ _ _
  have f₇ : Frame [⟨c.T, c.tl⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact Proof.AesGcm.AArch64.writeBytes_frame' _ hx
  have sv₇ : SavedAt s₇.mem c.W s := (m₆ ▸ sv₅).frame f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok E₇.x19 (by rw [E₇.sp, Ar.sp]) (covers_left E₇.perm.w) sv₇)
    fun s' ⟨ga, hm, _, _, _⟩ => ⟨ga, ?_⟩
  -- The ciphertext and the tag.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := VG.Proof.AesCcm.AArch64.entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [VG.Proof.AesCcm.AArch64.ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [VG.Proof.AesCcm.AArch64.ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [VG.Proof.AesCcm.AArch64.ciph_mut L f₁₄, k₁]
  have hd₁ : bytesAt s₁.mem c.D c.n = bytesAt s.mem c.D c.n := VG.Proof.AesCcm.AArch64.entry_buf En.frame (L.bufD Ar.perm)
  have ha₁ : bytesAt s₁.mem c.A c.al = bytesAt s.mem c.A c.al := VG.Proof.AesCcm.AArch64.entry_buf En.frame (L.bufA Ar.perm)
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.n_lt; omega), hd₁]
  have ha₂ : bytesAt s₂.mem c.A c.al = bytesAt s.mem c.A c.al := by rw [VG.Proof.AesCcm.AArch64.aad_mut L f₂', ha₁]
  have hd₄ : bytesAt s₄.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact L.d_w' (by decide)) (by have := L.n_lt; omega),
      VG.Proof.AesCcm.AArch64.buf_macR (L.bufD M.env.perm) (by decide) M.frame, hd₂]
  have w₅ : bytesAt s₅.mem c.W c.tl = bytesAt s₄.mem c.W c.tl :=
    Proof.AesGcm.AArch64.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w0_w (by have := L.t16; omega) (by decide)
      · exact L.w0_w (by have := L.t16; omega) (by decide)
      · exact (L.d_w.sub_right (Region.sub_prefix (by have := L.t16; omega))).symm) (by have := L.t16; omega)
  have e0 : c.W + BitVec.ofNat 64 0 = c.W := BitVec.add_zero c.W
  have M' := M.out
  rw [e0] at h₄ M'
  have hY := congrArg List.length h₄
  rw [length_bytesAt, length_xorFrom] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  have d₇ : bytesAt s₇.mem c.D c.n = bytesAt s₅.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.n_lt; omega), m₆]
  have t₇ : bytesAt s₇.mem c.T c.tl = bytesAt s₅.mem c.W c.tl := by
    have e := Proof.AesCcm.bytesAt_writeBytes_at s₆.mem c.T (o := 0) (n := c.tl) (bytesAt s₆.mem c.W c.tl)
      (by rw [hx]; omega) (by have := L.t16; omega)
    rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hx]), List.append_nil] at e
    rw [m₇, e, m₆]
  refine ⟨?_, ?_⟩
  · rw [hm, d₇, h₅, k₄, hd₄, crypt_eq (hBC _)]
  · rw [hm, t₇, w₅, Proof.AesCcm.bytesAt_prefix s₄.mem c.W L.t16, h₄, k₃,
      take_xorFrom_zero (hBC _) _ hY.symm L.t16, M', k₂, ha₂, hd₂,
      ← mac_eq _ _ (by rw [hnl]; have := L.h13; omega)]

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s : State} (h : sealAArch64.pre s) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  have A := VG.Proof.AesCcm.AArch64.args_of_seal h
  refine WP.mono (VG.Proof.AesCcm.AArch64.seal_wp' v A.1 A.2) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [VG.Proof.AesCcm.AArch64.sealAArch64]
  simpa only [VG.Proof.AesCcm.AArch64.cxOf] using hp

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Open`. -/
section

/-!
# AES-CCM on AArch64: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`
(`ctrs`), counter mode over the data (`ctr`), which decrypts it, the MAC of
the plaintext (`mac 96`), encrypted at `W + 96` (`tag 96`), the comparison
with the received tag at `tag`, whose address the entry keeps in `W`
(`loadTag_ok`, `cmp`), the result, the data masked with it (`mask`) and
`restore` (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.AesGcm.AArch64 (SavedAt exit_ok covers_left Others)
open VG.Impl.AesGcm.AArch64 (imm)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher
  cryptTag_eq_iff)

theorem cmpR_mut (c : VG.Proof.AesCcm.AArch64.Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.AArch64.sub_hi (by decide) (by decide)

theorem maskR_mut (c : VG.Proof.AesCcm.AArch64.Cx) : ∀ r ∈ [(⟨c.D, c.n⟩ : Region)], ∃ r' ∈ VG.Proof.AesCcm.AArch64.mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.AArch64.sub_data

/-- `x0 := 1 − x10`. -/
theorem ret_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block [imm .x0 1, .sub .x .x0 .x0 .x10]) s fun s' =>
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧ Others [.x0] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, h10]; cases b <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp [gpr_write, hr]

theorem length_chain {ciph : Spec.Ccm.Cipher} (hc : BlockCipher ciph) :
    ∀ (ms : List (List Byte)) (c : List Byte), c.length = 16 → (Spec.Cmac.chain ciph c ms).length = 16
  | [], _, h => h
  | _ :: ms, _, _ => VG.Proof.AesCcm.AArch64.length_chain hc ms _ (hc _)

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} {N : Addr} {s : State} (Ar : VG.Proof.AesCcm.AArch64.Args c N s) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧
      VG.Proof.AesCcm.AArch64.openOut (Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) (bytesAt s.mem c.T c.tl)) (s'.gpr .x0)
        (bytesAt s'.mem c.D c.n) c.n := by
  have L := Ar.lay
  have ht16 := L.t16
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.entry_ok Ar) fun s₁ En => ?_)
  have hN₁ : VG.Proof.AesCcm.AArch64.Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.ctrs_ok L En.env hN₁ En.x2 En.x3) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [VG.Proof.AesCcm.AArch64.entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₂.mem := f₂.sub (VG.Proof.AesCcm.AArch64.frame_ctrs_mut c)
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.ctr_ok v.ctr L E₂ hnl c₂) fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  have f₁₃ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₃.mem := f₂'.trans (f₃.sub (VG.Proof.AesCcm.AArch64.ctrR_mut c))
  have S₃ := En.slots.mut L f₁₃
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₃ (VG.Proof.AesCcm.AArch64.ctrR_disj L (.inl (by decide))) (by decide), c₂]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.mac_ok v L E₃ S₃ hnl c₃ (.inr rfl)) fun s₄ M => ?_)
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame M.frame (VG.Proof.AesCcm.AArch64.macR_c0 L (.inr rfl)) (by decide), c₃]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.tag_ok v.ctr L M.env hnl c₄ (.inr rfl)) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₁₄ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₄.mem := f₁₃.trans (M.frame.sub (VG.Proof.AesCcm.AArch64.macR_mut (.inr rfl)))
  have f₁₅ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (VG.Proof.AesCcm.AArch64.tagR_mut c (.inr rfl)))
  -- The address of the received tag, from its slot.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.loadTag_ok E₅ (En.slots.mut L f₁₅) .x12) fun s₉ ⟨x12₉, og₉, m₉, sp₉, rd₉, wr₉⟩ => ?_)
  have E₉ : VG.Proof.AesCcm.AArch64.Env c s₉ := E₅.others og₉ (by decide) sp₉ rd₉ wr₉
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.cmp_ok L E₉ x12₉) fun s₆ ⟨x10₆, E₆, og₆, f₆⟩ => ?_)
  rw [m₉] at x10₆ f₆
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.ret_ok (b := decide (bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      bytesAt s₅.mem c.T c.tl)) (by rw [x10₆]; congr 1; simp)) fun s₇ ⟨x0₇, og₇, hm₇, sp₇, rd₇, wr₇⟩ => ?_)
  have E₇ : VG.Proof.AesCcm.AArch64.Env c s₇ := E₆.others og₇ (by decide) sp₇ rd₇ wr₇
  refine WP.seq (WP.mono (VG.Proof.AesCcm.AArch64.mask_ok L E₇ (ok := decide (bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      bytesAt s₅.mem c.T c.tl)) (by rw [og₇ _ (by decide), x10₆]; congr 1; simp))
    fun s₈ ⟨hd₈, E₈, og₈, f₈⟩ => ?_)
  have f₁₆ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₆.mem := f₁₅.trans (f₆.sub (VG.Proof.AesCcm.AArch64.cmpR_mut c))
  have f₁₈ : Frame (VG.Proof.AesCcm.AArch64.mutR c) s₁.mem s₈.mem := by
    rw [hm₇] at f₈; exact f₁₆.trans (f₈.sub (VG.Proof.AesCcm.AArch64.maskR_mut c))
  have sv₈ : SavedAt s₈.mem c.W s := VG.Proof.AesCcm.AArch64.saved_mut L f₁₈ En.saved
  refine WP.mono (exit_ok E₈.x19 (by rw [E₈.sp, Ar.sp]) (covers_left E₈.perm.w) sv₈)
    fun s' ⟨ga, hm, x0', _, _⟩ => ⟨ga, ?_⟩
  -- The result.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := VG.Proof.AesCcm.AArch64.entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [VG.Proof.AesCcm.AArch64.ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [VG.Proof.AesCcm.AArch64.ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [VG.Proof.AesCcm.AArch64.ciph_mut L f₁₄, k₁]
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.n_lt; omega),
      VG.Proof.AesCcm.AArch64.entry_buf En.frame (L.bufD Ar.perm)]
  have ha₃ : bytesAt s₃.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [VG.Proof.AesCcm.AArch64.aad_mut L f₁₃, VG.Proof.AesCcm.AArch64.entry_buf En.frame (L.bufA Ar.perm)]
  have hpt : bytesAt s₃.mem c.D c.n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n) := by
    rw [h₃, k₂, hd₂, crypt_eq (hBC _)]
  have hd₇ : bytesAt s₇.mem c.D c.n = bytesAt s₃.mem c.D c.n := by
    rw [hm₇, Proof.AesGcm.AArch64.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.n_lt; omega),
      Proof.AesGcm.AArch64.bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact L.d_w' (by decide)) (by have := L.n_lt; omega),
      VG.Proof.AesCcm.AArch64.buf_macR (L.bufD M.env.perm) (by decide) M.frame]
  have hrecv : bytesAt s₅.mem c.T c.tl = bytesAt s.mem c.T c.tl := by
    rw [VG.Proof.AesCcm.AArch64.tag_mut L f₁₅ ht16, Proof.AesGcm.AArch64.bytesAt_frame En.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide))) (by omega)]
  have hY := congrArg List.length h₅
  rw [length_bytesAt, length_xorFrom] at hY
  have hcomp : bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) := by
    rw [show c.W + BitVec.ofNat 64 96 = c.W + BitVec.ofNat 64 uO from rfl, Proof.AesCcm.bytesAt_prefix s₅.mem _ L.t16, h₅, k₄, take_xorFrom_zero (hBC _) _ hY.symm L.t16, M.out, k₃,
      ha₃, hpt, ← mac_eq _ _ (by rw [hnl]; have := L.h13; omega)]
  have hmlen : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))).length =
      c.tl := by
    rw [mac_eq _ _ (by rw [hnl]; have := L.h13; omega), List.length_take,
      VG.Proof.AesCcm.AArch64.length_chain (hBC _) _ _ (by simp [Spec.Cmac.zeros])]
    omega
  have hiff := cryptTag_eq_iff (hBC s.mem) L.t16 (bytesAt s.mem N c.nl) hmlen (length_bytesAt s.mem c.T c.tl)
  simp only [VG.Proof.AesCcm.AArch64.openOut, Spec.Ccm.decryptWith]
  rw [hcomp, hrecv] at hd₈ x0₇
  by_cases he : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
      (bytesAt s.mem c.T c.tl) = Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (bytesAt s.mem c.A c.al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n))
  · have hq : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) =
        bytesAt s.mem c.T c.tl := hiff.mpr he.symm
    simp only [he, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [x0', og₈ _ (by decide), x0₇]; simp [hq]
    · rw [hm, hd₈]; simp only [hq, decide_true, ↓reduceIte]; rw [hd₇, hpt]
  · have hq : ¬ Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) =
        bytesAt s.mem c.T c.tl := fun h => he (hiff.mp h).symm
    simp only [he, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [x0', og₈ _ (by decide), x0₇]; simp [hq]
    · rw [hm, hd₈]; simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- `vg_aes_ccm_open`. -/
theorem open_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s : State} (h : openAArch64.pre s) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  have Ar := VG.Proof.AesCcm.AArch64.args_of_open h
  refine WP.mono (VG.Proof.AesCcm.AArch64.open_wp' v Ar) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  exact hp

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Rel`. -/
section

/-!
# AES-CCM on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2 σ₁ σ₂`) piece by piece, as AES-GCM's
do (`Proof.AesGcm.AArch64.rel_seq`): the code between calls by the taint
analysis, from the registers the environment pins to the same public values
in both runs and those the correctness proofs pin (`rel_env`); each call by
its callee's proof (`rel_upd`, `Proof.AesGcm.AArch64.rel_ctr`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)

/-- Two runs in the same environment agree on its registers. -/
theorem Env.agree {c : VG.Proof.AesCcm.AArch64.Cx} {σ₁ σ₂ : State} (E₁ : VG.Proof.AesCcm.AArch64.Env c σ₁) (E₂ : VG.Proof.AesCcm.AArch64.Env c σ₂) :
    ∀ r ∈ VG.Proof.AesCcm.AArch64.envRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.x19, E₂.x19]
  · rw [E₁.x20, E₂.x20]
  · rw [E₁.x21, E₂.x21]
  · rw [E₁.x22, E₂.x22]
  · rw [E₁.x27, E₂.x27]
  · rw [E₁.x28, E₂.x28]

/-- Code the taint analysis checks, from the environment's registers and
`rs`, on which the two runs agree. -/
theorem rel_env {c : VG.Proof.AesCcm.AArch64.Cx} {code : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (E₁ : VG.Proof.AesCcm.AArch64.Env c σ₁) (E₂ : VG.Proof.AesCcm.AArch64.Env c σ₂)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesCcm.AArch64.envRegs ++ rs)) code h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) code TT :=
  rel_taint (VG.Proof.AesCcm.AArch64.envRegs ++ rs) (by rw [E₁.sp, E₂.sp]) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact Env.agree E₁ E₂ r h
    · exact hr r h) hc

/-- A call of `vg_cmac_aes_update` with the same arguments in both runs. -/
theorem rel_upd (v : Proof.CmacAes.AArch64.UpdateImpl) {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat}
    (h₁ : Proof.CmacAes.Stream.AArch64.UArgs σ₁ K C D S R n) (h₂ : Proof.CmacAes.Stream.AArch64.UArgs σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call v.callee.name v.callee.code) TT :=
  Proof.CmacAes.Stream.AArch64.upd_rel v _ fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- `a; (b; (c; (d; (e; f))))`, related as `(a; (b; (c; (d; e)))); f`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e f : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) f) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e f))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ e₁ => cases e₁ with | seq x₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ e₂ => cases e₂ with | seq x₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ x₁)))) f₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ x₂)))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.CtrCT`. -/
section

/-!
# AES-CCM on AArch64: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. `tag y` and `ctr`, run from
two states that their correctness proofs describe with the same public
values, leak the same: the code between calls by the taint analysis
(`rel_env`), each call of `vg_aes_ctr32` by its proof
(`Proof.AesGcm.AArch64.rel_ctr`), and the chunks of `ctr` by induction on
the blocks left (`RelCT.loop`): both runs encrypt the same number of blocks
in each chunk, which depends only on the length.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite rel_ctr eval_zero eval_nonzero Others ctr_call CtrCall)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- Two runs from any states related by `P`, from those of each pair. -/
theorem rel_of_eq2 {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- What correctness says of the final states, added to two related runs. -/
theorem rel_post {σ₁ σ₂ : State} {c : Prog isa} {F₁ F₂ : State → Prop} (h : RelCT isa (Eq2 σ₁ σ₂) c TT)
    (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂) : RelCT isa (Eq2 σ₁ σ₂) c fun a b => F₁ a ∧ F₂ b :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

section
variable (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesCcm.AArch64.Env c σ₁) (E₂ : VG.Proof.AesCcm.AArch64.Env c σ₂)
include L E₁ E₂

/-- `tag y`. -/
theorem tag_rel {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    RelCT isa (Eq2 σ₁ σ₂) (tag v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesCcm.AArch64.envRegs ++ []))
      (.block (([imm .x9 0] : List Instr) ++ ctrAt ++ ctrArgs ++ ([ptr .x3 .x19 y, imm .x4 1] : List Instr))) h).isSome =
      true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] E₁ E₂ (by simp) t) (VG.Proof.AesCcm.AArch64.tagArgs_ok L E₁ hn₁ hc₁ hy) (VG.Proof.AesCcm.AArch64.tagArgs_ok L E₂ hn₂ hc₂ hy)
    fun τ₁ τ₂ ⟨F₁, C₁, _⟩ ⟨F₂, C₂, _⟩ => rel_ctr v C₁ C₂ (by rw [F₁.sp, F₂.sp])

/-- `ctrTail`. -/
theorem ctrTail_rel {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0)
    (h23₁ : σ₁.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h23₂ : σ₂.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16)) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16))
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 (c.n % 16)) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 (c.n % 16)) :
    RelCT isa (Eq2 σ₁ σ₂) (ctrTail v.callee) TT := by
  have hj : 1 + c.n / 16 < 256 ^ (15 - c.nl) := by
    have := L.hn
    have := Nat.le_self_pow (show 15 - c.nl ≠ 0 by have := L.h13; omega) 256
    omega
  -- After the call: the environment, the pointer and the length of the last bytes.
  have call : ∀ {σ τ : State}, σ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) →
      σ.gpr .x26 = BitVec.ofNat 64 (c.n % 16) → VG.Proof.AesCcm.AArch64.Env c τ →
      CtrCall τ c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 384) c.R 1 →
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] σ τ →
      WP isa (callCtr v.callee) τ fun ρ => VG.Proof.AesCcm.AArch64.Env c ρ ∧ ρ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
        ρ.gpr .x26 = BitVec.ofNat 64 (c.n % 16) :=
    fun h23 h26 F C g => WP.mono (ctr_call v C) fun ρ h =>
      ⟨F.of_saved h.saved h.sp h.rd h.wr, by rw [h.saved _ (by decide) (by decide), g _ (by decide), h23],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h26]⟩
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x25] E₁ E₂ (by agree_tac [h25₁, h25₂]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.tailSetup_ok L hn₁ E₁ hc₁ hj h25₁) (VG.Proof.AesCcm.AArch64.tailSetup_ok L hn₂ E₂ hc₂ hj h25₂)
    fun τ₁ τ₂ ⟨F₁, C₁, _, _, _, g₁, _⟩ ⟨F₂, C₂, _, _, _, g₂, _⟩ => ?_
  refine rel_seq (rel_ctr v C₁ C₂ (by rw [F₁.sp, F₂.sp])) (call h23₁ h26₁ F₁ C₁ g₁) (call h23₂ h26₂ F₂ C₂ g₂)
    fun ρ₁ ρ₂ ⟨G₁, x23₁, x26₁⟩ ⟨G₂, x23₂, x26₂⟩ => ?_
  exact VG.Proof.AesCcm.AArch64.rel_env [.x23, .x26] G₁ G₂ (by agree_tac [x23₁, x23₂, x26₁, x26₂]) ⟨_, by taint_decide⟩

end

/-- One chunk, from two states after the same number of blocks. -/
theorem chunk_rel (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) {s₁ s₂ : State}
    (hc₁ : bytesAt s₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt s₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) {b : Nat} {σ₁ σ₂ : State}
    (I₁ : VG.Proof.AesCcm.AArch64.CtrInv c n₁ s₁ b σ₁) (I₂ : VG.Proof.AesCcm.AArch64.CtrInv c n₂ s₂ b σ₂) (hb : b < c.n / 16) :
    RelCT isa (Eq2 σ₁ σ₂) (ctrChunk v.callee) TT := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  refine RelCT.assoc (rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x24, .x25] I₁.env I₂.env (by agree_tac [I₁.x24, I₂.x24, I₁.x25, I₂.x25])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.kSel_ok (b := b) I₁.x24 I₁.x25 (by omega)) (VG.Proof.AesCcm.AArch64.kSel_ok (b := b) I₂.x24 I₂.x25 (by omega))
    fun τ₁ τ₂ ⟨x26₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x26₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at x26₁ x26₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega
  have F₁ : VG.Proof.AesCcm.AArch64.Env c τ₁ := I₁.env.others g₁ (by decide) sp₁ rd₁ wr₁
  have F₂ : VG.Proof.AesCcm.AArch64.Env c τ₂ := I₂.env.others g₂ (by decide) sp₂ rd₂ wr₂
  have c0 : ∀ {n : List Byte} {s σ τ : State}, VG.Proof.AesCcm.AArch64.CtrInv c n s b σ → τ.mem = σ.mem →
      bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 →
      bytesAt τ.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 := fun I hm hc => by
    rw [hm, Proof.AesGcm.AArch64.bytesAt_frame I.frame (VG.Proof.AesCcm.AArch64.ctrR_disj L (.inl (by decide))) (by decide), hc]
  have y23₁ : τ₁.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) := by rw [g₁ _ (by decide), I₁.x23]
  have y23₂ : τ₂.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) := by rw [g₂ _ (by decide), I₂.x23]
  have y25₁ : τ₁.gpr .x25 = BitVec.ofNat 64 (1 + b) := by rw [g₁ _ (by decide), I₁.x25]
  have y25₂ : τ₂.gpr .x25 = BitVec.ofNat 64 (1 + b) := by rw [g₂ _ (by decide), I₂.x25]
  have y24₁ : τ₁.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) := by rw [g₁ _ (by decide), I₁.x24]
  have y24₂ : τ₂.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) := by rw [g₂ _ (by decide), I₂.x24]
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x23, .x25, .x26] F₁ F₂ (by agree_tac [y23₁, y23₂, y25₁, y25₂, x26₁, x26₂])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.setup_ok L hn₁ hkb hk1 F₁ (c0 I₁ m₁ hc₁) y23₁ y25₁ x26₁) (VG.Proof.AesCcm.AArch64.setup_ok L hn₂ hkb hk1 F₂ (c0 I₂ m₂ hc₂) y23₂ y25₂ x26₂)
    fun ρ₁ ρ₂ ⟨G₁, C₁, _, _, h₁, _⟩ ⟨G₂, C₂, _, _, h₂, _⟩ => ?_
  have call : ∀ {τ ρ : State}, τ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) → τ.gpr .x25 = BitVec.ofNat 64 (1 + b) →
      τ.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) → τ.gpr .x26 = BitVec.ofNat 64 k → VG.Proof.AesCcm.AArch64.Env c ρ →
      CtrCall ρ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k →
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] τ ρ →
      WP isa (callCtr v.callee) ρ fun ω => VG.Proof.AesCcm.AArch64.Env c ω ∧ ω.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) ∧
        ω.gpr .x25 = BitVec.ofNat 64 (1 + b) ∧ ω.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) ∧
        ω.gpr .x26 = BitVec.ofNat 64 k :=
    fun h23 h25 h24 h26 G C g => WP.mono (ctr_call v C) fun ω h =>
      ⟨G.of_saved h.saved h.sp h.rd h.wr, by rw [h.saved _ (by decide) (by decide), g _ (by decide), h23],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h25],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h24],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h26]⟩
  refine rel_seq (rel_ctr v C₁ C₂ (by rw [G₁.sp, G₂.sp])) (call y23₁ y25₁ y24₁ x26₁ G₁ C₁ h₁)
    (call y23₂ y25₂ y24₂ x26₂ G₂ C₂ h₂) fun ω₁ ω₂ ⟨H₁, z23₁, z25₁, z24₁, z26₁⟩ ⟨H₂, z23₂, z25₂, z24₂, z26₂⟩ => ?_
  exact VG.Proof.AesCcm.AArch64.rel_env [.x23, .x24, .x25, .x26] H₁ H₂ (by agree_tac [z23₁, z23₂, z24₁, z24₂, z25₁, z25₂, z26₁, z26₂])
    ⟨_, by taint_decide⟩

/-- `ctr`. -/
theorem ctr_rel (v : Ctr32Impl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesCcm.AArch64.Env c σ₁) (E₂ : VG.Proof.AesCcm.AArch64.Env c σ₂)
    {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (ctr v.callee) TT := by
  have hn64 := L.n_lt
  refine RelCT.assoc (rel_seq ?_ (VG.Proof.AesCcm.AArch64.ctrHead_ok v L hn₁ E₁ hc₁) (VG.Proof.AesCcm.AArch64.ctrHead_ok v L hn₂ E₂ hc₂) fun τ₁ τ₂ I₁ I₂ => ?_)
  · refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩) (VG.Proof.AesCcm.AArch64.ctrHeadBlk_ok L (nonce := n₁) E₁)
      (VG.Proof.AesCcm.AArch64.ctrHeadBlk_ok L (nonce := n₂) E₂) fun τ₁ τ₂ I₁ I₂ => ?_
    have e₁ := eval_zero (a := c.n / 16) (by rw [I₁.x24, Nat.sub_zero]) (by omega)
    have e₂ := eval_zero (a := c.n / 16) (by rw [I₂.x24, Nat.sub_zero]) (by omega)
    refine rel_ite e₁ e₂ (fun _ => ?_) (fun hf => ?_)
    · exact VG.Proof.AesCcm.AArch64.rel_env [] I₁.env I₂.env (by simp) ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine (RelCT.loop (Q := TT) (fun m a b => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧
        VG.Proof.AesCcm.AArch64.CtrInv c n₁ σ₁ j a ∧ VG.Proof.AesCcm.AArch64.CtrInv c n₂ σ₂ j b) (fun m => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨0, rfl, by omega, I₁, I₂⟩) fun _ _ h => h
    refine VG.Proof.AesCcm.AArch64.rel_of_eq2 fun a b ⟨j, hm, hj, J₁, J₂⟩ => ?_
    refine (VG.Proof.AesCcm.AArch64.rel_post (VG.Proof.AesCcm.AArch64.chunk_rel v L hn₁ hn₂ hc₁ hc₂ J₁ J₂ hj) (VG.Proof.AesCcm.AArch64.chunk_ok v L hn₁ hc₁ J₁ hj)
      (VG.Proof.AesCcm.AArch64.chunk_ok v L hn₂ hc₂ J₂ hj)).mono (fun _ _ h => h) fun a' b' ⟨⟨k, hk, hk1, hkb, K₁⟩, ⟨k', hk', _, _, K₂⟩⟩ => ?_
    have e : k = k' := by rw [hk, hk']
    subst e
    have ev₁ := eval_nonzero (r := .x24) (a := c.n / 16 - (j + k)) K₁.x24 (by omega)
    have ev₂ := eval_nonzero (r := .x24) (a := c.n / 16 - (j + k)) K₂.x24 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + k), ?_, j + k, rfl, ?_, K₁, K₂⟩⟩
    · rw [ev₁] at ht; simp at ht; omega
    · rw [ev₁] at ht; simp at ht; omega
  · refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] I₁.env I₂.env (by simp) ⟨_, by taint_decide⟩) (VG.Proof.AesCcm.AArch64.lastLen_ok L I₁.env) (VG.Proof.AesCcm.AArch64.lastLen_ok L I₂.env)
      fun ρ₁ ρ₂ ⟨x26₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x26₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
    have F₁ : VG.Proof.AesCcm.AArch64.Env c ρ₁ := I₁.env.others g₁ (by decide) sp₁ rd₁ wr₁
    have F₂ : VG.Proof.AesCcm.AArch64.Env c ρ₂ := I₂.env.others g₂ (by decide) sp₂ rd₂ wr₂
    refine rel_ite (eval_zero x26₁ (by omega)) (eval_zero x26₂ (by omega)) (fun _ => ?_) (fun _ => ?_)
    · exact VG.Proof.AesCcm.AArch64.rel_env [] F₁ F₂ (by simp) ⟨_, by taint_decide⟩
    · have c0 : ∀ {n : List Byte} {s σ τ : State}, VG.Proof.AesCcm.AArch64.CtrInv c n s (c.n / 16) σ → τ.mem = σ.mem →
          bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 →
          bytesAt τ.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 := fun I hm hc => by
        rw [hm, Proof.AesGcm.AArch64.bytesAt_frame I.frame (VG.Proof.AesCcm.AArch64.ctrR_disj L (.inl (by decide))) (by decide), hc]
      exact VG.Proof.AesCcm.AArch64.ctrTail_rel v L F₁ F₂ hn₁ hn₂ (c0 I₁ m₁ hc₁) (c0 I₂ m₂ hc₂)
        (by rw [g₁ _ (by decide), I₁.x23]) (by rw [g₂ _ (by decide), I₂.x23])
        (by rw [g₁ _ (by decide), I₁.x25]) (by rw [g₂ _ (by decide), I₂.x25]) x26₁ x26₂

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.EntryCT`. -/
section

/-!
# AES-CCM on AArch64: the arguments and the entry in two runs

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`,
the tag length and `tag` from the stack, which the taint analysis takes as
secret (it reads memory): the block is split after the loads
(`Proof.AesGcm.AArch64.RelCT.block_split`), and the rest runs from `x9`,
`x10` and `x11`, which hold `work`, the tag length and `tag`, public, in both
runs (`entry_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Impl.AesGcm.AArch64 (save)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint save_ok)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {σ₁ σ₂ : State} (A₁ : VG.Proof.AesCcm.AArch64.Args (VG.Proof.AesCcm.AArch64.cxOf σ₁) (σ₁.gpr .x2) σ₁) (A₂ : VG.Proof.AesCcm.AArch64.Args (VG.Proof.AesCcm.AArch64.cxOf σ₂) (σ₂.gpr .x2) σ₂)
    (hq : VG.Proof.AesCcm.AArch64.onePub σ₁ σ₂) : VG.Proof.AesCcm.AArch64.Args (VG.Proof.AesCcm.AArch64.cxOf σ₁) (σ₁.gpr .x2) σ₁ ∧ VG.Proof.AesCcm.AArch64.Args (VG.Proof.AesCcm.AArch64.cxOf σ₁) (σ₁.gpr .x2) σ₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have hcx : VG.Proof.AesCcm.AArch64.cxOf σ₂ = VG.Proof.AesCcm.AArch64.cxOf σ₁ := by
    simp only [VG.Proof.AesCcm.AArch64.cxOf, q0, q1, q3, q4, q5, q6, q7, qsp, qa 0 (by decide), qa 1 (by decide), qa 2 (by decide)]
  rw [hcx, ← q2] at A₂
  exact ⟨A₁, A₂⟩

/-- The entry in two runs. -/
theorem entry_rel {c : VG.Proof.AesCcm.AArch64.Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : VG.Proof.AesCcm.AArch64.Args c N σ₁) (A₂ : VG.Proof.AesCcm.AArch64.Args c N σ₂)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have run : ∀ {σ : State}, VG.Proof.AesCcm.AArch64.Args c N σ →
      WP isa (.block (([.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0] : List Instr) ++ save .x9)) σ fun s' =>
        s'.gpr .x9 = c.W ∧ s'.gpr .x10 = BitVec.ofNat 64 c.tl ∧ s'.gpr .x11 = c.T ∧
        (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp := fun A =>
    WP.block_append (WP.mono (VG.Proof.AesCcm.AArch64.ldr_ok A) fun s₁ ⟨x9₁, x10₁, x11₁, g₁, sp₁, _, _, wr₁⟩ => by
      obtain ⟨s₂, run₂, g₂, sp₂, _, _, _⟩ := VG.Proof.AesGcm.AArch64.save_ok s₁ .x9 x9₁ (by rw [wr₁]; exact A.perm.w)
      exact WP.of_runBlock ⟨s₂, run₂, by rw [g₂, x9₁], by rw [g₂, x10₁], by rw [g₂, x11₁],
        fun r h h' h'' => by rw [g₂, g₁ r h h' h''], by rw [sp₂, sp₁]⟩)
  have qsp : σ₁.sp = σ₂.sp := by rw [A₁.sp, A₂.sp]
  show RelCT isa _ (.block (([.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0] : List Instr) ++ save .x9 ++ _)) _
  refine Proof.AesGcm.AArch64.RelCT.block_split (rel_seq (Proof.AesGcm.AArch64.RelCT.block_split
      (rel_seq (rel_taint [] qsp (by simp) ⟨_, by taint_decide⟩) (VG.Proof.AesCcm.AArch64.ldr_ok A₁) (VG.Proof.AesCcm.AArch64.ldr_ok A₂)
        fun τ₁ τ₂ ⟨x9₁, _, _, _, sp₁, _⟩ ⟨x9₂, _, _, _, sp₂, _⟩ => ?_))
    (run A₁) (run A₂) fun τ₁ τ₂ ⟨x9₁, x10₁, x11₁, g₁, sp₁⟩ ⟨x9₂, x10₂, x11₂, g₂, sp₂⟩ => ?_)
  · exact rel_taint [.x9] (by rw [sp₁, sp₂, qsp]) (by agree_tac [x9₁, x9₂]) ⟨_, by taint_decide⟩
  refine rel_taint [.x9, .x10, .x11, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by rw [sp₁, sp₂, qsp]) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  by_cases h10 : r = .x10
  · subst h10; rw [x10₁, x10₂]
  by_cases h11 : r = .x11
  · subst h11; rw [x11₁, x11₂]
  rw [g₁ r h9 h10 h11, g₂ r h9 h10 h11]
  exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, h10, h11, false_or] at hr ⊢; exact hr)

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.MacCT`. -/
section

/-!
# AES-CCM on AArch64: the CBC-MAC in two runs

Untrusted: everything here is checked by Lean. Each piece of `mac y`, run
from two states that its correctness proof describes with the same public
values, leaks the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and those the correctness
proofs pin (the pointer and the length in `x23` and `x24`), and each call of
`vg_cmac_aes_update` by its proof (`rel_upd`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite eval_zero Others)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call)
open VG.Proof.AesCcm (headLen)

section
variable (v : Proof.CmacAes.AArch64.UpdateImpl) {c : VG.Proof.AesCcm.AArch64.Cx} (L : VG.Proof.AesCcm.AArch64.Lay c) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesCcm.AArch64.Env c σ₁)
  (E₂ : VG.Proof.AesCcm.AArch64.Env c σ₂) {y : Nat} (hy : y = 0 ∨ y = 96)
include L E₁ E₂ hy

/-- `updBlock y`. -/
theorem updBlock_rel : RelCT isa (Eq2 σ₁ σ₂) (updBlock v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesCcm.AArch64.envRegs ++ []))
      (.block (updArgs y ++ ([ptr .x3 .x19 bO, imm .x4 1] : List Instr))) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] E₁ E₂ (by simp) t) (VG.Proof.AesCcm.AArch64.updArgs_ok L E₁ hy) (VG.Proof.AesCcm.AArch64.updArgs_ok L E₂ hy)
    fun τ₁ τ₂ ⟨F₁, A₁, _⟩ ⟨F₂, A₂, _⟩ => VG.Proof.AesCcm.AArch64.rel_upd v A₁ A₂ (by rw [F₁.sp, F₂.sp])

/-- `absTail y`. -/
theorem absTail_rel {P : Addr} {len : Nat} (hP₁ : VG.Proof.AesCcm.AArch64.Buf c σ₁ P len) (hP₂ : VG.Proof.AesCcm.AArch64.Buf c σ₂ P len)
    (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 len)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 len) (h13₁ : σ₁.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h13₂ : σ₂.gpr .x13 = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (absTail v.callee y) TT := by
  refine RelCT.assoc (rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x23, .x24, .x13] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂, h13₁, h13₂])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.absTailPre_ok E₁ hP₁ h23₁ h24₁ h13₁ h0) (VG.Proof.AesCcm.AArch64.absTailPre_ok E₂ hP₂ h23₂ h24₂ h13₂ h0) fun τ₁ τ₂ a₁ a₂ => ?_)
  exact VG.Proof.AesCcm.AArch64.updBlock_rel v L a₁.1 a₂.1 hy

/-- `absorbPad y`. -/
theorem absorbPad_rel {P : Addr} {len : Nat} (hP₁ : VG.Proof.AesCcm.AArch64.Buf c σ₁ P len) (hP₂ : VG.Proof.AesCcm.AArch64.Buf c σ₂ P len)
    (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 len)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 len) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbPad v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesCcm.AArch64.envRegs ++ [.x23, .x24]))
      (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have hl := hP₁.lt
  -- After the call: the environment, the string's pointer and length.
  have call : ∀ {σ τ : State}, VG.Proof.AesCcm.AArch64.Env c σ → VG.Proof.AesCcm.AArch64.Buf c σ P len → σ.gpr .x23 = P → σ.gpr .x24 = BitVec.ofNat 64 len →
      Proof.CmacAes.Stream.AArch64.UArgs τ c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R
        (len / 16) → VG.Proof.AesCcm.AArch64.Env c τ → Others [.x0, .x1, .x2, .x3, .x4, .x5] σ τ → τ.rd = σ.rd → τ.wr = σ.wr →
      WP isa (callUpdate v.callee) τ fun ρ => VG.Proof.AesCcm.AArch64.Env c ρ ∧ VG.Proof.AesCcm.AArch64.Buf c ρ P len ∧ ρ.gpr .x23 = P ∧
        ρ.gpr .x24 = BitVec.ofNat 64 len :=
    fun _ hP h23 h24 U F g rd wr => WP.mono (upd_call v v.callee.name U) fun ρ h =>
      ⟨F.of_saved h.saved h.sp h.rd h.wr, hP.of_eq (by rw [h.rd, rd]) (by rw [h.wr, wr]),
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h23],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h24]⟩
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x23, .x24] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂]) t)
    (VG.Proof.AesCcm.AArch64.absArgs_ok L E₁ hy hP₁ h23₁ h24₁) (VG.Proof.AesCcm.AArch64.absArgs_ok L E₂ hy hP₂ h23₂ h24₂)
    fun τ₁ τ₂ ⟨U₁, F₁, g₁, _, rd₁, wr₁⟩ ⟨U₂, F₂, g₂, _, rd₂, wr₂⟩ => ?_
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_upd v U₁ U₂ (by rw [F₁.sp, F₂.sp])) (call E₁ hP₁ h23₁ h24₁ U₁ F₁ g₁ rd₁ wr₁)
    (call E₂ hP₂ h23₂ h24₂ U₂ F₂ g₂ rd₂ wr₂) fun ρ₁ ρ₂ ⟨G₁, B₁, x23₁, x24₁⟩ ⟨G₂, B₂, x23₂, x24₂⟩ => ?_
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x24] G₁ G₂ (by agree_tac [x24₁, x24₂]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.absMask_ok hl x24₁) (VG.Proof.AesCcm.AArch64.absMask_ok hl x24₂)
    fun κ₁ κ₂ ⟨x13₁, og₁, _, sp₁, rd₁', wr₁'⟩ ⟨x13₂, og₂, _, sp₂, rd₂', wr₂'⟩ => ?_
  have H₁ : VG.Proof.AesCcm.AArch64.Env c κ₁ := G₁.others og₁ (by decide) sp₁ rd₁' wr₁'
  have H₂ : VG.Proof.AesCcm.AArch64.Env c κ₂ := G₂.others og₂ (by decide) sp₂ rd₂' wr₂'
  refine rel_ite (eval_zero x13₁ (by omega)) (eval_zero x13₂ (by omega)) (fun _ => ?_) (fun hf => ?_)
  · exact VG.Proof.AesCcm.AArch64.rel_env [] H₁ H₂ (by simp) ⟨_, by taint_decide⟩
  · exact VG.Proof.AesCcm.AArch64.absTail_rel v L H₁ H₂ hy (B₁.of_eq rd₁' wr₁') (B₂.of_eq rd₂' wr₂')
      (by rw [og₁ _ (by decide), x23₁]) (by rw [og₂ _ (by decide), x23₂])
      (by rw [og₁ _ (by decide), x24₁]) (by rw [og₂ _ (by decide), x24₂]) x13₁ x13₂ (of_decide_eq_false hf)

/-- `aadHead y`. -/
theorem aadHead_rel {A : Addr} {a : Nat} (hA₁ : VG.Proof.AesCcm.AArch64.Buf c σ₁ A a) (hA₂ : VG.Proof.AesCcm.AArch64.Buf c σ₂ A a) (ha0 : 0 < a)
    (h23₁ : σ₁.gpr .x23 = A) (h23₂ : σ₂.gpr .x23 = A) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 a)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 a) :
    RelCT isa (Eq2 σ₁ σ₂) (aadHead v.callee y) TT :=
  VG.Proof.AesCcm.AArch64.rel_assoc5 (rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x23, .x24] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.aadHeadPre_ok E₁ hA₁ ha0 h23₁ h24₁) (VG.Proof.AesCcm.AArch64.aadHeadPre_ok E₂ hA₂ ha0 h23₂ h24₂)
    fun _ _ a₁ a₂ => VG.Proof.AesCcm.AArch64.updBlock_rel v L a₁.1 a₂.1 hy)

/-- The associated data, if there is any. -/
theorem aadPart_rel (h23₁ : σ₁.gpr .x23 = c.A) (h23₂ : σ₂.gpr .x23 = c.A)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 c.al) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 c.al) :
    RelCT isa (Eq2 σ₁ σ₂) (.ite (.zero .x .x24) (.block []) (.seq (aadHead v.callee y) (absorbPad v.callee y)))
      TT := by
  have ha := L.al_lt
  refine rel_ite (eval_zero h24₁ ha) (eval_zero h24₂ ha) (fun _ => ?_) (fun hf => ?_)
  · exact VG.Proof.AesCcm.AArch64.rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩
  have h0 : c.al ≠ 0 := of_decide_eq_false hf
  have hA₁ := L.bufA E₁.perm
  have hA₂ := L.bufA E₂.perm
  refine rel_seq (VG.Proof.AesCcm.AArch64.aadHead_rel v L E₁ E₂ hy hA₁ hA₂ (by omega) h23₁ h23₂ h24₁ h24₂)
    (VG.Proof.AesCcm.AArch64.aadHead_ok v L E₁ hy hA₁ (by omega) h23₁ h24₁) (VG.Proof.AesCcm.AArch64.aadHead_ok v L E₂ hy hA₂ (by omega) h23₂ h24₂)
    fun τ₁ τ₂ A₁ A₂ => ?_
  have hn1 : headLen c.al ≤ c.al := by unfold headLen; omega
  exact VG.Proof.AesCcm.AArch64.absorbPad_rel v L A₁.env A₂.env hy ((hA₁.drop hn1).of_eq A₁.rd A₁.wr) ((hA₂.drop hn1).of_eq A₂.rd A₂.wr)
    A₁.x23 A₂.x23 A₁.x24 A₂.x24

/-- `b0 y`. -/
theorem b0_rel (S₁ : VG.Proof.AesCcm.AArch64.Slots c σ₁.mem) (S₂ : VG.Proof.AesCcm.AArch64.Slots c σ₂.mem) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 c.al)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 c.al) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (b0 v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (VG.Proof.AesCcm.AArch64.envRegs ++ [])) (.block (b0Seg y)) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x24] E₁ E₂ (by agree_tac [h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.flags_ok L E₁ S₁ h24₁) (VG.Proof.AesCcm.AArch64.flags_ok L E₂ S₂ h24₂)
    fun τ₁ τ₂ ⟨x9₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x9₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : VG.Proof.AesCcm.AArch64.Env c τ₁ := E₁.others g₁ (by decide) sp₁ rd₁ wr₁
  have F₂ : VG.Proof.AesCcm.AArch64.Env c τ₂ := E₂.others g₂ (by decide) sp₂ rd₂ wr₂
  exact rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] F₁ F₂ (by simp) t) (VG.Proof.AesCcm.AArch64.b0Seg_ok L F₁ hn₁ (by rw [m₁]; exact hc₁) x9₁ hy)
    (VG.Proof.AesCcm.AArch64.b0Seg_ok L F₂ hn₂ (by rw [m₂]; exact hc₂) x9₂ hy) fun _ _ a₁ a₂ => VG.Proof.AesCcm.AArch64.updBlock_rel v L a₁.1 a₂.1 hy

/-- `mac y`. -/
theorem mac_rel (S₁ : VG.Proof.AesCcm.AArch64.Slots c σ₁.mem) (S₂ : VG.Proof.AesCcm.AArch64.Slots c σ₂.mem) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (mac v.callee y) TT := by
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩) (VG.Proof.AesCcm.AArch64.aadLd_ok E₁ S₁) (VG.Proof.AesCcm.AArch64.aadLd_ok E₂ S₂)
    fun τ₁ τ₂ ⟨x23₁, x24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x23₂, x24₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : VG.Proof.AesCcm.AArch64.Env c τ₁ := E₁.others g₁ (by decide) sp₁ rd₁ wr₁
  have F₂ : VG.Proof.AesCcm.AArch64.Env c τ₂ := E₂.others g₂ (by decide) sp₂ rd₂ wr₂
  refine rel_seq (VG.Proof.AesCcm.AArch64.b0_rel v L F₁ F₂ hy (by rw [m₁]; exact S₁) (by rw [m₂]; exact S₂) x24₁ x24₂ hn₁ hn₂
      (by rw [m₁]; exact hc₁) (by rw [m₂]; exact hc₂))
    (VG.Proof.AesCcm.AArch64.b0_ok v L F₁ (by rw [m₁]; exact S₁) x24₁ hn₁ (by rw [m₁]; exact hc₁) hy)
    (VG.Proof.AesCcm.AArch64.b0_ok v L F₂ (by rw [m₂]; exact S₂) x24₂ hn₂ (by rw [m₂]; exact hc₂) hy)
    fun κ₁ κ₂ ⟨M₁, y23₁, y24₁⟩ ⟨M₂, y23₂, y24₂⟩ => ?_
  refine rel_seq (VG.Proof.AesCcm.AArch64.aadPart_rel v L M₁.env M₂.env hy (by rw [y23₁, x23₁]) (by rw [y23₂, x23₂])
      (by rw [y24₁, x24₁]) (by rw [y24₂, x24₂]))
    (VG.Proof.AesCcm.AArch64.aadPart_ok v L M₁.env hy (by rw [y23₁, x23₁]) (by rw [y24₁, x24₁]))
    (VG.Proof.AesCcm.AArch64.aadPart_ok v L M₂.env hy (by rw [y23₂, x23₂]) (by rw [y24₂, x24₂])) fun ρ₁ ρ₂ P₁ P₂ => ?_
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] P₁.env P₂.env (by simp) ⟨_, by taint_decide⟩) (VG.Proof.AesCcm.AArch64.dataArgs_ok P₁.env) (VG.Proof.AesCcm.AArch64.dataArgs_ok P₂.env)
    fun ω₁ ω₂ ⟨z23₁, z24₁, h₁, _, sp₁', rd₁', wr₁'⟩ ⟨z23₂, z24₂, h₂, _, sp₂', rd₂', wr₂'⟩ => ?_
  have G₁ : VG.Proof.AesCcm.AArch64.Env c ω₁ := P₁.env.others h₁ (by decide) sp₁' rd₁' wr₁'
  have G₂ : VG.Proof.AesCcm.AArch64.Env c ω₂ := P₂.env.others h₂ (by decide) sp₂' rd₂' wr₂'
  exact VG.Proof.AesCcm.AArch64.absorbPad_rel v L G₁ G₂ hy (L.bufD G₁.perm) (L.bufD G₂.perm) z23₁ z23₂ z24₁ z24₂

end

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.OpenCT`. -/
section

/-!
# AES-CCM on AArch64: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. As `seal_ct`, with the
decryption first; then the load of the address of the received tag from its
slot, and the comparison of the tags, the result and the mask of the data,
whose branches and loops depend only on the tag length and the data's length,
by the taint analysis from that address, which correctness says both runs
load. Whether the function returns 1 or 0
leaks nothing: the comparison has no branch, and the mask writes every byte.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (imm)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)
open VG.Proof.AesCcm (length_bytesAt)

theorem open_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa openAArch64.pre openAArch64.pub (Impl.AesCcm.AArch64.open v.callee v.ctr.callee) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨A₁, A₂⟩ := VG.Proof.AesCcm.AArch64.args_two (VG.Proof.AesCcm.AArch64.args_of_open h₁) (VG.Proof.AesCcm.AArch64.args_of_open h₂) hq.1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, -⟩ := hq.1
  have L := A₁.lay
  refine rel_seq (VG.Proof.AesCcm.AArch64.entry_rel A₁ A₂ (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7])) (VG.Proof.AesCcm.AArch64.entry_ok A₁) (VG.Proof.AesCcm.AArch64.entry_ok A₂)
    fun τ₁ τ₂ En₁ En₂ => ?_
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x2, .x3] En₁.env En₂.env (by agree_tac [En₁.x2, En₂.x2, En₁.x3, En₂.x3])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.ctrs_ok L En₁.env (A₁.nonce.of_eq En₁.rd En₁.wr) En₁.x2 En₁.x3)
    (VG.Proof.AesCcm.AArch64.ctrs_ok L En₂.env (A₂.nonce.of_eq En₂.rd En₂.wr) En₂.x2 En₂.x3)
    fun ρ₁ ρ₂ ⟨E₁, f₁, c₁, _, _⟩ ⟨E₂, f₂, c₂, _, _⟩ => ?_
  have hn₁ := length_bytesAt τ₁.mem (σ₁.gpr .x2) (VG.Proof.AesCcm.AArch64.cxOf σ₁).nl
  have hn₂ := length_bytesAt τ₂.mem (σ₁.gpr .x2) (VG.Proof.AesCcm.AArch64.cxOf σ₁).nl
  refine rel_seq (VG.Proof.AesCcm.AArch64.ctr_rel v.ctr L E₁ E₂ hn₁ hn₂ c₁ c₂) (VG.Proof.AesCcm.AArch64.ctr_ok v.ctr L E₁ hn₁ c₁) (VG.Proof.AesCcm.AArch64.ctr_ok v.ctr L E₂ hn₂ c₂)
    fun π₁ π₂ ⟨F₁, _, _, g₁, _⟩ ⟨F₂, _, _, g₂, _⟩ => ?_
  have S₁ := En₁.slots.mut L ((f₁.sub (VG.Proof.AesCcm.AArch64.frame_ctrs_mut _)).trans (g₁.sub (VG.Proof.AesCcm.AArch64.ctrR_mut _)))
  have S₂ := En₂.slots.mut L ((f₂.sub (VG.Proof.AesCcm.AArch64.frame_ctrs_mut _)).trans (g₂.sub (VG.Proof.AesCcm.AArch64.ctrR_mut _)))
  have d₁ := (Proof.AesGcm.AArch64.bytesAt_frame g₁ (VG.Proof.AesCcm.AArch64.ctrR_disj L (.inl (by decide))) (by decide)).trans c₁
  have d₂ := (Proof.AesGcm.AArch64.bytesAt_frame g₂ (VG.Proof.AesCcm.AArch64.ctrR_disj L (.inl (by decide))) (by decide)).trans c₂
  refine rel_seq (VG.Proof.AesCcm.AArch64.mac_rel v L F₁ F₂ (.inr rfl) S₁ S₂ hn₁ hn₂ d₁ d₂) (VG.Proof.AesCcm.AArch64.mac_ok v L F₁ S₁ hn₁ d₁ (.inr rfl))
    (VG.Proof.AesCcm.AArch64.mac_ok v L F₂ S₂ hn₂ d₂ (.inr rfl)) fun κ₁ κ₂ M₁ M₂ => ?_
  have e₁ := (Proof.AesGcm.AArch64.bytesAt_frame M₁.frame (VG.Proof.AesCcm.AArch64.macR_c0 L (.inr rfl)) (by decide)).trans d₁
  have e₂ := (Proof.AesGcm.AArch64.bytesAt_frame M₂.frame (VG.Proof.AesCcm.AArch64.macR_c0 L (.inr rfl)) (by decide)).trans d₂
  refine rel_seq (VG.Proof.AesCcm.AArch64.tag_rel v.ctr L M₁.env M₂.env hn₁ hn₂ e₁ e₂ (.inr rfl))
    (VG.Proof.AesCcm.AArch64.tag_ok v.ctr L M₁.env hn₁ e₁ (.inr rfl)) (VG.Proof.AesCcm.AArch64.tag_ok v.ctr L M₂.env hn₂ e₂ (.inr rfl))
    fun ω₁ ω₂ ⟨G₁, _, _, k₁, _⟩ ⟨G₂, _, _, k₂, _⟩ => ?_
  have T₁ := S₁.mut L ((M₁.frame.sub (VG.Proof.AesCcm.AArch64.macR_mut (.inr rfl))).trans (k₁.sub (VG.Proof.AesCcm.AArch64.tagR_mut _ (.inr rfl))))
  have T₂ := S₂.mut L ((M₂.frame.sub (VG.Proof.AesCcm.AArch64.macR_mut (.inr rfl))).trans (k₂.sub (VG.Proof.AesCcm.AArch64.tagR_mut _ (.inr rfl))))
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] G₁ G₂ (by simp) ⟨_, by taint_decide⟩) (VG.Proof.AesCcm.AArch64.loadTag_ok G₁ T₁ .x12) (VG.Proof.AesCcm.AArch64.loadTag_ok G₂ T₂ .x12)
    fun ρ₁ ρ₂ ⟨x₁, og₁, _, sp₁, rd₁, wr₁⟩ ⟨x₂, og₂, _, sp₂, rd₂, wr₂⟩ => ?_
  exact VG.Proof.AesCcm.AArch64.rel_env [.x12] (G₁.others og₁ (by decide) sp₁ rd₁ wr₁) (G₂.others og₂ (by decide) sp₂ rd₂ wr₂)
    (by agree_tac [x₁, x₂]) ⟨_, by taint_decide⟩

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.SealCT`. -/
section

/-!
# AES-CCM on AArch64: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments (`args_two`): the entry by `entry_rel`, `Ctr₀` by the taint
analysis, the MAC by `mac_rel`, the tag by `tag_rel` and the encryption by
`ctr_rel`; the load of the address of `tag` from its slot by the taint
analysis, and the copy of the tag there and the restore by the taint
analysis from that address, which correctness says both runs load; between
them, the states the correctness proofs describe
(`Proof.AesGcm.AArch64.rel_seq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)
open VG.Proof.AesCcm (length_bytesAt)

theorem seal_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa sealAArch64.pre sealAArch64.pub (Impl.AesCcm.AArch64.seal v.callee v.ctr.callee) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨A₁, A₂⟩ := VG.Proof.AesCcm.AArch64.args_two (VG.Proof.AesCcm.AArch64.args_of_seal h₁).1 (VG.Proof.AesCcm.AArch64.args_of_seal h₂).1 hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, -⟩ := hq
  have L := A₁.lay
  refine rel_seq (VG.Proof.AesCcm.AArch64.entry_rel A₁ A₂ (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7])) (VG.Proof.AesCcm.AArch64.entry_ok A₁) (VG.Proof.AesCcm.AArch64.entry_ok A₂)
    fun τ₁ τ₂ En₁ En₂ => ?_
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [.x2, .x3] En₁.env En₂.env (by agree_tac [En₁.x2, En₂.x2, En₁.x3, En₂.x3])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesCcm.AArch64.ctrs_ok L En₁.env (A₁.nonce.of_eq En₁.rd En₁.wr) En₁.x2 En₁.x3)
    (VG.Proof.AesCcm.AArch64.ctrs_ok L En₂.env (A₂.nonce.of_eq En₂.rd En₂.wr) En₂.x2 En₂.x3)
    fun ρ₁ ρ₂ ⟨E₁, f₁, c₁, _, _⟩ ⟨E₂, f₂, c₂, _, _⟩ => ?_
  have S₁ := En₁.slots.mut L (f₁.sub (VG.Proof.AesCcm.AArch64.frame_ctrs_mut _))
  have S₂ := En₂.slots.mut L (f₂.sub (VG.Proof.AesCcm.AArch64.frame_ctrs_mut _))
  have hn₁ := length_bytesAt τ₁.mem (σ₁.gpr .x2) (VG.Proof.AesCcm.AArch64.cxOf σ₁).nl
  have hn₂ := length_bytesAt τ₂.mem (σ₁.gpr .x2) (VG.Proof.AesCcm.AArch64.cxOf σ₁).nl
  refine rel_seq (VG.Proof.AesCcm.AArch64.mac_rel v L E₁ E₂ (.inl rfl) S₁ S₂ hn₁ hn₂ c₁ c₂) (VG.Proof.AesCcm.AArch64.mac_ok v L E₁ S₁ hn₁ c₁ (.inl rfl))
    (VG.Proof.AesCcm.AArch64.mac_ok v L E₂ S₂ hn₂ c₂ (.inl rfl)) fun κ₁ κ₂ M₁ M₂ => ?_
  have d₁ := (Proof.AesGcm.AArch64.bytesAt_frame M₁.frame (VG.Proof.AesCcm.AArch64.macR_c0 L (.inl rfl)) (by decide)).trans c₁
  have d₂ := (Proof.AesGcm.AArch64.bytesAt_frame M₂.frame (VG.Proof.AesCcm.AArch64.macR_c0 L (.inl rfl)) (by decide)).trans c₂
  refine rel_seq (VG.Proof.AesCcm.AArch64.tag_rel v.ctr L M₁.env M₂.env hn₁ hn₂ d₁ d₂ (.inl rfl)) (VG.Proof.AesCcm.AArch64.tag_ok v.ctr L M₁.env hn₁ d₁ (.inl rfl))
    (VG.Proof.AesCcm.AArch64.tag_ok v.ctr L M₂.env hn₂ d₂ (.inl rfl)) fun ω₁ ω₂ ⟨F₁, _, _, g₁, _⟩ ⟨F₂, _, _, g₂, _⟩ => ?_
  have e₁ := (Proof.AesGcm.AArch64.bytesAt_frame g₁ (VG.Proof.AesCcm.AArch64.tagR_c0 L (.inl rfl)) (by decide)).trans d₁
  have e₂ := (Proof.AesGcm.AArch64.bytesAt_frame g₂ (VG.Proof.AesCcm.AArch64.tagR_c0 L (.inl rfl)) (by decide)).trans d₂
  refine rel_seq (VG.Proof.AesCcm.AArch64.ctr_rel v.ctr L F₁ F₂ hn₁ hn₂ e₁ e₂) (VG.Proof.AesCcm.AArch64.ctr_ok v.ctr L F₁ hn₁ e₁) (VG.Proof.AesCcm.AArch64.ctr_ok v.ctr L F₂ hn₂ e₂)
    fun π₁ π₂ ⟨G₁, _, _, h₁, _⟩ ⟨G₂, _, _, h₂, _⟩ => ?_
  have T₁ := S₁.mut L ((M₁.frame.sub (VG.Proof.AesCcm.AArch64.macR_mut (.inl rfl))).trans ((g₁.sub (VG.Proof.AesCcm.AArch64.tagR_mut _ (.inl rfl))).trans
    (h₁.sub (VG.Proof.AesCcm.AArch64.ctrR_mut _))))
  have T₂ := S₂.mut L ((M₂.frame.sub (VG.Proof.AesCcm.AArch64.macR_mut (.inl rfl))).trans ((g₂.sub (VG.Proof.AesCcm.AArch64.tagR_mut _ (.inl rfl))).trans
    (h₂.sub (VG.Proof.AesCcm.AArch64.ctrR_mut _))))
  refine rel_seq (VG.Proof.AesCcm.AArch64.rel_env [] G₁ G₂ (by simp) ⟨_, by taint_decide⟩) (VG.Proof.AesCcm.AArch64.loadTag_ok G₁ T₁ .x11) (VG.Proof.AesCcm.AArch64.loadTag_ok G₂ T₂ .x11)
    fun ρ₁ ρ₂ ⟨x₁, og₁, _, sp₁, rd₁, wr₁⟩ ⟨x₂, og₂, _, sp₂, rd₂, wr₂⟩ => ?_
  exact VG.Proof.AesCcm.AArch64.rel_env [.x11] (G₁.others og₁ (by decide) sp₁ rd₁ wr₁) (G₂.others og₂ (by decide) sp₂ rd₂ wr₂)
    (by agree_tac [x₁, x₂]) ⟨_, by taint_decide⟩

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Verified`. -/
section

/-!
# AES-CCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_cmac_aes_update`, with the `vg_aes_ctr32`
that goes with it), states satisfying the preconditions, and the shared
contracts of `Spec/Ccm/Contract.lean` with the working space as a last
argument (`Proof/AesCcm/Scratch.lean`), with no stack: the calls keep the
return address in `x30`, which each function saves in the working space.
`Frame.lean` allocates the working space.
-/

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-! ## v8–v15 -/

theorem seal_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («seal» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«seal», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, tagOut, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

theorem open_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («open» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«open», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, cmp, mask, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

/-! ## Correctness and constant time -/

theorem seal_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesCcm.AArch64.seal_wp v hs) (VG.Proof.AesCcm.AArch64.seal_keepsV v)

theorem open_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesCcm.AArch64.open_wp v hs) (VG.Proof.AesCcm.AArch64.open_keepsV v)

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 7 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8008 then 4 else if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { VG.Proof.AesCcm.AArch64.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («seal» v.callee v.ctr.callee) (Proof.AesCcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesCcm.AArch64.seal_correct v) (VG.Proof.AesCcm.AArch64.seal_ct v) (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
      VG.Proof.AesCcm.AArch64.sealAArch64, VG.Proof.AesCcm.AArch64.sealPre, VG.Proof.AesCcm.AArch64.oneLay, VG.Proof.AesCcm.AArch64.onePub, VG.Proof.AesCcm.AArch64.args, VG.Proof.AesCcm.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesCcm.AArch64.sealSat)

theorem open_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («open» v.callee v.ctr.callee) (Proof.AesCcm.openScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesCcm.AArch64.open_correct v) (VG.Proof.AesCcm.AArch64.open_ct v) (by
    sig_implies [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
      Spec.Ccm.openLeak, VG.Proof.AesCcm.AArch64.openAArch64, VG.Proof.AesCcm.AArch64.openPre, VG.Proof.AesCcm.AArch64.oneLay, VG.Proof.AesCcm.AArch64.onePub, VG.Proof.AesCcm.AArch64.openRes, VG.Proof.AesCcm.AArch64.openLeak, VG.Proof.AesCcm.AArch64.args, VG.Proof.AesCcm.AArch64.rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesCcm.AArch64.openSat)

end VG.Proof.AesCcm.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.AArch64.Frame`. -/
section

/-!
# AES-CCM on AArch64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is their third stack
argument, after `tag` and `tag_len`, so the frame of 2592 bytes holds a copy
of those two, the address of the working space and the working space, at the
next 16-byte boundary. The code itself uses no stack: its calls keep the
return address in `x30`. `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { VG.Proof.AesCcm.AArch64.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesCcm.AArch64.sealFrameSat

theorem seal_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» v.callee v.ctr.callee))
      (Spec.Ccm.sealContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre AArch64.abi.ptrBits)
    (post := Spec.Ccm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (VG.Proof.AesCcm.AArch64.seal_verified v) (by decide) (by decide) (sealPre_local _) (sealPost_local _) VG.Proof.AesCcm.AArch64.sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { VG.Proof.AesCcm.AArch64.openSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using VG.Proof.AesCcm.AArch64.openFrameSat

theorem open_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» v.callee v.ctr.callee))
      (Spec.Ccm.openContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre AArch64.abi.ptrBits)
    (post := Spec.Ccm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ccm.openLeak AArch64.abi.ptrBits))
    (VG.Proof.AesCcm.AArch64.open_verified v) (by decide) (by decide) (openPre_local _) (openPost_local _) VG.Proof.AesCcm.AArch64.openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.AArch64

end
