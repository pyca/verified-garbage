module

import VerifiedGarbage.Proof.AesGcm.Arm.Run
public import VerifiedGarbage.Proof.AesGcm.Arm.Env
public import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.AesOcb.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ocb

/-! ### `AesOcb.Arm.Contract`, which this module and modules that import it used -/

section

/-!
# AES-OCB on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesOcb/Scratch.lean`). `seal` and `open` call
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` in frames that push
their stack argument below the stack pointer: so the 8 bytes below the stack
pointer (`bel`) may not overlap any buffer.
-/

@[expose] public section

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros)

/-- The 8 bytes below the stack pointer, which the calls use. -/
abbrev bel (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-- The arguments on the stack, `n` words of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 4 * n⟩

abbrev roundsOk (s : State) : Prop :=
  (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` both need, but for the
permissions: `(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12],
tag = [sp + 16], tag_len = [sp + 20], work = [sp + 24])`. -/
def oneLay (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 7) ∧ work.Disjoint (args s 7) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint aad ∧ (bel s).Disjoint data ∧
    (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 28 ≤ 2 ^ 32 ∧ roundsOk s ∧
    lengthsOk (arg s 5).toNat (s.gpr .r3).toNat = true ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (bel s).Disjoint tag ∧ (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32

/-- What `vg_aes_ocb_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  s.rd = [ctx, nonce, aad, args s 7] ∧ s.wr = [data, tag, work] ∧ oneLay s ∧ tag.Disjoint (args s 7)

/-- What `vg_aes_ocb_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 7] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- The cipher of the key context. -/
abbrev ciph (s : State) : Spec.Ocb.Cipher := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- The inverse cipher of the key context. -/
abbrev inv (s : State) : Spec.Ocb.Cipher := ctxInv s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- `L_*` of the key context. -/
abbrev lstar (s : State) : Spec.Ocb.Block := ctxLstar s.mem (State.addr (s.gpr .r0))

/-- `vg_aes_ocb_seal`. -/
def sealArm : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ciph s) (lstar s) (arg s 5).toNat
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
        (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat) =
      (bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat, bytesAt s'.mem (State.addr (arg s 4)) (arg s 5).toNat)
  pub := onePub

/-- What `vg_aes_ocb_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ciph s) (inv s) (lstar s) (arg s 5).toNat
    (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)
    (bytesAt s.mem (State.addr (arg s 4)) (arg s 5).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬roundsOk s then [] else [if (openRes s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openArm : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = zeros (arg s 3).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key context (256 bytes at `K`), the working space (2560 bytes
at `W`), the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the stack
pointer and the number of rounds, all 32-bit; how their regions lie, apart
from each other, from the stack arguments (28 bytes at `SP`) and from the 8
bytes below `SP` that the calls' frames use (`Lay`); what a state may access
(`Perm`); the registers that hold some of them throughout (`Env`), which the
functions called preserve; and the stack arguments (`Args`), which nothing
writes. `orun` runs a block symbolically.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below covers_off in_off in_left covers_left covers_prefix)

/-- Runs a block of the instructions the AES-OCB code uses. -/
tactic_template "orun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  arun [Impl.AesOcb.Arm.tagO, Impl.AesOcb.Arm.ofsO, Impl.AesOcb.Arm.ckO, Impl.AesOcb.Arm.sumO,
    Impl.AesOcb.Arm.ldO, Impl.AesOcb.Arm.l0O, Impl.AesOcb.Arm.lO, Impl.AesOcb.Arm.tmpO, Impl.AesOcb.Arm.t2O,
    Impl.AesOcb.Arm.ohO, Impl.AesOcb.Arm.botO, Impl.AesOcb.Arm.cnO, Impl.AesOcb.Arm.o0O, Impl.AesOcb.Arm.vO,
    Impl.AesOcb.Arm.bufO, Impl.AesOcb.Arm.scrO, $ts,*])

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

/-- The registers apart from `rs` are kept. -/
abbrev Others (rs : List Reg) (s s' : State) : Prop := ∀ r, r ∉ rs → s'.gpr r = s.gpr r

/-- Proves `Others` of a state `orun` computed. -/
tactic_template "others_tac" : tactic => `(tactic| plain_simp_names (
                   intro r hr
                   simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
                   simp [gpr_setReg, hr]))

/-- The public arguments. -/
structure Prm where
  /-- The key context. -/
  K : BitVec 32
  /-- The working space. -/
  W : BitVec 32
  /-- The nonce. -/
  N : BitVec 32
  /-- The associated data. -/
  A : BitVec 32
  /-- The data. -/
  D : BitVec 32
  /-- The tag. -/
  T : BitVec 32
  /-- The stack pointer. -/
  SP : BitVec 32
  /-- The number of rounds. -/
  R : Nat
  /-- The length of the nonce. -/
  nl : Nat
  /-- The length of the associated data. -/
  al : Nat
  /-- The length of the data. -/
  n : Nat
  /-- The length of the tag. -/
  tl : Nat

/-- The stack arguments. -/
abbrev argR (SP : BitVec 32) : Region := ⟨State.addr SP, 28⟩

/-- How the regions lie. -/
structure Lay (p : Prm) : Prop where
  kw : p.K.toNat + 256 ≤ 2 ^ 32
  ww : p.W.toNat + 2560 ≤ 2 ^ 32
  nw : p.N.toNat + p.nl ≤ 2 ^ 32
  aw : p.A.toNat + p.al ≤ 2 ^ 32
  dw : p.D.toNat + p.n ≤ 2 ^ 32
  tw : p.T.toNat + p.tl ≤ 2 ^ 32
  al_lt : p.al < 2 ^ 32
  n_lt : p.n < 2 ^ 32
  sp8 : 8 ≤ p.SP.toNat
  spf : p.SP.toNat + 28 ≤ 2 ^ 32
  k_w : (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr p.W, 2560⟩
  k_d : (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  n_w : (⟨State.addr p.N, p.nl⟩ : Region).Disjoint ⟨State.addr p.W, 2560⟩
  n_d : (⟨State.addr p.N, p.nl⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  a_w : (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.W, 2560⟩
  a_d : (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  t_w : (⟨State.addr p.T, p.tl⟩ : Region).Disjoint ⟨State.addr p.W, 2560⟩
  t_d : (⟨State.addr p.T, p.tl⟩ : Region).Disjoint ⟨State.addr p.D, p.n⟩
  d_w : (⟨State.addr p.D, p.n⟩ : Region).Disjoint ⟨State.addr p.W, 2560⟩
  d_args : (⟨State.addr p.D, p.n⟩ : Region).Disjoint (argR p.SP)
  w_args : (⟨State.addr p.W, 2560⟩ : Region).Disjoint (argR p.SP)
  bk : (below p.SP).Disjoint ⟨State.addr p.K, 256⟩
  bn : (below p.SP).Disjoint ⟨State.addr p.N, p.nl⟩
  ba : (below p.SP).Disjoint ⟨State.addr p.A, p.al⟩
  bd : (below p.SP).Disjoint ⟨State.addr p.D, p.n⟩
  bt : (below p.SP).Disjoint ⟨State.addr p.T, p.tl⟩
  bw : (below p.SP).Disjoint ⟨State.addr p.W, 2560⟩
  rounds : p.R = 10 ∨ p.R = 12 ∨ p.R = 14
  nl1 : 1 ≤ p.nl
  nl15 : p.nl ≤ 15
  tl1 : 1 ≤ p.tl
  tl16 : p.tl ≤ 16

/-- What a state may access. -/
structure Perm (p : Prm) (s : State) : Prop where
  k : Covers [⟨State.addr p.K, 256⟩] (s.rd ++ s.wr)
  non : Covers [⟨State.addr p.N, p.nl⟩] (s.rd ++ s.wr)
  aad : Covers [⟨State.addr p.A, p.al⟩] (s.rd ++ s.wr)
  tag : Covers [⟨State.addr p.T, p.tl⟩] (s.rd ++ s.wr)
  d : Covers [⟨State.addr p.D, p.n⟩] s.wr
  w : Covers [⟨State.addr p.W, 2560⟩] s.wr
  args : Covers [argR p.SP] (s.rd ++ s.wr)
  /-- Nothing the state may write overlaps the stack arguments. -/
  argw : ∀ r ∈ s.wr, (argR p.SP).Disjoint r

theorem Perm.of_eq {p : Prm} {s s' : State} (h : Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm p s' := by
  obtain ⟨a, b, c, d, e, f, g, i⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c,
    by rw [hrd, hwr]; exact d, by rw [hwr]; exact e, by rw [hwr]; exact f, by rw [hrd, hwr]; exact g,
    by rw [hwr]; exact i⟩

/-- The registers holding some of the public arguments, the stack pointer,
and what the state may access. -/
structure Env (p : Prm) (s : State) : Prop where
  r9 : s.gpr .r9 = BitVec.ofNat 32 p.R
  r10 : s.gpr .r10 = p.K
  r11 : s.gpr .r11 = p.W
  sp : s.sp = p.SP
  perm : Perm p s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.r9, .r10, .r11]

/-- An environment, after code that keeps `r9`–`r11`, the stack pointer and
the permissions. -/
theorem Env.keep {p : Prm} {s s' : State} (h : Env p s) (hg : ∀ r ∈ envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env p s' :=
  ⟨by rw [hg _ (by simp), h.r9], by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {p : Prm} {s s' : State} (h : Env p s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env p s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.of_others {p : Prm} {s s' : State} {rs : List Reg} (h : Env p s) (ho : Others rs s s')
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hd : ∀ r ∈ envRegs, r ∉ rs := by decide) :
    Env p s' :=
  h.keep (fun r h' => ho r (hd r h')) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {p : Prm} (L : Lay p)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 2560) : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega_using [hd, this])

theorem wN {d : Nat} (hd : d < 2560) : (p.W + BitVec.ofNat 32 d).toNat = p.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨State.addr p.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha]) (by have := L.ww; omega_using [hd])

theorem k_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.N, p.nl⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.D, p.n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.T, p.tl⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (wSub hd)

theorem bw' {d k : Nat} (hd : d + k ≤ 2560) : (below p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.bw.sub_right (wSub hd)

theorem args_w' {d k : Nat} (hd : d + k ≤ 2560) : (argR p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.w_args.symm.sub_right (wSub hd)

/-- The stack arguments lie above the stack below `SP`. -/
theorem args_below : (argR p.SP).Disjoint (below p.SP) :=
  Offset.base_disjoint_below (State.addr p.SP) (n := 8) (k := 28) (by have := L.spf; omega_using [])

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {p : Prm} {s : State} (P : Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

theorem kC {d k : Nat} (h : d + k ≤ 256) :
    Covers [⟨State.addr p.K + BitVec.ofNat 64 d, k⟩] (s.rd ++ s.wr) :=
  covers_off P.k h (by decide)

end Perm

/-! ## The stack arguments -/

/-- The stack arguments `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`
in the memory `m`. -/
structure Args (p : Prm) (m : Mem) : Prop where
  a0 : m.readW (State.addr (p.SP + BitVec.ofNat 32 0)) 32 = p.A
  a4 : m.readW (State.addr (p.SP + BitVec.ofNat 32 4)) 32 = BitVec.ofNat 32 p.al
  a8 : m.readW (State.addr (p.SP + BitVec.ofNat 32 8)) 32 = p.D
  a12 : m.readW (State.addr (p.SP + BitVec.ofNat 32 12)) 32 = BitVec.ofNat 32 p.n
  a16 : m.readW (State.addr (p.SP + BitVec.ofNat 32 16)) 32 = p.T
  a20 : m.readW (State.addr (p.SP + BitVec.ofNat 32 20)) 32 = BitVec.ofNat 32 p.tl

theorem argA {p : Prm} (L : Lay p) {k : Nat} (hk : k < 28) :
    State.addr (p.SP + BitVec.ofNat 32 k) = State.addr p.SP + BitVec.ofNat 64 k :=
  addr_add (by have := L.spf; omega_using [hk, this])

/-- The stack arguments, after writes apart from them. -/
theorem Args.frame {p : Prm} (L : Lay p) {m m' : Mem} (h : Args p m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (argR p.SP).Disjoint r) : Args p m' := by
  have e : ∀ k, k + 4 ≤ 28 → m'.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 =
      m.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [argA L (by omega_using [hk])]
    exact hf.readW (r := ⟨State.addr p.SP + BitVec.ofNat 64 k, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega_using [hk]))) (by decide)
  exact ⟨by rw [e 0 (by decide), h.a0], by rw [e 4 (by decide), h.a4], by rw [e 8 (by decide), h.a8],
    by rw [e 12 (by decide), h.a12], by rw [e 16 (by decide), h.a16], by rw [e 20 (by decide), h.a20]⟩

/-- A stack argument may be read. -/
theorem Perm.argR' {p : Prm} {s : State} (P : Perm p s) (L : Lay p) {k : Nat} (hk : k + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (State.addr (p.SP + BitVec.ofNat 32 k)) 4 := by
  rw [argA L (by omega_using [hk])]; exact in_off P.args hk (by decide)

/-! ## Arithmetic -/

theorem ofNat_lsr32 {a : Nat} (ha : a < 2 ^ 32) (k : Nat) : BitVec.ofNat 32 a >>> k = BitVec.ofNat 32 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by have := Nat.div_le_self a (2 ^ k); omega_using [ha, this])]

theorem toNat_ofNat32 {a : Nat} (ha : a < 2 ^ 32) : (BitVec.ofNat 32 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

end VG.Proof.AesOcb.Arm
