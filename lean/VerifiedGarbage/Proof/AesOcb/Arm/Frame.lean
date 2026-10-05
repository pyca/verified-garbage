import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Impl.AesOcb.Arm
import VerifiedGarbage.Proof.Aes.Arm.Blocks
import VerifiedGarbage.Proof.CmacAes.Arm.Verified
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Contract`. -/
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
  let aad : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 0), (VG.Proof.AesOcb.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 2), (VG.Proof.AesOcb.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 4), (VG.Proof.AesOcb.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 6), 2560⟩
  ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesOcb.Arm.args s 7) ∧ work.Disjoint (VG.Proof.AesOcb.Arm.args s 7) ∧
    (VG.Proof.AesOcb.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesOcb.Arm.bel s).Disjoint nonce ∧ (VG.Proof.AesOcb.Arm.bel s).Disjoint aad ∧ (VG.Proof.AesOcb.Arm.bel s).Disjoint data ∧
    (VG.Proof.AesOcb.Arm.bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesOcb.Arm.arg s 0).toNat + (VG.Proof.AesOcb.Arm.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesOcb.Arm.arg s 2).toNat + (VG.Proof.AesOcb.Arm.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesOcb.Arm.arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 28 ≤ 2 ^ 32 ∧ VG.Proof.AesOcb.Arm.roundsOk s ∧
    lengthsOk (VG.Proof.AesOcb.Arm.arg s 5).toNat (s.gpr .r3).toNat = true ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (VG.Proof.AesOcb.Arm.bel s).Disjoint tag ∧ (VG.Proof.AesOcb.Arm.arg s 4).toNat + (VG.Proof.AesOcb.Arm.arg s 5).toNat ≤ 2 ^ 32

/-- What `vg_aes_ocb_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 0), (VG.Proof.AesOcb.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 2), (VG.Proof.AesOcb.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 4), (VG.Proof.AesOcb.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 6), 2560⟩
  s.rd = [ctx, nonce, aad, VG.Proof.AesOcb.Arm.args s 7] ∧ s.wr = [data, tag, work] ∧ VG.Proof.AesOcb.Arm.oneLay s ∧ tag.Disjoint (VG.Proof.AesOcb.Arm.args s 7)

/-- What `vg_aes_ocb_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 0), (VG.Proof.AesOcb.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 2), (VG.Proof.AesOcb.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 4), (VG.Proof.AesOcb.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 6), 2560⟩
  s.rd = [ctx, nonce, aad, tag, VG.Proof.AesOcb.Arm.args s 7] ∧ s.wr = [data, work] ∧ VG.Proof.AesOcb.Arm.oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 7, VG.Proof.AesOcb.Arm.arg s₁ i = VG.Proof.AesOcb.Arm.arg s₂ i

/-- The cipher of the key context. -/
abbrev ciph (s : State) : Spec.Ocb.Cipher := VG.Spec.Ocb.ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- The inverse cipher of the key context. -/
abbrev inv (s : State) : Spec.Ocb.Cipher := ctxInv s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- `L_*` of the key context. -/
abbrev lstar (s : State) : Spec.Ocb.Block := ctxLstar s.mem (State.addr (s.gpr .r0))

/-- `vg_aes_ocb_seal`. -/
def sealArm : Contract isa where
  pre := VG.Proof.AesOcb.Arm.sealPre
  post s s' :=
    VG.Spec.Ocb.encryptWith (VG.Proof.AesOcb.Arm.ciph s) (VG.Proof.AesOcb.Arm.lstar s) (VG.Proof.AesOcb.Arm.arg s 5).toNat
        (VG.Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 0)) (VG.Proof.AesOcb.Arm.arg s 1).toNat)
        (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 2)) (VG.Proof.AesOcb.Arm.arg s 3).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 2)) (VG.Proof.AesOcb.Arm.arg s 3).toNat, VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 4)) (VG.Proof.AesOcb.Arm.arg s 5).toNat)
  pub := VG.Proof.AesOcb.Arm.onePub

/-- What `vg_aes_ocb_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  VG.Spec.Ocb.decryptWith (VG.Proof.AesOcb.Arm.ciph s) (VG.Proof.AesOcb.Arm.inv s) (VG.Proof.AesOcb.Arm.lstar s) (VG.Proof.AesOcb.Arm.arg s 5).toNat
    (VG.Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 0)) (VG.Proof.AesOcb.Arm.arg s 1).toNat)
    (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 2)) (VG.Proof.AesOcb.Arm.arg s 3).toNat)
    (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 4)) (VG.Proof.AesOcb.Arm.arg s 5).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesOcb.Arm.roundsOk s then [] else [if (VG.Proof.AesOcb.Arm.openRes s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openArm : Contract isa where
  pre := VG.Proof.AesOcb.Arm.openPre
  post s s' :=
    match VG.Proof.AesOcb.Arm.openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 2)) (VG.Proof.AesOcb.Arm.arg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧ VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesOcb.Arm.arg s 2)) (VG.Proof.AesOcb.Arm.arg s 3).toNat = VG.Spec.Ocb.zeros (VG.Proof.AesOcb.Arm.arg s 3).toNat
  pub s₁ s₂ := VG.Proof.AesOcb.Arm.onePub s₁ s₂ ∧ VG.Proof.AesOcb.Arm.openLeak s₁ = VG.Proof.AesOcb.Arm.openLeak s₂

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Env`. -/
section

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

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below covers_off in_off in_left covers_left covers_prefix)

/-- Runs a block of the instructions the AES-OCB code uses. -/
macro "orun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  arun [Impl.AesOcb.Arm.tagO, Impl.AesOcb.Arm.ofsO, Impl.AesOcb.Arm.ckO, Impl.AesOcb.Arm.sumO,
    Impl.AesOcb.Arm.ldO, Impl.AesOcb.Arm.l0O, Impl.AesOcb.Arm.lO, Impl.AesOcb.Arm.tmpO, Impl.AesOcb.Arm.t2O,
    Impl.AesOcb.Arm.ohO, Impl.AesOcb.Arm.botO, Impl.AesOcb.Arm.cnO, Impl.AesOcb.Arm.o0O, Impl.AesOcb.Arm.vO,
    Impl.AesOcb.Arm.bufO, Impl.AesOcb.Arm.scrO, $ts,*])

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (VG.Arm.exec x s).bind (runBlock isa (a ++ b)) = ((VG.Arm.exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

/-- The registers apart from `rs` are kept. -/
abbrev Others (rs : List Reg) (s s' : State) : Prop := ∀ r, r ∉ rs → s'.gpr r = s.gpr r

/-- Proves `Others` of a state `orun` computed. -/
macro "others_tac" : tactic => `(tactic| (
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
structure Lay (p : VG.Proof.AesOcb.Arm.Prm) : Prop where
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
  d_args : (⟨State.addr p.D, p.n⟩ : Region).Disjoint (VG.Proof.AesOcb.Arm.argR p.SP)
  w_args : (⟨State.addr p.W, 2560⟩ : Region).Disjoint (VG.Proof.AesOcb.Arm.argR p.SP)
  bk : (VG.Proof.AesGcm.Arm.below p.SP).Disjoint ⟨State.addr p.K, 256⟩
  bn : (VG.Proof.AesGcm.Arm.below p.SP).Disjoint ⟨State.addr p.N, p.nl⟩
  ba : (VG.Proof.AesGcm.Arm.below p.SP).Disjoint ⟨State.addr p.A, p.al⟩
  bd : (VG.Proof.AesGcm.Arm.below p.SP).Disjoint ⟨State.addr p.D, p.n⟩
  bt : (VG.Proof.AesGcm.Arm.below p.SP).Disjoint ⟨State.addr p.T, p.tl⟩
  bw : (VG.Proof.AesGcm.Arm.below p.SP).Disjoint ⟨State.addr p.W, 2560⟩
  rounds : p.R = 10 ∨ p.R = 12 ∨ p.R = 14
  nl1 : 1 ≤ p.nl
  nl15 : p.nl ≤ 15
  tl1 : 1 ≤ p.tl
  tl16 : p.tl ≤ 16

/-- What a state may access. -/
structure Perm (p : VG.Proof.AesOcb.Arm.Prm) (s : State) : Prop where
  k : Covers [⟨State.addr p.K, 256⟩] (s.rd ++ s.wr)
  non : Covers [⟨State.addr p.N, p.nl⟩] (s.rd ++ s.wr)
  aad : Covers [⟨State.addr p.A, p.al⟩] (s.rd ++ s.wr)
  tag : Covers [⟨State.addr p.T, p.tl⟩] (s.rd ++ s.wr)
  d : Covers [⟨State.addr p.D, p.n⟩] s.wr
  w : Covers [⟨State.addr p.W, 2560⟩] s.wr
  args : Covers [VG.Proof.AesOcb.Arm.argR p.SP] (s.rd ++ s.wr)
  /-- Nothing the state may write overlaps the stack arguments. -/
  argw : ∀ r ∈ s.wr, (VG.Proof.AesOcb.Arm.argR p.SP).Disjoint r

theorem Perm.of_eq {p : VG.Proof.AesOcb.Arm.Prm} {s s' : State} (h : VG.Proof.AesOcb.Arm.Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesOcb.Arm.Perm p s' := by
  obtain ⟨a, b, c, d, e, f, g, i⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c,
    by rw [hrd, hwr]; exact d, by rw [hwr]; exact e, by rw [hwr]; exact f, by rw [hrd, hwr]; exact g,
    by rw [hwr]; exact i⟩

/-- The registers holding some of the public arguments, the stack pointer,
and what the state may access. -/
structure Env (p : VG.Proof.AesOcb.Arm.Prm) (s : State) : Prop where
  r9 : s.gpr .r9 = BitVec.ofNat 32 p.R
  r10 : s.gpr .r10 = p.K
  r11 : s.gpr .r11 = p.W
  sp : s.sp = p.SP
  perm : VG.Proof.AesOcb.Arm.Perm p s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.r9, .r10, .r11]

/-- An environment, after code that keeps `r9`–`r11`, the stack pointer and
the permissions. -/
theorem Env.keep {p : VG.Proof.AesOcb.Arm.Prm} {s s' : State} (h : VG.Proof.AesOcb.Arm.Env p s) (hg : ∀ r ∈ VG.Proof.AesOcb.Arm.envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.Arm.Env p s' :=
  ⟨by rw [hg _ (by simp), h.r9], by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {p : VG.Proof.AesOcb.Arm.Prm} {s s' : State} (h : VG.Proof.AesOcb.Arm.Env p s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.Arm.Env p s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.of_others {p : VG.Proof.AesOcb.Arm.Prm} {s s' : State} {rs : List Reg} (h : VG.Proof.AesOcb.Arm.Env p s) (ho : VG.Proof.AesOcb.Arm.Others rs s s')
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hd : ∀ r ∈ VG.Proof.AesOcb.Arm.envRegs, r ∉ rs := by decide) :
    VG.Proof.AesOcb.Arm.Env p s' :=
  h.keep (fun r h' => ho r (hd r h')) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 2560) : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

theorem wN {d : Nat} (hd : d < 2560) : (p.W + BitVec.ofNat 32 d).toNat = p.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- An offset into the key context, as a 64-bit address. -/
theorem kA {d : Nat} (hd : d < 256) : State.addr (p.K + BitVec.ofNat 32 d) = State.addr p.K + BitVec.ofNat 64 d :=
  addr_add (by have := L.kw; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨State.addr p.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (VG.Proof.AesOcb.Arm.Lay.wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.N, p.nl⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (VG.Proof.AesOcb.Arm.Lay.wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.A, p.al⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (VG.Proof.AesOcb.Arm.Lay.wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.D, p.n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (VG.Proof.AesOcb.Arm.Lay.wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨State.addr p.T, p.tl⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (VG.Proof.AesOcb.Arm.Lay.wSub hd)

theorem bw' {d k : Nat} (hd : d + k ≤ 2560) : (VG.Proof.AesGcm.Arm.below p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.bw.sub_right (VG.Proof.AesOcb.Arm.Lay.wSub hd)

theorem args_w' {d k : Nat} (hd : d + k ≤ 2560) : (VG.Proof.AesOcb.Arm.argR p.SP).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  L.w_args.symm.sub_right (VG.Proof.AesOcb.Arm.Lay.wSub hd)

/-- The stack arguments lie above the stack below `SP`. -/
theorem args_below : (VG.Proof.AesOcb.Arm.argR p.SP).Disjoint (VG.Proof.AesGcm.Arm.below p.SP) :=
  Offset.base_disjoint_below (State.addr p.SP) (n := 8) (k := 28) (by have := L.spf; omega)

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

theorem toNat_R : (BitVec.ofNat 32 p.R).toNat = p.R := by
  rcases L.rounds with h | h | h <;> rw [h] <;> rfl

theorem ofNat_R_lt : p.R < 2 ^ 32 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {p : VG.Proof.AesOcb.Arm.Prm} {s : State} (P : VG.Proof.AesOcb.Arm.Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

theorem kR {d k : Nat} (h : d + k ≤ 256) : InRegions (s.rd ++ s.wr) (State.addr p.K + BitVec.ofNat 64 d) k :=
  in_off P.k h (by decide)

theorem kC {d k : Nat} (h : d + k ≤ 256) :
    Covers [⟨State.addr p.K + BitVec.ofNat 64 d, k⟩] (s.rd ++ s.wr) :=
  covers_off P.k h (by decide)

end Perm

/-! ## The stack arguments -/

/-- The stack arguments `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`
in the memory `m`. -/
structure Args (p : VG.Proof.AesOcb.Arm.Prm) (m : Mem) : Prop where
  a0 : m.readW (State.addr (p.SP + BitVec.ofNat 32 0)) 32 = p.A
  a4 : m.readW (State.addr (p.SP + BitVec.ofNat 32 4)) 32 = BitVec.ofNat 32 p.al
  a8 : m.readW (State.addr (p.SP + BitVec.ofNat 32 8)) 32 = p.D
  a12 : m.readW (State.addr (p.SP + BitVec.ofNat 32 12)) 32 = BitVec.ofNat 32 p.n
  a16 : m.readW (State.addr (p.SP + BitVec.ofNat 32 16)) 32 = p.T
  a20 : m.readW (State.addr (p.SP + BitVec.ofNat 32 20)) 32 = BitVec.ofNat 32 p.tl

theorem argA {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {k : Nat} (hk : k < 28) :
    State.addr (p.SP + BitVec.ofNat 32 k) = State.addr p.SP + BitVec.ofNat 64 k :=
  addr_add (by have := L.spf; omega)

/-- The stack arguments, after writes apart from them. -/
theorem Args.frame {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m m' : Mem} (h : VG.Proof.AesOcb.Arm.Args p m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.AesOcb.Arm.argR p.SP).Disjoint r) : VG.Proof.AesOcb.Arm.Args p m' := by
  have e : ∀ k, k + 4 ≤ 28 → m'.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 =
      m.readW (State.addr (p.SP + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [VG.Proof.AesOcb.Arm.argA L (by omega)]
    exact hf.readW (r := ⟨State.addr p.SP + BitVec.ofNat 64 k, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)
  exact ⟨by rw [e 0 (by decide), h.a0], by rw [e 4 (by decide), h.a4], by rw [e 8 (by decide), h.a8],
    by rw [e 12 (by decide), h.a12], by rw [e 16 (by decide), h.a16], by rw [e 20 (by decide), h.a20]⟩

/-- A stack argument may be read. -/
theorem Perm.argR' {p : VG.Proof.AesOcb.Arm.Prm} {s : State} (P : VG.Proof.AesOcb.Arm.Perm p s) (L : VG.Proof.AesOcb.Arm.Lay p) {k : Nat} (hk : k + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (State.addr (p.SP + BitVec.ofNat 32 k)) 4 := by
  rw [VG.Proof.AesOcb.Arm.argA L (by omega)]; exact in_off P.args hk (by decide)

/-! ## Arithmetic -/

theorem ofNat_lsr32 {a : Nat} (ha : a < 2 ^ 32) (k : Nat) : BitVec.ofNat 32 a >>> k = BitVec.ofNat 32 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by have := Nat.div_le_self a (2 ^ k); omega)]

theorem toNat_ofNat32 {a : Nat} (ha : a < 2 ^ 32) : (BitVec.ofNat 32 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-- The `n` bytes at `p + d` within the `k` bytes at `p`. -/
theorem contains_at (p : Addr) {d n k : Nat} (h : d + n ≤ k) (hk : k < 2 ^ 64) :
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains_base p h (by omega)

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Callee`. -/
section

/-!
# AES-OCB on ARMv7: the functions called

Untrusted: everything here is checked by Lean. A call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` (`BlkFn`), from its
callee's contract (with `WP.call`), with the regions it is given: what it
needs (`BlkCall`) and what it leaves (`BlkPost`); and that it is constant
time (`blk_rel`). They are called in a frame that pushes their stack argument
(`push {r12, lr}`) in the 8 bytes below the stack pointer, as `vg_ghash` is
(`Proof.AesGcm.Arm.gh_call`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (below toNat_ofNat32 pushed_sp8 hspA fA popSlot view_gpr view_sp view_mem arg0
  argAddr0 cover_pushed cover_pushed' cover_frame covers_append' bytesAt_frame)

/-- A function on whole blocks that OCB calls: its name and code, what it
does to each block, and that it is verified. -/
structure BlkFn where
  name : String
  code : Prog isa
  f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State
  correct : ∀ s, (Proof.Aes.blocksArm f).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksArm f).post s s'
  ct : ConstantTime isa (Proof.Aes.blocksArm f).pre (Proof.Aes.blocksArm f).pub code
  noCalls : code.noCalls = true

theorem statesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Aes.statesAt m' p n = Spec.Aes.statesAt m p n := by
  simp only [Spec.Aes.statesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  simp only [Spec.Aes.stateAt]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  rw [Offset.add_add]
  exact hf.bytes (R := ⟨p, 16 * n⟩) hd hn (show 16 * i + j < 16 * n by omega)

theorem enc_noCalls : Impl.Aes.Arm.encryptBlocks.noCalls = true := by decide +kernel
theorem dec_noCalls : Impl.Aes.Arm.decryptBlocks.noCalls = true := by decide +kernel

/-- `vg_aes_encrypt_blocks`. -/
def encF : VG.Proof.AesOcb.Arm.BlkFn where
  name := "vg_aes_encrypt_blocks"
  code := Impl.Aes.Arm.encryptBlocks
  f := Spec.Aes.cipher
  correct := Proof.Aes.Arm.Ecb.blocks_correct Proof.Aes.Arm.Ecb.encrypt2_cryptOk
  ct := Proof.Aes.Arm.Ecb.encryptBlocks_ct
  noCalls := VG.Proof.AesOcb.Arm.enc_noCalls

/-- `vg_aes_decrypt_blocks`. -/
def decF : VG.Proof.AesOcb.Arm.BlkFn where
  name := "vg_aes_decrypt_blocks"
  code := Impl.Aes.Arm.decryptBlocks
  f := Spec.Aes.invCipher
  correct := Proof.Aes.Arm.Ecb.blocks_correct Proof.Aes.Arm.Ecb.decrypt2_cryptOk
  ct := Proof.Aes.Arm.Ecb.decryptBlocks_ct
  noCalls := VG.Proof.AesOcb.Arm.dec_noCalls

/-- The call of `F` in its frame. -/
def blkFrame (F : VG.Proof.AesOcb.Arm.BlkFn) : Prog isa := .frame (.push [.r12, .lr]) (.call F.name F.code) (.pop .r12 8)

theorem encFrame_eq : Impl.AesOcb.Arm.encFrame = VG.Proof.AesOcb.Arm.blkFrame VG.Proof.AesOcb.Arm.encF := rfl
theorem decFrame_eq : Impl.AesOcb.Arm.decFrame = VG.Proof.AesOcb.Arm.blkFrame VG.Proof.AesOcb.Arm.decF := rfl

/-- What a call of a `BlkFn` needs: the key schedule at `K` for `R` rounds,
`n` blocks at `D` and working space at `S`, in `r12` to push. -/
structure BlkCall (s : State) (K D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  r12 : s.gpr .r12 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  fitK : K.toNat + 240 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 2048 ≤ 2 ^ 32
  kd : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ks : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  bk : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr K, 240⟩
  bd : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr S, 2048⟩
  reads : Covers [⟨State.addr K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩] s.wr

/-- What a call of `F` leaves. -/
structure BlkPost (F : VG.Proof.AesOcb.Arm.BlkFn) (s : State) (K D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩, VG.Proof.AesGcm.Arm.below s.sp] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem (State.addr D) n =
    (Spec.Aes.statesAt s.mem (State.addr D) n).map
      (F.f R (Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1))))

abbrev blkRd (sp K : BitVec 32) : List Region := [⟨State.addr K, 240⟩, ⟨State.addr sp - 8, 4⟩]
abbrev blkWr (D S : BitVec 32) (n : Nat) : List Region := [⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩]

namespace BlkCall
variable {s : State} {K D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesOcb.Arm.BlkCall s K D S R n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem toNat_R : (BitVec.ofNat 32 R).toNat = R := VG.Proof.AesOcb.Arm.toNat_ofNat32 (by rcases h.rounds with h' | h' | h' <;> omega)

theorem pre (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : (Proof.Aes.blocksArm f).pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (VG.Proof.AesOcb.Arm.blkRd s.sp K) (VG.Proof.AesOcb.Arm.blkWr D S n)) := by
  have hn := VG.Proof.AesOcb.Arm.toNat_ofNat32 h.n_lt
  have b4 : ∀ x : Region, (VG.Proof.AesGcm.Arm.below s.sp).Disjoint x → (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint x :=
    fun x hx => hx.sub_left (Region.sub_prefix (by decide))
  simp only [Proof.Aes.blocksArm, VG.Proof.AesGcm.Arm.arg0 h.hsp, argAddr0 h.hsp, VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, h.r12, hn, h.toNat_R, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, view_sp, VG.Proof.AesGcm.Arm.hspA h.hsp, stackArgAddr_withRegions, stackArg_withRegions,
    Proof.AesGcm.Arm.stackArg_callEntry, Proof.AesGcm.Arm.stackArgAddr_callEntry, VG.Proof.AesGcm.Arm.arg0 h.hsp, argAddr0 h.hsp, h.r12]
  refine ⟨trivial, trivial, h.kd, h.ks, h.ds, (b4 _ h.bd).symm, (b4 _ h.bs).symm, h.fitK, h.fitD, h.fitS, ?_,
    h.rounds⟩
  have := s.sp.isLt; omega

theorem cov : Covers (VG.Proof.AesOcb.Arm.blkRd s.sp K ++ VG.Proof.AesOcb.Arm.blkWr D S n)
    ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  have e : VG.Proof.AesOcb.Arm.blkRd s.sp K = [⟨State.addr K, 240⟩] ++ [⟨State.addr s.sp - 8, 4⟩] := rfl
  rw [e]
  refine covers_append' (covers_append' (cover_pushed' h.reads) (cover_frame h.hsp (by decide)))
    (cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (VG.Proof.AesOcb.Arm.blkWr D S n) (pushed [.r12, .lr] s).wr := cover_pushed h.writes

end BlkCall

theorem blk_call (F : VG.Proof.AesOcb.Arm.BlkFn) {s : State} {K D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesOcb.Arm.BlkCall s K D S R n) :
    WP isa (VG.Proof.AesOcb.Arm.blkFrame F) s (VG.Proof.AesOcb.Arm.BlkPost F s K D S R n) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Aes.blocksArm F.f) F.correct
    (rd := VG.Proof.AesOcb.Arm.blkRd s.sp K) (wr := VG.Proof.AesOcb.Arm.blkWr D S n) (h.pre F.f) h.cov h.covW ?_ F.noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hn := VG.Proof.AesOcb.Arm.toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  have fA' := VG.Proof.AesGcm.Arm.fA (s := s) h.hsp
  have bytesK : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K) (16 * (R + 1)) =
      Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1)) :=
    bytesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.symm.sub_left (Region.sub_prefix hR'))) (by omega)
  have statesD : Spec.Aes.statesAt (pushed [.r12, .lr] s).mem (State.addr D) n =
      Spec.Aes.statesAt s.mem (State.addr D) n :=
    VG.Proof.AesOcb.Arm.statesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm) (by have := h.fitD; omega)
  simp only [Proof.Aes.blocksArm, State.withRegions_mem, State.callEntry_mem, VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, hn, h.toNat_R, bytesK, statesD] at hpost
  have fB : Frame (VG.Proof.AesOcb.Arm.blkWr D S n) (pushed [.r12, .lr] s).mem s₂.mem := hf
  have slot : s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 :=
    popSlot h.hsp fB (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.bd.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide))))
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · by_cases h12 : r = .r12
    · subst h12
      show (s₂.setReg .r12 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r12 = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot]
    · rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fB.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hpost

theorem blk_rel (F : VG.Proof.AesOcb.Arm.BlkFn) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : BitVec 32, ∃ R n : Nat,
      VG.Proof.AesOcb.Arm.BlkCall s₁ K D S R n ∧ VG.Proof.AesOcb.Arm.BlkCall s₂ K D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (VG.Proof.AesOcb.Arm.blkFrame F) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨K, D, S, R, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := Proof.Aes.blocksArm F.f) F.correct F.ct
    (VG.Proof.AesOcb.Arm.blkRd s₁.sp K) (VG.Proof.AesOcb.Arm.blkWr D S n) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₁ := h₁.pre F.f
  have p₂ := h₂.pre F.f
  rw [← hsp] at p₂
  refine ⟨p₁, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [Proof.Aes.blocksArm, stackArg_withRegions, Proof.AesGcm.Arm.stackArg_callEntry, VG.Proof.AesGcm.Arm.arg0 h₁.hsp,
    VG.Proof.AesGcm.Arm.arg0 h₂.hsp, VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Words`. -/
section

/-!
# AES-OCB on ARMv7: blocks a word at a time

Untrusted: everything here is checked by Lean. The straight-line pieces the
functions build blocks with, each leaving its memory and writing only some
registers (`Ran`): the XOR of two blocks into a third, a word at a time
(`xorB`, which is AES-CMAC's `xorBlk`: `Cmac.xor4Mem`, `blockAtMem_xor4`),
a block zeroed (`zero16`: `Cmac.zero4`), copied (`copy16`) and doubled
(`dbl`: `dblMem`, `blockAtMem_dbl`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.AesGcm.Arm (in_left in_off covers_left mem_store)

/-- What a straight-line piece leaves: the memory `m`, and only the registers
`rs` written. -/
structure Ran (rs : List Reg) (m : Mem) (s s' : State) : Prop where
  mem : s'.mem = m
  gpr : VG.Proof.AesOcb.Arm.Others rs s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Ran.mono {rs rs' : List Reg} {m : Mem} {s s' : State} (h : VG.Proof.AesOcb.Arm.Ran rs m s s') (hr : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.AesOcb.Arm.Ran rs' m s s' :=
  ⟨h.mem, fun r h' => h.gpr r fun h'' => h' (hr r h''), h.sp, h.rd, h.wr⟩

/-! ## XOR -/

theorem xorB_eq (pb qb cb : Reg) (pd qd cd : Nat) :
    xorB pb qb cb pd qd cd = Proof.CmacAes.Arm.xorBlk .r0 .r1 pb qb cb pd qd cd := rfl

/-- `cb + cd ← (pb + pd) ⊕ (qb + qd)`, through `r0` and `r1`. -/
theorem xorB_wp {pb qb cb : Reg} {pd qd cd : Nat} {s : State}
    (hp₁ : pb ≠ .r0) (hp₂ : pb ≠ .r1) (hq₁ : qb ≠ .r0) (hq₂ : qb ≠ .r1) (hc₁ : cb ≠ .r0) (hc₂ : cb ≠ .r1)
    (hpd : pd + 12 < 4096) (hqd : qd + 12 < 4096) (hcd : cd + 12 < 4096)
    (fp : (s.gpr pb).toNat + pd + 16 ≤ 2 ^ 32) (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32)
    (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨State.addr (s.gpr pb) + BitVec.ofNat 64 pd, 16⟩] (s.rd ++ s.wr))
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr) :
    WP isa (.block (xorB pb qb cb pd qd cd)) s (VG.Proof.AesOcb.Arm.Ran [.r0, .r1]
      (Proof.Cmac.xor4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr pb) + BitVec.ofNat 64 pd) (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) s) := by
  rw [VG.Proof.AesOcb.Arm.xorB_eq, ← List.append_nil (Proof.CmacAes.Arm.xorBlk ..)]
  refine Proof.CmacAes.Arm.xorBlk_ok (by decide) hp₁ hp₂ hq₁ hq₂ hc₁ hc₂ hpd hqd hcd fp fq fc rP rQ wC
    fun s' st => WP.block_nil_iff.mpr ⟨st.mem, fun r hr => ?_, st.sp, st.rd, st.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact st.gpr r hr.1 hr.2

/-- The block of an XOR. -/
theorem blockAtMem_xor4 (m : Mem) {c p q : Addr} (hp : Proof.Cmac.Sep4 c p) (hq : Proof.Cmac.Sep4 c q) :
    blockAtMem (Proof.Cmac.xor4Mem m c p q) c = blockAtMem m p ^^^ blockAtMem m q := by
  rw [blockAtMem, Proof.Cmac.xor4Mem_bytes m hp hq, ← Proof.Ocb.xor_eq,
    Proof.Ocb.ofBytes_xor (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

/-! ## Zeros -/

theorem zero16_eq (o : Nat) : Impl.AesGcm.Arm.zero16 o = .mov .r0 (.imm 0) :: Proof.CmacAes.Arm.zeroBlk .r0 .r11 o := rfl

/-- `W + o ← 0`, through `r0`. -/
theorem zero16_wp {o : Nat} {s : State} (ho : o + 12 < 4096) (fb : (s.gpr .r11).toNat + o + 16 ≤ 2 ^ 32)
    (wB : Covers [⟨State.addr (s.gpr .r11) + BitVec.ofNat 64 o, 16⟩] s.wr) :
    WP isa (.block (Impl.AesGcm.Arm.zero16 o)) s
      (VG.Proof.AesOcb.Arm.Ran [.r0] (Proof.Cmac.zero4 s.mem (State.addr (s.gpr .r11) + BitVec.ofNat 64 o)) s) := by
  rw [VG.Proof.AesOcb.Arm.zero16_eq]
  refine WP.block_cons_iff.mpr ⟨s.setReg .r0 0, by simp [isa, VG.Arm.exec, Op2.eval]; decide, ?_⟩
  rw [← List.append_nil (Proof.CmacAes.Arm.zeroBlk ..)]
  refine Proof.CmacAes.Arm.zeroBlk_ok (by simp [gpr_setReg]) ho (by simpa [gpr_setReg] using fb)
    (by simpa [gpr_setReg, wr_setReg] using wB) fun s' hg hm hrd hwr hsp => WP.block_nil_iff.mpr ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hm]; simp [gpr_setReg, mem_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hg]; simp [gpr_setReg, hr]
  · rw [hsp]; rfl
  · rw [hrd]; rfl
  · rw [hwr]; rfl

theorem blockAtMem_zero4 (m : Mem) (c : Addr) : blockAtMem (Proof.Cmac.zero4 m c) c = 0 := by
  rw [blockAtMem, Proof.Cmac.zero4_bytes]; decide

/-! ## Copies -/

/-- The memory after `copy16`: the four words at `s` stored at `d`. -/
def copyMem (m : Mem) (s d : Addr) : Mem :=
  Proof.Cmac.store4 m d (m.readW s 32) (m.readW (s + BitVec.ofNat 64 4) 32) (m.readW (s + BitVec.ofNat 64 8) 32)
    (m.readW (s + BitVec.ofNat 64 12) 32)

theorem blockAtMem_copy (m : Mem) (s d : Addr) : blockAtMem (VG.Proof.AesOcb.Arm.copyMem m s d) d = blockAtMem m s := by
  rw [blockAtMem, blockAtMem, VG.Proof.AesOcb.Arm.copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]

/-- `W + d ← W + s`, through `r0`–`r3`. -/
theorem copy16_wp {sO dO : Nat} {t : State} {W : Addr} (h11 : State.addr (t.gpr .r11) = W)
    (hs : sO + 12 < 4096) (hd : dO + 12 < 4096) (fw : (t.gpr .r11).toNat + 2560 ≤ 2 ^ 32)
    (hs' : sO + 16 ≤ 2560) (hd' : dO + 16 ≤ 2560)
    (rS : Covers [⟨W + BitVec.ofNat 64 sO, 16⟩] (t.rd ++ t.wr)) (wD : Covers [⟨W + BitVec.ofNat 64 dO, 16⟩] t.wr) :
    WP isa (.block (copy16 sO dO)) t (VG.Proof.AesOcb.Arm.Ran [.r0, .r1, .r2, .r3]
      (VG.Proof.AesOcb.Arm.copyMem t.mem (W + BitVec.ofNat 64 sO) (W + BitVec.ofNat 64 dO)) t) := by
  have ea : ∀ k, k < 2560 → State.addr (t.gpr .r11 + BitVec.ofNat 32 k) = W + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by omega), h11]
  have r₀ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 sO) 4 := Proof.CmacAes.Arm.in_word0 rS
  have r₁ := Proof.CmacAes.Arm.in_word rS (i := 4) (by decide)
  have r₂ := Proof.CmacAes.Arm.in_word rS (i := 8) (by decide)
  have r₃ := Proof.CmacAes.Arm.in_word rS (i := 12) (by decide)
  rw [Offset.add_add] at r₁ r₂ r₃
  have w₀ : InRegions t.wr (W + BitVec.ofNat 64 dO) 4 := Proof.CmacAes.Arm.in_word0 wD
  have w₁ := Proof.CmacAes.Arm.in_word wD (i := 4) (by decide)
  have w₂ := Proof.CmacAes.Arm.in_word wD (i := 8) (by decide)
  have w₃ := Proof.CmacAes.Arm.in_word wD (i := 12) (by decide)
  rw [Offset.add_add] at w₁ w₂ w₃
  have o₀ : sO < 4096 := by omega
  have o₁ : sO + 4 < 4096 := by omega
  have o₂ : sO + 8 < 4096 := by omega
  have o₃ : sO + 12 < 4096 := by omega
  have d₀ : dO < 4096 := by omega
  have d₁ : dO + 4 < 4096 := by omega
  have d₂ : dO + 8 < 4096 := by omega
  have d₃ : dO + 12 < 4096 := by omega
  refine WP.of_runBlock ⟨_, by
    simp only [copy16]
    orun [o₀, o₁, o₂, o₃, d₀, d₁, d₂, d₃, ea sO (by omega), ea (sO + 4) (by omega), ea (sO + 8) (by omega), ea (sO + 12) (by omega), ea dO (by omega),
      ea (dO + 4) (by omega), ea (dO + 8) (by omega), ea (dO + 12) (by omega), r₀, r₁, r₂, r₃, w₀, w₁, w₂,
      w₃, hs, hd], ⟨?_, by others_tac, by rfl, by rfl, by rfl⟩⟩
  simp only [mem_setReg, mem_store, VG.Proof.AesOcb.Arm.copyMem, Proof.Cmac.store4, Offset.add_add]

/-! ## Doubling -/

/-- The memory after doubling the block at `P` into `C`: the block as four
byte-reversed words (`Cmac.dblMem`'s). -/
def dblMem (m : Mem) (P C : Addr) : Mem :=
  let b₀ := byteRev32 (m.readW P 32)
  let b₁ := byteRev32 (m.readW (P + BitVec.ofNat 64 4) 32)
  let b₂ := byteRev32 (m.readW (P + BitVec.ofNat 64 8) 32)
  let b₃ := byteRev32 (m.readW (P + BitVec.ofNat 64 12) 32)
  Proof.Cmac.store4 m C (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (P C : Addr) : Frame [⟨C, 16⟩] m (VG.Proof.AesOcb.Arm.dblMem m P C) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_frame (m : Mem) (s d : Addr) : Frame [⟨d, 16⟩] m (VG.Proof.AesOcb.Arm.copyMem m s d) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem blockAtMem_dbl (m : Mem) (P C : Addr) :
    blockAtMem (VG.Proof.AesOcb.Arm.dblMem m P C) C = Spec.Ocb.double (blockAtMem m P) := by
  simp only [VG.Proof.AesOcb.Arm.dblMem, blockAtMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4, ← Proof.Cmac.ofBytes_rev4,
    Proof.Ocb.double_eq]
  exact Proof.Cmac.ofBytes_toBytes _

/-- The mask of the reduction, as `dbl` computes it. -/
theorem mask_eq (b : BitVec 32) :
    ((b >>> 31) - BitVec.ofNat 32 1 &&& BitVec.ofNat 32 0x87) ^^^ BitVec.ofNat 32 0x87 =
      ((0 : BitVec 32) - (b >>> 31)) &&& 0x87 := by
  have h : b >>> 31 = 0 ∨ b >>> 31 = 1 := by
    have : (b >>> 31).toNat < 2 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := b.isLt; omega
    rcases (show (b >>> 31).toNat = 0 ∨ (b >>> 31).toNat = 1 by omega) with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases h with h | h <;> rw [h] <;> decide

theorem rev_eq (a : BitVec 32) : rev a = byteRev32 a := rfl

/-- `W + d ← double(b + s)`, through `r0`–`r3` and `r12`. -/
theorem dbl_wp {b : Reg} {sO dO : Nat} {t : State} {P W : Addr} (hb : b ≠ .r0 ∧ b ≠ .r1 ∧ b ≠ .r2)
    (hP : State.addr (t.gpr b) = P) (h11 : State.addr (t.gpr .r11) = W)
    (hs : sO + 12 < 4096) (hd : dO + 12 < 4096) (fb : (t.gpr b).toNat + sO + 16 ≤ 2 ^ 32)
    (fw : (t.gpr .r11).toNat + dO + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨P + BitVec.ofNat 64 sO, 16⟩] (t.rd ++ t.wr)) (wD : Covers [⟨W + BitVec.ofNat 64 dO, 16⟩] t.wr) :
    WP isa (.block (dbl b sO dO)) t (VG.Proof.AesOcb.Arm.Ran [.r0, .r1, .r2, .r3, .r12]
      (VG.Proof.AesOcb.Arm.dblMem t.mem (P + BitVec.ofNat 64 sO) (W + BitVec.ofNat 64 dO)) t) := by
  obtain ⟨b0, b1, b2⟩ := hb
  have eb : ∀ k, k ≤ sO + 12 → State.addr (t.gpr b + BitVec.ofNat 32 k) = P + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by omega), hP]
  have ew : ∀ k, k ≤ dO + 12 → State.addr (t.gpr .r11 + BitVec.ofNat 32 k) = W + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by omega), h11]
  have r₀ : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 sO) 4 := Proof.CmacAes.Arm.in_word0 rS
  have r₁ := Proof.CmacAes.Arm.in_word rS (i := 4) (by decide)
  have r₂ := Proof.CmacAes.Arm.in_word rS (i := 8) (by decide)
  have r₃ := Proof.CmacAes.Arm.in_word rS (i := 12) (by decide)
  rw [Offset.add_add] at r₁ r₂ r₃
  have w₀ : InRegions t.wr (W + BitVec.ofNat 64 dO) 4 := Proof.CmacAes.Arm.in_word0 wD
  have w₁ := Proof.CmacAes.Arm.in_word wD (i := 4) (by decide)
  have w₂ := Proof.CmacAes.Arm.in_word wD (i := 8) (by decide)
  have w₃ := Proof.CmacAes.Arm.in_word wD (i := 12) (by decide)
  rw [Offset.add_add] at w₁ w₂ w₃
  have o₀ : sO < 4096 := by omega
  have o₁ : sO + 4 < 4096 := by omega
  have o₂ : sO + 8 < 4096 := by omega
  have o₃ : sO + 12 < 4096 := by omega
  have d₀ : dO < 4096 := by omega
  have d₁ : dO + 4 < 4096 := by omega
  have d₂ : dO + 8 < 4096 := by omega
  have d₃ : dO + 12 < 4096 := by omega
  refine WP.of_runBlock ⟨_, by
    simp only [dbl]
    orun [o₀, o₁, o₂, o₃, d₀, d₁, d₂, d₃, b0, b1, b2, eb sO (by omega), eb (sO + 4) (by omega), eb (sO + 8) (by omega), eb (sO + 12) (by omega),
      ew dO (by omega), ew (dO + 4) (by omega), ew (dO + 8) (by omega), ew (dO + 12) (by omega),
      r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, hs, hd], ⟨?_, by others_tac, by rfl, by rfl, by rfl⟩⟩
  simp only [mem_setReg, mem_store, VG.Proof.AesOcb.Arm.dblMem, Proof.Cmac.store4, VG.Proof.AesOcb.Arm.rev_eq, VG.Proof.AesOcb.Arm.mask_eq, gpr_setReg, ite_true, ite_false,
    reduceCtorEq, b0, b1, b2, Offset.add_add]
  rfl

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.LNtz`. -/
section

/-!
# AES-OCB on ARMv7: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `r6`), shifted right
once more each time (in `lr`), is even: `ntz(i)` times (`lNtz_ok`), as on
AArch64 (`Proof.AesOcb.AArch64.lNtz_ok`). The invariant: after `j`
doublings, `W + lO` holds `L_j`, `lr` is `i / 2^j`, which is positive, and
`ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.Arm (eval_eq' z_cmp0 z_subFlags)

theorem and1 {v : Nat} (hv : v < 2 ^ 32) :
    BitVec.ofNat 32 v &&& BitVec.ofNat 32 1 = BitVec.ofNat 32 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, VG.Proof.AesOcb.Arm.toNat_ofNat32 hv, show (BitVec.ofNat 32 1).toNat = 1 from rfl, Nat.and_one_is_mod,
    VG.Proof.AesOcb.Arm.toNat_ofNat32 (by omega)]

theorem shr1 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 1 = BitVec.ofNat 32 (v / 2) := by
  rw [VG.Proof.AesOcb.Arm.ofNat_lsr32 hv]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.ntzRegs s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `r12 ← lr ∧ 1` and `Z` set if it is zero, with `v` in `lr`. -/
theorem low1_wp (s : State) {v : Nat} (hv : v < 2 ^ 32) (hlr : s.gpr .lr = BitVec.ofNat 32 v) :
    WP isa (.block low1) s fun s' => s'.z = decide (v % 2 = 0) ∧ VG.Proof.AesOcb.Arm.Ran [.r12] s.mem s s' := by
  refine WP.of_runBlock ⟨_, by orun [low1], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [z_subFlags, gpr_setReg, ite_true, hlr, VG.Proof.AesOcb.Arm.and1 hv, BitVec.sub_zero]
  exact z_cmp0 (by omega)

theorem lNtz_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 32) (h6 : s.gpr .r6 = BitVec.ofNat 32 i)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (VG.Proof.AesOcb.Arm.LNtzPost (State.addr p.W) l i s) := by
  have fw := L.ww
  unfold lNtz
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.copy16_wp (W := State.addr p.W) (by rw [E.r11])
    (by decide) (by decide) (by rw [E.r11]; omega) (by decide) (by decide) (E.perm.wCR (by decide))
    (E.perm.wC (by decide))) fun s₁ R₁ => ?_)))
  have g₁ : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3] → s₁.gpr r = s.gpr r := R₁.gpr
  refine WP.block_cons_iff.mpr ⟨s₁.setReg .lr (s₁.gpr .r6), by simp [isa, VG.Arm.exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (VG.Proof.AesOcb.Arm.low1_wp _ hi' (by simp [gpr_setReg, g₁ .r6 (by decide), h6])) fun s₂ ⟨z₂, R₂⟩ => ?_
  -- The state before the loop.
  have post_of : ∀ t : State, Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.ntzRegs s₂ t → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      VG.Proof.AesOcb.Arm.LNtzPost (State.addr p.W) l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [VG.Proof.AesOcb.Arm.ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [VG.Proof.AesOcb.Arm.ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        R₂.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2), g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1,
          hr.2.2.2.1])], sp, rd, wr⟩
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by
    rw [R₂.mem, mem_setReg, R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have v₂ : blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l 0 := by
    rw [R₂.mem, mem_setReg, R₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_copy, hl0]
  have sp₂ : s₂.sp = s.sp := by rw [R₂.sp, sp_setReg, R₁.sp]
  have rd₂ : s₂.rd = s.rd := by rw [R₂.rd, rd_setReg, R₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [R₂.wr, wr_setReg, R₁.wr]
  have lr₂ : s₂.gpr .lr = BitVec.ofNat 32 i := by
    rw [R₂.gpr _ (by decide), gpr_setReg_self, g₁ _ (by decide), h6]
  have r11₂ : s₂.gpr .r11 = p.W := by
    rw [R₂.gpr _ (by decide), gpr_setReg_of_ne (h := by decide), g₁ _ (by decide), E.r11]
  refine WP.ite (decide (i % 2 = 0)) (eval_eq' z₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂ rd₂ wr₂))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) ∧
      Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l j ∧
      VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.ntzRegs s₂ t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using lr₂, fr₂, v₂,
      fun _ _ => rfl, sp₂, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, lrt, fr, v, g, sp, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have r11t : t.gpr .r11 = p.W := by rw [g _ (by decide), r11₂]
  have Pt : VG.Proof.AesOcb.Arm.Perm p t := E.perm.of_eq rd wr
  refine WP.block_append (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.dbl_wp (b := .r11) (W := State.addr p.W)
    (P := State.addr p.W) (by decide) (by rw [r11t]) (by rw [r11t]) (by decide) (by decide)
    (by rw [r11t]; simp only [lO]; omega) (by rw [r11t]; simp only [lO]; omega) (Pt.wCR (by decide)) (Pt.wC (by decide))) fun t₁ D₁ => ?_))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have lr₁ : t₁.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), lrt]
  refine WP.block_cons_iff.mpr ⟨t₁.setReg .lr (t₁.gpr .lr >>> 1), by simp [isa, VG.Arm.exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (VG.Proof.AesOcb.Arm.low1_wp _ (v := i / 2 ^ (j + 1)) (by omega) (by simp [gpr_setReg, lr₁, VG.Proof.AesOcb.Arm.shr1 hv, e]))
    fun t₃ ⟨z₃, R₃⟩ => ?_
  have fr' : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [R₃.mem, mem_setReg, D₁.mem]
    exact fun x hx => (VG.Proof.AesOcb.Arm.dblMem_frame _ _ _ x hx).trans (fr x hx)
  have v' : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by
    rw [R₃.mem, mem_setReg, D₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_dbl, v]; rfl
  have g' : VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.ntzRegs s₂ t₃ := fun r hr => by
    simp only [VG.Proof.AesOcb.Arm.ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2),
      D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [VG.Proof.AesOcb.Arm.ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  have sp' : t₃.sp = s.sp := by rw [R₃.sp, sp_setReg, D₁.sp, sp]
  have rd' : t₃.rd = s.rd := by rw [R₃.rd, rd_setReg, D₁.rd, rd]
  have wr' : t₃.wr = s.wr := by rw [R₃.wr, wr_setReg, D₁.wr, wr]
  have lr₃ : t₃.gpr .lr = BitVec.ofNat 32 (i / 2 ^ (j + 1)) := by
    rw [R₃.gpr _ (by decide), gpr_setReg_self, lr₁, VG.Proof.AesOcb.Arm.shr1 hv, e]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', lr₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), post_of t₃ fr' ?_ g' sp' rd' wr'⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.NonceBlock`. -/
section

/-!
# AES-OCB on ARMv7: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`), as on AArch64
(`Proof.AesOcb.AArch64.nonceBlock_ok`): zeros, the 1 before where the nonce
goes, the nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into
the first byte, and the last byte split into `bottom` and the rest. The 16
bytes are followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base)
open VG.Proof.AesGcm.Arm (copyLoop_ok LoopPre in_left in_off and15 mem_store rd_store wr_store sp_store gpr_store add_ofNat_zero setWidth8_32)

theorem ofNat_shl4 (a : Nat) : BitVec.ofNat 32 a <<< 4 = BitVec.ofNat 32 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  congr 1; omega

theorem or_byte32 (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 b ||| BitVec.ofNat 32 v) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 32 by omega, hi,
    decide_true, Bool.true_and]

theorem and_byte32 (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 b &&& BitVec.ofNat 32 v) = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 32 by omega, hi,
    decide_true, Bool.true_and]

theorem and63_32 (b : Byte) : BitVec.setWidth 32 b &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    show (63 : Nat) % 2 ^ 32 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show min k L.length = k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega, ↓reduceIte]
    congr 2; omega

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 4⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 32 = BitVec.ofNat 32 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : VG.Proof.AesOcb.Arm.Others [.r0, .r1, .r2, .r3, .r12] s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem w127 (W : BitVec 32) {nl : Nat} (h : nl ≤ 15) :
    W + BitVec.ofNat 32 127 - BitVec.ofNat 32 nl = W + BitVec.ofNat 32 (127 - nl) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega)]

theorem w128 (W : BitVec 32) {nl : Nat} (h : nl ≤ 15) :
    W + BitVec.ofNat 32 (127 - nl) + BitVec.ofNat 32 1 = W + BitVec.ofNat 32 (128 - nl) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

theorem nonceBlock_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem)
    (h4 : s.gpr .r4 = p.N) (h5 : s.gpr .r5 = BitVec.ofNat 32 p.nl) :
    WP isa nonceBlock s (VG.Proof.AesOcb.Arm.NoncePost (State.addr p.W) p.tl (bytesAt s.mem (State.addr p.N) p.nl) s) := by
  have fw := L.ww
  have h1 := L.nl1
  have h15 := L.nl15
  have nl32 : p.nl < 2 ^ 32 := by omega
  unfold nonceBlock
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.zero16_wp (o := tmpO) (by decide) (by rw [E.r11]; simp only [tmpO]; omega)
    (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  have r11₁ : s₁.gpr .r11 = p.W := by rw [R₁.gpr _ (by decide), E.r11]
  have r4₁ : s₁.gpr .r4 = p.N := by rw [R₁.gpr _ (by decide), h4]
  have r5₁ : s₁.gpr .r5 = BitVec.ofNat 32 p.nl := by rw [R₁.gpr _ (by decide), h5]
  have ea : State.addr (p.W + BitVec.ofNat 32 (127 - p.nl)) = State.addr p.W + BitVec.ofNat 64 (127 - p.nl) :=
    addr_add (by omega)
  have w₁ : InRegions s₁.wr (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) 1 := by
    rw [R₁.wr]; exact E.perm.wW (d := 127 - p.nl) (n := 1) (by omega)
  have eD : State.addr (p.W + BitVec.ofNat 32 (128 - p.nl)) = State.addr p.W + BitVec.ofNat 64 (128 - p.nl) :=
    addr_add (by omega)
  refine WP.of_runBlock ⟨_, by orun [r11₁, r4₁, r5₁, VG.Proof.AesOcb.Arm.w127 _ h15, add_ofNat_zero, ea, w₁, VG.Proof.AesOcb.Arm.w128 _ h15], ?_⟩
  refine WP.seq (WP.mono (copyLoop_ok _ (S := p.N) (D := p.W + BitVec.ofNat 32 (128 - p.nl)) (n := p.nl)
    ⟨by simp [gpr_setReg, r4₁], by simp [gpr_setReg], by simp [gpr_setReg, r5₁], h1, nl32, L.nw,
      by rw [L.wN (by omega)]; omega, by simp only [rd_setReg, wr_setReg, rd_store, wr_store, R₁.rd, R₁.wr]; exact E.perm.non,
      by simp only [wr_setReg, wr_store, R₁.wr, eD]; exact E.perm.wC (d := 128 - p.nl) (n := p.nl) (by omega),
      by rw [eD]; exact L.n_w' (by omega)⟩) fun s₃ ⟨m₃, O₃⟩ => ?_)
  simp only [mem_store, mem_setReg, eD] at m₃
  -- what the first two pieces wrote
  have e127 : State.addr p.W + BitVec.ofNat 64 (127 - p.nl) =
      State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - p.nl) := by
    rw [Offset.add_add, show 112 + (15 - p.nl) = 127 - p.nl by omega]
  have e128 : State.addr p.W + BitVec.ofNat 64 (128 - p.nl) =
      State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - p.nl) := by
    rw [Offset.add_add, show 112 + (16 - p.nl) = 128 - p.nl by omega]
  have f₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] s.mem
      (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1))) := by
    rw [R₁.mem]
    refine (Proof.Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [e127]; exact Offset.contains_base _ (by omega) (by omega)
  have f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] s.mem s₃.mem := by
    rw [m₃]
    refine fun x hx => (VG.WriteBytes.writeBytes_frame _ _ _ ?_ x hx).trans (f₂ x hx)
    rw [length_bytesAt, e128]; exact Offset.contains_base _ (by omega) (by omega)
  have A₃ : VG.Proof.AesOcb.Arm.Args p s₃.mem := A.frame L f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.args_w' (by decide))
  have sp₃ : s₃.sp = p.SP := by rw [O₃.sp]; simp [sp_setReg, sp_store, R₁.sp, E.sp]
  have rd₃ : s₃.rd = s.rd := by rw [O₃.rd]; simp [rd_setReg, rd_store, R₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [O₃.wr]; simp [wr_setReg, wr_store, R₁.wr]
  have r11₃ : s₃.gpr .r11 = p.W := by
    rw [O₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, gpr_store, r11₁]
  have P₃ : VG.Proof.AesOcb.Arm.Perm p s₃ := E.perm.of_eq rd₃ wr₃
  have a₂₀ := P₃.argR' L (k := 20) (by decide)
  have rb₀ : InRegions (s₃.rd ++ s₃.wr) (State.addr p.W + BitVec.ofNat 64 112) 1 := P₃.wR (by decide)
  have wb₀ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 112) 1 := P₃.wW (by decide)
  have rb₁ : InRegions (s₃.rd ++ s₃.wr) (State.addr p.W + BitVec.ofNat 64 127) 1 := P₃.wR (by decide)
  have wb₁ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 127) 1 := P₃.wW (by decide)
  have wb₂ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 208) 4 := P₃.wW (by decide)
  have ne : (State.addr p.W + BitVec.ofNat 64 127 = State.addr p.W + BitVec.ofNat 64 112) = False := by
    simp only [eq_iff_iff, iff_false]
    intro h
    have := congrArg (· - State.addr p.W) h
    simp only [Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  have ew : ∀ k, k < 2560 → State.addr (p.W + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 k :=
    fun k hk => L.wA hk
  have e112 := ew 112 (by decide)
  have e127' := ew 127 (by decide)
  have e208 := ew 208 (by decide)
  refine WP.of_runBlock ⟨_, by orun [r11₃, sp₃, A₃.a20, a₂₀, e112, e127', e208, rb₀, wb₀, rb₁, wb₁, wb₂,
    WriteBytes.writeW8_apply, ne], ?_⟩
  have htl : p.tl < 2 ^ 32 := by have := L.tl16; omega
  simp only [and15, VG.Proof.AesOcb.Arm.toNat_ofNat32 htl, VG.Proof.AesOcb.Arm.ofNat_shl4, VG.Proof.AesOcb.Arm.or_byte32, VG.Proof.AesOcb.Arm.and_byte32, VG.Proof.AesOcb.Arm.and63_32]
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem (State.addr p.N) p.nl).length = p.nl := length_bytesAt _ _ _
  have eN : bytesAt (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1)))
      (State.addr p.N) p.nl = bytesAt s.mem (State.addr p.N) p.nl :=
    Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.n_w' (by decide)) (by omega)
  rw [eN] at m₃
  have L₁ : bytesAt s₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := by
    rw [R₁.mem]; exact Proof.Cmac.zero4_bytes _ _
  have L₂ : bytesAt (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1)))
      (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ Spec.Ocb.zeros p.nl := by
    rw [e127, bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - p.nl) 16 = 15 - p.nl by omega,
      show 16 - (15 - p.nl + 1) = p.nl by omega]
    rfl
  have L₃ : bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ bytesAt s.mem (State.addr p.N) p.nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega) (by decide), L₂, hlen]
    rw [show 16 - p.nl + p.nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_append, List.length_singleton, List.append_assoc]
    simp only [show min (16 - p.nl) (15 - p.nl) = 15 - p.nl by omega, show 16 - p.nl - (15 - p.nl) = 1 by omega,
      show 16 - (15 - p.nl) = p.nl + 1 by omega, show 15 - p.nl + (1 + p.nl) = 16 by omega]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - p.nl - 16 = 0 by omega, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ p.nl + 1 by simp), show p.nl - (p.nl + 1 - 1) = 0 by omega,
      List.append_nil]
  have L₃d : ∀ k < 16, (bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      nbase (bytesAt s.mem (State.addr p.N) p.nl) k := fun k hk => by
    have := Proof.Ocb.nbase_list (bytesAt s.mem (State.addr p.N) p.nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
    rw [hlen] at this; rw [L₃]; exact this
  have b0 : s₃.mem (State.addr p.W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem (State.addr p.N) p.nl) 0 := by
    have := VG.Proof.AesOcb.Arm.getD_bytesAt_eq s₃.mem (State.addr p.W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  have e127' : State.addr p.W + BitVec.ofNat 64 127 = State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add _ 112 15).symm
  have b15 : s₃.mem (State.addr p.W + BitVec.ofNat 64 127) = nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) 15 := by
    rw [e127', VG.Proof.AesOcb.Arm.getD_bytesAt_eq s₃.mem (State.addr p.W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  have fr208 : ∀ (M : Mem) (v : BitVec 32), Frame [⟨State.addr p.W + BitVec.ofNat 64 208, 4⟩] M
      (M.writeW (State.addr p.W + BitVec.ofNat 64 208) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₄d : ∀ k < 16, (bytesAt (((s₃.mem.writeW (State.addr p.W + BitVec.ofNat 64 112)
        (s₃.mem (State.addr p.W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (p.tl % 16)))).writeW
        (State.addr p.W + BitVec.ofNat 64 208)
        (BitVec.ofNat 32 ((s₃.mem (State.addr p.W + BitVec.ofNat 64 127)).toNat % 64))).writeW
        (State.addr p.W + BitVec.ofNat 64 127) (s₃.mem (State.addr p.W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192))
        (State.addr p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) 15 &&& 0xc0
      else nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) k := by
    intro k hk
    rw [b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr208 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 208) (k := 4) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      VG.Proof.AesOcb.Arm.getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk]
    split
    · rfl
    · rename_i hk15
      rw [bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0]
      unfold nb
      rcases k with _ | k
      · rfl
      · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show 1 + k = k + 1 by omega]
        exact L₃d (k + 1) hk
  have fs₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩]
      s.mem s₃.mem := f₃.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [tmpO])
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_store, tmpO, botO]
    refine ((fs₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · exact VG.Proof.AesOcb.Arm.contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · simp only [mem_store, tmpO]
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _)]
    refine Proof.Cmac.ext16 (length_bytesAt _ _ _) (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · simp only [mem_store, botO]
    rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, b15, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_store, gpr_setReg, hr.1, hr.2.1, ↓reduceIte]
    rw [O₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_store, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ↓reduceIte]
    exact R₁.gpr r (by simp [hr.1])
  · simp only [sp_store, sp_setReg]; rw [O₃.sp]; simp [sp_store, sp_setReg, R₁.sp]
  · simp only [rd_store, rd_setReg]; exact rd₃
  · simp only [wr_store, wr_setReg]; exact wr₃

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Offset0`. -/
section

/-!
# AES-OCB on ARMv7: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
four byte-reversed words, computes the last two words of `Stretch`
(`Proof.Ocb.stretch_words32`), shifts the six words left by `bottom` in six
masked stages (`stage_ok`, `stage32_ok`, `Proof.Ocb.shl_stages`), and stores
the top four, byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`), as
on AArch64 (`Proof.AesOcb.AArch64.offset0_ok`) with 32-bit words.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf sel_mask32 shl6 shl6_32 bit32 bit32_0)
open VG.Proof.AesGcm.Arm (mem_store rd_store wr_store sp_store gpr_store)

/-- `Stretch`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- The six words of `Stretch`, high to low. -/
abbrev words (s : State) : BitVec 192 :=
  s.gpr .r0 ++ s.gpr .r1 ++ s.gpr .r2 ++ s.gpr .r3 ++ s.gpr .r4 ++ s.gpr .r5

/-- The registers a stage writes. -/
abbrev stageRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r7, .r8]

/-- The mask of a stage in `r7`. -/
theorem stageMask_ok (s : State) {k v : Nat} (hk : k ≤ 5) (hv : v < 64) (h6 : s.gpr .r6 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stageMask k) s = some s' ∧
      s'.gpr .r7 = (0 : BitVec 32) - (if v.testBit k then 1 else 0) ∧ VG.Proof.AesOcb.Arm.Ran [.r7, .r8] s.mem s s' := by
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨_, by orun [stageMask], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    simp only [gpr_setReg, ite_true, h6, bit32_0 hv]
    rfl
  · have h1 : 1 ≤ k := by omega
    have h31 : k ≤ 31 := by omega
    refine ⟨_, by orun [stageMask, hk0, h1, h31], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h6, bit32 hv]
    rfl

/-- The words of a stage. -/
def stageWords (a : Nat) : List Instr :=
  ([(Reg.r0, Reg.r1), (.r1, .r2), (.r2, .r3), (.r3, .r4), (.r4, .r5)].flatMap fun (x, y) =>
    [.mov .r8 (.shifted x .lsl a), .dp .orr .r8 .r8 (.shifted y .lsr (32 - a))] ++ sel x) ++
  [.mov .r8 (.shifted .r5 .lsl a)] ++ sel .r5

theorem stage_eq (k a : Nat) : stage k a = stageMask k ++ VG.Proof.AesOcb.Arm.stageWords a := by
  simp only [stage, VG.Proof.AesOcb.Arm.stageWords, List.append_assoc]

/-- The words of a stage, with the mask in `r7`. -/
theorem stageWords_ok (s : State) {a : Nat} (ha : 0 < a) (ha' : a < 32) (b : Bool)
    (h7 : s.gpr .r7 = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ s', runBlock isa (VG.Proof.AesOcb.Arm.stageWords a) s = some s' ∧ VG.Proof.AesOcb.Arm.words s' = shlIf b a (VG.Proof.AesOcb.Arm.words s) ∧
      VG.Proof.AesOcb.Arm.Ran [.r0, .r1, .r2, .r3, .r4, .r5, .r8] s.mem s s' := by
  have h1 : 1 ≤ a := ha
  have h31 : a ≤ 31 := by omega
  have h1' : 1 ≤ 32 - a := by omega
  have h31' : 32 - a ≤ 31 := by omega
  refine ⟨_, by orun [VG.Proof.AesOcb.Arm.stageWords, sel, h1, h31, h1', h31', List.flatMap_cons, List.flatMap_nil], ?_, by rfl,
    by others_tac, by rfl, by rfl, by rfl⟩
  simp only [VG.Proof.AesOcb.Arm.words, gpr_setReg, ite_true, ite_false, reduceCtorEq, h7]
  simp only [sel_mask32]
  cases b
  · rfl
  · exact shl6 _ _ _ _ _ _ ha ha'

/-- The words of the last stage. -/
def stageWords32 : List Instr :=
  ([(Reg.r0, Reg.r1), (.r1, .r2), (.r2, .r3), (.r3, .r4), (.r4, .r5)].flatMap fun (x, y) =>
    [.mov .r8 (.reg y)] ++ sel x) ++
  [.mov .r8 (Impl.AesGcm.Arm.imm 0)] ++ sel .r5

theorem stage32_eq : stage32 = stageMask 5 ++ VG.Proof.AesOcb.Arm.stageWords32 := by
  simp only [stage32, VG.Proof.AesOcb.Arm.stageWords32, List.append_assoc]

theorem stageWords32_ok (s : State) (b : Bool) (h7 : s.gpr .r7 = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ s', runBlock isa VG.Proof.AesOcb.Arm.stageWords32 s = some s' ∧ VG.Proof.AesOcb.Arm.words s' = shlIf b 32 (VG.Proof.AesOcb.Arm.words s) ∧
      VG.Proof.AesOcb.Arm.Ran [.r0, .r1, .r2, .r3, .r4, .r5, .r8] s.mem s s' := by
  refine ⟨_, by orun [VG.Proof.AesOcb.Arm.stageWords32, sel, List.flatMap_cons, List.flatMap_nil], ?_, by rfl,
    by others_tac, by rfl, by rfl, by rfl⟩
  simp only [VG.Proof.AesOcb.Arm.words, gpr_setReg, ite_true, ite_false, reduceCtorEq, h7, sel_mask32]
  cases b
  · rfl
  · exact shl6_32 _ _ _ _ _ _

/-- A stage, from `bottom` in `r6`. -/
theorem stage_ok (s : State) {k a v : Nat} (hk : k ≤ 5) (ha : 0 < a) (ha' : a < 32) (hv : v < 64)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧ VG.Proof.AesOcb.Arm.words s' = shlIf (v.testBit k) a (VG.Proof.AesOcb.Arm.words s) ∧
      VG.Proof.AesOcb.Arm.Ran VG.Proof.AesOcb.Arm.stageRegs s.mem s s' := by
  obtain ⟨s₁, run₁, h7, R₁⟩ := VG.Proof.AesOcb.Arm.stageMask_ok s hk hv h6
  obtain ⟨s₂, run₂, w₂, R₂⟩ := VG.Proof.AesOcb.Arm.stageWords_ok s₁ ha ha' _ h7
  refine ⟨s₂, by rw [VG.Proof.AesOcb.Arm.stage_eq, VG.Proof.AesOcb.Arm.runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_⟩
  · have e : VG.Proof.AesOcb.Arm.words s₁ = VG.Proof.AesOcb.Arm.words s := by
      simp only [VG.Proof.AesOcb.Arm.words, R₁.gpr .r0 (by decide), R₁.gpr .r1 (by decide), R₁.gpr .r2 (by decide),
        R₁.gpr .r3 (by decide), R₁.gpr .r4 (by decide), R₁.gpr .r5 (by decide)]
    rw [w₂, e]
  · refine ⟨by rw [R₂.mem, R₁.mem], fun r hr => ?_, by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd], by rw [R₂.wr, R₁.wr]⟩
    simp only [VG.Proof.AesOcb.Arm.stageRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₂.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      R₁.gpr r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]

theorem stage32_ok (s : State) {v : Nat} (hv : v < 64) (h6 : s.gpr .r6 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa stage32 s = some s' ∧ VG.Proof.AesOcb.Arm.words s' = shlIf (v.testBit 5) 32 (VG.Proof.AesOcb.Arm.words s) ∧
      VG.Proof.AesOcb.Arm.Ran VG.Proof.AesOcb.Arm.stageRegs s.mem s s' := by
  obtain ⟨s₁, run₁, h7, R₁⟩ := VG.Proof.AesOcb.Arm.stageMask_ok s (k := 5) (by decide) hv h6
  obtain ⟨s₂, run₂, w₂, R₂⟩ := VG.Proof.AesOcb.Arm.stageWords32_ok s₁ _ h7
  refine ⟨s₂, by rw [VG.Proof.AesOcb.Arm.stage32_eq, VG.Proof.AesOcb.Arm.runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_⟩
  · have e : VG.Proof.AesOcb.Arm.words s₁ = VG.Proof.AesOcb.Arm.words s := by
      simp only [VG.Proof.AesOcb.Arm.words, R₁.gpr .r0 (by decide), R₁.gpr .r1 (by decide), R₁.gpr .r2 (by decide),
        R₁.gpr .r3 (by decide), R₁.gpr .r4 (by decide), R₁.gpr .r5 (by decide)]
    rw [w₂, e]
  · refine ⟨by rw [R₂.mem, R₁.mem], fun r hr => ?_, by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd], by rw [R₂.wr, R₁.wr]⟩
    simp only [VG.Proof.AesOcb.Arm.stageRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₂.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      R₁.gpr r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : VG.Proof.AesOcb.Arm.Others [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The head of `offset0`: `Stretch` in `r0`–`r5` and `bottom` in `r6`. -/
def off0Head : List Instr :=
  [.ldr .r0 .r11 tmpO, .ldr .r1 .r11 (tmpO + 4), .ldr .r2 .r11 (tmpO + 8), .ldr .r3 .r11 (tmpO + 12),
   .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .mov .r4 (.shifted .r0 .lsl 8), .dp .orr .r4 .r4 (.shifted .r1 .lsr 24), .dp .eor .r4 .r4 (.reg .r0),
   .mov .r5 (.shifted .r1 .lsl 8), .dp .orr .r5 .r5 (.shifted .r2 .lsr 24), .dp .eor .r5 .r5 (.reg .r1),
   .ldr .r6 .r11 botO]

/-- The tail of `offset0`: the top four words, byte-reversed, to `W + ofsO`
and `W + o0O`. -/
def off0Tail : List Instr :=
  [.rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .str .r0 .r11 ofsO, .str .r1 .r11 (ofsO + 4), .str .r2 .r11 (ofsO + 8), .str .r3 .r11 (ofsO + 12),
   .str .r0 .r11 o0O, .str .r1 .r11 (o0O + 4), .str .r2 .r11 (o0O + 8), .str .r3 .r11 (o0O + 12)]

theorem offset0_eq : offset0 = VG.Proof.AesOcb.Arm.off0Head ++ stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++
    stage32 ++ VG.Proof.AesOcb.Arm.off0Tail := by
  simp only [offset0, VG.Proof.AesOcb.Arm.off0Head, VG.Proof.AesOcb.Arm.off0Tail, List.append_assoc, List.cons_append, List.nil_append]

theorem offset0_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) {v : Nat} (hv : v < 64)
    (hbot : s.mem.readW (State.addr p.W + BitVec.ofNat 64 botO) 32 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      VG.Proof.AesOcb.Arm.Off0Post (State.addr p.W)
        ((VG.Proof.AesOcb.Arm.stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  have ew : ∀ k, k < 2560 → State.addr (p.W + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 k :=
    fun k hk => L.wA hk
  have e112 := ew 112 (by decide)
  have e116 := ew 116 (by decide)
  have e120 := ew 120 (by decide)
  have e124 := ew 124 (by decide)
  have e208 := ew 208 (by decide)
  have r112 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 112) 4 := E.perm.wR (by decide)
  have r116 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 116) 4 := E.perm.wR (by decide)
  have r120 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 120) 4 := E.perm.wR (by decide)
  have r124 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 124) 4 := E.perm.wR (by decide)
  have r208 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 208) 4 := E.perm.wR (by decide)
  simp only [botO] at hbot
  obtain ⟨s₁, run₁, w₁, r6₁, R₁⟩ : ∃ s₁, runBlock isa VG.Proof.AesOcb.Arm.off0Head s = some s₁ ∧
      VG.Proof.AesOcb.Arm.words s₁ = VG.Proof.AesOcb.Arm.stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .r6 = BitVec.ofNat 32 v ∧ VG.Proof.AesOcb.Arm.Ran [.r0, .r1, .r2, .r3, .r4, .r5, .r6] s.mem s s₁ := by
    refine ⟨_, by orun [VG.Proof.AesOcb.Arm.off0Head, E.r11, e112, e116, e120, e124, e208, r112, r116, r120, r124, r208], ?_, ?_,
      by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [VG.Proof.AesOcb.Arm.words, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesOcb.Arm.rev_eq]
      have hb : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
          byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 112) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 116) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 120) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 124) 32) := by
        have := Proof.Cmac.ofBytes_rev4 s.mem (State.addr p.W + BitVec.ofNat 64 112)
        simp only [Offset.add_add] at this
        exact this
      rw [VG.Proof.AesOcb.Arm.stretch, hb, Proof.Ocb.stretch_words32]
    · simp only [gpr_setReg, ite_true, hbot]
  have keep : ∀ {t t' : State}, VG.Proof.AesOcb.Arm.Ran VG.Proof.AesOcb.Arm.stageRegs t.mem t t' → t.gpr .r6 = BitVec.ofNat 32 v →
      t'.gpr .r6 = BitVec.ofNat 32 v := fun R h => by rw [R.gpr _ (by decide), h]
  obtain ⟨s₂, run₂, w₂, R₂⟩ := VG.Proof.AesOcb.Arm.stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv r6₁
  obtain ⟨s₃, run₃, w₃, R₃⟩ := VG.Proof.AesOcb.Arm.stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv (keep R₂ r6₁)
  obtain ⟨s₄, run₄, w₄, R₄⟩ := VG.Proof.AesOcb.Arm.stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (keep R₃ (keep R₂ r6₁))
  obtain ⟨s₅, run₅, w₅, R₅⟩ := VG.Proof.AesOcb.Arm.stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv
    (keep R₄ (keep R₃ (keep R₂ r6₁)))
  obtain ⟨s₆, run₆, w₆, R₆⟩ := VG.Proof.AesOcb.Arm.stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep R₅ (keep R₄ (keep R₃ (keep R₂ r6₁))))
  obtain ⟨s₇, run₇, w₇, R₇⟩ := VG.Proof.AesOcb.Arm.stage32_ok s₆ hv (keep R₆ (keep R₅ (keep R₄ (keep R₃ (keep R₂ r6₁)))))
  have hw7 : VG.Proof.AesOcb.Arm.words s₇ = VG.Proof.AesOcb.Arm.stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  have hO : s₇.gpr .r0 ++ s₇.gpr .r1 ++ s₇.gpr .r2 ++ s₇.gpr .r3 =
      (VG.Proof.AesOcb.Arm.stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← Proof.Ocb.top4 _ _ _ _ (s₇.gpr .r4) (s₇.gpr .r5), show s₇.gpr .r0 ++ s₇.gpr .r1 ++ s₇.gpr .r2 ++
      s₇.gpr .r3 ++ s₇.gpr .r4 ++ s₇.gpr .r5 = VG.Proof.AesOcb.Arm.words s₇ from rfl, hw7, Proof.Ocb.offset_shl _ (by omega)]
  have hm₇ : s₇.mem = s.mem := by rw [R₇.mem, R₆.mem, R₅.mem, R₄.mem, R₃.mem, R₂.mem, R₁.mem]
  have hsp₇ : s₇.sp = s.sp := by rw [R₇.sp, R₆.sp, R₅.sp, R₄.sp, R₃.sp, R₂.sp, R₁.sp]
  have hrd₇ : s₇.rd = s.rd := by rw [R₇.rd, R₆.rd, R₅.rd, R₄.rd, R₃.rd, R₂.rd, R₁.rd]
  have hwr₇ : s₇.wr = s.wr := by rw [R₇.wr, R₆.wr, R₅.wr, R₄.wr, R₃.wr, R₂.wr, R₁.wr]
  have g₁₇ : VG.Proof.AesOcb.Arm.Others [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] s s₇ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h' : r ∉ VG.Proof.AesOcb.Arm.stageRegs := by
      simp [VG.Proof.AesOcb.Arm.stageRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2]
    rw [R₇.gpr r h', R₆.gpr r h', R₅.gpr r h', R₄.gpr r h', R₃.gpr r h', R₂.gpr r h',
      R₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1])]
  have r11₇ : s₇.gpr .r11 = p.W := by rw [g₁₇ _ (by decide), E.r11]
  have P₇ : VG.Proof.AesOcb.Arm.Perm p s₇ := E.perm.of_eq hrd₇ hwr₇
  have ww : ∀ d, d + 4 ≤ 2560 → InRegions s₇.wr (State.addr p.W + BitVec.ofNat 64 d) 4 := fun d h => P₇.wW h
  have e16 := ew 16 (by decide)
  have e20 := ew 20 (by decide)
  have e24 := ew 24 (by decide)
  have e28 := ew 28 (by decide)
  have e224 := ew 224 (by decide)
  have e228 := ew 228 (by decide)
  have e232 := ew 232 (by decide)
  have e236 := ew 236 (by decide)
  have w16 := ww 16 (by decide)
  have w20 := ww 20 (by decide)
  have w24 := ww 24 (by decide)
  have w28 := ww 28 (by decide)
  have w224 := ww 224 (by decide)
  have w228 := ww 228 (by decide)
  have w232 := ww 232 (by decide)
  have w236 := ww 236 (by decide)
  obtain ⟨s₈, run₈, m₈, R₈⟩ : ∃ s₈, runBlock isa VG.Proof.AesOcb.Arm.off0Tail s₇ = some s₈ ∧
      s₈.mem = Proof.Cmac.store4 (Proof.Cmac.store4 s₇.mem (State.addr p.W + BitVec.ofNat 64 16)
          (byteRev32 (s₇.gpr .r0)) (byteRev32 (s₇.gpr .r1)) (byteRev32 (s₇.gpr .r2)) (byteRev32 (s₇.gpr .r3)))
        (State.addr p.W + BitVec.ofNat 64 224)
          (byteRev32 (s₇.gpr .r0)) (byteRev32 (s₇.gpr .r1)) (byteRev32 (s₇.gpr .r2)) (byteRev32 (s₇.gpr .r3)) ∧
      VG.Proof.AesOcb.Arm.Ran [.r0, .r1, .r2, .r3] s₈.mem s₇ s₈ := by
    refine ⟨_, by orun [VG.Proof.AesOcb.Arm.off0Tail, r11₇, e16, e20, e24, e28, e224, e228, e232, e236, w16, w20, w24, w28, w224, w228,
      w232, w236], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesOcb.Arm.rev_eq, Proof.Cmac.store4,
      Offset.add_add]
  have val : ∀ (M : Mem) (C : Addr), blockAtMem (Proof.Cmac.store4 M C
      (byteRev32 (s₇.gpr .r0)) (byteRev32 (s₇.gpr .r1)) (byteRev32 (s₇.gpr .r2)) (byteRev32 (s₇.gpr .r3))) C =
      (VG.Proof.AesOcb.Arm.stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := fun M C => by
    rw [blockAtMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, ← hO]
    exact Proof.Cmac.ofBytes_toBytes _
  refine ⟨s₈, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [R₈.sp, hsp₇], by rw [R₈.rd, hrd₇], by rw [R₈.wr, hwr₇]⟩
  · rw [VG.Proof.AesOcb.Arm.offset0_eq, VG.Proof.AesOcb.Arm.runBlock_append, VG.Proof.AesOcb.Arm.runBlock_append, VG.Proof.AesOcb.Arm.runBlock_append, VG.Proof.AesOcb.Arm.runBlock_append, VG.Proof.AesOcb.Arm.runBlock_append,
      VG.Proof.AesOcb.Arm.runBlock_append, VG.Proof.AesOcb.Arm.runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  · rw [m₈, ← hm₇]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp [ofsO])).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp [o0O]))
  · rw [m₈, Proof.Ocb.blockAtMem_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 224) (k := 16) (.inl (by decide)) (by decide) (by decide))]
    exact val _ _
  · rw [m₈]; exact val _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₈.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), g₁₇ r (by simp [hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Calls`. -/
section

/-!
# AES-OCB on ARMv7: the calls

Untrusted: everything here is checked by Lean. A call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on `n` blocks at `D`, with
the key context's schedule and the working space at `W + scrO`
(`blkFrame_ok`): each block is replaced with the cipher (`BlkFn.ciph`) of
it, for the key schedule in the key context, and the registers `r4`–`r11`
are kept (`CallPost`). `encOne d` enciphers the block at `W + d`
(`encOne_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- The registers the calls keep. -/
abbrev keptRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- `F` as a blockcipher on OCB's blocks. -/
def BlkFn.ciph (F : VG.Proof.AesOcb.Arm.BlkFn) (R : Nat) (w : List Byte) : Spec.Ocb.Cipher := fun x =>
  Spec.Ocb.ofBytes (F.f R w (Vector.ofFn fun i => (Spec.Ocb.toBytes x).getD i.1 0)).toList

theorem encF_ciph (R : Nat) (w : List Byte) : encF.ciph R w = Spec.Ocb.aesWith R w := rfl
theorem decF_ciph (R : Nat) (w : List Byte) : decF.ciph R w = Spec.Ocb.aesInvWith R w := rfl

/-- The key schedule in the memory `m`, for `R` rounds. -/
abbrev sched (p : VG.Proof.AesOcb.Arm.Prm) (m : Mem) : List Byte := bytesAt m (State.addr p.K) (16 * (p.R + 1))

/-- What a call leaves, from `t`. -/
structure CallPost (F : VG.Proof.AesOcb.Arm.BlkFn) (p : VG.Proof.AesOcb.Arm.Prm) (D : Addr) (n : Nat) (t t' : State) : Prop where
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  saved : ∀ r ∈ VG.Proof.AesOcb.Arm.keptRegs, t'.gpr r = t.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] t.mem t'.mem
  out : ∀ i < n, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * i)) =
    F.ciph p.R (VG.Proof.AesOcb.Arm.sched p t.mem) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)))

theorem CallPost.env {F : VG.Proof.AesOcb.Arm.BlkFn} {p : VG.Proof.AesOcb.Arm.Prm} {D : Addr} {n : Nat} {t t' : State} (h : VG.Proof.AesOcb.Arm.CallPost F p D n t t')
    (E : VG.Proof.AesOcb.Arm.Env p t) : VG.Proof.AesOcb.Arm.Env p t' :=
  E.keep (fun r hr => h.saved r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    h.sp h.rd h.wr

/-- The arguments of a call, set up. -/
theorem blkCall_of {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {D : BitVec 32} {n : Nat}
    (h0 : t.gpr .r0 = p.K) (h1 : t.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : t.gpr .r2 = D)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 n) (h12 : t.gpr .r12 = p.W + BitVec.ofNat 32 scrO)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (wD : Covers [⟨State.addr D, 16 * n⟩] t.wr)
    (dk : (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩)
    (db : (below p.SP).Disjoint ⟨State.addr D, 16 * n⟩) :
    VG.Proof.AesOcb.Arm.BlkCall t p.K D (p.W + BitVec.ofNat 32 scrO) p.R n := by
  have fw := L.ww
  have eS : State.addr (p.W + BitVec.ofNat 32 scrO) = State.addr p.W + BitVec.ofNat 64 scrO := L.wA (by decide)
  exact {
    r0 := h0, r1 := h1, r2 := h2, r3 := h3, r12 := h12, rounds := L.rounds
    hsp := by rw [E.sp]; exact L.sp8
    fitK := by have := L.kw; omega
    fitD := fD
    fitS := by rw [L.wN (by decide)]; simp only [scrO]; omega
    kd := dk.sub_left (Region.sub_prefix (by decide))
    ks := by rw [eS]; exact (L.k_w' (by decide)).sub_left (Region.sub_prefix (by decide))
    ds := by rw [eS]; exact ds
    bk := by rw [E.sp]; exact L.bk.sub_right (Region.sub_prefix (by decide))
    bd := by rw [E.sp]; exact db
    bs := by rw [E.sp, eS]; exact L.bw' (by decide)
    reads := Proof.AesGcm.Arm.covers_prefix E.perm.k (by decide)
    writes := by
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact wD a k ⟨_, List.mem_singleton_self _, hc⟩
      · rw [eS] at hc; exact E.perm.wC (d := scrO) (n := 2048) (by decide) a k ⟨_, List.mem_singleton_self _, hc⟩ }

/-- A call of `F`, set up. -/
theorem blkFrame_ok (F : VG.Proof.AesOcb.Arm.BlkFn) {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {D : BitVec 32} {n : Nat}
    (h0 : t.gpr .r0 = p.K) (h1 : t.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : t.gpr .r2 = D)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 n) (h12 : t.gpr .r12 = p.W + BitVec.ofNat 32 scrO)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (wD : Covers [⟨State.addr D, 16 * n⟩] t.wr)
    (dk : (⟨State.addr p.K, 256⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩)
    (db : (below p.SP).Disjoint ⟨State.addr D, 16 * n⟩) :
    WP isa (VG.Proof.AesOcb.Arm.blkFrame F) t (VG.Proof.AesOcb.Arm.CallPost F p (State.addr D) n t) := by
  have eS : State.addr (p.W + BitVec.ofNat 32 scrO) = State.addr p.W + BitVec.ofNat 64 scrO := L.wA (by decide)
  have hB := VG.Proof.AesOcb.Arm.blkCall_of L E h0 h1 h2 h3 h12 fD wD dk ds db
  refine WP.mono (VG.Proof.AesOcb.Arm.blk_call F hB) fun t' P => ⟨P.rd, P.wr, P.sp, fun r hr => P.saved r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h | h | h <;> simp [h]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with h | h | h | h | h | h | h | h <;>
        subst h <;> decide), ?_, fun i hi => ?_⟩
  · have f := P.frame; rw [eS, E.sp] at f; exact f
  · rw [Proof.Ocb.blockAtMem_of_state _ (Proof.Ocb.stateAt_of_statesAt P.out hi)]
    rfl

/-- `ENCIPHER` of the block at `W + d`, in place. -/
theorem encOne_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {d : Nat} (hd : d + 16 ≤ 512)
    (he : encodable (BitVec.ofNat 32 d) = true) :
    WP isa (encOne d) t (VG.Proof.AesOcb.Arm.CallPost VG.Proof.AesOcb.Arm.encF p (State.addr p.W + BitVec.ofNat 64 d) 1 t) := by
  have fw := L.ww
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [encOne, callArgs, E.r9, E.r10, E.r11, he], ?_⟩)
  have := VG.Proof.AesOcb.Arm.blkFrame_ok VG.Proof.AesOcb.Arm.encF L (t := ((((((t.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 (p.W + BitVec.ofNat 32 d)).setReg .r3 (BitVec.ofNat 32 1))))
    (D := p.W + BitVec.ofNat 32 d) (n := 1) (E.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac)
      (by rfl) (by rfl) (by rfl)) (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by omega)]; omega)
      (by rw [ed]; exact E.perm.wC (by omega)) (by rw [ed]; exact L.k_w' (by omega))
      (by rw [ed]; exact L.w_w (.inl (by simp only [scrO]; omega)) (by omega) (by decide))
      (by rw [ed]; exact L.bw' (by omega))
  rw [ed] at this
  refine WP.mono (VG.Proof.AesOcb.Arm.encFrame_eq ▸ this) fun t' P => ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [P.rd]; rfl
  · rw [P.wr]; rfl
  · rw [P.sp]; rfl
  · rw [P.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · exact P.frame
  · intro i hi; rw [P.out i hi]; rfl

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Nonce`. -/
section

/-!
# AES-OCB on ARMv7: `Offset_0` (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers it in
place (`encOne_ok`) into `Ktop`, and takes `Offset_0` from `Stretch`
(`offset0_ok`): §4.2's `Offset_0` (`Proof.Ocb.offset0_eq`), at `W + ofsO` and
`W + o0O` (`nonce_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- What `nonce` writes. -/
abbrev nonceR (p : VG.Proof.AesOcb.Arm.Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 o0O, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP]

/-- What `nonce` leaves, from `t`. -/
structure NonceOut (p : VG.Proof.AesOcb.Arm.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (VG.Proof.AesOcb.Arm.nonceR p) t.mem t'.mem
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (VG.Proof.AesOcb.Arm.sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl)
  o0 : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (VG.Proof.AesOcb.Arm.sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl)

theorem nonce_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) (A : VG.Proof.AesOcb.Arm.Args p t.mem)
    (h4 : t.gpr .r4 = p.N) (h5 : t.gpr .r5 = BitVec.ofNat 32 p.nl) :
    WP isa nonce t (VG.Proof.AesOcb.Arm.NonceOut p t) := by
  unfold nonce
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.nonceBlock_ok L E A h4 h5) fun t₁ N₁ => ?_)
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others N₁.gpr N₁.sp N₁.rd N₁.wr
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.encOne_ok L E₁ (d := tmpO) (by decide) (by decide)) fun t₂ C₂ => ?_)
  have E₂ := C₂.env E₁
  -- `bottom`, kept through the call
  have hv : ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat < 64 :=
    BitVec.isLt _
  have hbot : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 botO) 32 =
      BitVec.ofNat 32 ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat := by
    rw [C₂.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide), N₁.bot]
  obtain ⟨t₃, run₃, O₃⟩ := VG.Proof.AesOcb.Arm.offset0_ok L E₂ hv hbot
  refine WP.of_runBlock ⟨t₃, run₃, ?_⟩
  have hK : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      Spec.Ocb.aesWith p.R (VG.Proof.AesOcb.Arm.sched p t.mem) (Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl) &&&
        ~~~(63 : Block)) := by
    have := C₂.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, VG.Proof.AesOcb.Arm.encF_ciph, N₁.blk]
    refine congrArg (fun w => Spec.Ocb.aesWith p.R w _) ?_
    exact Proof.Cmac.bytesAt_frame N₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (L.k_w' (d := tmpO) (k := 16) (by decide)).sub_left
          (Region.sub_prefix (show 16 * (p.R + 1) ≤ 256 by have := L.rounds_le; omega))
      · exact (L.k_w' (d := botO) (k := 4) (by decide)).sub_left
          (Region.sub_prefix (show 16 * (p.R + 1) ≤ 256 by have := L.rounds_le; omega))) (by have := L.rounds_le; omega)
  have hO : (VG.Proof.AesOcb.Arm.stretch (blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb'
      (64 - ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat) 128 =
      Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (VG.Proof.AesOcb.Arm.sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl) := by
    rw [hK, Proof.Ocb.offset0_eq]; rfl
  refine ⟨E₂.of_others O₃.gpr O₃.sp O₃.rd O₃.wr, by rw [O₃.rd, C₂.rd, N₁.rd], by rw [O₃.wr, C₂.wr, N₁.wr], ?_,
    by rw [O₃.ofs, hO], by rw [O₃.o0, hO]⟩
  exact ((N₁.frame.mono (by simp)).trans (C₂.frame.mono (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [tmpO]))).trans (O₃.frame.mono (by simp))

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.HashFill`. -/
section

/-!
# AES-OCB on ARMv7: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xorB_wp`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`), as on AArch64
(`Proof.AesOcb.AArch64.hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (z_subFlags dec32 z_dec)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r8, .r12, .lr]

theorem w_A {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {k : Nat} (h : 16 + k ≤ p.al) :
    State.addr (p.A + BitVec.ofNat 32 k) = State.addr p.A + BitVec.ofNat 64 k :=
  addr_add (by have := L.aw; omega)

/-- What one `hashFill` leaves. -/
structure FillPost (p : VG.Proof.AesOcb.Arm.Prm) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i)) =
    blockAtMem t.mem (State.addr p.A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  r4 : t'.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i + 1))
  r6 : t'.gpr .r6 = BitVec.ofNat 32 (j + i + 2)
  r8 : t'.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1))
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (c - (i + 1))
  z : t'.z = decide (i + 1 = c)
  gpr : VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.fillRegs t t'
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {l : Block} {j i c : Nat} (hi : i < c)
    (hc : c ≤ 16) (hj : 16 * (j + i + 1) ≤ p.al)
    (h6 : t.gpr .r6 = BitVec.ofNat 32 (j + i + 1)) (h4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)))
    (h8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i)) (h5 : t.gpr .r5 = BitVec.ofNat 32 (c - i))
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)) :
    WP isa hashFill t (VG.Proof.AesOcb.Arm.FillPost p l j i c t) := by
  have fw := L.ww
  have fa := L.aw
  have al32 := L.al_lt
  have hb : bufO + 16 * i + 16 ≤ 512 := by simp only [bufO]; omega
  unfold hashFill
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.lNtz_ok (i := j + i + 1) L E (by omega) (by omega) h6 hl0) fun t₁ P₁ => ?_)
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others P₁.gpr P₁.sp P₁.rd P₁.wr
  have g₁ : VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.ntzRegs t t₁ := P₁.gpr
  -- the offset
  refine WP.block_append (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t₁) (pb := .r11) (qb := .r11) (cb := .r11)
    (pd := ohO) (qd := lO) (cd := ohO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [E₁.r11]; simp only [ohO]; omega)
    (by rw [E₁.r11]; simp only [lO]; omega) (by rw [E₁.r11]; simp only [ohO]; omega)
    (by rw [E₁.r11]; exact E₁.perm.wCR (by decide)) (by rw [E₁.r11]; exact E₁.perm.wCR (by decide))
    (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_))
  rw [E₁.r11] at R₂
  have E₂ : VG.Proof.AesOcb.Arm.Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have oh₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [R₂.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by decide)) (by decide) (by decide))), P₁.val,
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  have g₂ : ∀ r, r ∉ VG.Proof.AesOcb.Arm.ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    have h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [R₂.gpr r h', g₁ r hr]
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]; exact (P₁.frame.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  -- the block of the associated data
  have eA : State.addr (p.A + BitVec.ofNat 32 (16 * (j + i))) = State.addr p.A + BitVec.ofNat 64 (16 * (j + i)) :=
    VG.Proof.AesOcb.Arm.w_A L (by omega)
  have eB : State.addr (p.W + BitVec.ofNat 32 (bufO + 16 * i)) = State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i) :=
    L.wA (by omega)
  have r4₂ : t₂.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [g₂ _ (by decide), h4]
  have r8₂ : t₂.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [g₂ _ (by decide), h8]
  have hj' : 16 * (j + i) + 16 ≤ p.al := by omega
  have dA : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Sub ⟨State.addr p.A, p.al⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t₂) (pb := .r4) (qb := .r11) (cb := .r8) (pd := 0) (qd := ohO) (cd := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [r4₂, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (j + i)) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (by rw [E₂.r11]; simp only [ohO]; omega) (by rw [r8₂, L.wN (by omega)]; omega)
    (by rw [r4₂, eA, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_off E₂.perm.aad hj' (by omega))
    (by rw [E₂.r11]; exact E₂.perm.wCR (by decide))
    (by rw [r8₂, eB, BitVec.add_zero]; exact E₂.perm.wC (by omega))) fun t₃ R₃ => ?_
  rw [r4₂, r8₂, E₂.r11, eA, eB, BitVec.add_zero, BitVec.add_zero] at R₃
  have fB : Frame [⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t₂.mem t₃.mem := by
    rw [R₃.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have dAW : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩ := (L.a_w' (by omega)).sub_left dA
  have g₃ : ∀ r, r ∉ VG.Proof.AesOcb.Arm.fillRegs → t₃.gpr r = t.gpr r := fun r hr => by
    simp only [VG.Proof.AesOcb.Arm.fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.1, hr.2.1]), g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2])]
  have r4₃ : t₃.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [R₃.gpr _ (by decide), r4₂]
  have r8₃ : t₃.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [R₃.gpr _ (by decide), r8₂]
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (j + i + 1) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h6]
  have r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 (c - i) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h5]
  refine WP.of_runBlock ⟨_, by orun [r4₃, r8₃, r6₃, r5₃], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact (fr₂.mono (by simp)).trans (fB.mono (by simp))
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [blockAtMem_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by simp only [ohO, bufO]; omega)) (by decide) (by omega)), oh₂]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [R₃.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.of_disjoint dAW.symm)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by simp only [ohO, bufO]; omega)) (by omega) (by decide))),
      blockAtMem_frame fr₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (L.a_w' (by decide)).sub_left dA), oh₂]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ← BitVec.ofNat_add]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 256 + 16 * i + 16 = bufO + 16 * (i + 1) by simp only [bufO]; omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hi (by omega)]
  · simp only [z_setReg, z_subFlags, dec32 hi (by omega), z_dec hi (by omega)]
  · simp only [VG.Proof.AesOcb.Arm.fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, ite_false,
      Proof.AesGcm.Arm.gpr_subFlags]
    exact g₃ r (by simp [VG.Proof.AesOcb.Arm.fillRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2])
  · simp only [sp_setReg, Proof.AesGcm.Arm.sp_subFlags]; rw [R₃.sp, R₂.sp, P₁.sp]
  · simp only [rd_setReg, Proof.AesGcm.Arm.rd_subFlags]; rw [R₃.rd, R₂.rd, P₁.rd]
  · simp only [wr_setReg, Proof.AesGcm.Arm.wr_subFlags]; rw [R₃.wr, R₂.wr, P₁.wr]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Mut`. -/
section

/-!
# AES-OCB on ARMv7: what the pieces write

Untrusted: everything here is checked by Lean. The pieces after the entry
write only `W` but for our caller's saved registers, the stack below `SP`
and the data (`mutR`), which miss the key context, the nonce, the
associated data, the tag (`open`'s received one), the stack arguments and the
saved registers: those are the same in every state after the entry
(`sched_mut`, `lstar_mut`, `bytes_mut`, `Args.mut`, `saved_mut`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- What the pieces after the entry write. -/
abbrev mutR (p : VG.Proof.AesOcb.Arm.Prm) : List Region :=
  [⟨State.addr p.W, 128⟩, ⟨State.addr p.W + BitVec.ofNat 64 164, 2396⟩, below p.SP, ⟨State.addr p.D, p.n⟩]

/-- Our caller's saved registers in `W`. -/
abbrev savedR (p : VG.Proof.AesOcb.Arm.Prm) : Region := ⟨State.addr p.W + BitVec.ofNat 64 128, 36⟩

section
variable {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p)
include L

omit L in
/-- A part of `W` but the saved registers is in `mutR`. -/
theorem w_mut (_L : VG.Proof.AesOcb.Arm.Lay p) {a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ VG.Proof.AesOcb.Arm.mutR p, Region.Sub ⟨State.addr p.W + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega)⟩

omit L in
theorem below_mut (_L : VG.Proof.AesOcb.Arm.Lay p) : ∃ r' ∈ VG.Proof.AesOcb.Arm.mutR p, Region.Sub (below p.SP) r' := ⟨_, by simp, fun _ h => h⟩

omit L in
theorem data_mut (_L : VG.Proof.AesOcb.Arm.Lay p) {a l : Nat} (h : a + l ≤ p.n) :
    ∃ r' ∈ VG.Proof.AesOcb.Arm.mutR p, Region.Sub ⟨State.addr p.D + BitVec.ofNat 64 a, l⟩ r' :=
  ⟨_, by simp, Offset.sub_base _ h⟩

omit L in
/-- A region apart from `W`, the stack below `SP` and the data misses `mutR`. -/
theorem disj_mut (_L : VG.Proof.AesOcb.Arm.Lay p) {r : Region} (hw : r.Disjoint ⟨State.addr p.W, 2560⟩) (hb : (below p.SP).Disjoint r)
    (hd : r.Disjoint ⟨State.addr p.D, p.n⟩) : ∀ r' ∈ VG.Proof.AesOcb.Arm.mutR p, r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Region.sub_prefix (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hb.symm
  · exact hd

theorem saved_mut : ∀ r ∈ VG.Proof.AesOcb.Arm.mutR p, (VG.Proof.AesOcb.Arm.savedR p).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 36) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm
  · exact (L.d_w' (by decide)).symm

theorem args_mut : ∀ r ∈ VG.Proof.AesOcb.Arm.mutR p, (VG.Proof.AesOcb.Arm.argR p.SP).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_args.symm.sub_right (Region.sub_prefix (by decide))
  · exact L.args_w' (by decide)
  · exact L.args_below
  · exact L.d_args.symm

theorem k_mut : ∀ r ∈ VG.Proof.AesOcb.Arm.mutR p, (⟨State.addr p.K, 256⟩ : Region).Disjoint r :=
  VG.Proof.AesOcb.Arm.disj_mut L L.k_w L.bk L.k_d

theorem sched_mut {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.mutR p) m m') : VG.Proof.AesOcb.Arm.sched p m' = VG.Proof.AesOcb.Arm.sched p m :=
  Proof.Cmac.bytesAt_frame h (fun r hr => (VG.Proof.AesOcb.Arm.k_mut L r hr).sub_left
    (Region.sub_prefix (by have := L.rounds_le; omega))) (by have := L.rounds_le; omega)

theorem lstar_mut {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.mutR p) m m') :
    Spec.Ocb.ctxLstar m' (State.addr p.K) = Spec.Ocb.ctxLstar m (State.addr p.K) := by
  unfold Spec.Ocb.ctxLstar
  exact Proof.Ocb.blockAtMem_frame h fun r hr => (VG.Proof.AesOcb.Arm.k_mut L r hr).sub_left (Offset.sub_base _ (by decide))

theorem nonce_mut {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.mutR p) m m') :
    bytesAt m' (State.addr p.N) p.nl = bytesAt m (State.addr p.N) p.nl :=
  Proof.Cmac.bytesAt_frame h (VG.Proof.AesOcb.Arm.disj_mut L L.n_w L.bn L.n_d) (by have := L.nl15; omega)

theorem aad_mut {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.mutR p) m m') :
    bytesAt m' (State.addr p.A) p.al = bytesAt m (State.addr p.A) p.al :=
  Proof.Cmac.bytesAt_frame h (VG.Proof.AesOcb.Arm.disj_mut L L.a_w L.ba L.a_d) (by have := L.al_lt; omega)

theorem tag_mut {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.mutR p) m m') :
    bytesAt m' (State.addr p.T) p.tl = bytesAt m (State.addr p.T) p.tl :=
  Proof.Cmac.bytesAt_frame h (VG.Proof.AesOcb.Arm.disj_mut L L.t_w L.bt L.t_d) (by have := L.tl16; omega)

/-- A block of the associated data. -/
theorem aadBlk_mut {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.mutR p) m m') {k : Nat} (hk : k + 16 ≤ p.al) :
    blockAtMem m' (State.addr p.A + BitVec.ofNat 64 k) = blockAtMem m (State.addr p.A + BitVec.ofNat 64 k) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => (VG.Proof.AesOcb.Arm.disj_mut L L.a_w L.ba L.a_d r hr).sub_left (Offset.sub_base _ hk)

theorem Args.mut {m m' : Mem} (A : VG.Proof.AesOcb.Arm.Args p m) (h : Frame (VG.Proof.AesOcb.Arm.mutR p) m m') : VG.Proof.AesOcb.Arm.Args p m' :=
  A.frame L h (VG.Proof.AesOcb.Arm.args_mut L)

end

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.HashChunk`. -/
section

/-!
# AES-OCB on ARMv7: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`), `r4`
points at block `j`, `r6` is `j + 1` and `r7` is `m − j`. `hashChunk` takes
`c = min(16, m − j)` blocks: fills the buffer with each block XORed with its
offset (`fill_ok`), enciphers the buffer, adds it to the sum (`sum_ok`), and
leaves `HInv` at `j + c` (`hashChunk_ok`), as on AArch64
(`Proof.AesOcb.AArch64.hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 dec32 z_dec mem_store gpr_store rd_store wr_store
  sp_store)

/-- The associated data in the memory `m`. -/
abbrev aadOf (p : VG.Proof.AesOcb.Arm.Prm) (m : Mem) : List Byte := bytesAt m (State.addr p.A) p.al

/-- `ENCIPHER(K, ·)` of the key context in the memory `m`. -/
abbrev ciphOf (p : VG.Proof.AesOcb.Arm.Prm) (m : Mem) : Cipher := Spec.Ocb.aesWith p.R (VG.Proof.AesOcb.Arm.sched p m)

/-- `L_*` of the key context in the memory `m`. -/
abbrev lstarOf (p : VG.Proof.AesOcb.Arm.Prm) (m : Mem) : Block := Spec.Ocb.ctxLstar m (State.addr p.K)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, its offset and the count of a
chunk, the buffer and the working space of the functions called, and the
stack below `SP`. -/
abbrev hashR (p : VG.Proof.AesOcb.Arm.Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 48, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 192, 24⟩, ⟨State.addr p.W + BitVec.ofNat 64 256, 2304⟩,
   Proof.AesGcm.Arm.below p.SP]

theorem hashR_mut {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.hashR p) m m') : Frame (VG.Proof.AesOcb.Arm.mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.Arm.below_mut L

/-- A part of one of the parts of `W` that `HASH` writes. -/
theorem w_hash {p : VG.Proof.AesOcb.Arm.Prm} {a l b k : Nat} (hb : (⟨State.addr p.W + BitVec.ofNat 64 b, k⟩ : Region) ∈ VG.Proof.AesOcb.Arm.hashR p)
    (h : b ≤ a ∧ a + l ≤ b + k) (_hk : b + k ≤ 2560) :
    ∃ r' ∈ VG.Proof.AesOcb.Arm.hashR p, Region.Sub ⟨State.addr p.W + BitVec.ofNat 64 a, l⟩ r' :=
  ⟨_, hb, Offset.sub _ h.1 (by omega)⟩

/-- What holds of `HASH` after `j` of the whole blocks of the associated data,
from the state `t₀` at its start. -/
structure HInv (p : VG.Proof.AesOcb.Arm.Prm) (t₀ t : State) (j : Nat) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t
  frame : Frame (VG.Proof.AesOcb.Arm.hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  le : j ≤ p.al / 16
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (VG.Proof.AesOcb.Arm.ciphOf p t₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) j
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) j
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * j)
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + 1)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j)
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) 0

/-- Block `i` of the associated data, in a state after `t₀`. -/
theorem aadBlk {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {m : Mem} (h : Frame (VG.Proof.AesOcb.Arm.mutR p) t₀.mem m) {i : Nat}
    (hi : i < p.al / 16) :
    blockAtMem m (State.addr p.A + BitVec.ofNat 64 (16 * i)) = blockAt (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) i := by
  rw [Proof.Ocb.blockAt_bytesAt _ _ (by omega), VG.Proof.AesOcb.Arm.aadBlk_mut L h (by omega)]

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (p : VG.Proof.AesOcb.Arm.Prm) (t₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t
  frame : Frame (VG.Proof.AesOcb.Arm.hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i))
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + i + 1)
  r8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (c - i)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j - c)
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (j + i)
  buf : ∀ k < i, blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
    blockAt (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) (j + k) ^^^ offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (j + k + 1)
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (VG.Proof.AesOcb.Arm.ciphOf p t₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) j
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) 0
  cnt : t.mem.readW (State.addr p.W + BitVec.ofNat 64 cnO) 32 = BitVec.ofNat 32 c

theorem fill_step {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {j c : Nat} (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    {t : State} {i : Nat} (hi : i < c) (F : VG.Proof.AesOcb.Arm.FillInv p t₀ j c t i) :
    WP isa hashFill t fun t' => VG.Proof.AesOcb.Arm.FillInv p t₀ j c t' (i + 1) ∧ t'.z = decide (i + 1 = c) := by
  refine WP.mono (VG.Proof.AesOcb.Arm.hashFill_ok L F.env hi hc (by omega) F.r6 F.r4 F.r8 F.r5 F.l0 F.oh) fun t' P => ?_
  have hfr : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩], ∃ r' ∈ VG.Proof.AesOcb.Arm.hashR p, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 96) (k := 16) (by simp) (by decide) (by decide)
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 192) (k := 24) (by simp) (by decide) (by decide)
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 256) (k := 2304) (by simp) ⟨by simp only [bufO]; omega, by simp only [bufO]; omega⟩
        (by decide)
  have kept : ∀ {d k : Nat}, d + k ≤ 2560 →
      (∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩],
        (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r) →
      bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 d) k = bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 d) k :=
    fun hd h => Proof.Cmac.bytesAt_frame P.frame h (by omega)
  have kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ lO ∨ lO + 16 ≤ d) → (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) →
      (d + 16 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h₁ h₂ h₃ => by
      unfold blockAtMem
      rw [kept hd (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.w_w h₁ hd (by decide)
        · exact L.w_w h₂ hd (by decide)
        · exact L.w_w h₃ hd (by simp only [bufO]; omega))]
  refine ⟨⟨F.env.of_others P.gpr P.sp P.rd P.wr, F.frame.trans (P.frame.sub hfr), by rw [P.rd, F.rd],
    by rw [P.wr, F.wr], by rw [P.r4]; congr 2, by rw [P.r6]; congr 1, P.r8, P.r5,
    by rw [P.gpr _ (by decide), F.r7], by rw [P.oh]; rfl, fun k hk => ?_, ?_, ?_, ?_⟩, P.z⟩
  · rcases (show k < i ∨ k = i by omega) with hk | rfl
    · rw [kblk (by simp only [bufO]; omega) (.inr (by simp only [lO, bufO]; omega))
        (.inr (by simp only [ohO, bufO]; omega)) (.inl (by omega)), F.buf k hk]
    · rw [P.buf, VG.Proof.AesOcb.Arm.aadBlk L (VG.Proof.AesOcb.Arm.hashR_mut L F.frame) (by omega)]
  · rw [kblk (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by simp only [sumO, bufO]; omega)), F.sum]
  · rw [kblk (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by simp only [l0O, bufO]; omega)), F.l0]
  · rw [P.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 cnO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by simp only [cnO, bufO]; omega)) (by decide) (by simp only [bufO]; omega)) (by decide),
      F.cnt]

theorem fill_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 16)
    (hjc : j + c ≤ p.al / 16) {t : State} (F : VG.Proof.AesOcb.Arm.FillInv p t₀ j c t 0) :
    WP isa (.loop hashFill .ne) t fun t' => VG.Proof.AesOcb.Arm.FillInv p t₀ j c t' c := by
  refine WP.loop (M := isa) (fun k t' => ∃ i, k = c - i ∧ i < c ∧ VG.Proof.AesOcb.Arm.FillInv p t₀ j c t' i) ?_ (c - 0) t
    ⟨0, rfl, hc0, F⟩
  rintro k t' ⟨i, rfl, hi, Fi⟩
  refine WP.mono (VG.Proof.AesOcb.Arm.fill_step L hc hjc hi Fi) fun t'' ⟨F', z⟩ => ?_
  by_cases h : i + 1 = c
  · left
    refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
    subst h; exact F'
  · right
    exact ⟨(eval_ne' z).trans (by simp [h]), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

/-- The sum loop after `k` of the `c` enciphered blocks of a chunk from block
`j`. -/
structure SumInv (p : VG.Proof.AesOcb.Arm.Prm) (t₀ : State) (j c : Nat) (t : State) (k : Nat) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t
  frame : Frame (VG.Proof.AesOcb.Arm.hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + c))
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + c + 1)
  r8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * k)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (c - k)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j - c)
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (j + c)
  buf : ∀ k' < c, blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k')) =
    VG.Proof.AesOcb.Arm.ciphOf p t₀.mem (blockAt (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) (j + k') ^^^ offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (j + k' + 1))
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (VG.Proof.AesOcb.Arm.ciphOf p t₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) (j + k)
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) 0

theorem sum_step {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {j c : Nat} (hc : c ≤ 16)
    {t : State} {k : Nat} (hk : k < c) (S : VG.Proof.AesOcb.Arm.SumInv p t₀ j c t k) :
    WP isa (.block (xorB .r11 .r8 .r11 sumO 0 sumO ++ [Impl.AesGcm.Arm.addI .r8 .r8 16, .subs .r5 .r5 (Impl.AesGcm.Arm.imm 1)]))
      t fun t' => VG.Proof.AesOcb.Arm.SumInv p t₀ j c t' (k + 1) ∧ t'.z = decide (k + 1 = c) := by
  have fw := L.ww
  have eB : State.addr (p.W + BitVec.ofNat 32 (bufO + 16 * k)) = State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k) :=
    L.wA (by simp only [bufO]; omega)
  refine WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t) (pb := .r11) (qb := .r8) (cb := .r11) (pd := sumO) (qd := 0)
    (cd := sumO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [S.env.r11]; simp only [sumO]; omega) (by rw [S.r8, L.wN (by simp only [bufO]; omega)]; simp only [bufO]; omega)
    (by rw [S.env.r11]; simp only [sumO]; omega) (by rw [S.env.r11]; exact S.env.perm.wCR (by decide))
    (by rw [S.r8, eB, BitVec.add_zero]; exact S.env.perm.wCR (by simp only [bufO]; omega))
    (by rw [S.env.r11]; exact S.env.perm.wC (by decide))) fun t₁ R₁ => ?_)
  rw [S.env.r11, S.r8, eB, BitVec.add_zero] at R₁
  have dSB : (⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k), 16⟩ :=
    L.w_w (.inl (by simp only [sumO, bufO]; omega)) (by decide) (by simp only [bufO]; omega)
  have r5₁ : t₁.gpr .r5 = BitVec.ofNat 32 (c - k) := by rw [R₁.gpr _ (by decide), S.r5]
  have r8₁ : t₁.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * k) := by rw [R₁.gpr _ (by decide), S.r8]
  refine WP.of_runBlock ⟨_, by orun [r5₁, r8₁], ?_⟩
  have fr : Frame [⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ sumO ∨ sumO + 16 ≤ d) →
      blockAtMem t₁.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h => blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w h hd (by decide)
  refine ⟨⟨S.env.of_others (rs := [.r0, .r1, .r5, .r8]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.1, hr.2.2.2, ↓reduceIte]
      exact R₁.gpr r (by simp [hr.1, hr.2.1])) (by simp [sp_setReg, Proof.AesGcm.Arm.sp_subFlags, R₁.sp])
      (by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, R₁.rd]) (by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, R₁.wr]),
    ?_, by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, R₁.rd, S.rd], by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, R₁.wr, S.wr],
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r4 (by decide), S.r4],
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r6 (by decide), S.r6], ?_, ?_,
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r7 (by decide), S.r7], ?_, fun k' hk' => ?_, ?_, ?_⟩,
    ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact S.frame.trans (fr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.AesOcb.Arm.w_hash (b := 48) (k := 16) (by simp) (by decide) (by decide))
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    congr 2
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hk (by omega)]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by decide) (.inr (by decide)), S.oh]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by simp only [bufO]; omega) (.inr (by simp only [sumO, bufO]; omega)), S.buf k' hk']
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [R₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dSB), S.sum, S.buf k hk]
    rfl
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by decide) (.inr (by decide)), S.l0]
  · simp only [z_setReg, z_subFlags, dec32 hk (by omega), z_dec hk (by omega)]

theorem sum_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 16) {t : State}
    (S : VG.Proof.AesOcb.Arm.SumInv p t₀ j c t 0) : WP isa hashSum t fun t' => VG.Proof.AesOcb.Arm.SumInv p t₀ j c t' c := by
  refine WP.loop (M := isa) (fun k t' => ∃ i, k = c - i ∧ i < c ∧ VG.Proof.AesOcb.Arm.SumInv p t₀ j c t' i) ?_ (c - 0) t
    ⟨0, rfl, hc0, S⟩
  rintro k t' ⟨i, rfl, hi, Si⟩
  refine WP.mono (VG.Proof.AesOcb.Arm.sum_step L hc hi Si) fun t'' ⟨S', z⟩ => ?_
  by_cases h : i + 1 = c
  · left
    refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
    subst h; exact S'
  · right
    exact ⟨(eval_ne' z).trans (by simp [h]), c - (i + 1), by omega, i + 1, rfl, by omega, S'⟩

/-! ## The chunk -/

/-- The start of a chunk of `c` blocks from block `j`, once `c` is in `r5`:
`c` saved at `W + cnO`, the blocks left in `r7` and the buffer in `r8`. -/
theorem chunkHead_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {t : State} {j c : Nat}
    (H : VG.Proof.AesOcb.Arm.HInv p t₀ t j) (_hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 c) :
    WP isa (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), Impl.AesGcm.Arm.addI .r8 .r11 bufO]) t fun t' => VG.Proof.AesOcb.Arm.FillInv p t₀ j c t' 0 := by
  have fw := L.ww
  have al32 := L.al_lt
  have E := H.env
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have wC : InRegions t.wr (State.addr p.W + BitVec.ofNat 64 212) 4 := E.perm.wW (by decide)
  have kblk0 : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ cnO ∨ cnO + 4 ≤ d) → ∀ m : Mem, ∀ v : BitVec 32,
      blockAtMem (m.writeW (State.addr p.W + BitVec.ofNat 64 212) v) (State.addr p.W + BitVec.ofNat 64 d) =
        blockAtMem m (State.addr p.W + BitVec.ofNat 64 d) := fun hd h m v =>
    blockAtMem_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.w_w h hd (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.r11, h5, eC, wC, H.r7], ?_⟩
  refine ⟨H.env.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl), ?_, by simp [rd_setReg, rd_store, H.rd],
    by simp [wr_setReg, wr_store, H.wr], by simp [gpr_setReg, gpr_store, H.r4], by simp [gpr_setReg, gpr_store, H.r6], ?_,
    by simp [gpr_setReg, gpr_store, h5], ?_,
    ?_, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store]
    exact H.frame.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Proof.AesOcb.Arm.w_hash (b := 192) (k := 24) (by simp) (by decide) (by decide))
  · simp [gpr_setReg, gpr_store, E.r11, bufO]
  · simp only [gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, H.r7, h5]
    rw [Offset.ofNat_sub_ofNat (by omega)]
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.oh]; simp
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.sum]
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.l0]
  · simp only [mem_setReg, mem_store, cnO, Mem.readW_writeW_self32]

/-- The state at the chunk's call. -/
abbrev chunkCallSt (p : VG.Proof.AesOcb.Arm.Prm) (c : Nat) (t : State) : State :=
  ((((t.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12 (p.W + BitVec.ofNat 32 scrO)).setReg .r2
    (p.W + BitVec.ofNat 32 bufO)).setReg .r3 (BitVec.ofNat 32 c)

/-- The arguments of the chunk's call. -/
theorem chunkArgs_run {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t : State} {j c : Nat} (F : VG.Proof.AesOcb.Arm.FillInv p t₀ j c t c) :
    runBlock isa (callArgs ++ [Impl.AesGcm.Arm.addI .r2 .r11 bufO, .ldr .r3 .r11 cnO]) t =
      some (VG.Proof.AesOcb.Arm.chunkCallSt p c t) := by
  have E₂ := F.env
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have rC : InRegions (t.rd ++ t.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₂.perm.wR (by decide)
  have cnt : t.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := F.cnt
  orun [callArgs, E₂.r9, E₂.r10, E₂.r11, eC, rC, cnt]

/-- The chunk's call, set up. -/
theorem chunkCall_blk {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t : State} {j c : Nat} (F : VG.Proof.AesOcb.Arm.FillInv p t₀ j c t c) (hc : c ≤ 16) :
    VG.Proof.AesOcb.Arm.BlkCall (VG.Proof.AesOcb.Arm.chunkCallSt p c t) p.K (p.W + BitVec.ofNat 32 bufO) (p.W + BitVec.ofNat 32 scrO) p.R c ∧
      VG.Proof.AesOcb.Arm.Env p (VG.Proof.AesOcb.Arm.chunkCallSt p c t) := by
  have fw := L.ww
  have E₂ := F.env
  have eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have E' : VG.Proof.AesOcb.Arm.Env p (VG.Proof.AesOcb.Arm.chunkCallSt p c t) :=
    E₂.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨VG.Proof.AesOcb.Arm.blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by decide)]; simp only [bufO]; omega)
      (by rw [eB]; exact E₂.perm.wC (by simp only [bufO]; omega)) (by rw [eB]; exact L.k_w' (by simp only [bufO]; omega))
      (by rw [eB]; exact L.w_w (.inl (by simp only [scrO, bufO]; omega)) (by simp only [bufO]; omega) (by decide))
      (by rw [eB]; exact L.bw' (by simp only [bufO]; omega)), E'⟩

/-- The rest of a chunk, from its call. -/
theorem chunkTail_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t₂ : State} {j c : Nat} (F : VG.Proof.AesOcb.Arm.FillInv p t₀ j c t₂ c)
    (hc0 : 0 < c) (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16) :
    WP isa (.seq encFrame
      (.seq (.block [Impl.AesGcm.Arm.addI .r8 .r11 bufO, .ldr .r5 .r11 cnO])
      (.seq hashSum (.block [.cmp .r7 (Impl.AesGcm.Arm.imm 0)]))))
      (VG.Proof.AesOcb.Arm.chunkCallSt p c t₂) fun t' => VG.Proof.AesOcb.Arm.HInv p t₀ t' (j + c) ∧ t'.z = decide (p.al / 16 - (j + c) = 0) := by
  have fw := L.ww
  have al32 := L.al_lt
  have E₂ := F.env
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have cnt : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := F.cnt
  have hB := VG.Proof.AesOcb.Arm.blkFrame_ok VG.Proof.AesOcb.Arm.encF L (t := VG.Proof.AesOcb.Arm.chunkCallSt p c t₂)
    (D := p.W + BitVec.ofNat 32 bufO) (n := c) (VG.Proof.AesOcb.Arm.chunkCall_blk L F hc).2 (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by decide)]; simp only [bufO]; omega)
      (by rw [eB]; exact E₂.perm.wC (by simp only [bufO]; omega)) (by rw [eB]; exact L.k_w' (by simp only [bufO]; omega))
      (by rw [eB]; exact L.w_w (.inl (by simp only [scrO, bufO]; omega)) (by simp only [bufO]; omega) (by decide))
      (by rw [eB]; exact L.bw' (by simp only [bufO]; omega))
  rw [eB] at hB
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.encFrame_eq ▸ hB) fun t₃ C₃ => ?_)
  -- what the call leaves
  have g₃ : ∀ r ∈ VG.Proof.AesOcb.Arm.keptRegs, t₃.gpr r = t₂.gpr r := fun r hr => by
    rw [C₃.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  have E₃ : VG.Proof.AesOcb.Arm.Env p t₃ := E₂.keep (fun r hr => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    (by rw [C₃.sp]; rfl) (by rw [C₃.rd]; rfl) (by rw [C₃.wr]; rfl)
  have frC : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 bufO, 16 * c⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, Proof.AesGcm.Arm.below p.SP], ∃ r' ∈ VG.Proof.AesOcb.Arm.hashR p, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by simp only [bufO]; omega⟩ (by decide)
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact ⟨_, by simp, fun _ h => h⟩
  have fr₃ : Frame (VG.Proof.AesOcb.Arm.hashR p) t₀.mem t₃.mem := F.frame.trans (C₃.frame.sub frC)
  have kW : ∀ {d k : Nat}, d + k ≤ bufO → (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 bufO, 16 * c⟩ ∧
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩ ∧
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (Proof.AesGcm.Arm.below p.SP) := fun hd =>
    ⟨L.w_w (.inl hd) (by simp only [bufO] at hd ⊢; omega) (by simp only [bufO]; omega),
      L.w_w (.inl (by simp only [bufO, scrO] at hd ⊢; omega)) (by simp only [bufO] at hd ⊢; omega) (by decide),
      (L.bw' (by simp only [bufO] at hd ⊢; omega)).symm⟩
  have kblk : ∀ {d : Nat}, d + 16 ≤ bufO →
      blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame C₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [(kW hd).1, (kW hd).2.1, (kW hd).2.2]
  have cnt₃ : t₃.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := by
    rw [C₃.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 212, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [(kW (by decide)).1, (kW (by decide)).2.1, (kW (by decide)).2.2]) (by decide)]
    exact cnt
  have rC₃ : InRegions (t₃.rd ++ t₃.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₃.perm.wR (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E₃.r11, eC, rC₃, cnt₃], ?_⟩)
  have hsched : VG.Proof.AesOcb.Arm.sched p t₂.mem = VG.Proof.AesOcb.Arm.sched p t₀.mem := VG.Proof.AesOcb.Arm.sched_mut L (VG.Proof.AesOcb.Arm.hashR_mut L F.frame)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.sum_ok L (t₀ := t₀) (j := j) (c := c) hc0 hc ?S0) fun t₄ S => ?_)
  case S0 =>
    refine ⟨E₃.of_others (rs := [.r5, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl),
      by simp only [mem_setReg]; exact fr₃, by simp [rd_setReg, C₃.rd, F.rd], by simp [wr_setReg, C₃.wr, F.wr],
      by simp [gpr_setReg, g₃ .r4 (by decide), F.r4], by simp [gpr_setReg, g₃ .r6 (by decide), F.r6],
      by simp [gpr_setReg, E₃.r11, bufO], by simp [gpr_setReg],
      by simp [gpr_setReg, g₃ .r7 (by decide), F.r7], ?_, fun k hk => ?_, ?_, ?_⟩
    · simp only [mem_setReg]; rw [kblk (by decide), F.oh]
    · simp only [mem_setReg]
      have := C₃.out k hk
      simp only [mem_setReg, Offset.add_add] at this
      rw [this, F.buf k hk, VG.Proof.AesOcb.Arm.encF_ciph]
      simp only [mem_setReg, hsched]
    · simp only [mem_setReg]; rw [kblk (by decide), F.sum]; simp
    · simp only [mem_setReg]; rw [kblk (by decide), F.l0]
  -- the end
  refine WP.of_runBlock ⟨_, by orun [S.r7], ?_⟩
  refine ⟨⟨S.env.of_others (rs := []) (by others_tac) (by rfl) (by rfl) (by rfl), S.frame, S.rd, S.wr, hjc,
    S.sum, S.oh, S.r4, S.r6, by simp only [Proof.AesGcm.Arm.gpr_subFlags, S.r7]; congr 1; omega, S.l0⟩, ?_⟩
  simp only [z_subFlags, S.r7, BitVec.sub_zero, z_cmp0 (show p.al / 16 - j - c < 2 ^ 32 by omega)]
  congr 1; apply propext; omega


/-- A chunk of `c` blocks from block `j`, once `c` is in `r5`. -/
theorem chunkRest_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {t : State} {j c : Nat}
    (H : VG.Proof.AesOcb.Arm.HInv p t₀ t j) (hc0 : 0 < c) (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 c) :
    WP isa (.seq (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), Impl.AesGcm.Arm.addI .r8 .r11 bufO])
      (.seq (.loop hashFill .ne)
      (.seq (.block (callArgs ++ [Impl.AesGcm.Arm.addI .r2 .r11 bufO, .ldr .r3 .r11 cnO]))
      (.seq encFrame
      (.seq (.block [Impl.AesGcm.Arm.addI .r8 .r11 bufO, .ldr .r5 .r11 cnO])
      (.seq hashSum (.block [.cmp .r7 (Impl.AesGcm.Arm.imm 0)])))))))
      t fun t' => VG.Proof.AesOcb.Arm.HInv p t₀ t' (j + c) ∧ t'.z = decide (p.al / 16 - (j + c) = 0) :=
  WP.seq (WP.mono (VG.Proof.AesOcb.Arm.chunkHead_ok L H hc hjc h5) fun _ F₁ => WP.seq (WP.mono (VG.Proof.AesOcb.Arm.fill_ok L hc0 hc hjc F₁)
    fun _ F₂ => WP.seq (WP.of_runBlock ⟨_, VG.Proof.AesOcb.Arm.chunkArgs_run L F₂, VG.Proof.AesOcb.Arm.chunkTail_ok L F₂ hc0 hc hjc⟩)))

theorem hashChunk_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ : State} {t : State} {j : Nat}
    (H : VG.Proof.AesOcb.Arm.HInv p t₀ t j) (hj : j < p.al / 16) :
    WP isa hashChunk t fun t' => VG.Proof.AesOcb.Arm.HInv p t₀ t' (j + min 16 (p.al / 16 - j)) ∧
      t'.z = decide (p.al / 16 - (j + min 16 (p.al / 16 - j)) = 0) := by
  have al32 := L.al_lt
  have m32 : p.al / 16 - j < 2 ^ 32 := by omega
  unfold hashChunk
  have z₁ : (BitVec.ofNat 32 (p.al / 16 - j) >>> 4 == 0) = decide (p.al / 16 - j < 16) := by
    rw [VG.Proof.AesOcb.Arm.ofNat_lsr32 m32, z_cmp0 (by omega)]; congr 1; apply propext; omega
  refine WP.seq (WP.of_runBlock ⟨_, by orun [H.r7], ?_⟩)
  have Hk : ∀ {t' : State}, t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      VG.Proof.AesOcb.Arm.Others [.r5, .r12] t t' → VG.Proof.AesOcb.Arm.HInv p t₀ t' j := fun hm hrd hwr hsp ho =>
    ⟨H.env.of_others ho hsp hrd hwr, by rw [hm]; exact H.frame, by rw [hrd, H.rd], by rw [hwr, H.wr], H.le,
      by rw [hm]; exact H.sum, by rw [hm]; exact H.oh, by rw [ho _ (by decide), H.r4], by rw [ho _ (by decide), H.r6],
      by rw [ho _ (by decide), H.r7], by rw [hm]; exact H.l0⟩
  refine WP.seq (WP.ite (decide (p.al / 16 - j < 16))
    (eval_eq' (by simp only [z_subFlags, gpr_setReg, ite_true, H.r7, BitVec.sub_zero, z₁])) (fun hb => ?_)
    (fun hb => ?_))
  · have hlt : p.al / 16 - j < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by orun [H.r7], ?_⟩
    have e : min 16 (p.al / 16 - j) = p.al / 16 - j := by omega
    rw [e]
    exact VG.Proof.AesOcb.Arm.chunkRest_ok L (Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac)) (by omega) (by omega) (by omega)
      (by simp [gpr_setReg, H.r7])
  · have hlt : ¬ p.al / 16 - j < 16 := by simpa using hb
    refine WP.of_runBlock ⟨_, by orun [], ?_⟩
    have e : min 16 (p.al / 16 - j) = 16 := by omega
    rw [e]
    exact VG.Proof.AesOcb.Arm.chunkRest_ok L (Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac)) (by omega) (by omega) (by omega)
      (by simp [gpr_setReg])

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.PadTo`. -/
section

/-!
# AES-OCB on ARMv7: `pad(S)` (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes
`pad(S) = S ‖ 1 ‖ zeros` (§4.1), for the `n` bytes `S` at `r4`
(`0 < n < 16`), to `W + d`: zeros, the bytes copied (`copyLoop`), and `0x80`
after them (`padTo_ok`), as on AArch64 (`Proof.AesOcb.AArch64.padTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)
open VG.Proof.AesGcm.Arm (copyLoop_ok LoopPre mem_store gpr_store rd_store wr_store sp_store)

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.r0, .r1, .r2, .r3, .r12]

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `r4`, `0 < n < 16`. -/
theorem padTo_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) {S : BitVec 32} {n d : Nat} (hn : 0 < n)
    (hn' : n < 16) (hd : d + 16 ≤ 2560) (he : encodable (BitVec.ofNat 32 d) = true)
    (h4 : s.gpr .r4 = S) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (fS : S.toNat + n ≤ 2 ^ 32)
    (hS : Covers [⟨State.addr S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨State.addr S, n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) = pad (bytesAt s.mem (State.addr S) n) ∧
      VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.padRegs s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega)
  unfold padTo
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.zero16_wp (s := s) (o := d) (by omega) (by rw [E.r11]; omega)
    (by rw [E.r11]; exact E.perm.wC hd)) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  have r11₁ : s₁.gpr .r11 = p.W := by rw [R₁.gpr _ (by decide), E.r11]
  have r4₁ : s₁.gpr .r4 = S := by rw [R₁.gpr _ (by decide), h4]
  have r5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [R₁.gpr _ (by decide), h5]
  refine WP.of_runBlock ⟨_, by orun [he, r11₁, r4₁, r5₁], ?_⟩
  have eS : bytesAt s₁.mem (State.addr S) n = bytesAt s.mem (State.addr S) n := by
    rw [R₁.mem]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega)
  have z₁ : bytesAt s₁.mem (State.addr p.W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [R₁.mem]; exact Proof.Cmac.zero4_bytes _ _
  refine WP.seq (WP.mono (copyLoop_ok _ (S := S) (D := p.W + BitVec.ofNat 32 d) (n := n)
    ⟨by simp [gpr_setReg, r4₁], by simp [gpr_setReg], by simp [gpr_setReg, r5₁], hn, by omega, fS,
      by rw [L.wN (by omega)]; omega, by simp only [rd_setReg, wr_setReg, R₁.rd, R₁.wr]; exact hS,
      by simp only [wr_setReg, R₁.wr, ed]; exact Proof.AesGcm.Arm.covers_prefix (E.perm.wC hd) (by omega),
      by rw [ed]; exact hSD.sub_right (Region.sub_prefix (by omega))⟩) fun s₃ ⟨m₃, O₃⟩ => ?_)
  simp only [mem_setReg, ed] at m₃
  rw [eS] at m₃
  have edn : State.addr (p.W + BitVec.ofNat 32 d + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n := by
    rw [BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add, L.wA (by omega), Offset.add_add]
  have w₃ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [O₃.wr]; simp only [wr_setReg, R₁.wr, Offset.add_add]; exact E.perm.wW (d := d + n) (n := 1) (by omega)
  refine WP.of_runBlock ⟨_, by orun [O₃.r2, edn, w₃], ?_⟩
  have hlen : (bytesAt s.mem (State.addr S) n).length = n := length_bytesAt _ _ _
  have key : ∀ (m : Mem) (b : Byte), (VG.WriteBytes.writeBytes m (State.addr p.W + BitVec.ofNat 64 d)
      (bytesAt s.mem (State.addr S) n)).writeW (State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b =
      VG.WriteBytes.writeBytes m (State.addr p.W + BitVec.ofNat 64 d) (bytesAt s.mem (State.addr S) n ++ [b]) :=
    fun m b => by rw [VG.WriteBytes.writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_store, mem_setReg]
    rw [m₃, key]
    intro x hx
    rw [VG.WriteBytes.writeBytes_frame _ _ _ (by simp [hlen]; exact VG.Proof.AesOcb.Arm.contains_pre _ (by omega)) x hx]
    have F1 : Frame [⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩] s.mem s₁.mem := by
      rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    exact F1 x hx
  · simp only [mem_store, mem_setReg]
    rw [m₃, key, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₁]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
    rfl
  · simp only [VG.Proof.AesOcb.Arm.padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_store, gpr_setReg, hr.1, ite_false]
    rw [O₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_setReg, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
    exact R₁.gpr r (by simp [hr.1])
  · simp only [sp_store, sp_setReg]; rw [O₃.sp]; simp [sp_setReg, R₁.sp]
  · simp only [rd_store, rd_setReg]; rw [O₃.rd]; simp [rd_setReg, R₁.rd]
  · simp only [wr_store, wr_setReg]; rw [O₃.wr]; simp [wr_setReg, R₁.wr]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Hash`. -/
section

/-!
# AES-OCB on ARMv7: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, takes the whole blocks of the associated data in chunks
(`hashChunk_ok`), then the rest, padded, XORed with the offset `⊕ L_*`,
enciphered and added to the sum (`hashRest`): `HASH(K, A)` at `W + sumO`
(`hash_ok`, `Proof.Ocb.hash_eq`), as on AArch64
(`Proof.AesOcb.AArch64.hash_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz pad)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 and15 mem_store gpr_store rd_store wr_store
  sp_store)

/-- What `hash` leaves, from `t`. -/
structure HashOut (p : VG.Proof.AesOcb.Arm.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  frame : Frame (VG.Proof.AesOcb.Arm.hashR p) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sum : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (VG.Proof.AesOcb.Arm.ciphOf p t.mem) (VG.Proof.AesOcb.Arm.lstarOf p t.mem) (VG.Proof.AesOcb.Arm.aadOf p t.mem)

/-- The whole blocks of the associated data. -/
theorem hashWhole_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t : State} (H : VG.Proof.AesOcb.Arm.HInv p t₀ t 0)
    (hz : t.z = decide (p.al / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop hashChunk .ne)) t fun t' => VG.Proof.AesOcb.Arm.HInv p t₀ t' (p.al / 16) := by
  refine WP.ite (decide (p.al / 16 = 0)) (eval_eq' hz) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : p.al / 16 = 0 := of_decide_eq_true hb
    rw [h0]; exact H
  · have hm : p.al / 16 ≠ 0 := by simpa using hb
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ VG.Proof.AesOcb.Arm.HInv p t₀ t' j) ?_
      (p.al / 16 - 0) t ⟨0, rfl, by omega, H⟩
    rintro k t' ⟨j, rfl, hj, Hj⟩
    refine WP.mono (VG.Proof.AesOcb.Arm.hashChunk_ok L Hj hj) fun t'' ⟨H', z⟩ => ?_
    by_cases h : p.al / 16 - (j + min 16 (p.al / 16 - j)) = 0
    · left
      refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
      have e : j + min 16 (p.al / 16 - j) = p.al / 16 := by omega
      rw [e] at H'; exact H'
    · right
      exact ⟨(eval_ne' z).trans (by simp [h]), p.al / 16 - (j + min 16 (p.al / 16 - j)), by omega,
        j + min 16 (p.al / 16 - j), rfl, by omega, H'⟩

/-- The rest of the associated data, `n` bytes after the `m` whole blocks. -/
theorem hashRest_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t : State} (H : VG.Proof.AesOcb.Arm.HInv p t₀ t (p.al / 16))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.al % 16)) (hn : p.al % 16 ≠ 0) :
    WP isa hashRest t fun t' => VG.Proof.AesOcb.Arm.Env p t' ∧ Frame (VG.Proof.AesOcb.Arm.hashR p) t₀.mem t'.mem ∧ t'.rd = t₀.rd ∧ t'.wr = t₀.wr ∧
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
        hsum (VG.Proof.AesOcb.Arm.ciphOf p t₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) (p.al / 16) ^^^
          VG.Proof.AesOcb.Arm.ciphOf p t₀.mem (pad ((VG.Proof.AesOcb.Arm.aadOf p t₀.mem).drop (16 * (p.al / 16))) ^^^
            (offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (p.al / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t₀.mem)) := by
  have fw := L.ww
  have fk := L.kw
  have al32 := L.al_lt
  have E := H.env
  have eK : State.addr (p.K + BitVec.ofNat 32 0) = State.addr p.K := by rw [BitVec.add_zero]
  unfold hashRest
  -- the offset `⊕ L_*`
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t) (pb := .r11) (qb := .r10) (cb := .r11) (pd := ohO) (qd := 240)
    (cd := ohO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [E.r11]; simp only [ohO]; omega) (by rw [E.r10]; omega)
    (by rw [E.r11]; simp only [ohO]; omega) (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [E.r10]; exact E.perm.kC (by decide)) (by rw [E.r11]; exact E.perm.wC (by decide))) fun t₁ R₁ => ?_)
  rw [E.r11, E.r10] at R₁
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fr₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have lK : blockAtMem t.mem (State.addr p.K + BitVec.ofNat 64 240) = VG.Proof.AesOcb.Arm.lstarOf p t₀.mem := by
    show Spec.Ocb.ctxLstar t.mem (State.addr p.K) = _
    exact VG.Proof.AesOcb.Arm.lstar_mut L (VG.Proof.AesOcb.Arm.hashR_mut L H.frame)
  have oh₁ : blockAtMem t₁.mem (State.addr p.W + BitVec.ofNat 64 ohO) =
      offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (p.al / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t₀.mem := by
    rw [R₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint
      ((L.k_w' (d := ohO) (k := 16) (by decide)).symm.sub_right (Offset.sub_base _ (by decide)))), H.oh, lK]
  -- `pad(A_*)` at `W + bufO`
  have hm : 16 * (p.al / 16) + p.al % 16 = p.al := by omega
  have eA : State.addr (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) =
      State.addr p.A + BitVec.ofNat 64 (16 * (p.al / 16)) := addr_add (by have := L.aw; omega)
  have hSA : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (p.al / 16)), p.al % 16⟩ : Region).Sub ⟨State.addr p.A, p.al⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.padTo_ok L E₁ (S := p.A + BitVec.ofNat 32 (16 * (p.al / 16))) (n := p.al % 16)
    (d := bufO) (by omega) (by omega) (by decide) (by decide) (by rw [R₁.gpr _ (by decide), H.r4])
    (by rw [R₁.gpr _ (by decide), h5])
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (p.al / 16)) (by omega),
      Nat.mod_eq_of_lt (by have := L.aw; omega)]; have := L.aw; omega)
    (by rw [eA]; exact Proof.AesGcm.Arm.covers_off E₁.perm.aad (by omega) (by omega))
    (by rw [eA]; exact (L.a_w' (by decide)).sub_left hSA)) fun t₂ ⟨fr₂, pad₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesOcb.Arm.Env p t₂ := E₁.of_others g₂ sp₂ rd₂ wr₂
  have hrest : bytesAt t₁.mem (State.addr (p.A + BitVec.ofNat 32 (16 * (p.al / 16)))) (p.al % 16) =
      (VG.Proof.AesOcb.Arm.aadOf p t₀.mem).drop (16 * (p.al / 16)) := by
    rw [eA, Proof.Ocb.bytesAt_drop _ _ (by omega), show p.al - 16 * (p.al / 16) = p.al % 16 by omega]
    rw [R₁.mem]
    exact Proof.Cmac.bytesAt_frame ((VG.Proof.AesOcb.Arm.hashR_mut L H.frame).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)))
      (fun r hr => (VG.Proof.AesOcb.Arm.disj_mut L L.a_w L.ba L.a_d r hr).sub_left hSA) (by omega)
  rw [hrest] at pad₂
  have oh₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ohO) =
      offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (p.al / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t₀.mem := by
    rw [blockAtMem_frame fr₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), oh₁]
  -- the XOR with the offset
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t₂) (pb := .r11) (qb := .r11) (cb := .r11) (pd := bufO) (qd := ohO)
    (cd := bufO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [E₂.r11]; simp only [bufO]; omega) (by rw [E₂.r11]; simp only [ohO]; omega)
    (by rw [E₂.r11]; simp only [bufO]; omega) (by rw [E₂.r11]; exact E₂.perm.wCR (by decide))
    (by rw [E₂.r11]; exact E₂.perm.wCR (by decide)) (by rw [E₂.r11]; exact E₂.perm.wC (by decide))) fun t₃ R₃ => ?_)
  rw [E₂.r11] at R₃
  have E₃ : VG.Proof.AesOcb.Arm.Env p t₃ := E₂.of_others R₃.gpr R₃.sp R₃.rd R₃.wr
  have fr₃' : Frame [⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 bufO, 16⟩]
      t.mem t₃.mem := ((fr₁.mono (by simp)).trans (fr₂.mono (by simp))).trans
        ((by rw [R₃.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _ : Frame [⟨State.addr p.W + BitVec.ofNat 64 bufO, 16⟩]
          t₂.mem t₃.mem).mono (by simp))
  have fr₃ : Frame (VG.Proof.AesOcb.Arm.hashR p) t₀.mem t₃.mem := H.frame.trans (fr₃'.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 192) (k := 24) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide))
  have b₃ : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 bufO) =
      pad ((VG.Proof.AesOcb.Arm.aadOf p t₀.mem).drop (16 * (p.al / 16))) ^^^
        (offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (p.al / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) := by
    rw [R₃.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by decide)) (by decide) (by decide))), pad₂, oh₂]
  -- enciphered
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.encOne_ok L E₃ (d := bufO) (by decide) (by decide)) fun t₄ C₄ => ?_)
  have E₄ := C₄.env E₃
  have b₄ : blockAtMem t₄.mem (State.addr p.W + BitVec.ofNat 64 bufO) =
      VG.Proof.AesOcb.Arm.ciphOf p t₀.mem (pad ((VG.Proof.AesOcb.Arm.aadOf p t₀.mem).drop (16 * (p.al / 16))) ^^^
        (offAt 0 (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (p.al / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t₀.mem)) := by
    have := C₄.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, VG.Proof.AesOcb.Arm.encF_ciph, b₃, VG.Proof.AesOcb.Arm.sched_mut L (VG.Proof.AesOcb.Arm.hashR_mut L fr₃)]
  have fr₄ : Frame (VG.Proof.AesOcb.Arm.hashR p) t₀.mem t₄.mem := fr₃.trans (C₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact ⟨_, by simp, fun _ h => h⟩)
  have sum₄ : blockAtMem t₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      hsum (VG.Proof.AesOcb.Arm.ciphOf p t₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p t₀.mem) (VG.Proof.AesOcb.Arm.aadOf p t₀.mem) (p.al / 16) := by
    rw [blockAtMem_frame C₄.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm),
      blockAtMem_frame fr₃' (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)), H.sum]
  -- added to the sum
  refine WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t₄) (pb := .r11) (qb := .r11) (cb := .r11) (pd := sumO) (qd := bufO)
    (cd := sumO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [E₄.r11]; simp only [sumO]; omega) (by rw [E₄.r11]; simp only [bufO]; omega)
    (by rw [E₄.r11]; simp only [sumO]; omega) (by rw [E₄.r11]; exact E₄.perm.wCR (by decide))
    (by rw [E₄.r11]; exact E₄.perm.wCR (by decide)) (by rw [E₄.r11]; exact E₄.perm.wC (by decide))) fun t₅ R₅ => ?_
  rw [E₄.r11] at R₅
  refine ⟨E₄.of_others R₅.gpr R₅.sp R₅.rd R₅.wr, ?_, by rw [R₅.rd, C₄.rd, R₃.rd, rd₂, R₁.rd, H.rd],
    by rw [R₅.wr, C₄.wr, R₃.wr, wr₂, R₁.wr, H.wr], ?_⟩
  · rw [R₅.mem]
    exact fr₄.trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.Arm.w_hash (b := 48) (k := 16) (by simp) (by decide) (by decide))
  · rw [R₅.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inl (by decide)) (by decide) (by decide))), sum₄, b₄]

/-- The start of `hash`: the sum and the offset zeroed, the associated data
in `r4`, its whole blocks in `r7` and `i = 1` in `r6`. -/
theorem hashHead_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) (A : VG.Proof.AesOcb.Arm.Args p t.mem)
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p t.mem) 0) :
    WP isa (.block (Impl.AesGcm.Arm.zero16 sumO ++ Impl.AesGcm.Arm.zero16 ohO ++
      ([.ldrSp .r4 0, .ldrSp .r7 4, .mov .r7 (.shifted .r7 .lsr 4), .mov .r6 (Impl.AesGcm.Arm.imm 1),
        .cmp .r7 (Impl.AesGcm.Arm.imm 0)] : List Instr))) t
      fun t₂ => VG.Proof.AesOcb.Arm.HInv p t t₂ 0 ∧ t₂.z = decide (p.al / 16 = 0) := by
  have fw := L.ww
  have al32 := L.al_lt
  refine WP.block_append (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.zero16_wp (s := t) (o := sumO) (by decide)
    (by rw [E.r11]; simp only [sumO]; omega) (by rw [E.r11]; exact E.perm.wC (by decide))) fun t₁ R₁ => ?_))
  rw [E.r11] at R₁
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  refine WP.mono (VG.Proof.AesOcb.Arm.zero16_wp (s := t₁) (o := ohO) (by decide) (by rw [E₁.r11]; simp only [ohO]; omega)
    (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_
  rw [E₁.r11] at R₂
  have E₂ : VG.Proof.AesOcb.Arm.Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]
    exact ((by rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _ :
      Frame [⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem t₁.mem).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  have A₂ : VG.Proof.AesOcb.Arm.Args p t₂.mem := A.frame L fr₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.args_w' (by decide))
  have a₀ := E₂.perm.argR' L (k := 0) (by decide)
  have a₄ := E₂.perm.argR' L (k := 4) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₂.sp, a₀, a₄, A₂.a0, A₂.a4], ?_⟩
  have fsub : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩],
      ∃ r' ∈ VG.Proof.AesOcb.Arm.hashR p, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 48) (k := 16) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact VG.Proof.AesOcb.Arm.w_hash (b := 192) (k := 24) (by simp) ⟨by decide, by decide⟩ (by decide)
  have kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ sumO ∨ sumO + 16 ≤ d) → (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) →
      blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h₁ h₂ => blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w h₁ hd (by decide)
      · exact L.w_w h₂ hd (by decide)
  refine ⟨?_, ?_⟩
  · refine ⟨E₂.of_others (rs := [.r4, .r6, .r7]) (by others_tac) (by rfl) (by rfl) (by rfl),
        fr₂.sub fsub, by simp [rd_setReg, R₂.rd, R₁.rd], by simp [wr_setReg, R₂.wr, R₁.wr], Nat.zero_le _, ?_, ?_,
        by simp [gpr_setReg], by simp [gpr_setReg], ?_, ?_⟩
    · simp only [Proof.AesGcm.Arm.mem_subFlags, mem_setReg]
      have fz : Frame [⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩] t₁.mem
          (Proof.Cmac.zero4 t₁.mem (State.addr p.W + BitVec.ofNat 64 ohO)) := Proof.Cmac.frame_store4 _ _ _ _ _
      rw [R₂.mem, blockAtMem_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := sumO) (n := 16) (d := ohO) (k := 16) (.inl (by decide)) (by decide) (by decide)),
        R₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_zero4]; rfl
    · simp only [Proof.AesGcm.Arm.mem_subFlags, mem_setReg]
      rw [R₂.mem, VG.Proof.AesOcb.Arm.blockAtMem_zero4]; rfl
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, VG.Proof.AesOcb.Arm.ofNat_lsr32 al32]
      rfl
    · simp only [Proof.AesGcm.Arm.mem_subFlags, mem_setReg]
      rw [kblk (by decide) (.inr (by decide)) (.inl (by decide)), hl0]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, BitVec.sub_zero, VG.Proof.AesOcb.Arm.ofNat_lsr32 al32,
      z_cmp0 (show p.al / 2 ^ 4 < 2 ^ 32 by omega)]

/-- After the whole blocks of the associated data: the rest's length in `r5`. -/
theorem hashMid_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t : State} (H : VG.Proof.AesOcb.Arm.HInv p t₀ t (p.al / 16)) (A : VG.Proof.AesOcb.Arm.Args p t.mem) :
    WP isa (.block [.ldrSp .r5 4, .dp .and .r5 .r5 (Impl.AesGcm.Arm.imm 15), .cmp .r5 (Impl.AesGcm.Arm.imm 0)]) t
      fun t' => VG.Proof.AesOcb.Arm.HInv p t₀ t' (p.al / 16) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.al % 16) ∧
        t'.z = decide (p.al % 16 = 0) := by
  have E₃ := H.env
  have a₄' := E₃.perm.argR' L (k := 4) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₃.sp, a₄', A.a4], ?_, ?_, ?_⟩
  · exact ⟨E₃.of_others (rs := [.r5]) (by others_tac) (by rfl) (by rfl) (by rfl), H.frame, H.rd, H.wr, H.le,
      H.sum, H.oh, H.r4, H.r6, H.r7, H.l0⟩
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, and15, VG.Proof.AesOcb.Arm.toNat_ofNat32 L.al_lt]
  · simp only [z_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15, VG.Proof.AesOcb.Arm.toNat_ofNat32 L.al_lt,
      z_cmp0 (show p.al % 16 < 2 ^ 32 by omega)]

theorem hash_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) (A : VG.Proof.AesOcb.Arm.Args p t.mem)
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p t.mem) 0) :
    WP isa Impl.AesOcb.Arm.hash t (VG.Proof.AesOcb.Arm.HashOut p t) := by
  have al32 := L.al_lt
  unfold Impl.AesOcb.Arm.hash
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.hashHead_ok L E A hl0) fun t₂ ⟨H₂, hz₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.hashWhole_ok L H₂ hz₂) fun t₃ H₃ => ?_)
  have A₃ : VG.Proof.AesOcb.Arm.Args p t₃.mem := A.mut L (VG.Proof.AesOcb.Arm.hashR_mut L H₃.frame)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.hashMid_ok L H₃ A₃) fun t₄ ⟨H₄, h5₄, hz₄⟩ => ?_)
  have hlen : (VG.Proof.AesOcb.Arm.aadOf p t.mem).length = p.al := Proof.Ocb.length_bytesAt _ _ _
  have hdrop : ((VG.Proof.AesOcb.Arm.aadOf p t.mem).drop (16 * ((VG.Proof.AesOcb.Arm.aadOf p t.mem).length / 16))).length = p.al % 16 := by
    rw [List.length_drop, hlen]; omega
  have heq := Proof.Ocb.hash_eq (VG.Proof.AesOcb.Arm.ciphOf p t.mem) (VG.Proof.AesOcb.Arm.lstarOf p t.mem) (VG.Proof.AesOcb.Arm.aadOf p t.mem)
  rw [hdrop, hlen] at heq
  refine WP.ite (decide (p.al % 16 = 0)) (eval_eq' hz₄) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : p.al % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₄.env, H₄.frame, H₄.rd, H₄.wr, ?_⟩
    rw [H₄.sum, heq]; simp only [show ¬ p.al % 16 > 0 by omega, ↓reduceIte]
  · have h0 : p.al % 16 ≠ 0 := by simpa using hb
    refine WP.mono (VG.Proof.AesOcb.Arm.hashRest_ok L H₄ h5₄ h0) fun t' ⟨E', fr', rd', wr', sum'⟩ => ⟨E', fr', rd', wr', ?_⟩
    rw [sum', heq]; simp only [show p.al % 16 > 0 by omega, ↓reduceIte, hlen]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Pass`. -/
section

/-!
# AES-OCB on ARMv7: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xorB_wp`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`, as on AArch64
(`Proof.AesOcb.AArch64.pass_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_ne' z_subFlags dec32 z_dec)

/-- The data block at offset `k` of the data, as a 64-bit address. -/
theorem dA {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {k : Nat} (h : k + 16 ≤ p.n) :
    State.addr (p.D + BitVec.ofNat 32 k) = State.addr p.D + BitVec.ofNat 64 k :=
  addr_add (by have := L.dw; omega)

/-- What a body does to the block at `B` (in `r4`) and the checksum, with the
offset at `W + ofsO`. -/
def BodyOk (p : VG.Proof.AesOcb.Arm.Prm) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (k : Nat), VG.Proof.AesOcb.Arm.Env p t → t.gpr .r4 = p.D + BitVec.ofNat 32 k → k + 16 ≤ p.n →
    WP isa (.block body) t fun t' =>
      blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 k) =
        fB (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k))
          (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k)) (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      VG.Proof.AesOcb.Arm.Others [.r0, .r1] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr

section
variable {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p)
include L

theorem bW {k : Nat} (h : k + 16 ≤ p.n) :
    (⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ :=
  (L.d_w' (by decide)).sub_left (Offset.sub_base _ h)

theorem bO {k : Nat} (h : k + 16 ≤ p.n) :
    (⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ :=
  (L.d_w' (by decide)).sub_left (Offset.sub_base _ h)

/-- `(r4) ⊕= W + ofsO`. -/
theorem xorOfs_wp {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {k : Nat} (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 k)
    (hk : k + 16 ≤ p.n) :
    WP isa (.block xorOfs) t (VG.Proof.AesOcb.Arm.Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.D + BitVec.ofNat 64 k)
      (State.addr p.D + BitVec.ofNat 64 k) (State.addr p.W + BitVec.ofNat 64 ofsO)) t) := by
  have fw := L.ww
  have fd := L.dw
  have e := VG.Proof.AesOcb.Arm.dA L hk
  have := VG.Proof.AesOcb.Arm.xorB_wp (s := t) (pb := .r4) (qb := .r11) (cb := .r4) (pd := 0) (qd := ofsO) (cd := 0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega) (by rw [E.r11]; simp only [ofsO]; omega)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega)))
    (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega))
  rw [h4, E.r11, e, BitVec.add_zero] at this
  exact this

/-- `W + ckO ⊕= (r4)`. -/
theorem addCk_wp {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {k : Nat} (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 k)
    (hk : k + 16 ≤ p.n) :
    WP isa (.block addCk) t (VG.Proof.AesOcb.Arm.Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.W + BitVec.ofNat 64 ckO)
      (State.addr p.W + BitVec.ofNat 64 ckO) (State.addr p.D + BitVec.ofNat 64 k)) t) := by
  have fw := L.ww
  have fd := L.dw
  have e := VG.Proof.AesOcb.Arm.dA L hk
  have := VG.Proof.AesOcb.Arm.xorB_wp (s := t) (pb := .r11) (qb := .r4) (cb := .r11) (pd := ckO) (qd := 0) (cd := ckO) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [E.r11]; simp only [ckO]; omega)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega) (by rw [E.r11]; simp only [ckO]; omega)
    (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega)))
    (by rw [E.r11]; exact E.perm.wC (by decide))
  rw [h4, E.r11, e, BitVec.add_zero] at this
  exact this

theorem xorOfs_ok : VG.Proof.AesOcb.Arm.BodyOk p xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t k E h4 hk
  refine WP.mono (VG.Proof.AesOcb.Arm.xorOfs_wp L E h4 hk) fun t' R => ⟨?_, ?_, ?_, R.gpr, R.sp, R.rd, R.wr⟩
  · rw [R.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (VG.Proof.AesOcb.Arm.bO L hk))]
  · rw [R.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesOcb.Arm.bW L hk).symm)]
  · rw [R.mem]; exact (Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp)

theorem sealPre_ok : VG.Proof.AesOcb.Arm.BodyOk p (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t k E h4 hk
  refine WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.addCk_wp L E h4 hk) fun t₁ R₁ => ?_)
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fr₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  refine WP.mono (VG.Proof.AesOcb.Arm.xorOfs_wp L E₁ (by rw [R₁.gpr _ (by decide), h4]) hk) fun t₂ R₂ =>
    ⟨?_, ?_, ?_, fun r hr => by rw [R₂.gpr r hr, R₁.gpr r hr], by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd],
      by rw [R₂.wr, R₁.wr]⟩
  · rw [R₂.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (VG.Proof.AesOcb.Arm.bO L hk)),
      blockAtMem_frame fr₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.Arm.bW L hk),
      blockAtMem_frame fr₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))]
  · rw [R₂.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesOcb.Arm.bW L hk).symm), R₁.mem,
      VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (VG.Proof.AesOcb.Arm.bW L hk).symm)]
  · rw [R₂.mem]
    exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))

theorem openPost_ok : VG.Proof.AesOcb.Arm.BodyOk p (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t k E h4 hk
  refine WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.xorOfs_wp L E h4 hk) fun t₁ R₁ => ?_)
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fr₁ : Frame [⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have b₁ : blockAtMem t₁.mem (State.addr p.D + BitVec.ofNat 64 k) =
      blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k) ^^^ blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) := by
    rw [R₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (VG.Proof.AesOcb.Arm.bO L hk))]
  refine WP.mono (VG.Proof.AesOcb.Arm.addCk_wp L E₁ (by rw [R₁.gpr _ (by decide), h4]) hk) fun t₂ R₂ =>
    ⟨?_, ?_, ?_, fun r hr => by rw [R₂.gpr r hr, R₁.gpr r hr], by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd],
      by rw [R₂.wr, R₁.wr]⟩
  · rw [R₂.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.Arm.bW L hk), b₁]
  · rw [R₂.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (VG.Proof.AesOcb.Arm.bW L hk).symm), b₁,
      blockAtMem_frame fr₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesOcb.Arm.bW L hk).symm)]
  · rw [R₂.mem]
    exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))

end

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr]

/-- What a pass writes, over `m` blocks. -/
abbrev passR (p : VG.Proof.AesOcb.Arm.Prm) (m : Nat) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨State.addr p.D, 16 * m⟩]

/-- A pass over the `m` whole blocks of the data (`X k` at its start, `t₀`),
after `i` of them. -/
structure PassInv (p : VG.Proof.AesOcb.Arm.Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t
  frame : Frame (VG.Proof.AesOcb.Arm.passR p m) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * i)
  r6 : t.gpr .r6 = BitVec.ofNat 32 (i + 1)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (m - i)
  ofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.passRegs t₀ t

theorem pass_step {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.Arm.BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    (hm : 16 * m ≤ p.n) {t₀ t : State} {i : Nat} (hi : i < m) (P : VG.Proof.AesOcb.Arm.PassInv p m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      VG.Proof.AesOcb.Arm.PassInv p m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.z = decide (i + 1 = m) := by
  have fw := L.ww
  have n32 := L.n_lt
  have E := P.env
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (VG.Proof.AesOcb.Arm.lNtz_ok L E (i := i + 1) (by omega) (by omega) P.r6 P.l0) fun t₁ P₁ => ?_))
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others P₁.gpr P₁.sp P₁.rd P₁.wr
  refine WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t₁) (pb := .r11) (qb := .r11) (cb := .r11) (pd := ofsO) (qd := lO) (cd := ofsO)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [E₁.r11]; simp only [ofsO]; omega) (by rw [E₁.r11]; simp only [lO]; omega)
    (by rw [E₁.r11]; simp only [ofsO]; omega) (by rw [E₁.r11]; exact E₁.perm.wCR (by decide))
    (by rw [E₁.r11]; exact E₁.perm.wCR (by decide)) (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_
  rw [E₁.r11] at R₂
  have E₂ : VG.Proof.AesOcb.Arm.Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have g₂ : ∀ r, r ∉ VG.Proof.AesOcb.Arm.ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    have h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [R₂.gpr r h', P₁.gpr r hr]
  have fW₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]; exact (P₁.frame.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  have kD₂ : ∀ {k : Nat}, k + 16 ≤ p.n → blockAtMem t₂.mem (State.addr p.D + BitVec.ofNat 64 k) =
      blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k) := fun hk =>
    blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hk)
  have ofs₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [R₂.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inl (by decide)) (by decide) (by decide))),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      P.ofs, P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  have Bi₂ : blockAtMem t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kD₂ (by omega), P.blk i hi]; simp
  -- the body
  refine WP.block_append (WP.mono (hB t₂ (16 * i) E₂ (by rw [g₂ _ (by decide), P.r4]) (by omega))
    fun t₃ ⟨blk₃, ck₃, fr₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  have g₃' : ∀ r, r ∉ VG.Proof.AesOcb.Arm.ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    have h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [g₃ r h', g₂ r hr]
  have r4₃ : t₃.gpr .r4 = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₃' _ (by decide), P.r4]
  have r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 (m - i) := by rw [g₃' _ (by decide), P.r5]
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (i + 1) := by rw [g₃' _ (by decide), P.r6]
  refine WP.of_runBlock ⟨_, by orun [nextBlock, r4₃, r5₃, r6₃], ?_⟩
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ →
      blockAtMem t₃.mem Q = blockAtMem t₂.mem Q := fun h₁ h₂ =>
    blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂)
  refine ⟨⟨E₂.of_others (rs := [.r0, .r1, .r4, .r5, .r6]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ↓reduceIte]
      exact g₃ r (by simp [hr.1, hr.2.1])) (by simp [sp_setReg, Proof.AesGcm.Arm.sp_subFlags, sp₃])
      (by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, rd₃]) (by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, wr₃]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, Offset.sub_base _ (by omega)⟩
      · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
  · simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, rd₃, R₂.rd, P₁.rd, P.rd]
  · simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, wr₃, R₂.wr, P₁.wr, P.wr]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ← BitVec.ofNat_add]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hi (by omega)]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kB₃ (VG.Proof.AesOcb.Arm.bO L (by omega)).symm (L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    by_cases hki : k = i
    · subst hki
      rw [blk₃, Bi₂, ofs₂]; simp
    · rw [kB₃ (Offset.disjoint _ (by omega) (by omega) (by have := L.dw; omega)) (VG.Proof.AesOcb.Arm.bW L (by omega)),
        kD₂ (by omega), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    have l0D : (⟨State.addr p.W + BitVec.ofNat 64 l0O, 16⟩ : Region).Disjoint
        ⟨State.addr p.D + BitVec.ofNat 64 (16 * i), 16⟩ :=
      ((L.d_w' (d := l0O) (k := 16) (by decide)).sub_left (Offset.sub_base _ (by omega))).symm
    rw [kB₃ l0D (L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  · simp only [VG.Proof.AesOcb.Arm.passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, ite_false]
    rw [g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      P.gpr r (by simp [VG.Proof.AesOcb.Arm.passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · simp only [z_setReg, z_subFlags, dec32 hi (by omega), z_dec hi (by omega)]

theorem pass_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.Arm.BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    (hm : 16 * m ≤ p.n) (hm0 : 0 < m) {t₀ t : State} (P : VG.Proof.AesOcb.Arm.PassInv p m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => VG.Proof.AesOcb.Arm.PassInv p m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ VG.Proof.AesOcb.Arm.PassInv p m O0 l X fB ckF t₀ u i) ?_
    (m - 0) _ ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (VG.Proof.AesOcb.Arm.pass_step L hB hckF hm hi P) fun u' ⟨P', z⟩ => ?_
  by_cases he : i + 1 = m
  · left
    exact ⟨(eval_ne' z).trans (by simp [he]), he ▸ P'⟩
  · right
    exact ⟨(eval_ne' z).trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Whole`. -/
section

/-!
# AES-OCB on ARMv7: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`, as on AArch64
(`Proof.AesOcb.AArch64.whole_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (below)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called, the data and the stack below `SP`. -/
abbrev wholeR (p : VG.Proof.AesOcb.Arm.Prm) (m : Nat) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 512, 2048⟩, ⟨State.addr p.D, 16 * m⟩, below p.SP]

theorem wholeR_mut {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m : Nat} (hm : 16 * m ≤ p.n) {M M' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.wholeR p m) M M') :
    Frame (VG.Proof.AesOcb.Arm.mutR p) M M' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
  · simpa using VG.Proof.AesOcb.Arm.data_mut L (a := 0) (l := 16 * m) (by omega)
  · exact VG.Proof.AesOcb.Arm.below_mut L

/-- The registers `whole` writes. -/
abbrev wholeRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr]

/-- What `whole` leaves. -/
structure WholePost (p : VG.Proof.AesOcb.Arm.Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  frame : Frame (VG.Proof.AesOcb.Arm.wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck
  gpr : VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.wholeRegs t t'

/-- The start of a pass: `r4 ← D`, `r5 ← m`, `r6 ← 1`. -/
theorem passStart_run {p : VG.Proof.AesOcb.Arm.Prm} {t : State} (h8 : t.gpr .r8 = p.D) {m : Nat} (h7 : t.gpr .r7 = BitVec.ofNat 32 m) :
    ∃ t', runBlock isa passStart t = some t' ∧
      t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * 0) ∧ t'.gpr .r5 = BitVec.ofNat 32 (m - 0) ∧
      t'.gpr .r6 = BitVec.ofNat 32 (0 + 1) ∧ VG.Proof.AesOcb.Arm.Ran [.r4, .r5, .r6] t.mem t t' := by
  refine ⟨_, by orun [passStart], ?_, ?_, ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
  · simp [gpr_setReg, h8]
  · simp [gpr_setReg, h7]
  · simp [gpr_setReg]

theorem passR_mut {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m : Nat} (hm : 16 * m ≤ p.n) {M M' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.passR p m) M M') :
    Frame (VG.Proof.AesOcb.Arm.mutR p) M M' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
  · simpa using VG.Proof.AesOcb.Arm.data_mut L (a := 0) (l := 16 * m) (by omega)

theorem whole_ok (F : VG.Proof.AesOcb.Arm.BlkFn) {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    {ckF1 ckF2 : Nat → Block} {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p)
    (hB1 : VG.Proof.AesOcb.Arm.BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : VG.Proof.AesOcb.Arm.BodyOk p post (fun b o => b ^^^ o) fC2)
    {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {m : Nat} (hmn : 16 * m ≤ p.n) (hm0 : 0 < m) {O0 l : Block}
    (h8 : t.gpr .r8 = p.D) (h7 : t.gpr .r7 = BitVec.ofNat 32 m)
    (hofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) =
      fC1 (ckF1 i) (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (F.ciph p.R (VG.Proof.AesOcb.Arm.sched p t.mem) (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole (VG.Proof.AesOcb.Arm.blkFrame F) pre post) t (VG.Proof.AesOcb.Arm.WholePost p m O0 l
      (fun k => F.ciph p.R (VG.Proof.AesOcb.Arm.sched p t.mem)
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have fw := L.ww
  have fd := L.dw
  have n32 := L.n_lt
  -- the first pass
  obtain ⟨s₁, run₁, r4₁, r5₁, r6₁, R₁⟩ := VG.Proof.AesOcb.Arm.passStart_run h8 h7
  have E₁ : VG.Proof.AesOcb.Arm.Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have P₀ : VG.Proof.AesOcb.Arm.PassInv p m O0 l (fun k => blockAtMem s₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, r4 := r4₁, r6 := r6₁, r5 := r5₁
      ofs := by rw [R₁.mem, hofs]; rfl
      ck := by rw [R₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [R₁.mem, hl0]
      gpr := fun _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.pass_ok L hB1 (fun i _ => by rw [hckF1, R₁.mem]) hmn hm0 P₀) fun s₂ P₂ => ?_)
  have E₂ := P₂.env
  have r8₂ : s₂.gpr .r8 = p.D := by rw [P₂.gpr _ (by decide), R₁.gpr _ (by decide), h8]
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 m := by rw [P₂.gpr _ (by decide), R₁.gpr _ (by decide), h7]
  -- the call
  refine WP.seq (WP.of_runBlock ⟨_, by orun [callArgs, E₂.r9, E₂.r10, E₂.r11, r8₂, r7₂], ?_⟩)
  have hB := VG.Proof.AesOcb.Arm.blkFrame_ok F L (t := ((((((s₂.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 p.D).setReg .r3 (BitVec.ofNat 32 m))))
    (D := p.D) (n := m) (E₂.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac)
      (by rfl) (by rfl) (by rfl)) (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by omega)
      (Proof.AesGcm.Arm.covers_prefix E₂.perm.d hmn) (L.k_d.sub_right (Region.sub_prefix hmn))
      ((L.d_w' (d := scrO) (k := 2048) (by decide)).sub_left (Region.sub_prefix hmn))
      (L.bd.sub_right (Region.sub_prefix hmn))
  refine WP.seq (WP.mono hB fun s₃ C₃ => ?_)
  have g₃ : ∀ r ∈ VG.Proof.AesOcb.Arm.keptRegs, s₃.gpr r = s₂.gpr r := fun r hr => by
    rw [C₃.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  have E₃ : VG.Proof.AesOcb.Arm.Env p s₃ := E₂.keep (fun r hr => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    (by rw [C₃.sp]; rfl) (by rw [C₃.rd]; rfl) (by rw [C₃.wr]; rfl)
  have kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩ →
      (⟨Q, 16⟩ : Region).Disjoint (below p.SP) → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ h₃ => blockAtMem_frame C₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  have dW : ∀ {d : Nat}, d + 16 ≤ 512 → (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint
      ⟨State.addr p.D, 16 * m⟩ := fun hd =>
    ((L.d_w' (k := 16) (by omega)).sub_left (Region.sub_prefix hmn)).symm
  have kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [kC (dW (by omega)) (L.w_w (.inl (by simp only [scrO]; omega)) (by omega) (by decide))
          (L.bw' (by omega)).symm,
        blockAtMem_frame P₂.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) (by omega) (by decide)
          · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) (by omega) (by decide)
          · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) (by omega) (by decide)
          · exact dW (by omega))]
  have o0₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0 := by
    rw [kWP (by decide), R₁.mem, ho0]
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.copy16_wp (t := s₃) (W := State.addr p.W) (sO := o0O) (dO := ofsO)
    (by rw [E₃.r11]) (by decide) (by decide) (by rw [E₃.r11]; omega) (by decide) (by decide)
    (E₃.perm.wCR (by decide)) (E₃.perm.wC (by decide))) fun s₄a R₄ => ?_))
  have E₄a : VG.Proof.AesOcb.Arm.Env p s₄a := E₃.of_others R₄.gpr R₄.sp R₄.rd R₄.wr
  have r8₄ : s₄a.gpr .r8 = p.D := by rw [R₄.gpr _ (by decide), g₃ _ (by decide), r8₂]
  have r7₄ : s₄a.gpr .r7 = BitVec.ofNat 32 m := by rw [R₄.gpr _ (by decide), g₃ _ (by decide), r7₂]
  obtain ⟨s₄, run₄, r4₄, r5₄, r6₄, R₄'⟩ := VG.Proof.AesOcb.Arm.passStart_run r8₄ r7₄
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have E₄ : VG.Proof.AesOcb.Arm.Env p s₄ := E₄a.of_others R₄'.gpr R₄'.sp R₄'.rd R₄'.wr
  have m₄ : s₄.mem = VG.Proof.AesOcb.Arm.copyMem s₃.mem (State.addr p.W + BitVec.ofNat 64 o0O) (State.addr p.W + BitVec.ofNat 64 ofsO) := by
    rw [R₄'.mem, R₄.mem]
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ →
      blockAtMem s₄.mem Q = blockAtMem s₃.mem Q := fun hQ => by
    rw [m₄]; exact blockAtMem_frame (VG.Proof.AesOcb.Arm.copyMem_frame _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hQ
  have hsched : VG.Proof.AesOcb.Arm.sched p s₂.mem = VG.Proof.AesOcb.Arm.sched p t.mem := by
    rw [VG.Proof.AesOcb.Arm.sched_mut L (VG.Proof.AesOcb.Arm.passR_mut L hmn P₂.frame), R₁.mem]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) =
      F.ciph p.R (VG.Proof.AesOcb.Arm.sched p t.mem)
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) := fun k hk => by
    rw [kB₄ (VG.Proof.AesOcb.Arm.bO L (by omega)), C₃.out k hk]
    simp only [mem_setReg]
    rw [hsched, P₂.blk k hk]
    simp only [hk, ↓reduceIte, R₁.mem]
  have ck₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC (dW (by decide)) (L.w_w (.inl (by decide)) (by decide) (by decide)) (L.bw' (by decide)).symm,
      P₂.ck, hckF2₀]
  have P₀' : VG.Proof.AesOcb.Arm.PassInv p m O0 l (fun k => blockAtMem s₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, r4 := r4₄, r6 := r6₄, r5 := r5₄
      ofs := by rw [m₄, VG.Proof.AesOcb.Arm.blockAtMem_copy, o0₃]; rfl
      ck := by rw [kB₄ (L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by rw [kB₄ (L.w_w (.inr (by decide)) (by decide) (by decide)), kWP (by decide), R₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (VG.Proof.AesOcb.Arm.pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hmn hm0 P₀') fun s₅ P₅ => ?_
  have subW : ∀ r ∈ VG.Proof.AesOcb.Arm.passR p m, ∃ r' ∈ VG.Proof.AesOcb.Arm.wholeR p m, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, R₄'.rd, R₄.rd, C₃.rd]; simp only [rd_setReg]; rw [P₂.rd, R₁.rd],
    by rw [P₅.wr, R₄'.wr, R₄.wr, C₃.wr]; simp only [wr_setReg]; rw [P₂.wr, R₁.wr], fun k hk => ?_, P₅.ofs, P₅.ck, fun r hr => ?_⟩
  · rw [← R₁.mem]
    refine (P₂.frame.sub subW).trans ((C₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp [scrO], fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact ((VG.Proof.AesOcb.Arm.copyMem_frame _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
          (by decide)⟩).trans (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]
  · simp only [VG.Proof.AesOcb.Arm.wholeRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have hk : r ∈ VG.Proof.AesOcb.Arm.keptRegs := by
      simp only [VG.Proof.AesOcb.Arm.keptRegs, List.mem_cons, List.not_mem_nil, or_false]
      cases r <;> simp_all
    rw [P₅.gpr r (by simp [VG.Proof.AesOcb.Arm.passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      R₄'.gpr r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      R₄.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), g₃ r hk,
      P₂.gpr r (by simp [VG.Proof.AesOcb.Arm.passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      R₁.gpr r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1])]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.RestTag`. -/
section

/-!
# AES-OCB on ARMv7: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)`, XORs the last
`r` bytes of the data with it (`xorLoop`) and adds their padding to the
checksum (`padCk`), before the XOR for `seal` and after it for `open`
(`rest_ok`); `tag d` writes `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ Sum` to
`W + d` (`tag_ok`), as on AArch64 (`Proof.AesOcb.AArch64.rest_ok`,
`Proof.AesOcb.AArch64.tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz pad)
open VG.Proof.Ocb (offAt blockAtMem_frame length_bytesAt)
open VG.Proof.AesGcm.Arm (below xorLoop_ok xorBytes LoopPre)

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (blockAtMem m Q)) := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = r + (16 - r) by omega,
    Proof.Ocb.bytesAt_append, VG.Proof.AesOcb.Arm.xor_append_right _ _ _ (by rw [hl, length_bytesAt])]

/-- The last `r` bytes of the data, from offset `a`. -/
structure Tail (p : VG.Proof.AesOcb.Arm.Prm) (a r : Nat) : Prop where
  fit : a + r ≤ p.n
  pos : 0 < r
  lt : r < 16

namespace Tail

variable {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {a r : Nat} (T : VG.Proof.AesOcb.Arm.Tail p a r)
include L T

theorem addr : State.addr (p.D + BitVec.ofNat 32 a) = State.addr p.D + BitVec.ofNat 64 a :=
  addr_add (by have := L.dw; have := T.fit; have := T.pos; omega)

theorem toNat : (p.D + BitVec.ofNat 32 a).toNat = p.D.toNat + a := by
  have := L.dw; have := T.fit; have := T.pos
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (by omega)]

omit L in
theorem sub : Region.Sub ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ ⟨State.addr p.D, p.n⟩ :=
  Offset.sub_base _ T.fit

theorem w {d k : Nat} (h : d + k ≤ 2560) :
    (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  (L.d_w' h).sub_left T.sub

end Tail

/-- What the head of `rest` leaves: `Offset_*` at `W + ofsO` and `Pad` at
`W + tmpO`. -/
structure RestHead (p : VG.Proof.AesOcb.Arm.Prm) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] t.mem t'.mem
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem
  tmp : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
    VG.Proof.AesOcb.Arm.ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem)
  saved : ∀ r ∈ VG.Proof.AesOcb.Arm.keptRegs, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) :
    WP isa (.seq (.block (xorB .r11 .r10 .r11 ofsO 240 ofsO ++ copy16 ofsO tmpO)) (encOne tmpO)) t
      (VG.Proof.AesOcb.Arm.RestHead p t) := by
  have fw := L.ww
  have fk := L.kw
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.xorB_wp (s := t) (pb := .r11) (qb := .r10) (cb := .r11) (pd := ofsO)
    (qd := 240) (cd := ofsO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [E.r11]; simp only [ofsO]; omega) (by rw [E.r10]; omega)
    (by rw [E.r11]; simp only [ofsO]; omega) (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [E.r10]; exact E.perm.kC (by decide)) (by rw [E.r11]; exact E.perm.wC (by decide))) fun t₁ R₁ => ?_))
  rw [E.r11, E.r10] at R₁
  have E₁ : VG.Proof.AesOcb.Arm.Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  refine WP.mono (VG.Proof.AesOcb.Arm.copy16_wp (t := t₁) (W := State.addr p.W) (sO := ofsO) (dO := tmpO) (by rw [E₁.r11])
    (by decide) (by decide) (by rw [E₁.r11]; omega) (by decide) (by decide) (E₁.perm.wCR (by decide))
    (E₁.perm.wC (by decide))) fun t₂ R₂ => ?_
  have E₂ : VG.Proof.AesOcb.Arm.Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have kOW : (⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint ⟨State.addr p.K + BitVec.ofNat 64 240, 16⟩ :=
    (L.k_w' (by decide)).symm.sub_right (Offset.sub_base _ (by decide))
  have ofs₁ : blockAtMem t₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem := by
    rw [R₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint kOW)]; rfl
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem, R₁.mem]
    exact ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp)).trans ((VG.Proof.AesOcb.Arm.copyMem_frame _ _ _).mono (by simp))
  have tmp₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem := by
    rw [R₂.mem, VG.Proof.AesOcb.Arm.blockAtMem_copy, ofs₁]
  refine WP.mono (VG.Proof.AesOcb.Arm.encOne_ok L E₂ (d := tmpO) (by decide) (by decide)) fun t₃ C₃ => ?_
  have hs : VG.Proof.AesOcb.Arm.sched p t₂.mem = VG.Proof.AesOcb.Arm.sched p t.mem :=
    VG.Proof.AesOcb.Arm.sched_mut L (fr₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide)))
  refine ⟨C₃.env E₂, ?_, ?_, ?_, fun r hr => ?_, by rw [C₃.rd, R₂.rd, R₁.rd], by rw [C₃.wr, R₂.wr, R₁.wr]⟩
  · refine (fr₂.mono (by simp)).trans (C₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [blockAtMem_frame C₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm), R₂.mem, blockAtMem_frame (VG.Proof.AesOcb.Arm.copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      ofs₁]
  · have := C₃.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, VG.Proof.AesOcb.Arm.encF_ciph, tmp₂, hs]
  · rw [C₃.saved r hr, R₂.gpr r (fun h => by
      simp only [VG.Proof.AesOcb.Arm.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h),
      R₁.gpr r (fun h => by
      simp only [VG.Proof.AesOcb.Arm.keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h)]

/-- `W + d ← (W + d) ⊕ (W + s)`. -/
theorem xorW_wp {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) :
    WP isa (.block (xorW s d)) t (VG.Proof.AesOcb.Arm.Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.W + BitVec.ofNat 64 d)
      (State.addr p.W + BitVec.ofNat 64 d) (State.addr p.W + BitVec.ofNat 64 s)) t) := by
  have fw := L.ww
  have := VG.Proof.AesOcb.Arm.xorB_wp (s := t) (pb := .r11) (qb := .r11) (cb := .r11) (pd := d) (qd := s) (cd := d) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (by rw [E.r11]; omega) (by rw [E.r11]; omega) (by rw [E.r11]; omega) (by rw [E.r11]; exact E.perm.wCR hd)
    (by rw [E.r11]; exact E.perm.wCR hs) (by rw [E.r11]; exact E.perm.wC hd)
  rw [E.r11] at this
  exact this

theorem xorW_val {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) (m : Mem) {s d : Nat} (h : s + 16 ≤ d ∨ d + 16 ≤ s) (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) :
    blockAtMem (Proof.Cmac.xor4Mem m (State.addr p.W + BitVec.ofNat 64 d) (State.addr p.W + BitVec.ofNat 64 d)
      (State.addr p.W + BitVec.ofNat 64 s)) (State.addr p.W + BitVec.ofNat 64 d) =
      blockAtMem m (State.addr p.W + BitVec.ofNat 64 d) ^^^ blockAtMem m (State.addr p.W + BitVec.ofNat 64 s) :=
  VG.Proof.AesOcb.Arm.blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (L.w_w (by omega) hd hs))

/-- `padCk`: the checksum with the padded `r` bytes at `D + a`. -/
theorem padCk_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) {a r : Nat} (T : VG.Proof.AesOcb.Arm.Tail p a r)
    (h4 : s.gpr .r4 = p.D + BitVec.ofNat 32 a) (h5 : s.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa padCk s fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
        pad (bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 a) r) ∧
      VG.Proof.AesOcb.Arm.Others VG.Proof.AesOcb.Arm.padRegs s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have := L.dw; have := T.fit; have := L.n_lt
  unfold padCk
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.padTo_ok L E (S := p.D + BitVec.ofNat 32 a) (n := r) (d := t2O) T.pos T.lt (by decide)
    (by decide) h4 h5 (by rw [T.toNat L]; omega)
    (by rw [T.addr L]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d T.fit (by omega)))
    (by rw [T.addr L]; exact T.w L (by decide))) fun t₁ ⟨fr₁, b₁, O₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ := E.of_others O₁ sp₁ rd₁ wr₁
  refine WP.mono (VG.Proof.AesOcb.Arm.xorW_wp L E₁ (s := t2O) (d := ckO) (by decide) (by decide)) fun t₂ R₂ => ?_
  refine ⟨?_, ?_, fun r hr => ?_, by rw [R₂.sp, sp₁], by rw [R₂.rd, rd₁], by rw [R₂.wr, wr₁]⟩
  · rw [R₂.mem]; exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  · rw [R₂.mem, VG.Proof.AesOcb.Arm.xorW_val L _ (by decide) (by decide) (by decide), b₁, blockAtMem_frame fr₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      T.addr L]
  · rw [R₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with rfl | rfl <;> simp)), O₁ r hr]

/-- `xorPad`: the `r` bytes at `D + a` XORed with the first `r` bytes at
`W + tmpO`. -/
theorem xorPad_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) {a r : Nat} (T : VG.Proof.AesOcb.Arm.Tail p a r)
    (h4 : s.gpr .r4 = p.D + BitVec.ofNat 32 a) (h5 : s.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa xorPad s fun t => t.mem = VG.WriteBytes.writeBytes s.mem (State.addr p.D + BitVec.ofNat 64 a)
        (Spec.Ocb.xor (bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 a) r)
          (bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 tmpO) r)) ∧
      VG.Proof.AesOcb.Arm.Others [.r0, .r1, .r2, .r3, .r12] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww; have := L.dw; have := T.fit; have := L.n_lt; have := T.lt
  have he : encodable (BitVec.ofNat 32 112) = true := by decide
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨_, by orun [he, E.r11, h4, h5], ?_⟩)
  refine WP.mono (xorLoop_ok _ (S := p.W + BitVec.ofNat 32 tmpO) (D := p.D + BitVec.ofNat 32 a) (n := r)
    ⟨by simp [gpr_setReg, tmpO], by simp [gpr_setReg, h4], by simp [gpr_setReg, h5], T.pos, by omega,
      by rw [L.wN (by decide)]; simp only [tmpO]; omega, by rw [T.toNat L]; omega,
      by simp only [rd_setReg, wr_setReg, L.wA (show tmpO < 2560 by decide)]; exact E.perm.wCR (by simp only [tmpO]; omega),
      by simp only [wr_setReg, T.addr L]; exact Proof.AesGcm.Arm.covers_off E.perm.d T.fit (by omega),
      by rw [T.addr L, L.wA (by decide)]; exact (T.w L (by simp only [tmpO]; omega)).symm⟩) fun t ⟨m, O⟩ => ?_
  refine ⟨?_, fun r hr => ?_, by rw [O.sp]; rfl, by rw [O.rd]; rfl, by rw [O.wr]; rfl⟩
  · rw [m]; simp only [mem_setReg, T.addr L, L.wA (show tmpO < 2560 by decide)]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [O.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_setReg, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]

/-- What `rest` leaves: `Offset_*`, the data XORed with `Pad`, and the
checksum with the padded plaintext (before the XOR for `seal`, after it for
`open`). -/
structure RestPost (enc : Bool) (p : VG.Proof.AesOcb.Arm.Prm) (a r : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem
  out : bytesAt t'.mem (State.addr p.D + BitVec.ofNat 64 a) r = Spec.Ocb.xor
    (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r)
    (Spec.Ocb.toBytes (VG.Proof.AesOcb.Arm.ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem)))
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (State.addr p.D + BitVec.ofNat 64 a) r)
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (enc : Bool) {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {a r : Nat} (T : VG.Proof.AesOcb.Arm.Tail p a r)
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 a) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa (rest enc) t (VG.Proof.AesOcb.Arm.RestPost enc p a r t) := by
  have := T.lt
  unfold rest
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.Arm.restHead_ok L E) fun t₃ H => ?_))
  have h4₃ : t₃.gpr .r4 = p.D + BitVec.ofNat 32 a := by rw [H.saved _ (by decide), h4]
  have h5₃ : t₃.gpr .r5 = BitVec.ofNat 32 r := by rw [H.saved _ (by decide), h5]
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => T.w L h
  have dH : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP],
      (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact (L.bd.sub_right T.sub).symm
  have dT : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dTmp : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have dOfs : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have pP₃ : bytesAt t₃.mem (State.addr p.D + BitVec.ofNat 64 a) r = bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r :=
    Proof.Cmac.bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r) (Spec.Ocb.toBytes ys)).length = r :=
    fun ys => by simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r →
      Frame [⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] m (VG.WriteBytes.writeBytes m (State.addr p.D + BitVec.ofNat 64 a) xs) :=
    fun m xs h => VG.WriteBytes.writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  have xP : ∀ u : State, bytesAt u.mem (State.addr p.D + BitVec.ofNat 64 a) r =
        bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r →
      blockAtMem u.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
        blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 tmpO) →
      bytesAt (VG.WriteBytes.writeBytes u.mem (State.addr p.D + BitVec.ofNat 64 a)
        (Spec.Ocb.xor (bytesAt u.mem (State.addr p.D + BitVec.ofNat 64 a) r)
          (bytesAt u.mem (State.addr p.W + BitVec.ofNat 64 tmpO) r))) (State.addr p.D + BitVec.ofNat 64 a) r =
        Spec.Ocb.xor (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r) (Spec.Ocb.toBytes
          (VG.Proof.AesOcb.Arm.ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem))) := by
    intro u hu ht
    rw [hu, VG.Proof.AesOcb.Arm.xor_bytesAt_block _ _ _ hl (by omega), ht, H.tmp,
      Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have dCk : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP],
      (⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have ck₃ : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have E₃ := H.env
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.xorPad_ok L E₃ T h4₃ h5₃) fun t₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.of_others g₄ sp₄ rd₄ wr₄
    have fr₄ : Frame [⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t₃.mem t₄.mem := by
      rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (VG.Proof.AesOcb.Arm.padCk_ok L E₄ T (by rw [g₄ _ (by decide), h4₃]) (by rw [g₄ _ (by decide), h5₃]))
      fun t₅ ⟨fr₅, ck₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have p₅ : bytesAt t₅.mem (State.addr p.D + BitVec.ofNat 64 a) r = bytesAt t₄.mem (State.addr p.D + BitVec.ofNat 64 a) r :=
      Proof.Cmac.bytesAt_frame fr₅ dT (by omega)
    refine ⟨E₄.of_others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.padCk_ok L E₃ T h4₃ h5₃) fun t₄ ⟨fr₄, ck₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.of_others g₄ sp₄ rd₄ wr₄
    have p₄ : bytesAt t₄.mem (State.addr p.D + BitVec.ofNat 64 a) r = bytesAt t₃.mem (State.addr p.D + BitVec.ofNat 64 a) r :=
      Proof.Cmac.bytesAt_frame fr₄ dT (by omega)
    refine WP.mono (VG.Proof.AesOcb.Arm.xorPad_ok L E₄ T (by rw [g₄ _ (by decide), h4₃]) (by rw [g₄ _ (by decide), h5₃]))
      fun t₅ ⟨m₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have fr₅ : Frame [⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t₄.mem t₅.mem := by
      rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E₄.of_others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ (pW (by decide)), blockAtMem_frame fr₄ dOfs, H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (blockAtMem_frame fr₄ dTmp)]
    · simp only [↓reduceIte]
      rw [blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (p : VG.Proof.AesOcb.Arm.Prm) (d : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] t.mem t'.mem
  val : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 d) =
    VG.Proof.AesOcb.Arm.ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ldO)) ^^^
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO)
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag d) t (VG.Proof.AesOcb.Arm.TagPost p d t) := by
  have fw := L.ww
  have hd' : d = 0 ∨ d = 176 := hd
  have tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩ : Region)],
        (⟨State.addr p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  unfold tag
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.copy16_wp (t := t) (W := State.addr p.W) (sO := ckO)
    (dO := tmpO) (by rw [E.r11]) (by decide) (by decide) (by rw [E.r11]; omega) (by decide) (by decide)
    (E.perm.wCR (by decide)) (E.perm.wC (by decide))) fun t₁ R₁ => ?_)))
  have E₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  refine WP.mono (VG.Proof.AesOcb.Arm.xorW_wp L E₁ (s := ofsO) (d := tmpO) (by decide) (by decide)) fun t₂ R₂ => ?_
  have E₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  refine WP.mono (VG.Proof.AesOcb.Arm.xorW_wp L E₂ (s := ldO) (d := tmpO) (by decide) (by decide)) fun t₃ R₃ => ?_
  have E₃ := E₂.of_others R₃.gpr R₃.sp R₃.rd R₃.wr
  have fr₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact VG.Proof.AesOcb.Arm.copyMem_frame _ _ _
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem := by
    rw [R₂.mem]; exact fr₁.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
  have fr₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := by
    rw [R₃.mem]; exact fr₂.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
  have tmp₃ : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ldO) := by
    rw [R₃.mem, VG.Proof.AesOcb.Arm.xorW_val L _ (by decide) (by decide) (by decide), R₂.mem, VG.Proof.AesOcb.Arm.xorW_val L _ (by decide) (by decide)
      (by decide), ← R₂.mem, blockAtMem_frame fr₂ (tW (by decide) (by decide)), R₁.mem, VG.Proof.AesOcb.Arm.blockAtMem_copy, ← R₁.mem,
      blockAtMem_frame fr₁ (tW (by decide) (by decide))]
  have hs : VG.Proof.AesOcb.Arm.sched p t₃.mem = VG.Proof.AesOcb.Arm.sched p t.mem :=
    VG.Proof.AesOcb.Arm.sched_mut L (fr₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide)))
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.encOne_ok L E₃ (d := tmpO) (by decide) (by decide)) fun t₄ C₄ => ?_)
  have E₄ := C₄.env E₃
  refine WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.copy16_wp (t := t₄) (W := State.addr p.W) (sO := tmpO) (dO := d)
    (by rw [E₄.r11]) (by decide) (by omega) (by rw [E₄.r11]; omega) (by decide) (by omega) (E₄.perm.wCR (by decide))
    (E₄.perm.wC (by omega))) fun t₅ R₅ => ?_)
  have E₅ := E₄.of_others R₅.gpr R₅.sp R₅.rd R₅.wr
  refine WP.mono (VG.Proof.AesOcb.Arm.xorW_wp L E₅ (s := sumO) (d := d) (by decide) (by omega)) fun t₆ R₆ => ?_
  have tmp₄ : blockAtMem t₄.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      VG.Proof.AesOcb.Arm.ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ldO)) := by
    have := C₄.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, VG.Proof.AesOcb.Arm.encF_ciph, tmp₃, hs]
  have dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (by simp only [sumO]; omega) (by decide) (by omega)
  have dCall : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP],
      (⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  refine ⟨E₅.of_others R₆.gpr R₆.sp R₆.rd R₆.wr, ?_, ?_,
    by rw [R₆.rd, R₅.rd, C₄.rd, R₃.rd, R₂.rd, R₁.rd], by rw [R₆.wr, R₅.wr, C₄.wr, R₃.wr, R₂.wr, R₁.wr]⟩
  · rw [R₆.mem, R₅.mem]
    refine (((fr₃.mono (by simp)).trans (C₄.frame.sub fun r hr => ?_)).trans
      ((VG.Proof.AesOcb.Arm.copyMem_frame _ _ _).mono (by simp))).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [R₆.mem, VG.Proof.AesOcb.Arm.xorW_val L _ (by simp only [sumO]; omega) (by decide) (by omega), R₅.mem, VG.Proof.AesOcb.Arm.blockAtMem_copy, tmp₄,
      blockAtMem_frame (VG.Proof.AesOcb.Arm.copyMem_frame _ _ _) dD, blockAtMem_frame C₄.frame dCall,
      blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Body`. -/
section

/-!
# AES-OCB on ARMv7: the data (`body`)

Untrusted: everything here is checked by Lean. `body` takes the whole blocks
(if any, `wholeIte_ok`) and then the rest (if any, `restIte_ok`); for `seal`
the result is `OCB-ENCRYPT`'s ciphertext, offset and checksum
(`bodySeal_ok`), for `open` `OCB-DECRYPT`'s (`bodyOpen_ok`), as on AArch64
(`Proof.AesOcb.AArch64.bodySeal_ok`, `Proof.AesOcb.AArch64.bodyOpen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm)
open VG.Proof.AesGcm.Arm (eval_eq' z_subFlags z_cmp0 and15 ofNat_sub32 below)

/-- What the whole blocks leave, if there are any. -/
structure WholeIte (p : VG.Proof.AesOcb.Arm.Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  frame : Frame (VG.Proof.AesOcb.Arm.wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck
  r8 : t'.gpr .r8 = p.D

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok (F : VG.Proof.AesOcb.Arm.BlkFn) {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    {ckF1 ckF2 : Nat → Block} {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p)
    (hB1 : VG.Proof.AesOcb.Arm.BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : VG.Proof.AesOcb.Arm.BodyOk p post (fun b o => b ^^^ o) fC2)
    {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem) {O0 l : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) =
      fC1 (ckF1 i) (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (p.n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (F.ciph p.R (VG.Proof.AesOcb.Arm.sched p s.mem) (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)])
      (.ite .eq (.block []) (whole (VG.Proof.AesOcb.Arm.blkFrame F) pre post))) s
      (VG.Proof.AesOcb.Arm.WholeIte p (p.n / 16) O0 l
        (fun k => F.ciph p.R (VG.Proof.AesOcb.Arm.sched p s.mem)
          (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (p.n / 16)) s) := by
  have n32 := L.n_lt
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₈, a₁₂, A.a8, A.a12], ?_⟩)
  refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' (by
    simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, VG.Proof.AesOcb.Arm.ofNat_lsr32 n32,
      Nat.reducePow, z_cmp0 (show p.n / 16 < 2 ^ 32 by omega)])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hm : p.n / 16 = 0 := of_decide_eq_true hb
    refine ⟨E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl), Frame.refl _ _, rfl, rfl,
      fun k hk => absurd hk (by omega), ?_, ?_, ?_⟩
    · show blockAtMem s.mem _ = _
      rw [hofs, hm]; rfl
    · show blockAtMem s.mem _ = _
      rw [hck, hm, hckF2₀, hm]
    · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]
  · have hm : p.n / 16 ≠ 0 := by simpa using hb
    refine WP.mono (VG.Proof.AesOcb.Arm.whole_ok F L hB1 hB2 (E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)) (m := p.n / 16) (O0 := O0) (l := l) (Nat.mul_div_le p.n 16)
      (by omega) (by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg])
      (by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, VG.Proof.AesOcb.Arm.ofNat_lsr32 n32]) hofs ho0 hck hl0 hckF1 hckF2₀ hckF2)
      fun t P => ⟨P.env, P.frame, P.rd, P.wr, P.blk, P.ofs, P.ck, ?_⟩
    rw [P.gpr .r8 (by decide)]
    simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]

/-- What the rest of the data leaves, if there is any: `r` bytes at `D + a`. -/
structure TailPost (enc : Bool) (p : VG.Proof.AesOcb.Arm.Prm) (a r : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem
    else blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem (State.addr p.D + BitVec.ofNat 64 a) r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r)
      (Spec.Ocb.toBytes (VG.Proof.AesOcb.Arm.ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ VG.Proof.AesOcb.Arm.lstarOf p t.mem)))
    else bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (State.addr p.D + BitVec.ofNat 64 a) r)
    else blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) (A : VG.Proof.AesOcb.Arm.Args p t.mem)
    (h8 : t.gpr .r8 = p.D) :
    WP isa (.seq (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
        .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) (.ite .eq (.block []) (rest enc))) t
      (VG.Proof.AesOcb.Arm.TailPost enc p (16 * (p.n / 16)) (p.n % 16) t) := by
  have n32 := L.n_lt
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₁₂, A.a12, h8], ?_⟩)
  refine WP.ite (decide (p.n % 16 = 0)) (eval_eq' (by
    simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15,
      VG.Proof.AesOcb.Arm.toNat_ofNat32 n32, z_cmp0 (show p.n % 16 < 2 ^ 32 by omega)])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hr : ¬ 0 < p.n % 16 := by have := of_decide_eq_true hb; omega
    refine ⟨E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl), Frame.refl _ _, rfl, rfl, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte] <;> rfl
  · have hr : 0 < p.n % 16 := by have : p.n % 16 ≠ 0 := by simpa using hb
                                 omega
    refine WP.mono (VG.Proof.AesOcb.Arm.rest_ok enc L (E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl)) ⟨by omega, hr, Nat.mod_lt _ (by decide)⟩ ?_ ?_) fun t' P =>
      ⟨P.env, P.frame, P.rd, P.wr, ?_, ?_, ?_⟩
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
        VG.Proof.AesOcb.Arm.toNat_ofNat32 n32, h8]
      rw [ofNat_sub32 (Nat.mod_le _ _) n32, BitVec.add_comm, show p.n - p.n % 16 = 16 * (p.n / 16) by omega]
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
        VG.Proof.AesOcb.Arm.toNat_ofNat32 n32]
    · simp only [hr, ↓reduceIte]; exact P.ofs
    · simp only [hr, ↓reduceIte]; exact P.out
    · simp only [hr, ↓reduceIte]; exact P.ck

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad`,
`pad(·)`, the working space of the functions called, the stack and the
data. -/
abbrev bodyR (p : VG.Proof.AesOcb.Arm.Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 512, 2048⟩, below p.SP,
   ⟨State.addr p.D, p.n⟩]

theorem bodyR_mut {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.bodyR p) m m') : Frame (VG.Proof.AesOcb.Arm.mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.Arm.below_mut L
    · exact ⟨_, by simp, fun _ h => h⟩

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (p : VG.Proof.AesOcb.Arm.Prm) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p t
  frame : Frame (VG.Proof.AesOcb.Arm.bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem (State.addr p.D) p.n = out
  ofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => VG.Proof.AesOcb.Arm.ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {q : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt q i) :
    VG.Proof.AesOcb.Arm.ckOf X m = Proof.Ocb.ckAt q m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.AesOcb.Arm.ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : VG.Proof.AesOcb.Arm.ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.AesOcb.Arm.ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

section
variable {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p)

include L in
/-- The rest of the data misses what `whole` writes. -/
theorem disj_whole {a r : Nat} (ha : 16 * (p.n / 16) ≤ a) (hf : a + r ≤ p.n) :
    ∀ x ∈ VG.Proof.AesOcb.Arm.wholeR p (p.n / 16), (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (Offset.base_disjoint _ ha (by have := L.dw; omega)).symm
  · exact (L.bd.sub_right (Offset.sub_base _ hf)).symm

include L in
/-- The whole blocks miss what `rest` writes. -/
theorem disj_tail {a r : Nat} (ha : 16 * (p.n / 16) ≤ a) (hf : a + r ≤ p.n) :
    ∀ x ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩],
      (⟨State.addr p.D, 16 * (p.n / 16)⟩ : Region).Disjoint x := by
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr p.D, 16 * (p.n / 16)⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => (L.d_w' h).sub_left (Region.sub_prefix (Nat.mul_div_le p.n 16))
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact (L.bd.sub_right (Region.sub_prefix (Nat.mul_div_le p.n 16))).symm
  · exact Offset.base_disjoint _ ha (by have := L.dw; omega)

theorem wholeR_sub : ∀ r ∈ VG.Proof.AesOcb.Arm.wholeR p (p.n / 16), ∃ r' ∈ VG.Proof.AesOcb.Arm.bodyR p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp [scrO], fun _ h => h⟩
  · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Region.sub_prefix (Nat.mul_div_le p.n 16)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem tailR_sub {a r : Nat} (h : a + r ≤ p.n) :
    ∀ x ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ VG.Proof.AesOcb.Arm.bodyR p, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp [scrO], fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ h⟩

end

/-- `body` for `seal`. -/
theorem bodySeal_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem) {O0 : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p s.mem) 0) :
    WP isa (body true) s (VG.Proof.AesOcb.Arm.BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.encBlocks (VG.Proof.AesOcb.Arm.ciphOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (VG.Proof.AesOcb.Arm.ciphOf p s.mem (offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (p.n / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p s.mem)))
      else Proof.Ocb.encBlocks (VG.Proof.AesOcb.Arm.ciphOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (p.n / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p s.mem
       else offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ^^^
          pad ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16)) s) := by
  have hn := L.n_lt
  have hmn : 16 * (p.n / 16) ≤ p.n := Nat.mul_div_le p.n 16
  have hl : ∀ i < p.n / 16, blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.blockAt (bytesAt s.mem (State.addr p.D) p.n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem _ (by omega)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.Arm.wholeIte_ok VG.Proof.AesOcb.Arm.encF (O0 := O0) (l := VG.Proof.AesOcb.Arm.lstarOf p s.mem)
    (ckF1 := VG.Proof.AesOcb.Arm.ckOf fun i => blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => VG.Proof.AesOcb.Arm.ckOf (fun i => blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
    L (VG.Proof.AesOcb.Arm.sealPre_ok L) (VG.Proof.AesOcb.Arm.xorOfs_ok L) E A hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (VG.Proof.AesOcb.Arm.mutR p) s.mem t.mem := VG.Proof.AesOcb.Arm.wholeR_mut L hmn Pw.frame
  refine WP.mono (VG.Proof.AesOcb.Arm.restIte_ok true L Pw.env (A.mut L fW) Pw.r8) fun t' Pt => ?_
  have cT : VG.Proof.AesOcb.Arm.ciphOf p t.mem = VG.Proof.AesOcb.Arm.ciphOf p s.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, VG.Proof.AesOcb.Arm.sched_mut L fW]
  have lT : VG.Proof.AesOcb.Arm.lstarOf p t.mem = VG.Proof.AesOcb.Arm.lstarOf p s.mem := VG.Proof.AesOcb.Arm.lstar_mut L fW
  have pT : bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    exact Proof.Cmac.bytesAt_frame Pw.frame (VG.Proof.AesOcb.Arm.disj_whole L (Nat.le_refl _) (by omega)) (by omega)
  have rest : (bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem _ hmn, show p.n - 16 * (p.n / 16) = p.n % 16 by omega]
  have ckT : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, VG.Proof.AesOcb.Arm.ckOf_eq hl]
  have blk : bytesAt t'.mem (State.addr p.D) (16 * (p.n / 16)) =
      Proof.Ocb.encBlocks (VG.Proof.AesOcb.Arm.ciphOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (VG.Proof.AesOcb.Arm.disj_tail L (Nat.le_refl _) (by omega)) (by omega),
      Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine VG.Proof.AesOcb.Arm.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, VG.Proof.AesOcb.Arm.encF_ciph, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub VG.Proof.AesOcb.Arm.wholeR_sub).trans (Pt.frame.sub (VG.Proof.AesOcb.Arm.tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem (State.addr p.D) (16 * (p.n / 16)) (p.n % 16)
    rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show p.n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

/-- `DECIPHER` with the key schedule in `m`. -/
abbrev invOf (p : VG.Proof.AesOcb.Arm.Prm) (m : Mem) : Cipher := Spec.Ocb.aesInvWith p.R (VG.Proof.AesOcb.Arm.sched p m)

/-- `body` for `open`. -/
theorem bodyOpen_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem) {O0 : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p s.mem) 0) :
    WP isa (body false) s (VG.Proof.AesOcb.Arm.BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.decBlocks (VG.Proof.AesOcb.Arm.invOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (VG.Proof.AesOcb.Arm.ciphOf p s.mem (offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (p.n / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p s.mem)))
      else Proof.Ocb.decBlocks (VG.Proof.AesOcb.Arm.invOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (p.n / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p s.mem
       else offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.dckAt (VG.Proof.AesOcb.Arm.invOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (VG.Proof.AesOcb.Arm.ciphOf p s.mem (offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (p.n / 16) ^^^ VG.Proof.AesOcb.Arm.lstarOf p s.mem))))
      else Proof.Ocb.dckAt (VG.Proof.AesOcb.Arm.invOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16)) s) := by
  have hn := L.n_lt
  have hmn : 16 * (p.n / 16) ≤ p.n := Nat.mul_div_le p.n 16
  have hl : ∀ i < p.n / 16, blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.blockAt (bytesAt s.mem (State.addr p.D) p.n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem _ (by omega)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.Arm.wholeIte_ok VG.Proof.AesOcb.Arm.decF (O0 := O0) (l := VG.Proof.AesOcb.Arm.lstarOf p s.mem) (ckF1 := fun _ => 0)
    (ckF2 := VG.Proof.AesOcb.Arm.ckOf fun i => VG.Proof.AesOcb.Arm.invOf p s.mem
      (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (i + 1)) ^^^
        offAt O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (i + 1))
    L (VG.Proof.AesOcb.Arm.xorOfs_ok L) (VG.Proof.AesOcb.Arm.openPost_ok L) E A hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (VG.Proof.AesOcb.Arm.mutR p) s.mem t.mem := VG.Proof.AesOcb.Arm.wholeR_mut L hmn Pw.frame
  refine WP.mono (VG.Proof.AesOcb.Arm.restIte_ok false L Pw.env (A.mut L fW) Pw.r8) fun t' Pt => ?_
  have cT : VG.Proof.AesOcb.Arm.ciphOf p t.mem = VG.Proof.AesOcb.Arm.ciphOf p s.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, VG.Proof.AesOcb.Arm.sched_mut L fW]
  have lT : VG.Proof.AesOcb.Arm.lstarOf p t.mem = VG.Proof.AesOcb.Arm.lstarOf p s.mem := VG.Proof.AesOcb.Arm.lstar_mut L fW
  have pT : bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (VG.Proof.AesOcb.Arm.disj_whole L (Nat.le_refl _) (by omega)) (by omega)
  have rest : (bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem _ hmn, show p.n - 16 * (p.n / 16) = p.n % 16 by omega]
  have ckT : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (VG.Proof.AesOcb.Arm.invOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, VG.Proof.AesOcb.Arm.ckOf_dck fun i hi => by rw [hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem (State.addr p.D) (16 * (p.n / 16)) =
      Proof.Ocb.decBlocks (VG.Proof.AesOcb.Arm.invOf p s.mem) O0 (VG.Proof.AesOcb.Arm.lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (VG.Proof.AesOcb.Arm.disj_tail L (Nat.le_refl _) (by omega)) (by omega),
      Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine VG.Proof.AesOcb.Arm.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, VG.Proof.AesOcb.Arm.decF_ciph, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem (State.addr p.D) (16 * (p.n / 16)) (p.n % 16)
  rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega] at e
  refine ⟨Pt.env, (Pw.frame.sub VG.Proof.AesOcb.Arm.wholeR_sub).trans (Pt.frame.sub (VG.Proof.AesOcb.Arm.tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show p.n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Front`. -/
section

/-!
# AES-OCB on ARMv7: before the data

Untrusted: everything here is checked by Lean. What the contracts'
preconditions give about the arguments (`prmOf`, `lay_of`, `perm_of`,
`args_of`); the entry, which saves our caller's registers in `W`, keeps `W`,
the key context and the rounds in registers, and computes `L_$` and `L_0`
(`entry_wp`); and the entry, `Offset_0` (`nonce`) and `HASH` (`hash`)
together (`pre_wp`), as on AArch64 (`Proof.AesOcb.AArch64.pre_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Proof.AesGcm.Arm (below SavedAt savedR entry_ok covers_of_mem covers_left)

/-! ## The arguments -/

/-- The public arguments of a call. -/
def prmOf (s : State) : VG.Proof.AesOcb.Arm.Prm where
  K := s.gpr .r0
  W := VG.Proof.AesOcb.Arm.arg s 6
  N := s.gpr .r2
  A := VG.Proof.AesOcb.Arm.arg s 0
  D := VG.Proof.AesOcb.Arm.arg s 2
  T := VG.Proof.AesOcb.Arm.arg s 4
  SP := s.sp
  R := (s.gpr .r1).toNat
  nl := (s.gpr .r3).toNat
  al := (VG.Proof.AesOcb.Arm.arg s 1).toNat
  n := (VG.Proof.AesOcb.Arm.arg s 3).toNat
  tl := (VG.Proof.AesOcb.Arm.arg s 5).toNat

theorem ofNat_toNat32' (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem argR_eq (s : State) : VG.Proof.AesOcb.Arm.args s 7 = VG.Proof.AesOcb.Arm.argR s.sp := by
  simp only [VG.Proof.AesOcb.Arm.args, VG.Proof.AesOcb.Arm.argR, stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem lay_of {s : State} (h : VG.Proof.AesOcb.Arm.oneLay s) : VG.Proof.AesOcb.Arm.Lay (VG.Proof.AesOcb.Arm.prmOf s) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5, sp8, spf, hR,
    hv, t1, t2, t3, t4⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  rw [VG.Proof.AesOcb.Arm.argR_eq] at d8 d9
  exact ⟨f1, f5, f2, f3, f4, t4, BitVec.isLt _, BitVec.isLt _, sp8, spf, d2, d1, d4, d3, d6, d5, t2, t1, d7, d8, d9,
    b1, b2, b3, b4, t3, b5, hR, hn1, hn15, ht1, ht16⟩

/-- The permissions, from the regions each function may read and write. -/
theorem perm_of {s : State} (_h : VG.Proof.AesOcb.Arm.oneLay s)
    (mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 256⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 0), (VG.Proof.AesOcb.Arm.arg s 1).toNat⟩, ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 4), (VG.Proof.AesOcb.Arm.arg s 5).toNat⟩, VG.Proof.AesOcb.Arm.args s 7],
      Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [(⟨State.addr (VG.Proof.AesOcb.Arm.arg s 2), (VG.Proof.AesOcb.Arm.arg s 3).toNat⟩ : Region), ⟨State.addr (VG.Proof.AesOcb.Arm.arg s 6), 2560⟩], Covers [r] s.wr)
    (hwr : ∀ r ∈ s.wr, (VG.Proof.AesOcb.Arm.args s 7).Disjoint r) : VG.Proof.AesOcb.Arm.Perm (VG.Proof.AesOcb.Arm.prmOf s) s := by
  rw [VG.Proof.AesOcb.Arm.argR_eq] at mrd hwr
  exact ⟨mrd _ (by simp [VG.Proof.AesOcb.Arm.prmOf]), mrd _ (by simp [VG.Proof.AesOcb.Arm.prmOf]), mrd _ (by simp [VG.Proof.AesOcb.Arm.prmOf]), mrd _ (by simp [VG.Proof.AesOcb.Arm.prmOf]),
    mwr _ (by simp [VG.Proof.AesOcb.Arm.prmOf]), mwr _ (by simp [VG.Proof.AesOcb.Arm.prmOf]), mrd _ (by simp [VG.Proof.AesOcb.Arm.prmOf]), hwr⟩

theorem args_of (s : State) : VG.Proof.AesOcb.Arm.Args (VG.Proof.AesOcb.Arm.prmOf s) s.mem :=
  ⟨rfl, by rw [VG.Proof.AesOcb.Arm.prmOf, VG.Proof.AesOcb.Arm.ofNat_toNat32']; rfl, rfl, by rw [VG.Proof.AesOcb.Arm.prmOf, VG.Proof.AesOcb.Arm.ofNat_toNat32']; rfl, rfl,
    by rw [VG.Proof.AesOcb.Arm.prmOf, VG.Proof.AesOcb.Arm.ofNat_toNat32']; rfl⟩

theorem sealPerm {s : State} (h : VG.Proof.AesOcb.Arm.sealPre s) : VG.Proof.AesOcb.Arm.Perm (VG.Proof.AesOcb.Arm.prmOf s) s := by
  obtain ⟨hrd, hwr, hl, ht⟩ := h
  have d8 := hl.2.2.2.2.2.2.2.1
  have d9 := hl.2.2.2.2.2.2.2.2.1
  refine VG.Proof.AesOcb.Arm.perm_of hl (fun r hr => ?_) (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_left (covers_of_mem (by rw [hwr]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d8.symm
    · exact ht.symm
    · exact d9.symm

theorem openPerm {s : State} (h : VG.Proof.AesOcb.Arm.openPre s) : VG.Proof.AesOcb.Arm.Perm (VG.Proof.AesOcb.Arm.prmOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have d8 := hl.2.2.2.2.2.2.2.1
  have d9 := hl.2.2.2.2.2.2.2.2.1
  refine VG.Proof.AesOcb.Arm.perm_of hl (fun r hr => ?_) (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact d8.symm
  · exact d9.symm

/-! ## Frames within `W` -/

section
variable {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m m' : Mem} (h : Frame [⟨State.addr p.W, 2560⟩] m m')
include L h

theorem sched_W : VG.Proof.AesOcb.Arm.sched p m' = VG.Proof.AesOcb.Arm.sched p m :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.k_w.sub_left (Region.sub_prefix (by have := L.rounds_le; omega))) (by have := L.rounds_le; omega)

theorem lstar_W : VG.Proof.AesOcb.Arm.lstarOf p m' = VG.Proof.AesOcb.Arm.lstarOf p m := by
  unfold VG.Proof.AesOcb.Arm.lstarOf Spec.Ocb.ctxLstar
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Offset.sub_base _ (by decide))

theorem nonce_W : bytesAt m' (State.addr p.N) p.nl = bytesAt m (State.addr p.N) p.nl :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.n_w)
    (by have := L.nl15; omega)

theorem aad_W : bytesAt m' (State.addr p.A) p.al = bytesAt m (State.addr p.A) p.al :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.a_w)
    (by have := L.al_lt; omega)

theorem data_W : bytesAt m' (State.addr p.D) p.n = bytesAt m (State.addr p.D) p.n :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.d_w)
    (by have := L.n_lt; omega)

theorem tag_W : bytesAt m' (State.addr p.T) p.tl = bytesAt m (State.addr p.T) p.tl :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.t_w)
    (by have := L.tl16; omega)

theorem args_W (A : VG.Proof.AesOcb.Arm.Args p m) : VG.Proof.AesOcb.Arm.Args p m' :=
  A.frame L h fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.w_args.symm

end

/-- Proves that a block of `W` misses a frame of parts of `W` and the stack
below `sp`. -/
macro "wdisj" L:term : tactic => `(tactic| (
  simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  and_intros
  all_goals first
    | (with_reducible refine Lay.w_w $L ?_ ?_ ?_) <;> decide
    | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
    | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide))

/-- Proves that the data misses a frame of parts of `W` and the stack below
`sp`. -/
macro "ddisj" L:term : tactic => `(tactic| (
  simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  and_intros
  all_goals first
    | (with_reducible refine Lay.d_w' $L ?_) <;> decide
    | with_reducible exact (Lay.bd $L).symm))

/-! ## The entry -/

/-- What the entry leaves. -/
structure EntryPost (p : VG.Proof.AesOcb.Arm.Prm) (s₀ s : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r4 : s.gpr .r4 = p.N
  r5 : s.gpr .r5 = BitVec.ofNat 32 p.nl
  frame : Frame [⟨State.addr p.W, 2560⟩] s₀.mem s.mem
  saved : SavedAt s.mem p.W s₀
  ld : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem)
  l0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) 0
  ck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0

theorem entry_wp {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s₀ : State} (P : VG.Proof.AesOcb.Arm.Perm p s₀) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.block entry) s₀ (VG.Proof.AesOcb.Arm.EntryPost p s₀) := by
  have fw := L.ww
  have fk := L.kw
  have i24 : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 24)) 4 := by
    rw [hsp]; exact P.argR' L (k := 24) (by decide)
  simp only [entry, lsetup, List.append_assoc]
  refine entry_ok (off := 24) (by decide) i24 (by rw [hW]; exact L.ww) (by rw [hW]; exact P.w)
    fun s₁ g12 g rd₁ wr₁ sp₁ sv₁ fr₁ => ?_
  rw [hW] at g12 sv₁ fr₁
  obtain ⟨s₂, run₂, E₂, r4₂, r5₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .r11 (.reg .r12), .mov .r10 (.reg .r0),
      .mov .r9 (.reg .r1), .mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] s₁ = some s₂ ∧ VG.Proof.AesOcb.Arm.Env p s₂ ∧
      s₂.gpr .r4 = p.N ∧ s₂.gpr .r5 = BitVec.ofNat 32 p.nl ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr := by
    refine ⟨_, by orun [], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, by rfl, by simp [rd_setReg, rd₁], by simp [wr_setReg, wr₁]⟩
    · simp [gpr_setReg, g .r1 (by decide), h1]
    · simp [gpr_setReg, g .r0 (by decide), h0]
    · simp [gpr_setReg, g12]
    · simp [sp_setReg, sp₁, hsp]
    · exact P.of_eq (by simp [rd_setReg, rd₁]) (by simp [wr_setReg, wr₁])
    · simp [gpr_setReg, g .r2 (by decide), h2]
    · simp [gpr_setReg, g .r3 (by decide), h3]
  refine WP.block_append (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  -- `L_$`
  refine WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.dbl_wp (b := .r10) (t := s₂) (P := State.addr p.K) (W := State.addr p.W)
    (sO := 240) (dO := ldO) ⟨by decide, by decide, by decide⟩ (by rw [E₂.r10]) (by rw [E₂.r11]) (by decide)
    (by decide) (by rw [E₂.r10]; omega) (by rw [E₂.r11]; simp only [ldO]; omega) (E₂.perm.kC (by decide))
    (E₂.perm.wC (by decide))) fun s₃ R₃ => ?_)
  have E₃ := E₂.of_others R₃.gpr R₃.sp R₃.rd R₃.wr
  -- `L_0`
  refine WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.dbl_wp (b := .r11) (t := s₃) (P := State.addr p.W) (W := State.addr p.W)
    (sO := ldO) (dO := l0O) ⟨by decide, by decide, by decide⟩ (by rw [E₃.r11]) (by rw [E₃.r11]) (by decide)
    (by decide) (by rw [E₃.r11]; simp only [ldO]; omega) (by rw [E₃.r11]; simp only [l0O]; omega)
    (E₃.perm.wCR (by decide)) (E₃.perm.wC (by decide))) fun s₄ R₄ => ?_)
  have E₄ := E₃.of_others R₄.gpr R₄.sp R₄.rd R₄.wr
  -- the checksum
  refine WP.mono (VG.Proof.AesOcb.Arm.zero16_wp (s := s₄) (o := ckO) (by decide) (by rw [E₄.r11]; simp only [ckO]; omega)
    (by rw [E₄.r11]; exact E₄.perm.wC (by decide))) fun s₅ R₅ => ?_
  rw [E₄.r11] at R₅
  have f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ldO, 16⟩] s₂.mem s₃.mem := by
    rw [R₃.mem]; exact VG.Proof.AesOcb.Arm.dblMem_frame _ _ _
  have f₄ : Frame [⟨State.addr p.W + BitVec.ofNat 64 l0O, 16⟩] s₃.mem s₄.mem := by
    rw [R₄.mem]; exact VG.Proof.AesOcb.Arm.dblMem_frame _ _ _
  have f₅ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] s₄.mem s₅.mem := by
    rw [R₅.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have inW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region)],
      ∃ r' ∈ [(⟨State.addr p.W, 2560⟩ : Region)], Region.Sub r r' := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, Lay.wSub h⟩
  have F₂ : Frame [⟨State.addr p.W, 2560⟩] s₀.mem s₂.mem := by rw [m₂]; exact fr₁.sub (inW (by decide))
  have F₅ : Frame [⟨State.addr p.W, 2560⟩] s₂.mem s₅.mem :=
    ((f₃.sub (inW (by decide))).trans (f₄.sub (inW (by decide)))).trans (f₅.sub (inW (by decide)))
  have hl : blockAtMem s₂.mem (State.addr p.K + BitVec.ofNat 64 240) = VG.Proof.AesOcb.Arm.lstarOf p s₀.mem :=
    (VG.Proof.AesOcb.Arm.lstar_W L F₂).symm ▸ rfl
  have ld₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) := by
    rw [R₃.mem, VG.Proof.AesOcb.Arm.blockAtMem_dbl, hl]; rfl
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) := by
    rw [blockAtMem_frame f₄ (by wdisj L), ld₃]
  have l0₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) 0 := by
    rw [R₄.mem, VG.Proof.AesOcb.Arm.blockAtMem_dbl, ld₃]; rfl
  refine ⟨E₄.of_others R₅.gpr R₅.sp R₅.rd R₅.wr, by rw [R₅.rd, R₄.rd, R₃.rd, rd₂],
    by rw [R₅.wr, R₄.wr, R₃.wr, wr₂], by rw [R₅.gpr _ (by decide), R₄.gpr _ (by decide), R₃.gpr _ (by decide), r4₂],
    by rw [R₅.gpr _ (by decide), R₄.gpr _ (by decide), R₃.gpr _ (by decide), r5₂], F₂.trans F₅, ?_,
    by rw [blockAtMem_frame f₅ (by wdisj L), ld₄], by rw [blockAtMem_frame f₅ (by wdisj L), l0₄],
    by rw [R₅.mem, VG.Proof.AesOcb.Arm.blockAtMem_zero4]⟩
  rw [← m₂] at sv₁
  exact ((sv₁.frame f₃ (by wdisj L)).frame f₄ (by wdisj L)).frame f₅ (by wdisj L)

/-! ## Before the data -/

theorem nonceR_mut {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {m m' : Mem} (h : Frame (VG.Proof.AesOcb.Arm.nonceR p) m m') : Frame (VG.Proof.AesOcb.Arm.mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesOcb.Arm.below_mut L

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`, and the inputs as they were. -/
structure Pre (p : VG.Proof.AesOcb.Arm.Prm) (s₀ s : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  args : VG.Proof.AesOcb.Arm.Args p s.mem
  saved : SavedAt s.mem p.W s₀
  sched : VG.Proof.AesOcb.Arm.sched p s.mem = VG.Proof.AesOcb.Arm.sched p s₀.mem
  lstar : VG.Proof.AesOcb.Arm.lstarOf p s.mem = VG.Proof.AesOcb.Arm.lstarOf p s₀.mem
  data : bytesAt s.mem (State.addr p.D) p.n = bytesAt s₀.mem (State.addr p.D) p.n
  tag : bytesAt s.mem (State.addr p.T) p.tl = bytesAt s₀.mem (State.addr p.T) p.tl
  ofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (VG.Proof.AesOcb.Arm.ciphOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
  o0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (VG.Proof.AesOcb.Arm.ciphOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
  ck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem)
  l0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) 0
  sum : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (VG.Proof.AesOcb.Arm.ciphOf p s₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) (VG.Proof.AesOcb.Arm.aadOf p s₀.mem)

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp' {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s₀ : State} (P : VG.Proof.AesOcb.Arm.Perm p s₀) (A : VG.Proof.AesOcb.Arm.Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.seq (.block entry) (.seq nonce Impl.AesOcb.Arm.hash)) s₀ (VG.Proof.AesOcb.Arm.Pre p s₀) := by
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.entry_wp L P hsp h0 h1 h2 h3 hW) fun s₁ P₁ => ?_)
  have A₁ := VG.Proof.AesOcb.Arm.args_W L P₁.frame A
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.nonce_ok L P₁.env A₁ P₁.r4 P₁.r5) fun s₂ N₂ => ?_)
  have F₂ := VG.Proof.AesOcb.Arm.nonceR_mut L N₂.frame
  have l₂ : VG.Proof.AesOcb.Arm.lstarOf p s₂.mem = VG.Proof.AesOcb.Arm.lstarOf p s₀.mem := (VG.Proof.AesOcb.Arm.lstar_mut L F₂).trans (VG.Proof.AesOcb.Arm.lstar_W L P₁.frame)
  have l0₂ : blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) =
      blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) := blockAtMem_frame N₂.frame (by wdisj L)
  refine WP.mono (VG.Proof.AesOcb.Arm.hash_ok L N₂.env (A₁.mut L F₂) (by rw [l0₂, P₁.l0, l₂])) fun s₃ H₃ => ?_
  have F₃ := VG.Proof.AesOcb.Arm.hashR_mut L H₃.frame
  have sc₂ : VG.Proof.AesOcb.Arm.sched p s₂.mem = VG.Proof.AesOcb.Arm.sched p s₀.mem := (VG.Proof.AesOcb.Arm.sched_mut L F₂).trans (VG.Proof.AesOcb.Arm.sched_W L P₁.frame)
  have c₂ : VG.Proof.AesOcb.Arm.ciphOf p s₂.mem = VG.Proof.AesOcb.Arm.ciphOf p s₀.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, sc₂]
  have c₁ : VG.Proof.AesOcb.Arm.ciphOf p s₁.mem = VG.Proof.AesOcb.Arm.ciphOf p s₀.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, VG.Proof.AesOcb.Arm.sched_W L P₁.frame]
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 192) ∨
      (216 ≤ d ∧ d + 16 ≤ 256)) →
      blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => blockAtMem_frame H₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have k₂ : ∀ {d : Nat}, d ∈ [ckO, ldO, l0O] →
      blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> exact blockAtMem_frame N₂.frame (by wdisj L)
  refine ⟨H₃.env, by rw [H₃.rd, N₂.rd, P₁.rd], by rw [H₃.wr, N₂.wr, P₁.wr], (A₁.mut L F₂).mut L F₃,
    ((P₁.saved.frame N₂.frame (by wdisj L)).frame H₃.frame (by wdisj L)),
    (VG.Proof.AesOcb.Arm.sched_mut L F₃).trans sc₂, (VG.Proof.AesOcb.Arm.lstar_mut L F₃).trans l₂,
    by rw [Proof.Cmac.bytesAt_frame H₃.frame (by ddisj L) (by have := L.n_lt; omega),
      Proof.Cmac.bytesAt_frame N₂.frame (by ddisj L) (by have := L.n_lt; omega), VG.Proof.AesOcb.Arm.data_W L P₁.frame],
    by rw [VG.Proof.AesOcb.Arm.tag_mut L F₃, VG.Proof.AesOcb.Arm.tag_mut L F₂, VG.Proof.AesOcb.Arm.tag_W L P₁.frame], ?_, ?_,
    by rw [k₃ (by decide), k₂ (by simp), P₁.ck], by rw [k₃ (by decide), k₂ (by simp), P₁.ld],
    by rw [k₃ (by decide), k₂ (by simp), P₁.l0], ?_⟩
  · rw [k₃ (by decide), N₂.ofs]
    show Spec.Ocb.offset0 (VG.Proof.AesOcb.Arm.ciphOf p s₁.mem) _ _ = _
    rw [c₁, VG.Proof.AesOcb.Arm.nonce_W L P₁.frame]
  · rw [k₃ (by decide), N₂.o0]
    show Spec.Ocb.offset0 (VG.Proof.AesOcb.Arm.ciphOf p s₁.mem) _ _ = _
    rw [c₁, VG.Proof.AesOcb.Arm.nonce_W L P₁.frame]
  · rw [H₃.sum, c₂, l₂, VG.Proof.AesOcb.Arm.aadOf, VG.Proof.AesOcb.Arm.aad_mut L F₂, VG.Proof.AesOcb.Arm.aad_W L P₁.frame]

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Seal`. -/
section

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. `seal` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W`
(`tag`); then the copy of the tag to `tag`, whose address is on the stack
(`tagOut_ok`), and `restore` (`seal_wp`), as on AArch64
(`Proof.AesOcb.AArch64.seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (blockAtMem_frame length_bytesAt)
open VG.Proof.AesGcm.Arm (below SavedAt restore_ok copyLoop_ok covers_left covers_prefix covers_of_mem)

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`. -/
theorem tagOut_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem)
    (hTw : Covers [⟨State.addr p.T, p.tl⟩] s.wr) :
    WP isa tagOut s fun t => t.mem = VG.WriteBytes.writeBytes s.mem (State.addr p.T) (bytesAt s.mem (State.addr p.W) p.tl) ∧
      VG.Proof.AesOcb.Arm.Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have t16 := L.tl16
  have a₁₆ := E.perm.argR' L (k := 16) (by decide)
  have a₂₀ := E.perm.argR' L (k := 20) (by decide)
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₁₆, a₂₀, A.a16, A.a20], ?_⟩)
  refine WP.mono (copyLoop_ok _ (S := p.W) (D := p.T) (n := p.tl)
    ⟨by simp [gpr_setReg, E.r11], by simp [gpr_setReg, E.sp, A.a16], by simp [gpr_setReg, E.sp, A.a20], L.tl1,
      by omega, by omega, L.tw, by simp only [rd_setReg, wr_setReg]; exact covers_left (covers_prefix E.perm.w (by omega)),
      by simp only [wr_setReg]; exact hTw, (L.t_w.sub_right (Region.sub_prefix (by omega))).symm⟩)
    fun t ⟨m, O⟩ => ⟨by rw [m]; rfl, E.keep (fun r hr => ?_) (by rw [O.sp]; rfl) (by rw [O.rd]; rfl)
      (by rw [O.wr]; rfl), by rw [O.rd]; rfl, by rw [O.wr]; rfl⟩
  simp only [VG.Proof.AesOcb.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    (rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg])

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (q : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m q t = (Spec.Ocb.toBytes (blockAtMem m q)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {d : Nat} (hd : d + 16 ≤ 128 ∨ (164 ≤ d ∧ d + 16 ≤ 2560)) {m m' : Mem}
    (h : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] m m') :
    Frame (VG.Proof.AesOcb.Arm.mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inl (by decide))
  · exact VG.Proof.AesOcb.Arm.w_mut L hd
  · exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
  · exact VG.Proof.AesOcb.Arm.below_mut L

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s₀ : State} (P : VG.Proof.AesOcb.Arm.Perm p s₀) (A : VG.Proof.AesOcb.Arm.Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W)
    (hTw : Covers [⟨State.addr p.T, p.tl⟩] s₀.wr) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ocb.encryptWith (VG.Proof.AesOcb.Arm.ciphOf p s₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
        (VG.Proof.AesOcb.Arm.aadOf p s₀.mem) (bytesAt s₀.mem (State.addr p.D) p.n) =
        (bytesAt s'.mem (State.addr p.D) p.n, bytesAt s'.mem (State.addr p.T) p.tl) := by
  unfold «seal» front
  refine WP.seq (WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (VG.Proof.AesOcb.Arm.pre_wp' L P A hsp h0 h1 h2 h3 hW))
    fun s₃ P₃ => ?_))))
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.bodySeal_ok L P₃.env P₃.args P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar]))
    fun s₄ B => ?_)
  have F₄ : Frame (VG.Proof.AesOcb.Arm.mutR p) s₃.mem s₄.mem := VG.Proof.AesOcb.Arm.bodyR_mut L B.frame
  refine WP.mono (VG.Proof.AesOcb.Arm.tag_ok L B.env (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (VG.Proof.AesOcb.Arm.mutR p) s₄.mem s₅.mem := VG.Proof.AesOcb.Arm.tagR_mut L (.inl (by decide)) T₅.frame
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.tagOut_ok L T₅.env ((P₃.args.mut L F₄).mut L F₅)
    (by rw [T₅.wr, B.wr, P₃.wr]; exact hTw)) fun s₆ ⟨m₆, E₆, rd₆, wr₆⟩ => ?_)
  have hx : (bytesAt s₅.mem (State.addr p.W) p.tl).length = p.tl := length_bytesAt _ _ _
  have f₆ : Frame [⟨State.addr p.T, p.tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self _ _)
  have sv₆ : SavedAt s₆.mem p.W s₀ :=
    ((P₃.saved.frame F₄ (VG.Proof.AesOcb.Arm.saved_mut L)).frame F₅ (VG.Proof.AesOcb.Arm.saved_mut L)).frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w' (by decide)).symm
  refine WP.mono (restore_ok E₆.r11 L.ww (covers_left E₆.perm.w) sv₆ (by rw [E₆.sp, hsp]))
    fun s' ⟨ab, hm, _, _, _⟩ => ⟨ab, ?_⟩
  have c₄ : VG.Proof.AesOcb.Arm.ciphOf p s₄.mem = VG.Proof.AesOcb.Arm.ciphOf p s₀.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, VG.Proof.AesOcb.Arm.sched_mut L F₄, P₃.sched]
  have c₃ : VG.Proof.AesOcb.Arm.ciphOf p s₃.mem = VG.Proof.AesOcb.Arm.ciphOf p s₀.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, P₃.sched]
  have hout := B.out
  rw [c₃, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (VG.Proof.AesOcb.Arm.ciphOf p s₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) (VG.Proof.AesOcb.Arm.aadOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.sum]
  have d₆ : bytesAt s'.mem (State.addr p.D) p.n = bytesAt s₄.mem (State.addr p.D) p.n := by
    rw [hm, Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.n_lt; omega)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (by ddisj L) (by have := L.n_lt; omega)
  have tv := T₅.val
  rw [show State.addr p.W + BitVec.ofNat 64 tagO = State.addr p.W from BitVec.add_zero _] at tv
  have t₆ : bytesAt s'.mem (State.addr p.T) p.tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem (State.addr p.W))).take p.tl := by
    rw [hm, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hx]) (by have := L.tl16; omega), hx,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, VG.Proof.AesOcb.Arm.bytesAt_take_block _ _ L.tl16]
  rw [Proof.Ocb.encryptWith_eq, d₆, hout, t₆, tv, hck, hofs, ld₄, sum₄, c₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp {s : State} (h : sealArm.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' :=
  VG.Proof.AesOcb.Arm.seal_wp' (VG.Proof.AesOcb.Arm.lay_of h.2.2.1) (VG.Proof.AesOcb.Arm.sealPerm h) (VG.Proof.AesOcb.Arm.args_of s) rfl rfl (VG.Proof.AesOcb.Arm.ofNat_toNat32' _).symm rfl (VG.Proof.AesOcb.Arm.ofNat_toNat32' _).symm rfl
    (covers_of_mem (by rw [h.2.1]; simp [VG.Proof.AesOcb.Arm.prmOf]))

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Open`. -/
section

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at
`W + t2O` (`tag`); then the received tag, padded with zeros at `W`
(`recv_ok`); the first `tag_len` bytes of the tag, padded with zeros at
`W + vO`, compared with it (`cmp_ok`); the data ANDed with `0 − ok`
(`mask_ok`); and `restore` (`open_wp`), as on AArch64
(`Proof.AesOcb.AArch64.open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.Ocb (blockAtMem_frame length_bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Proof.AesGcm.Arm (below SavedAt restore_ok copyLoop_ok LoopPre covers_left covers_prefix covers_of_mem
  store4_zero_tail bytes_words words_eq_iff cmp_value runBlock_app_of Keeps add_ofNat_assoc add_ofNat_zero
  bytesAt_writeBytes_prefix writeBytes_frame' z_subFlags gpr_subFlags mem_subFlags z_cmp eval_eq' eval_ne' addr_i
  dec32 z_dec in_of_covers bytesAt_succ mem_store gpr_store add32_ofNat_assoc)

/-! ## The received tag -/

/-- `recv`: the received tag, the `tl` bytes at `T`, padded with zeros at
`W`. -/
theorem recv_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem) :
    WP isa recv s fun t => bytesAt t.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.T) p.tl ++ zeros (16 - p.tl) ∧
      Frame [⟨State.addr p.W, 16⟩] s.mem t.mem ∧ VG.Proof.AesOcb.Arm.Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have t16 := L.tl16
  unfold recv
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.zero16_wp (s := s) (o := tagO) (by decide)
    (by rw [E.r11]; simp only [tagO]; omega) (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11, show State.addr p.W + BitVec.ofNat 64 tagO = State.addr p.W from BitVec.add_zero _] at R₁
  have E₁ : VG.Proof.AesOcb.Arm.Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fz : Frame [⟨State.addr p.W, 16⟩] s.mem s₁.mem := by rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have A₁ : VG.Proof.AesOcb.Arm.Args p s₁.mem := A.frame L fz fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_args.symm.sub_right (Region.sub_prefix (by decide))
  have a₁₆ := E₁.perm.argR' L (k := 16) (by decide)
  have a₂₀ := E₁.perm.argR' L (k := 20) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₁.sp, a₁₆, a₂₀, A₁.a16, A₁.a20], ?_⟩
  have tW : (⟨State.addr p.T, p.tl⟩ : Region).Disjoint ⟨State.addr p.W, 16⟩ :=
    L.t_w.sub_right (Region.sub_prefix (by decide))
  refine WP.mono (copyLoop_ok _ (S := p.T) (D := p.W) (n := p.tl)
    ⟨by simp [gpr_setReg, E₁.sp, A₁.a16], by simp [gpr_setReg, E₁.r11], by simp [gpr_setReg, E₁.sp, A₁.a20],
      L.tl1, by omega, L.tw, by omega, by simp only [rd_setReg, wr_setReg]; exact E₁.perm.tag,
      by simp only [wr_setReg]; exact covers_prefix E₁.perm.w (by omega),
      tW.sub_right (Region.sub_prefix (by omega))⟩) fun t ⟨m, O⟩ => ?_
  have hT : bytesAt s₁.mem (State.addr p.T) p.tl = bytesAt s.mem (State.addr p.T) p.tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact tW)
      (by omega)
  have hlen := length_bytesAt s₁.mem (State.addr p.T) p.tl
  simp only [mem_setReg] at m
  refine ⟨?_, ?_, E₁.keep (fun r hr => ?_) (by rw [O.sp]; rfl) (by rw [O.rd]; rfl) (by rw [O.wr]; rfl),
    by rw [O.rd]; exact R₁.rd, by rw [O.wr]; exact R₁.wr⟩
  · rw [m, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, hT, R₁.mem]
    have := store4_zero_tail s.mem (State.addr p.W) t16
    exact congrArg _ this
  · rw [m]
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  · simp only [VG.Proof.AesOcb.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      (rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg])

/-! ## The comparison -/

/-- `cmpTail`: `r0` is 1 iff the 16 bytes at `W` and `W + vO` are equal. -/
theorem cmpTail_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) :
    ∃ s', runBlock isa cmpTail s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr p.W) 16 =
        bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 vO) 16 then 1 else 0) ∧
      VG.Proof.AesOcb.Arm.Others [.r0, .r1, .r2] s s' ∧ Keeps s s' := by
  have h11 := E.r11
  have r₀ := E.perm.wR (show 0 + 4 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 4 + 4 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 8 + 4 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 12 + 4 ≤ 2560 by decide)
  have q₀ := E.perm.wR (show 240 + 4 ≤ 2560 by decide)
  have q₁ := E.perm.wR (show 244 + 4 ≤ 2560 by decide)
  have q₂ := E.perm.wR (show 248 + 4 ≤ 2560 by decide)
  have q₃ := E.perm.wR (show 252 + 4 ≤ 2560 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr p.W + BitVec.ofNat 64 (4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr p.W + BitVec.ofNat 64 (240 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorT .r0 0 ++ xorT .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ VG.Proof.AesOcb.Arm.Others [.r0, .r1, .r2] s s₁ ∧ s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorT]; orun [h11, L.wA, r₀, r₁, q₀, q₁], by others_tac, ?_, by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    simp [gpr_setReg, a, b, m]
  have h11₁ : s₁.gpr .r11 = p.W := by rw [g₁ _ (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, h1₂, k₂⟩ : ∃ s₂, runBlock isa (xorT .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++
      xorT .r1 3) s₁ = some s₂ ∧ VG.Proof.AesOcb.Arm.Others [.r0, .r1, .r2] s₁ s₂ ∧
      s₂.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2 ∧ s₂.gpr .r1 = a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorT]; orun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], by others_tac, ?_, ?_,
      by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · simp [gpr_setReg, a, b, m, hm₁]
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0),
      .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1),
      .dp .sub .r0 .r1 (.reg .r0)] s₂ = some s₃ ∧ VG.Proof.AesOcb.Arm.Others [.r0, .r1] s₂ s₃ ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - (((s₂.gpr .r0 ||| s₂.gpr .r1) ||| (BitVec.ofNat 32 0 - (s₂.gpr .r0 ||| s₂.gpr .r1))) >>> 31) ∧
      Keeps s₂ s₃ := by
    refine ⟨_, by orun [], by others_tac, ?_, by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show cmpTail = (xorT .r0 0 ++ xorT .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorT .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorT .r1 3) ++
      [.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1),
        .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, h1₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m, Nat.mul_zero, BitVec.add_zero]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₃ r (by simp [hr.1, hr.2.1]), g₂ r (by simp [hr.1, hr.2.1, hr.2.2]), g₁ r (by simp [hr.1, hr.2.1, hr.2.2])]

/-- `cmp`: the first `tl` bytes of the tag at `W + t2O`, padded with zeros
at `W + vO`, compared with the received tag at `W`. -/
theorem cmp_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem) :
    WP isa cmp s fun t => t.gpr .r0 = (if bytesAt s.mem (State.addr p.W) 16 =
        bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl) then 1 else 0) ∧
      Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem t.mem ∧ VG.Proof.AesOcb.Arm.Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have t16 := L.tl16
  unfold cmp
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.AesOcb.Arm.zero16_wp (s := s) (o := vO) (by decide)
    (by rw [E.r11]; simp only [vO]; omega) (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  have E₁ : VG.Proof.AesOcb.Arm.Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fz : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have A₁ : VG.Proof.AesOcb.Arm.Args p s₁.mem := A.frame L fz fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.args_w' (by decide)
  have a₂₀ := E₁.perm.argR' L (k := 20) (by decide)
  have e₁ : encodable (BitVec.ofNat 32 176) = true := by decide
  have e₂ : encodable (BitVec.ofNat 32 240) = true := by decide
  obtain ⟨s₂, run₂, r1₂, r2₂, r3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 t2O, addI .r2 .r11 vO, .ldrSp .r3 20] s₁ =
      some s₂ ∧ s₂.gpr .r1 = p.W + BitVec.ofNat 32 t2O ∧ s₂.gpr .r2 = p.W + BitVec.ofNat 32 vO ∧
      s₂.gpr .r3 = BitVec.ofNat 32 p.tl ∧ VG.Proof.AesOcb.Arm.Others [.r1, .r2, .r3] s₁ s₂ ∧ Keeps s₁ s₂ :=
    ⟨_, by orun [E₁.r11, E₁.sp, a₂₀, A₁.a20, e₁, e₂], by simp [gpr_setReg, E₁.r11, t2O],
      by simp [gpr_setReg, E₁.r11, vO], by simp [gpr_setReg, E₁.sp, A₁.a20], by others_tac,
      by exact ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have E₂ : VG.Proof.AesOcb.Arm.Env p s₂ := E₁.of_others g₂ k₂.sp k₂.rd k₂.wr
  have eS := L.wA (d := t2O) (by decide)
  have eD := L.wA (d := vO) (by decide)
  have dSD : (⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩ :=
    L.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (copyLoop_ok s₂ (S := p.W + BitVec.ofNat 32 t2O) (D := p.W + BitVec.ofNat 32 vO) (n := p.tl)
    ⟨r1₂, r2₂, r3₂, L.tl1, by omega, by rw [L.wN (by decide)]; simp only [t2O]; omega,
      by rw [L.wN (by decide)]; simp only [vO]; omega, by rw [eS]; exact E₂.perm.wCR (by simp only [t2O]; omega),
      by rw [eD]; exact E₂.perm.wC (by simp only [vO]; omega),
      by rw [eS, eD]; exact (dSD.sub_left (Region.sub_prefix t16)).sub_right (Region.sub_prefix t16)⟩)
    fun s₃ ⟨m₃, O₃⟩ => ?_)
  rw [eS, eD] at m₃
  have E₃ : VG.Proof.AesOcb.Arm.Env p s₃ := E₂.keep (fun r hr => by
    simp only [VG.Proof.AesOcb.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact O₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    O₃.sp O₃.rd O₃.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := VG.Proof.AesOcb.Arm.cmpTail_ok L E₃
  have hlen := length_bytesAt s₂.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl
  have f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₃.mem := by
    have fz' : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₂.mem := by rw [k₂.mem]; exact fz
    rw [m₃]
    exact fz'.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  have hS : bytesAt s₂.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl =
      bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl := by
    rw [k₂.mem]
    exact Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dSD.sub_left (Region.sub_prefix t16)) (by omega)
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [k₄.mem]; exact f₃, E₃.keep (fun r hr => g₄ r (by
      simp only [VG.Proof.AesOcb.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) k₄.sp k₄.rd k₄.wr,
    by rw [k₄.rd, O₃.rd, k₂.rd, R₁.rd], by rw [k₄.wr, O₃.wr, k₂.wr, R₁.wr]⟩
  have hW : bytesAt s₃.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.W) 16 :=
    Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 0) (n := 16) (d := vO) (k := 16) (.inl (by decide)) (by decide) (by decide))
      (by decide)
  have hV : bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 vO) 16 =
      bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl) := by
    rw [m₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, hS, k₂.mem, R₁.mem]
    exact congrArg _ (store4_zero_tail s.mem _ t16)
  rw [h0₄, hW, hV]

/-! ## The mask -/

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1, .subs .r5 .r5 (imm 1)]

theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {c : Bool} (h4 : s.gpr .r4 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if c then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa VG.Proof.AesOcb.Arm.maskBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if c then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by orun [h4, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      VG.Proof.AesOcb.Arm.mask_byte]
  · simp [gpr_setReg, h4, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- `mask`: every byte of the data ANDed with `0 − ok`, for `ok ∈ {0, 1}` in
`r0`. -/
theorem mask_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s : State} (E : VG.Proof.AesOcb.Arm.Env p s) (A : VG.Proof.AesOcb.Arm.Args p s.mem) {c : Bool}
    (h0 : s.gpr .r0 = if c then 1 else 0) :
    WP isa mask s fun t => VG.Proof.AesOcb.Arm.Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .r0 = s.gpr .r0 ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr p.D) (if c then bytesAt s.mem (State.addr p.D) p.n else zeros p.n) := by
  have hn := L.dw
  have hn32 := L.n_lt
  have i2 := E.perm.argR' L (k := 8) (by decide)
  have i3 := E.perm.argR' L (k := 12) (by decide)
  obtain ⟨s₁, run₁, h4₁, h5₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r1 (imm 0),
      .dp .sub .r1 .r1 (.reg .r0), .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r4 = p.D ∧ s₁.gpr .r5 = BitVec.ofNat 32 p.n ∧ s₁.gpr .r1 = 0 - (if c then 1 else 0) ∧
      s₁.z = decide (p.n = 0) ∧ VG.Proof.AesOcb.Arm.Others [.r1, .r4, .r5] s s₁ ∧ Keeps s s₁ := by
    refine ⟨_, by orun [E.sp, i2, i3, A.a8, A.a12], ?_, ?_, ?_, ?_, by others_tac, by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_setReg, E.sp, A.a8]
    · simp [gpr_setReg, E.sp, A.a12]
    · simp [gpr_setReg, h0, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, E.sp, A.a12, imm]
      rw [z_cmp hn32 (by decide)]
  have E₁ : VG.Proof.AesOcb.Arm.Env p s₁ := E.of_others g₁ k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (p.n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : p.n = 0 := by simpa using hb
    refine ⟨E₁, k₁.rd, k₁.wr, g₁ _ (by decide), ?_⟩
    rw [k₁.mem, hn0]; cases c <;> simp [bytesAt, zeros, VG.WriteBytes.writeBytes_nil]
  have hn0 : 0 < p.n := by have : p.n ≠ 0 := by simpa using hb
                           omega
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ t.gpr .r4 = p.D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (p.n - j) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr p.D) (if c then bytesAt s.mem (State.addr p.D) j else zeros j) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (p.n - 0) _
    ⟨0, rfl, hn0, by rw [h4₁, add_ofNat_zero], by rw [h5₁]; rfl,
      by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, VG.WriteBytes.writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr, k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r4, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r4', r5', z', g', rd', wr', sp'⟩ := VG.Proof.AesOcb.Arm.maskStep_ok t (c := c) r4 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers (covers_left E.perm.d) hj (by omega))
    (by rw [wr, aD]; exact in_of_covers E.perm.d hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr p.D, j⟩] s.mem t.mem := by
    rw [mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.Arm.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr p.D + BitVec.ofNat 64 j) = s.mem (State.addr p.D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr p.D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (State.addr p.D)
      (if c then bytesAt s.mem (State.addr p.D) (j + 1) else zeros (j + 1)) := by
    rw [mem', aD, hq, mem, VG.Proof.AesOcb.Arm.mask_succ, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesOcb.Arm.length_mask]; omega), VG.Proof.AesOcb.Arm.length_mask]
  have hz : t'.z = decide (j + 1 = p.n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = p.n) := eval_ne' hz
  by_cases hjn : j + 1 = p.n
  · left
    refine ⟨by rw [ev]; simp [hjn], E₁.keep (fun r hr => by
        simp only [VG.Proof.AesOcb.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], by rw [gg _ (by decide) (by decide) (by decide), g₁ _ (by decide)], by rw [hmem, hjn]⟩
  · right
    refine ⟨by rw [ev]; simp [hjn], p.n - (j + 1), by omega, j + 1, rfl, by omega, r4',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-! ## `open` -/

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s₀ : State} (P : VG.Proof.AesOcb.Arm.Perm p s₀) (A : VG.Proof.AesOcb.Arm.Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      match Spec.Ocb.decryptWith (VG.Proof.AesOcb.Arm.ciphOf p s₀.mem) (VG.Proof.AesOcb.Arm.invOf p s₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) p.tl
          (bytesAt s₀.mem (State.addr p.N) p.nl) (VG.Proof.AesOcb.Arm.aadOf p s₀.mem) (bytesAt s₀.mem (State.addr p.D) p.n)
          (bytesAt s₀.mem (State.addr p.T) p.tl) with
      | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr p.D) p.n = pt
      | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr p.D) p.n = Spec.Ocb.zeros p.n := by
  have hn := L.n_lt
  have t16 := L.tl16
  unfold «open» front
  refine WP.seq (WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (VG.Proof.AesOcb.Arm.pre_wp' L P A hsp h0 h1 h2 h3 hW))
    fun s₃ P₃ => ?_))))
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.bodyOpen_ok L P₃.env P₃.args P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar]))
    fun s₄ B => ?_)
  have F₄ : Frame (VG.Proof.AesOcb.Arm.mutR p) s₃.mem s₄.mem := VG.Proof.AesOcb.Arm.bodyR_mut L B.frame
  refine WP.mono (VG.Proof.AesOcb.Arm.tag_ok L B.env (.inr rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (VG.Proof.AesOcb.Arm.mutR p) s₄.mem s₅.mem := VG.Proof.AesOcb.Arm.tagR_mut L (.inr ⟨by decide, by decide⟩) T₅.frame
  have A₅ : VG.Proof.AesOcb.Arm.Args p s₅.mem := (P₃.args.mut L F₄).mut L F₅
  -- The received tag, at `W`.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.recv_ok L T₅.env A₅) fun s₆ ⟨b₆, f₆, E₆, rd₆, wr₆⟩ => ?_)
  have F₆ : Frame (VG.Proof.AesOcb.Arm.mutR p) s₅.mem s₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
  -- The comparison.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.cmp_ok L E₆ (A₅.mut L F₆)) fun s₇ ⟨h0₇, f₇, E₇, rd₇, wr₇⟩ => ?_)
  have F₇ : Frame (VG.Proof.AesOcb.Arm.mutR p) s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.Arm.w_mut L (.inr ⟨by decide, by decide⟩)
  let c : Bool := decide (bytesAt s₆.mem (State.addr p.W) 16 =
    bytesAt s₆.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl))
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.Arm.mask_ok L E₇ ((A₅.mut L F₆).mut L F₇) (c := c) (by
    rw [h0₇]; simp only [c]; split <;> simp_all)) fun s₈ ⟨E₈, rd₈, wr₈, g0₈, m₈⟩ => ?_)
  have F₈ : Frame [⟨State.addr p.D, p.n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.Arm.length_mask]; exact Region.contains_self _ _)
  have sv₈ : SavedAt s₈.mem p.W s₀ :=
    ((((P₃.saved.frame F₄ (VG.Proof.AesOcb.Arm.saved_mut L)).frame F₅ (VG.Proof.AesOcb.Arm.saved_mut L)).frame F₆ (VG.Proof.AesOcb.Arm.saved_mut L)).frame F₇
      (VG.Proof.AesOcb.Arm.saved_mut L)).frame F₈ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.d_w' (by decide)).symm
  -- `restore`.
  refine WP.mono (restore_ok E₈.r11 L.ww (covers_left E₈.perm.w) sv₈ (by rw [E₈.sp, hsp]))
    fun s' ⟨ab, hm, hr0, _, _⟩ => ⟨ab, ?_⟩
  have x0 : s'.gpr .r0 = if c then 1 else 0 := by
    rw [hr0, g0₈, h0₇]; simp only [c]; split <;> simp_all
  have c₃ : VG.Proof.AesOcb.Arm.ciphOf p s₃.mem = VG.Proof.AesOcb.Arm.ciphOf p s₀.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, P₃.sched]
  have i₃ : VG.Proof.AesOcb.Arm.invOf p s₃.mem = VG.Proof.AesOcb.Arm.invOf p s₀.mem := by simp only [VG.Proof.AesOcb.Arm.invOf, P₃.sched]
  have c₄ : VG.Proof.AesOcb.Arm.ciphOf p s₄.mem = VG.Proof.AesOcb.Arm.ciphOf p s₀.mem := by simp only [VG.Proof.AesOcb.Arm.ciphOf, VG.Proof.AesOcb.Arm.sched_mut L F₄, P₃.sched]
  have hout := B.out
  rw [c₃, i₃, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [c₃, i₃, P₃.lstar, P₃.data] at hck
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (VG.Proof.AesOcb.Arm.ciphOf p s₀.mem) (VG.Proof.AesOcb.Arm.lstarOf p s₀.mem) (VG.Proof.AesOcb.Arm.aadOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.sum]
  have tagv := T₅.val
  rw [hck, hofs, ld₄, sum₄, c₄] at tagv
  have d₇ : bytesAt s₇.mem (State.addr p.D) p.n = bytesAt s₄.mem (State.addr p.D) p.n := by
    rw [Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega),
      Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.d_w.sub_right (Region.sub_prefix (by decide))) (by omega)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (by ddisj L) (by omega)
  have d₈ : bytesAt s'.mem (State.addr p.D) p.n = if c then bytesAt s₄.mem (State.addr p.D) p.n else zeros p.n := by
    rw [hm, m₈, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesOcb.Arm.length_mask]) (by omega), VG.Proof.AesOcb.Arm.length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₇]
  have recv : bytesAt s₆.mem (State.addr p.W) 16 = bytesAt s₀.mem (State.addr p.T) p.tl ++ zeros (16 - p.tl) := by
    rw [b₆, VG.Proof.AesOcb.Arm.tag_mut L F₅, VG.Proof.AesOcb.Arm.tag_mut L F₄, P₃.tag]
  have t2₆ : bytesAt s₆.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl =
      bytesAt s₅.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (L.w_w (a := t2O) (n := p.tl) (d := 0) (k := 16) (.inr (by decide)) (by simp only [t2O]; omega)
        (by decide))) (by omega)
  have hc : ∀ x : Block, bytesAt s₅.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl = (Spec.Ocb.toBytes x).take p.tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take p.tl = bytesAt s₀.mem (State.addr p.T) p.tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [recv, t2₆, hx, decide_eq_true_iff, List.append_cancel_right_eq, eq_comm]
  rw [x0, d₈, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [VG.Proof.AesOcb.Arm.bytesAt_take_block _ _ t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, rfl⟩
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [VG.Proof.AesOcb.Arm.bytesAt_take_block _ _ t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, rfl⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp {s : State} (h : openArm.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' :=
  VG.Proof.AesOcb.Arm.open_wp' (VG.Proof.AesOcb.Arm.lay_of h.2.2) (VG.Proof.AesOcb.Arm.openPerm h) (VG.Proof.AesOcb.Arm.args_of s) rfl rfl (VG.Proof.AesOcb.Arm.ofNat_toNat32' _).symm rfl (VG.Proof.AesOcb.Arm.ofNat_toNat32' _).symm rfl

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.CTBase`. -/
section

/-!
# AES-OCB on ARMv7: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2`) piece by piece, as AES-GCM-SIV's
do (`Proof.AesGcmSiv.Arm`): the code between calls by the taint analysis,
from the registers that hold the public arguments in both runs (`Env`,
`rel_env`), those the pieces pin to the same values, and the stack
arguments, which both runs hold and nothing writes (`Args`, `rel_envArg`);
each call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` by its
proof, with the same arguments in both runs (`rel_blk`, `encOne_rel`); a
branch on a flag both runs agree on (`rel_ite`); a loop whose condition both
runs agree on (`rel_loop`); and the next piece from the states the
correctness proofs describe (`rel_seq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Impl.AesGcm.Arm (imm addI)

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c₁ VG.Proof.AesOcb.Arm.TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) c₂ VG.Proof.AesOcb.Arm.TT) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.seq c₁ c₂) VG.Proof.AesOcb.Arm.TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesOcb.Arm.TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.Arm.taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact Taint.agree_ofRegs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.block []) VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_taint [] (by simp) ⟨.block [], rfl⟩

/-- Code the taint analysis checks, from registers the two runs agree on and
the first `n` bytes of stack arguments, the same in both runs and apart from
the writable regions. -/
theorem rel_arg {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (n : Nat) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hsp : σ₁.sp = σ₂.sp)
    (hw₁ : σ₁.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ σ₁.wr, Region.Disjoint ⟨State.addr σ₁.sp, n⟩ r)
    (hw₂ : σ₂.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ σ₂.wr, Region.Disjoint ⟨State.addr σ₂.sp, n⟩ r)
    (hm : ∀ k < n, σ₁.mem (VG.Arm.Taint.argByte σ₁ k) = σ₂.mem (VG.Arm.Taint.argByte σ₂ k))
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint rs n) c h).isSome = true) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesOcb.Arm.TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.Arm.taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact agree_argTaint hr hsp hw₁ hw₂ hm) hc

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) t VG.Proof.AesOcb.Arm.TT)
    (hf : b = false → RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) e VG.Proof.AesOcb.Arm.TT) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.ite c t e) VG.Proof.AesOcb.Arm.TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- A loop step in two runs: the condition agrees, and the runs are related
anew while it loops. -/
theorem rel_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n σ₁ σ₂, I n σ₁ σ₂ → RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) body fun s₁ s₂ => isa.eval c s₁ = isa.eval c s₂ ∧
      (isa.eval c s₁ = some true → ∃ m < n, I m s₁ s₂))
    (n : Nat) {σ₁ σ₂ : State} (h : I n σ₁ σ₂) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.loop body c) VG.Proof.AesOcb.Arm.TT := by
  refine (RelCT.loop (Q := VG.Proof.AesOcb.Arm.TT) I (fun n => ?_) n).mono (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact h)
    fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hc, hi⟩ := hstep n s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, hc, fun _ => trivial, hi⟩

/-- The last piece of a loop's body, with what correctness says of each run's
final state. -/
theorem rel_wpQ {c : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesOcb.Arm.TT) (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂)
    (hq : ∀ a b, F₁ a → F₂ b → Q a b) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c Q :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun a b h => hq a b h.2.1 h.2.2

/-- Then, towards any relation of the final states. -/
theorem rel_seqQ {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c₁ VG.Proof.AesOcb.Arm.TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c VG.Proof.AesOcb.Arm.TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The public arguments -/

theorem Env.agree {p : VG.Proof.AesOcb.Arm.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) :
    ∀ r ∈ VG.Proof.AesOcb.Arm.envRegs, τ₁.gpr r = τ₂.gpr r := by
  intro r hr
  simp only [VG.Proof.AesOcb.Arm.envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [E₁.r9, E₂.r9]
  · rw [E₁.r10, E₂.r10]
  · rw [E₁.r11, E₂.r11]

theorem Env.sp_eq {p : VG.Proof.AesOcb.Arm.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) : τ₁.sp = τ₂.sp := by
  rw [E₁.sp, E₂.sp]

/-- The registers holding the public arguments, and `rs`. -/
abbrev pubRegs (rs : List Reg) : List Reg := VG.Proof.AesOcb.Arm.envRegs ++ rs

/-- Code the taint analysis checks, from the registers holding the public
arguments and the registers `rs` the two runs agree on. -/
theorem rel_env {c : Prog isa} {p : VG.Proof.AesOcb.Arm.Prm} {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs rs)) c h).isSome = true) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) c VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_taint (VG.Proof.AesOcb.Arm.pubRegs rs) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) hc

theorem argByte_eq {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s₁ s₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p s₁) (E₂ : VG.Proof.AesOcb.Arm.Env p s₂) (A₁ : VG.Proof.AesOcb.Arm.Args p s₁.mem)
    (A₂ : VG.Proof.AesOcb.Arm.Args p s₂.mem) : ∀ k < 24, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  refine argMem_of (j := 6) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega) fun i hi => ?_
  have e : ∀ {s : State}, VG.Proof.AesOcb.Arm.Env p s → VG.Proof.AesOcb.Arm.Args p s.mem → stackArg s i =
      [p.A, BitVec.ofNat 32 p.al, p.D, BitVec.ofNat 32 p.n, p.T, BitVec.ofNat 32 p.tl].getD i 0 := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.a0
    · exact A.a4
    · exact A.a8
    · exact A.a12
    · exact A.a16
    · exact A.a20
  rw [e E₁ A₁, e E₂ A₂]

/-- Code the taint analysis checks, from the registers holding the public
arguments, the registers `rs` the two runs agree on, and the first six
stack arguments. -/
theorem rel_envArg {c : Prog isa} {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂)
    (A₁ : VG.Proof.AesOcb.Arm.Args p τ₁.mem) (A₂ : VG.Proof.AesOcb.Arm.Args p τ₂.mem) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs rs) 24) c h).isSome = true) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) c VG.Proof.AesOcb.Arm.TT := by
  have spf := L.spf
  have hw : ∀ {τ : State}, VG.Proof.AesOcb.Arm.Env p τ →
      τ.sp.toNat + 24 ≤ 2 ^ 32 ∧ ∀ r ∈ τ.wr, Region.Disjoint ⟨State.addr τ.sp, 24⟩ r := fun E =>
    ⟨by rw [E.sp]; omega, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact VG.Proof.AesOcb.Arm.rel_arg (VG.Proof.AesOcb.Arm.pubRegs rs) 24 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (VG.Proof.AesOcb.Arm.argByte_eq L E₁ E₂ A₁ A₂) hc

/-! ## The calls -/

/-- A call of `F` in two runs, with the same arguments. -/
theorem rel_blk (F : VG.Proof.AesOcb.Arm.BlkFn) {σ₁ σ₂ : State} {K D S : BitVec 32} {R n : Nat} (h₁ : VG.Proof.AesOcb.Arm.BlkCall σ₁ K D S R n)
    (h₂ : VG.Proof.AesOcb.Arm.BlkCall σ₂ K D S R n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (VG.Proof.AesOcb.Arm.blkFrame F) VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.blk_rel F fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, D, S, R, n, h₁, h₂, hsp⟩

/-! ## What a run keeps -/

/-- Then, from what every execution of the first piece leaves. -/
theorem rel_seqX {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) c₁ VG.Proof.AesOcb.Arm.TT) (w₁ : ∀ t τ, Exec isa c₁ σ₁ t τ → F₁ τ)
    (w₂ : ∀ t τ, Exec isa c₁ σ₂ t τ → F₂ τ)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) c₂ VG.Proof.AesOcb.Arm.TT) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.seq c₁ c₂) VG.Proof.AesOcb.Arm.TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => ?_) ?_
  · obtain ⟨rfl, rfl⟩ := hp
    exact ⟨(h₁ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, w₁ _ _ e₁, w₂ _ _ e₂⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- What every execution leaves, from a correctness proof. -/
theorem exec_of_wp {c : Prog isa} {σ : State} {F : State → Prop} (w : WP isa c σ F) :
    ∀ t τ, Exec isa c σ t τ → F τ := fun _ _ e => by
  obtain ⟨_, _, e', hf⟩ := w
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hf

/-- The environment, after code that writes none of its registers. -/
theorem Env.exec {p : VG.Proof.AesOcb.Arm.Prm} {c : Prog isa} {τ τ' : State} {t : List Leak} (E : VG.Proof.AesOcb.Arm.Env p τ) (h : Exec isa c τ t τ')
    (h9 : ∀ i ∈ instrs c, dstOf i ≠ some .r9) (h10 : ∀ i ∈ instrs c, dstOf i ≠ some .r10)
    (h11 : ∀ i ∈ instrs c, dstOf i ≠ some .r11) : VG.Proof.AesOcb.Arm.Env p τ' :=
  have ⟨rd, wr, sp⟩ := Exec.rdwr h
  ⟨by rw [Exec.gpr h9 h, E.r9], by rw [Exec.gpr h10 h, E.r10], by rw [Exec.gpr h11 h, E.r11], by rw [sp, E.sp],
    E.perm.of_eq rd wr⟩

/-- The stack arguments, after code without frames. -/
theorem Args.exec {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {c : Prog isa} {τ τ' : State} {t : List Leak} (E : VG.Proof.AesOcb.Arm.Env p τ)
    (A : VG.Proof.AesOcb.Arm.Args p τ.mem) (h : Exec isa c τ t τ') (hn : c.noFrames = true) : VG.Proof.AesOcb.Arm.Args p τ'.mem :=
  A.frame L (Exec.regions h hn).2.2.2 fun r hr => E.perm.argw r hr

/-- What every execution of frame-free code that keeps the environment's
registers leaves: the environment, the stack arguments, and the registers in
`rs` it does not write. -/
structure Kept (p : VG.Proof.AesOcb.Arm.Prm) (rs : List Reg) (τ τ' : State) : Prop where
  env : VG.Proof.AesOcb.Arm.Env p τ'
  args : VG.Proof.AesOcb.Arm.Args p τ.mem → VG.Proof.AesOcb.Arm.Args p τ'.mem
  gpr : ∀ r ∈ rs, τ'.gpr r = τ.gpr r

theorem kept_of {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {c : Prog isa} {τ : State} (E : VG.Proof.AesOcb.Arm.Env p τ) (rs : List Reg)
    (hk : ∀ r ∈ VG.Proof.AesOcb.Arm.envRegs ++ rs, ∀ i ∈ instrs c, dstOf i ≠ some r) (hn : c.noFrames = true)
    (hc : c.noCalls = true) : ∀ t τ', Exec isa c τ t τ' → VG.Proof.AesOcb.Arm.Kept p rs τ τ' := fun _ _ h =>
  ⟨E.exec h (hk _ (by simp)) (hk _ (by simp)) (hk _ (by simp)), fun A => A.exec L E h hn,
    fun r hr => Exec.gpr (hk r (List.mem_append_right _ hr)) h (.inl hc)⟩

/-! ## The calls -/

/-- `ENCIPHER` of the block at `W + d`, set up. -/
theorem encOne_pre {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ : State} (E : VG.Proof.AesOcb.Arm.Env p τ) {d : Nat} (hd : d + 16 ≤ 512)
    (he : encodable (BitVec.ofNat 32 d) = true) :
    WP isa (.block (callArgs ++ ([addI .r2 .r11 d, .mov .r3 (imm 1)] : List Instr))) τ fun t =>
      VG.Proof.AesOcb.Arm.BlkCall t p.K (p.W + BitVec.ofNat 32 d) (p.W + BitVec.ofNat 32 scrO) p.R 1 ∧ VG.Proof.AesOcb.Arm.Env p t := by
  have fw := L.ww
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega)
  refine WP.of_runBlock ⟨_, by orun [callArgs, E.r9, E.r10, E.r11, he], ?_⟩
  have E' := E.of_others (s' := ((((τ.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 (p.W + BitVec.ofNat 32 d)).setReg .r3 (BitVec.ofNat 32 1))
    (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨VG.Proof.AesOcb.Arm.blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
    (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by omega)]; omega)
    (by rw [ed]; exact E.perm.wC (by omega)) (by rw [ed]; exact L.k_w' (by omega))
    (by rw [ed]; exact L.w_w (.inl (by simp only [scrO]; omega)) (by omega) (by decide))
    (by rw [ed]; exact L.bw' (by omega)), E'⟩

theorem encOneA_check {d : Nat} (hd : d = tmpO ∨ d = bufO) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [])) (.block (callArgs ++ ([addI .r2 .r11 d, .mov .r3 (imm 1)] : List Instr))) h).isSome
      = true := by
  rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `ENCIPHER` of the block at `W + d`, in two runs with the same public
arguments. -/
theorem encOne_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) {d : Nat}
    (hd : d = tmpO ∨ d = bufO) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (encOne d) VG.Proof.AesOcb.Arm.TT := by
  have hd' : d + 16 ≤ 512 := by rcases hd with rfl | rfl <;> decide
  have he : encodable (BitVec.ofNat 32 d) = true := by rcases hd with rfl | rfl <;> decide
  exact VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_env E₁ E₂ [] (by simp) (VG.Proof.AesOcb.Arm.encOneA_check hd)) (VG.Proof.AesOcb.Arm.encOne_pre L E₁ hd' he) (VG.Proof.AesOcb.Arm.encOne_pre L E₂ hd' he)
    fun a b A B => VG.Proof.AesOcb.Arm.rel_blk VG.Proof.AesOcb.Arm.encF A.1 B.1 (A.2.sp_eq B.2)

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.CTPre`. -/
section

/-!
# AES-OCB on ARMv7: `Offset_0` and `HASH` in two runs

Untrusted: everything here is checked by Lean. `nonce` and `hash`, in two
runs with the same public arguments: the code between the calls by the taint
analysis, from the registers holding the public arguments and those pinned
to the same values in both runs (the nonce and its length, the associated
data's pointer and its blocks, the count of a chunk), and each call of
`vg_aes_encrypt_blocks` with the same arguments in both runs (`nonce_rel`,
`hash_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0)

/-! ## `Offset_0` -/

theorem nonceBlock_check :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs [.r4, .r5]) 24) nonceBlock h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem offset0_check :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [])) (.block offset0) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `nonce`, in two runs with the same public arguments, nonce pointer and
length. -/
theorem nonce_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) (A₁ : VG.Proof.AesOcb.Arm.Args p τ₁.mem)
    (A₂ : VG.Proof.AesOcb.Arm.Args p τ₂.mem) (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) nonce VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_envArg L E₁ E₂ A₁ A₂ [.r4, .r5] (by simp [h4, h5]) VG.Proof.AesOcb.Arm.nonceBlock_check)
    (VG.Proof.AesOcb.Arm.kept_of L E₁ [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L E₂ [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.encOne_rel L K₁.env K₂.env (.inl rfl)) (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  VG.Proof.AesOcb.Arm.rel_env (C₁.env K₁.env) (C₂.env K₂.env) [] (by simp) VG.Proof.AesOcb.Arm.offset0_check

/-! ## A chunk of `HASH` -/

/-- The start of a chunk: `Z` set if fewer than 16 blocks are left. -/
theorem chunkB0_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t : State} {j : Nat} (H : VG.Proof.AesOcb.Arm.HInv p t₀ t j) :
    WP isa (.block [.mov .r12 (.shifted .r7 .lsr 4), .cmp .r12 (imm 0)]) t fun t' =>
      VG.Proof.AesOcb.Arm.HInv p t₀ t' j ∧ t'.z = decide (p.al / 16 - j < 16) := by
  have al32 := L.al_lt
  have m32 : p.al / 16 - j < 2 ^ 32 := by omega
  have z₁ : (BitVec.ofNat 32 (p.al / 16 - j) >>> 4 == 0) = decide (p.al / 16 - j < 16) := by
    rw [VG.Proof.AesOcb.Arm.ofNat_lsr32 m32, z_cmp0 (by omega)]; congr 1; apply propext; omega
  refine WP.of_runBlock ⟨_, by orun [H.r7], ?_, ?_⟩
  · exact ⟨H.env.of_others (rs := [.r12]) (by others_tac) (by rfl) (by rfl) (by rfl), H.frame, H.rd, H.wr, H.le,
      H.sum, H.oh, by simp [gpr_setReg, H.r4], by simp [gpr_setReg, H.r6], by simp [gpr_setReg, H.r7], H.l0⟩
  · simp only [z_subFlags, gpr_setReg, ite_true, H.r7, BitVec.sub_zero, z₁]

/-- The count of a chunk, `min(16, r7)`, in `r5`. -/
theorem chunkSel_ok {p : VG.Proof.AesOcb.Arm.Prm} {t₀ t : State} {j : Nat} (H : VG.Proof.AesOcb.Arm.HInv p t₀ t j)
    (hz : t.z = decide (p.al / 16 - j < 16)) :
    WP isa (.ite .eq (.block [.mov .r5 (.reg .r7)]) (.block [.mov .r5 (imm 16)])) t fun t' =>
      VG.Proof.AesOcb.Arm.HInv p t₀ t' j ∧ t'.gpr .r5 = BitVec.ofNat 32 (min 16 (p.al / 16 - j)) := by
  have Hk : ∀ {t' : State}, t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      VG.Proof.AesOcb.Arm.Others [.r5] t t' → VG.Proof.AesOcb.Arm.HInv p t₀ t' j := fun hm hrd hwr hsp ho =>
    ⟨H.env.of_others ho hsp hrd hwr, by rw [hm]; exact H.frame, by rw [hrd, H.rd], by rw [hwr, H.wr], H.le,
      by rw [hm]; exact H.sum, by rw [hm]; exact H.oh, by rw [ho _ (by decide), H.r4], by rw [ho _ (by decide), H.r6],
      by rw [ho _ (by decide), H.r7], by rw [hm]; exact H.l0⟩
  refine WP.ite (decide (p.al / 16 - j < 16)) (eval_eq' hz) (fun hb => ?_) (fun hb => ?_)
  · have hlt : p.al / 16 - j < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by orun [H.r7], Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac), ?_⟩
    simp [gpr_setReg, H.r7, show min 16 (p.al / 16 - j) = p.al / 16 - j by omega]
  · have hlt : ¬ p.al / 16 - j < 16 := by simpa using hb
    refine WP.of_runBlock ⟨_, by orun [], Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac), ?_⟩
    simp [gpr_setReg, show min 16 (p.al / 16 - j) = 16 by omega]

/-- After a chunk's call: the count back in `r5`, the buffer in `r8`. -/
theorem chunkB4_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t₀ t₂ t₃ : State} {j c : Nat} (F : VG.Proof.AesOcb.Arm.FillInv p t₀ j c t₂ c)
    (hc : c ≤ 16) (C : VG.Proof.AesOcb.Arm.BlkPost VG.Proof.AesOcb.Arm.encF (VG.Proof.AesOcb.Arm.chunkCallSt p c t₂) p.K (p.W + BitVec.ofNat 32 bufO)
      (p.W + BitVec.ofNat 32 scrO) p.R c t₃) :
    WP isa (.block [addI .r8 .r11 bufO, .ldr .r5 .r11 cnO]) t₃ fun t' =>
      VG.Proof.AesOcb.Arm.Env p t' ∧ t'.gpr .r5 = BitVec.ofNat 32 c ∧ t'.gpr .r8 = p.W + BitVec.ofNat 32 bufO := by
  have fw := L.ww
  have E₂ : VG.Proof.AesOcb.Arm.Env p (VG.Proof.AesOcb.Arm.chunkCallSt p c t₂) := (VG.Proof.AesOcb.Arm.chunkCall_blk L F hc).2
  have E₃ : VG.Proof.AesOcb.Arm.Env p t₃ := E₂.of_saved C.saved C.sp C.rd C.wr
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have eS : State.addr (p.W + BitVec.ofNat 32 scrO) = State.addr p.W + BitVec.ofNat 64 scrO := L.wA (by decide)
  have fr := C.frame
  rw [eB, eS, E₂.sp] at fr
  have cnt₃ : t₃.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := by
    rw [fr.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 212, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by simp only [bufO]; omega)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)]
    exact F.cnt
  have rC₃ : InRegions (t₃.rd ++ t₃.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₃.perm.wR (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₃.r11, eC, rC₃, cnt₃], ?_, ?_, ?_⟩
  · exact E₃.of_others (rs := [.r5, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp [gpr_setReg]
  · simp [gpr_setReg, E₃.r11, bufO]

theorem chunkB0_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r7]))
    (.block [.mov .r12 (.shifted .r7 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSelT_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block [.mov .r5 (.reg .r7)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSelF_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block [.mov .r5 (imm 16)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB1_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), addI .r8 .r11 bufO]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkFill_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r4, .r5, .r6, .r8]))
    (.loop hashFill .ne) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB3_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block (callArgs ++ [addI .r2 .r11 bufO, .ldr .r3 .r11 cnO])) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB4_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block [addI .r8 .r11 bufO, .ldr .r5 .r11 cnO]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSum_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r5, .r8]))
    (.seq hashSum (.block [.cmp .r7 (imm 0)])) h).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs at the same block of the associated data. -/
theorem chunk_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {a b τ₁ τ₂ : State} {j : Nat} (H₁ : VG.Proof.AesOcb.Arm.HInv p a τ₁ j) (H₂ : VG.Proof.AesOcb.Arm.HInv p b τ₂ j)
    (hj : j < p.al / 16) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) hashChunk VG.Proof.AesOcb.Arm.TT := by
  have hc0 : 0 < min 16 (p.al / 16 - j) := by omega
  have hc : min 16 (p.al / 16 - j) ≤ 16 := Nat.min_le_left _ _
  have hjc : j + min 16 (p.al / 16 - j) ≤ p.al / 16 := by omega
  unfold hashChunk
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_env H₁.env H₂.env [.r7] (by simp [H₁.r7, H₂.r7]) VG.Proof.AesOcb.Arm.chunkB0_check) (VG.Proof.AesOcb.Arm.chunkB0_ok L H₁)
    (VG.Proof.AesOcb.Arm.chunkB0_ok L H₂) fun u₁ u₂ ⟨U₁, z₁⟩ ⟨U₂, z₂⟩ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => VG.Proof.AesOcb.Arm.rel_env U₁.env U₂.env [] (by simp) VG.Proof.AesOcb.Arm.chunkSelT_check)
    (fun _ => VG.Proof.AesOcb.Arm.rel_env U₁.env U₂.env [] (by simp) VG.Proof.AesOcb.Arm.chunkSelF_check)) (VG.Proof.AesOcb.Arm.chunkSel_ok U₁ z₁) (VG.Proof.AesOcb.Arm.chunkSel_ok U₂ z₂)
    fun v₁ v₂ ⟨V₁, h5₁⟩ ⟨V₂, h5₂⟩ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_env V₁.env V₂.env [] (by simp) VG.Proof.AesOcb.Arm.chunkB1_check) (VG.Proof.AesOcb.Arm.chunkHead_ok L V₁ hc hjc h5₁)
    (VG.Proof.AesOcb.Arm.chunkHead_ok L V₂ hc hjc h5₂) fun w₁ w₂ F₁ F₂ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_env F₁.env F₂.env [.r4, .r5, .r6, .r8] (by simp [F₁.r4, F₂.r4, F₁.r5, F₂.r5, F₁.r6, F₂.r6,
                                            F₁.r8, F₂.r8]) VG.Proof.AesOcb.Arm.chunkFill_check) (VG.Proof.AesOcb.Arm.fill_ok L hc0 hc hjc F₁) (VG.Proof.AesOcb.Arm.fill_ok L hc0 hc hjc F₂) fun x₁ x₂ G₁ G₂ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq (F₁ := fun y => y = VG.Proof.AesOcb.Arm.chunkCallSt p _ x₁) (F₂ := fun y => y = VG.Proof.AesOcb.Arm.chunkCallSt p _ x₂)
    (VG.Proof.AesOcb.Arm.rel_env G₁.env G₂.env [] (by simp) VG.Proof.AesOcb.Arm.chunkB3_check) (WP.of_runBlock ⟨_, VG.Proof.AesOcb.Arm.chunkArgs_run L G₁, rfl⟩)
    (WP.of_runBlock ⟨_, VG.Proof.AesOcb.Arm.chunkArgs_run L G₂, rfl⟩) fun y₁ y₂ e₁ e₂ => ?_
  subst e₁ e₂
  have B₁ := VG.Proof.AesOcb.Arm.chunkCall_blk L G₁ hc
  have B₂ := VG.Proof.AesOcb.Arm.chunkCall_blk L G₂ hc
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_blk VG.Proof.AesOcb.Arm.encF B₁.1 B₂.1 (B₁.2.sp_eq B₂.2)) (VG.Proof.AesOcb.Arm.blk_call VG.Proof.AesOcb.Arm.encF B₁.1) (VG.Proof.AesOcb.Arm.blk_call VG.Proof.AesOcb.Arm.encF B₂.1)
    fun z₁ z₂ C₁ C₂ => ?_
  have E₁ : VG.Proof.AesOcb.Arm.Env p z₁ := B₁.2.of_saved C₁.saved C₁.sp C₁.rd C₁.wr
  have E₂ : VG.Proof.AesOcb.Arm.Env p z₂ := B₂.2.of_saved C₂.saved C₂.sp C₂.rd C₂.wr
  exact VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_env E₁ E₂ [] (by simp) VG.Proof.AesOcb.Arm.chunkB4_check) (VG.Proof.AesOcb.Arm.chunkB4_ok L G₁ hc C₁) (VG.Proof.AesOcb.Arm.chunkB4_ok L G₂ hc C₂)
    fun _ _ ⟨D₁, r5₁, r8₁⟩ ⟨D₂, r5₂, r8₂⟩ => VG.Proof.AesOcb.Arm.rel_env D₁ D₂ [.r5, .r8] (by simp [r5₁, r5₂, r8₁, r8₂]) VG.Proof.AesOcb.Arm.chunkSum_check

/-! ## `HASH` -/

theorem hashHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs []) 24)
    (.block (Impl.AesGcm.Arm.zero16 sumO ++ Impl.AesGcm.Arm.zero16 ohO ++
      ([.ldrSp .r4 0, .ldrSp .r7 4, .mov .r7 (.shifted .r7 .lsr 4), .mov .r6 (imm 1), .cmp .r7 (imm 0)] :
        List Instr))) h).isSome =
      true := ⟨_, by taint_decide⟩

theorem hashMid_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs []) 24)
    (.block [.ldrSp .r5 4, .dp .and .r5 .r5 (imm 15), .cmp .r5 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block (xorB .r11 .r10 .r11 ohO 240 ohO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestPad_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r4, .r5]))
    (padTo bufO) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestB_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block (xorW ohO bufO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestC_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block (xorW bufO sumO)) h).isSome = true := ⟨_, by taint_decide⟩

/-- The rest of the associated data, in two runs with the same pointer and
length. -/
theorem hashRest_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂)
    (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) hashRest VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_env E₁ E₂ [] (by simp) VG.Proof.AesOcb.Arm.hashRestA_check)
    (VG.Proof.AesOcb.Arm.kept_of L E₁ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L E₂ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_env K₁.env K₂.env [.r4, .r5] (by
      simp [K₁.gpr .r4 (by simp), K₂.gpr .r4 (by simp), K₁.gpr .r5 (by simp), K₂.gpr .r5 (by simp), h4, h5])
      VG.Proof.AesOcb.Arm.hashRestPad_check)
    (VG.Proof.AesOcb.Arm.kept_of L K₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L K₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ M₁ M₂ =>
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_env M₁.env M₂.env [] (by simp) VG.Proof.AesOcb.Arm.hashRestB_check)
    (VG.Proof.AesOcb.Arm.kept_of L M₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L M₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ N₁ N₂ =>
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.encOne_rel L N₁.env N₂.env (.inr rfl))
    (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L N₁.env (d := bufO) (by decide) (by decide)))
    (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L N₂.env (d := bufO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  VG.Proof.AesOcb.Arm.rel_env (C₁.env N₁.env) (C₂.env N₂.env) [] (by simp) VG.Proof.AesOcb.Arm.hashRestC_check

/-- `HASH`, in two runs with the same public arguments. -/
theorem hash_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) (A₁ : VG.Proof.AesOcb.Arm.Args p τ₁.mem)
    (A₂ : VG.Proof.AesOcb.Arm.Args p τ₂.mem)
    (hl₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (VG.Proof.AesOcb.Arm.lstarOf p τ₁.mem) 0)
    (hl₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (VG.Proof.AesOcb.Arm.lstarOf p τ₂.mem) 0) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) Impl.AesOcb.Arm.hash VG.Proof.AesOcb.Arm.TT := by
  unfold Impl.AesOcb.Arm.hash
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_envArg L E₁ E₂ A₁ A₂ [] (by simp) VG.Proof.AesOcb.Arm.hashHead_check) (VG.Proof.AesOcb.Arm.hashHead_ok L E₁ A₁ hl₁)
    (VG.Proof.AesOcb.Arm.hashHead_ok L E₂ A₂ hl₂) fun u₁ u₂ ⟨U₁, z₁⟩ ⟨U₂, z₂⟩ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq ?_ (VG.Proof.AesOcb.Arm.hashWhole_ok L U₁ z₁) (VG.Proof.AesOcb.Arm.hashWhole_ok L U₂ z₂) fun v₁ v₂ V₁ V₂ => ?_
  · refine VG.Proof.AesOcb.Arm.rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => VG.Proof.AesOcb.Arm.rel_skip) fun hb => ?_
    have hm : p.al / 16 ≠ 0 := by simpa using hb
    refine VG.Proof.AesOcb.Arm.rel_loop (fun k σ₁ σ₂ => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ VG.Proof.AesOcb.Arm.HInv p τ₁ σ₁ j ∧ VG.Proof.AesOcb.Arm.HInv p τ₂ σ₂ j)
      (fun k σ₁ σ₂ ⟨j, hk, hj, H₁, H₂⟩ => ?_) (p.al / 16 - 0) ⟨0, rfl, by omega, U₁, U₂⟩
    refine VG.Proof.AesOcb.Arm.rel_wpQ (VG.Proof.AesOcb.Arm.chunk_rel L H₁ H₂ hj) (VG.Proof.AesOcb.Arm.hashChunk_ok L H₁ hj) (VG.Proof.AesOcb.Arm.hashChunk_ok L H₂ hj)
      fun x y ⟨X, zx⟩ ⟨Y, zy⟩ => ⟨by rw [eval_ne' zx, eval_ne' zy], fun hc => ?_⟩
    rw [eval_ne' zx] at hc
    have hlt : j + min 16 (p.al / 16 - j) < p.al / 16 := by
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hc; omega
    exact ⟨p.al / 16 - (j + min 16 (p.al / 16 - j)), by omega, _, rfl, hlt, X, Y⟩
  · have Av₁ : VG.Proof.AesOcb.Arm.Args p v₁.mem := A₁.mut L (VG.Proof.AesOcb.Arm.hashR_mut L V₁.frame)
    have Av₂ : VG.Proof.AesOcb.Arm.Args p v₂.mem := A₂.mut L (VG.Proof.AesOcb.Arm.hashR_mut L V₂.frame)
    refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_envArg L V₁.env V₂.env Av₁ Av₂ [] (by simp) VG.Proof.AesOcb.Arm.hashMid_check) (VG.Proof.AesOcb.Arm.hashMid_ok L V₁ Av₁)
      (VG.Proof.AesOcb.Arm.hashMid_ok L V₂ Av₂) fun w₁ w₂ ⟨W₁, h5₁, z₁'⟩ ⟨W₂, h5₂, z₂'⟩ => ?_
    exact VG.Proof.AesOcb.Arm.rel_ite (eval_eq' z₁') (eval_eq' z₂') (fun _ => VG.Proof.AesOcb.Arm.rel_skip)
      (fun _ => VG.Proof.AesOcb.Arm.hashRest_rel L W₁.env W₂.env (by rw [W₁.r4, W₂.r4]) (by rw [h5₁, h5₂]))

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.CTBody`. -/
section

/-!
# AES-OCB on ARMv7: the data and the tag in two runs

Untrusted: everything here is checked by Lean. `body` and `tag d`, in two
runs with the same public arguments: the passes over the whole blocks and
the rest by the taint analysis, from the registers holding the data's
pointer, its blocks and the block index, the same in both runs; the calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` with the same arguments
in both runs (`body_rel`, `tag_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 and15 ofNat_sub32)

/-! ## The whole blocks -/

theorem passStart_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r7, .r8]))
    (.block passStart) h).isSome = true := ⟨_, by taint_decide⟩

theorem pass_check {b : List Instr} (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r4, .r5, .r6, .r7, .r8])) (pass b) h).isSome =
      true := by
  rcases hb with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem wholeArgs_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block (callArgs ++ ([.mov .r2 (.reg .r8), .mov .r3 (.reg .r7)] : List Instr))) h).isSome = true := ⟨_, by taint_decide⟩

theorem wholeTail_check {b : List Instr} (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r7, .r8]))
      (.seq (.block (copy16 o0O ofsO ++ passStart)) (pass b)) h).isSome = true := by
  rcases hb with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem pass_kept {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ : State} (E : VG.Proof.AesOcb.Arm.Env p τ) {b : List Instr}
    (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∀ t τ', Exec isa (pass b) τ t τ' → VG.Proof.AesOcb.Arm.Kept p [.r7, .r8] τ τ' := by
  rcases hb with rfl | rfl | rfl <;>
    exact VG.Proof.AesOcb.Arm.kept_of L E [.r7, .r8] (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The call between the passes, set up. -/
theorem wholeArgs_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ : State} (E : VG.Proof.AesOcb.Arm.Env p τ) {m : Nat} (hmn : 16 * m ≤ p.n)
    (h8 : τ.gpr .r8 = p.D) (h7 : τ.gpr .r7 = BitVec.ofNat 32 m) :
    WP isa (.block (callArgs ++ ([.mov .r2 (.reg .r8), .mov .r3 (.reg .r7)] : List Instr))) τ fun t =>
      VG.Proof.AesOcb.Arm.BlkCall t p.K p.D (p.W + BitVec.ofNat 32 scrO) p.R m ∧ VG.Proof.AesOcb.Arm.Env p t ∧ t.gpr .r8 = p.D ∧
        t.gpr .r7 = BitVec.ofNat 32 m := by
  have fd := L.dw
  refine WP.of_runBlock ⟨_, by orun [callArgs, E.r9, E.r10, E.r11, h8, h7], ?_⟩
  have E' := E.of_others (s' := ((((τ.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 p.D).setReg .r3 (BitVec.ofNat 32 m))
    (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨VG.Proof.AesOcb.Arm.blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
    (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by omega)
    (Proof.AesGcm.Arm.covers_prefix E.perm.d hmn) (L.k_d.sub_right (Region.sub_prefix hmn))
    ((L.d_w' (d := scrO) (k := 2048) (by decide)).sub_left (Region.sub_prefix hmn))
    (L.bd.sub_right (Region.sub_prefix hmn)), E', by simp [gpr_setReg, h8], by simp [gpr_setReg, h7]⟩

/-- The whole blocks, in two runs with the same public arguments. -/
theorem whole_rel (F : VG.Proof.AesOcb.Arm.BlkFn) {pre post : List Instr}
    (hpre : pre = addCk ++ xorOfs ∨ pre = xorOfs ∨ pre = xorOfs ++ addCk)
    (hpost : post = addCk ++ xorOfs ∨ post = xorOfs ∨ post = xorOfs ++ addCk)
    {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) {m : Nat} (hmn : 16 * m ≤ p.n)
    (h8₁ : τ₁.gpr .r8 = p.D) (h8₂ : τ₂.gpr .r8 = p.D) (h7₁ : τ₁.gpr .r7 = BitVec.ofNat 32 m)
    (h7₂ : τ₂.gpr .r7 = BitVec.ofNat 32 m) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (whole (VG.Proof.AesOcb.Arm.blkFrame F) pre post) VG.Proof.AesOcb.Arm.TT := by
  unfold whole
  obtain ⟨s₁, run₁, r4₁, r5₁, r6₁, R₁⟩ := VG.Proof.AesOcb.Arm.passStart_run h8₁ h7₁
  obtain ⟨s₂, run₂, r4₂, r5₂, r6₂, R₂⟩ := VG.Proof.AesOcb.Arm.passStart_run h8₂ h7₂
  refine VG.Proof.AesOcb.Arm.rel_seq (F₁ := (s₁ = ·)) (F₂ := (s₂ = ·)) (VG.Proof.AesOcb.Arm.rel_env E₁ E₂ [.r7, .r8] (by simp [h7₁, h7₂, h8₁, h8₂])
    VG.Proof.AesOcb.Arm.passStart_check) (WP.of_runBlock ⟨s₁, run₁, rfl⟩) (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun u₁ u₂ e₁ e₂ => ?_
  subst e₁ e₂
  have Es₁ : VG.Proof.AesOcb.Arm.Env p s₁ := E₁.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have Es₂ : VG.Proof.AesOcb.Arm.Env p s₂ := E₂.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have g₁ : ∀ r ∈ [Reg.r7, .r8], s₁.gpr r = τ₁.gpr r := fun r hr => R₁.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide)
  have g₂ : ∀ r ∈ [Reg.r7, .r8], s₂.gpr r = τ₂.gpr r := fun r hr => R₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide)
  refine VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_env Es₁ Es₂ [.r4, .r5, .r6, .r7, .r8] (by
      simp [r4₁, r4₂, r5₁, r5₂, r6₁, r6₂, g₁ .r7 (by simp), g₂ .r7 (by simp), g₁ .r8 (by simp), g₂ .r8 (by simp),
        h7₁, h7₂, h8₁, h8₂]) (VG.Proof.AesOcb.Arm.pass_check hpre))
    (VG.Proof.AesOcb.Arm.pass_kept L Es₁ hpre) (VG.Proof.AesOcb.Arm.pass_kept L Es₂ hpre) fun v₁ v₂ K₁ K₂ => ?_
  have h8v₁ : v₁.gpr .r8 = p.D := by rw [K₁.gpr _ (by simp), g₁ _ (by simp), h8₁]
  have h8v₂ : v₂.gpr .r8 = p.D := by rw [K₂.gpr _ (by simp), g₂ _ (by simp), h8₂]
  have h7v₁ : v₁.gpr .r7 = BitVec.ofNat 32 m := by rw [K₁.gpr _ (by simp), g₁ _ (by simp), h7₁]
  have h7v₂ : v₂.gpr .r7 = BitVec.ofNat 32 m := by rw [K₂.gpr _ (by simp), g₂ _ (by simp), h7₂]
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_env K₁.env K₂.env [] (by simp) VG.Proof.AesOcb.Arm.wholeArgs_check) (VG.Proof.AesOcb.Arm.wholeArgs_ok L K₁.env hmn h8v₁ h7v₁)
    (VG.Proof.AesOcb.Arm.wholeArgs_ok L K₂.env hmn h8v₂ h7v₂) fun w₁ w₂ ⟨B₁, Ew₁, h8w₁, h7w₁⟩ ⟨B₂, Ew₂, h8w₂, h7w₂⟩ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_blk F B₁ B₂ (Ew₁.sp_eq Ew₂)) (VG.Proof.AesOcb.Arm.blk_call F B₁) (VG.Proof.AesOcb.Arm.blk_call F B₂) fun x₁ x₂ C₁ C₂ => ?_
  exact VG.Proof.AesOcb.Arm.rel_env (Ew₁.of_saved C₁.saved C₁.sp C₁.rd C₁.wr) (Ew₂.of_saved C₂.saved C₂.sp C₂.rd C₂.wr) [.r7, .r8]
    (by simp [C₁.saved .r7 (by decide) (by decide), C₂.saved .r7 (by decide) (by decide),
      C₁.saved .r8 (by decide) (by decide), C₂.saved .r8 (by decide) (by decide), h7w₁, h7w₂, h8w₁, h8w₂])
    (VG.Proof.AesOcb.Arm.wholeTail_check hpost)

/-! ## The rest of the data -/

theorem restA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block (xorB .r11 .r10 .r11 ofsO 240 ofsO ++ copy16 ofsO tmpO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem restTail_check (enc : Bool) : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [.r4, .r5]))
    (if enc then .seq padCk xorPad else .seq xorPad padCk) h).isSome = true := by
  cases enc <;> exact ⟨_, by taint_decide⟩

/-- The rest of the data, in two runs with the same pointer and length. -/
theorem rest_rel (enc : Bool) {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂)
    (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (rest enc) VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_env E₁ E₂ [] (by simp) VG.Proof.AesOcb.Arm.restA_check)
    (VG.Proof.AesOcb.Arm.kept_of L E₁ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L E₂ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.encOne_rel L K₁.env K₂.env (.inl rfl))
    (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  VG.Proof.AesOcb.Arm.rel_env (C₁.env K₁.env) (C₂.env K₂.env) [.r4, .r5] (by
    simp [C₁.saved .r4 (by decide), C₂.saved .r4 (by decide), C₁.saved .r5 (by decide), C₂.saved .r5 (by decide),
      K₁.gpr .r4 (by simp), K₂.gpr .r4 (by simp), K₁.gpr .r5 (by simp), K₂.gpr .r5 (by simp), h4, h5])
    (VG.Proof.AesOcb.Arm.restTail_check enc)

/-! ## The data -/

/-- The start of `body`: the data in `r8`, its whole blocks in `r7`. -/
theorem bodyHead_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) (A : VG.Proof.AesOcb.Arm.Args p t.mem) :
    WP isa (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)]) t fun t' =>
      VG.Proof.AesOcb.Arm.Env p t' ∧ t'.gpr .r8 = p.D ∧ t'.gpr .r7 = BitVec.ofNat 32 (p.n / 16) ∧ t'.z = decide (p.n / 16 = 0) := by
  have n32 := L.n_lt
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.sp, a₈, a₁₂, A.a8, A.a12], ?_, ?_, ?_, ?_⟩
  · exact E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]
  · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, VG.Proof.AesOcb.Arm.ofNat_lsr32 n32]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, VG.Proof.AesOcb.Arm.ofNat_lsr32 n32,
      Nat.reducePow, z_cmp0 (show p.n / 16 < 2 ^ 32 by omega)]

/-- Where the rest of the data is. -/
theorem restBlk_ok {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {t : State} (E : VG.Proof.AesOcb.Arm.Env p t) (A : VG.Proof.AesOcb.Arm.Args p t.mem) (h8 : t.gpr .r8 = p.D) :
    WP isa (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
        .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) t fun t' =>
      VG.Proof.AesOcb.Arm.Env p t' ∧ t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.n % 16) ∧
        t'.z = decide (p.n % 16 = 0) := by
  have n32 := L.n_lt
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.sp, a₁₂, A.a12, h8], ?_, ?_, ?_, ?_⟩
  · exact E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
      VG.Proof.AesOcb.Arm.toNat_ofNat32 n32, h8]
    rw [ofNat_sub32 (Nat.mod_le _ _) n32, BitVec.add_comm, show p.n - p.n % 16 = 16 * (p.n / 16) by omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
      VG.Proof.AesOcb.Arm.toNat_ofNat32 n32]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15,
      VG.Proof.AesOcb.Arm.toNat_ofNat32 n32, z_cmp0 (show p.n % 16 < 2 ^ 32 by omega)]

theorem bodyHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs []) 24)
    (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restBlk_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs [.r8]) 24)
    (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
      .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

/-- The whole blocks, if there are any, in two runs. -/
theorem wholeIte_rel (F : VG.Proof.AesOcb.Arm.BlkFn) {pre post : List Instr}
    (hpre : pre = addCk ++ xorOfs ∨ pre = xorOfs ∨ pre = xorOfs ++ addCk)
    (hpost : post = addCk ++ xorOfs ∨ post = xorOfs ∨ post = xorOfs ++ addCk)
    {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) (A₁ : VG.Proof.AesOcb.Arm.Args p τ₁.mem)
    (A₂ : VG.Proof.AesOcb.Arm.Args p τ₂.mem) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (.seq (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4),
      .cmp .r7 (imm 0)]) (.ite .eq (.block []) (whole (VG.Proof.AesOcb.Arm.blkFrame F) pre post))) VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_envArg L E₁ E₂ A₁ A₂ [] (by simp) VG.Proof.AesOcb.Arm.bodyHead_check) (VG.Proof.AesOcb.Arm.bodyHead_ok L E₁ A₁) (VG.Proof.AesOcb.Arm.bodyHead_ok L E₂ A₂)
    fun _ _ ⟨U₁, h8₁, h7₁, z₁⟩ ⟨U₂, h8₂, h7₂, z₂⟩ =>
  VG.Proof.AesOcb.Arm.rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => VG.Proof.AesOcb.Arm.rel_skip)
    (fun _ => VG.Proof.AesOcb.Arm.whole_rel F hpre hpost L U₁ U₂ (Nat.mul_div_le p.n 16) h8₁ h8₂ h7₁ h7₂)

/-- The rest of the data, if there is any, in two runs. -/
theorem restIte_rel (enc : Bool) {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂)
    (A₁ : VG.Proof.AesOcb.Arm.Args p τ₁.mem) (A₂ : VG.Proof.AesOcb.Arm.Args p τ₂.mem) (h8₁ : τ₁.gpr .r8 = p.D) (h8₂ : τ₂.gpr .r8 = p.D) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (.seq (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12,
      .dp .sub .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) (.ite .eq (.block []) (rest enc)))
      VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_envArg L E₁ E₂ A₁ A₂ [.r8] (by simp [h8₁, h8₂]) VG.Proof.AesOcb.Arm.restBlk_check) (VG.Proof.AesOcb.Arm.restBlk_ok L E₁ A₁ h8₁)
    (VG.Proof.AesOcb.Arm.restBlk_ok L E₂ A₂ h8₂) fun _ _ ⟨U₁, h4₁, h5₁, z₁⟩ ⟨U₂, h4₂, h5₂, z₂⟩ =>
  VG.Proof.AesOcb.Arm.rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => VG.Proof.AesOcb.Arm.rel_skip)
    (fun _ => VG.Proof.AesOcb.Arm.rest_rel enc L U₁ U₂ (by rw [h4₁, h4₂]) (by rw [h5₁, h5₂]))

/-- `body` for `seal`, in two runs from the states `body` starts from. -/
theorem bodySeal_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂)
    (A₁ : VG.Proof.AesOcb.Arm.Args p τ₁.mem) (A₂ : VG.Proof.AesOcb.Arm.Args p τ₂.mem) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₁)
    (ho0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p τ₁.mem) 0)
    (hofs₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₂)
    (ho0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p τ₂.mem) 0) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (body true) VG.Proof.AesOcb.Arm.TT := by
  simp only [body, ↓reduceIte]
  refine RelCT.assoc (VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.wholeIte_rel VG.Proof.AesOcb.Arm.encF (.inl rfl) (.inr (.inl rfl)) L E₁ E₂ A₁ A₂)
    (VG.Proof.AesOcb.Arm.wholeIte_ok VG.Proof.AesOcb.Arm.encF (O0 := O₁) (l := VG.Proof.AesOcb.Arm.lstarOf p τ₁.mem)
      (ckF1 := VG.Proof.AesOcb.Arm.ckOf fun i => blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => VG.Proof.AesOcb.Arm.ckOf (fun i => blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      L (VG.Proof.AesOcb.Arm.sealPre_ok L) (VG.Proof.AesOcb.Arm.xorOfs_ok L) E₁ A₁ hofs₁ ho0₁ hck₁ hl0₁ (fun _ => rfl) rfl (fun _ => rfl))
    (VG.Proof.AesOcb.Arm.wholeIte_ok VG.Proof.AesOcb.Arm.encF (O0 := O₂) (l := VG.Proof.AesOcb.Arm.lstarOf p τ₂.mem)
      (ckF1 := VG.Proof.AesOcb.Arm.ckOf fun i => blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => VG.Proof.AesOcb.Arm.ckOf (fun i => blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      L (VG.Proof.AesOcb.Arm.sealPre_ok L) (VG.Proof.AesOcb.Arm.xorOfs_ok L) E₂ A₂ hofs₂ ho0₂ hck₂ hl0₂ (fun _ => rfl) rfl (fun _ => rfl))
    fun _ _ W₁ W₂ => ?_)
  exact VG.Proof.AesOcb.Arm.restIte_rel true L W₁.env W₂.env (A₁.mut L (VG.Proof.AesOcb.Arm.wholeR_mut L (Nat.mul_div_le p.n 16) W₁.frame))
    (A₂.mut L (VG.Proof.AesOcb.Arm.wholeR_mut L (Nat.mul_div_le p.n 16) W₂.frame)) W₁.r8 W₂.r8

/-- `body` for `open`, in two runs from the states `body` starts from. -/
theorem bodyOpen_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂)
    (A₁ : VG.Proof.AesOcb.Arm.Args p τ₁.mem) (A₂ : VG.Proof.AesOcb.Arm.Args p τ₂.mem) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₁)
    (ho0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p τ₁.mem) 0)
    (hofs₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₂)
    (ho0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (VG.Proof.AesOcb.Arm.lstarOf p τ₂.mem) 0) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (body false) VG.Proof.AesOcb.Arm.TT := by
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.wholeIte_rel VG.Proof.AesOcb.Arm.decF (.inr (.inl rfl)) (.inr (.inr rfl)) L E₁ E₂ A₁ A₂)
    (VG.Proof.AesOcb.Arm.wholeIte_ok VG.Proof.AesOcb.Arm.decF (O0 := O₁) (l := VG.Proof.AesOcb.Arm.lstarOf p τ₁.mem) (ckF1 := fun _ => 0)
      (ckF2 := VG.Proof.AesOcb.Arm.ckOf fun i => VG.Proof.AesOcb.Arm.invOf p τ₁.mem
        (blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₁ (VG.Proof.AesOcb.Arm.lstarOf p τ₁.mem) (i + 1)) ^^^
          offAt O₁ (VG.Proof.AesOcb.Arm.lstarOf p τ₁.mem) (i + 1))
      L (VG.Proof.AesOcb.Arm.xorOfs_ok L) (VG.Proof.AesOcb.Arm.openPost_ok L) E₁ A₁ hofs₁ ho0₁ hck₁ hl0₁ (fun _ => rfl) rfl (fun _ => rfl))
    (VG.Proof.AesOcb.Arm.wholeIte_ok VG.Proof.AesOcb.Arm.decF (O0 := O₂) (l := VG.Proof.AesOcb.Arm.lstarOf p τ₂.mem) (ckF1 := fun _ => 0)
      (ckF2 := VG.Proof.AesOcb.Arm.ckOf fun i => VG.Proof.AesOcb.Arm.invOf p τ₂.mem
        (blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₂ (VG.Proof.AesOcb.Arm.lstarOf p τ₂.mem) (i + 1)) ^^^
          offAt O₂ (VG.Proof.AesOcb.Arm.lstarOf p τ₂.mem) (i + 1))
      L (VG.Proof.AesOcb.Arm.xorOfs_ok L) (VG.Proof.AesOcb.Arm.openPost_ok L) E₂ A₂ hofs₂ ho0₂ hck₂ hl0₂ (fun _ => rfl) rfl (fun _ => rfl))
    fun _ _ W₁ W₂ => ?_)
  exact VG.Proof.AesOcb.Arm.restIte_rel false L W₁.env W₂.env (A₁.mut L (VG.Proof.AesOcb.Arm.wholeR_mut L (Nat.mul_div_le p.n 16) W₁.frame))
    (A₂.mut L (VG.Proof.AesOcb.Arm.wholeR_mut L (Nat.mul_div_le p.n 16) W₂.frame)) W₁.r8 W₂.r8

/-! ## The tag -/

theorem tagA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs []))
    (.block (copy16 ckO tmpO ++ xorW ofsO tmpO ++ xorW ldO tmpO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem tagB_check {d : Nat} (hd : d = tagO ∨ d = t2O) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [])) (.block (copy16 tmpO d ++ xorW sumO d)) h).isSome = true := by
  rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag d`, in two runs with the same public arguments. -/
theorem tag_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {τ₁ τ₂ : State} (E₁ : VG.Proof.AesOcb.Arm.Env p τ₁) (E₂ : VG.Proof.AesOcb.Arm.Env p τ₂) {d : Nat}
    (hd : d = tagO ∨ d = t2O) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 τ₁ τ₂) (tag d) VG.Proof.AesOcb.Arm.TT :=
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_env E₁ E₂ [] (by simp) VG.Proof.AesOcb.Arm.tagA_check)
    (VG.Proof.AesOcb.Arm.kept_of L E₁ [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L E₂ [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.encOne_rel L K₁.env K₂.env (.inl rfl))
    (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (VG.Proof.AesOcb.Arm.exec_of_wp (VG.Proof.AesOcb.Arm.encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  VG.Proof.AesOcb.Arm.rel_env (C₁.env K₁.env) (C₂.env K₂.env) [] (by simp) (VG.Proof.AesOcb.Arm.tagB_check hd)

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.CTFn`. -/
section

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_seal` and `vg_aes_ocb_open` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments (`onePub`) have the same `prmOf`; each piece of `seal` and
`open` is related in the two runs by the lemmas of `CTPre.lean` and
`CTBody.lean`, the entry, the copy of the tag, the comparison, the mask and
the restore by the taint analysis (`seal_ct`, `open_ct`). `open` compares
the tags and masks the data without a branch: whether the tag is right, in
`r0`, is never branched on nor used as an address.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm addI restore)

/-- `(a; (b; (c; (d; e)))); f`, from `a; (b; (c; (d; (e; f))))`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e f : Prog isa}
    (h : RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e f))))) Q) :
    RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) f) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ f₁ => cases a₁ with | seq a₁ b₁ => cases b₁ with | seq b₁ c₁ => cases c₁ with
    | seq c₁ d₁ => cases d₁ with | seq d₁ e₁ =>
  cases e₂ with | seq a₂ f₂ => cases a₂ with | seq a₂ b₂ => cases b₂ with | seq b₂ c₂ => cases c₂ with
    | seq c₂ d₂ => cases d₂ with | seq d₂ e₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq e₁ f₁)))))
    (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq e₂ f₂)))))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- Two runs with the same public arguments have the same `prmOf`. -/
theorem prm_eq {s₁ s₂ : State} (h : VG.Proof.AesOcb.Arm.onePub s₁ s₂) : VG.Proof.AesOcb.Arm.prmOf s₂ = VG.Proof.AesOcb.Arm.prmOf s₁ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := h
  simp only [VG.Proof.AesOcb.Arm.prmOf, ← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide), ← qa 6 (by decide)]

theorem entry_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint [.r0, .r1, .r2, .r3] 28) (.block entry) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {σ₁ σ₂ : State} (P₁ : VG.Proof.AesOcb.Arm.Perm p σ₁) (P₂ : VG.Proof.AesOcb.Arm.Perm p σ₂) (h₁ : σ₁.sp = p.SP)
    (h₂ : σ₂.sp = p.SP) (hq : VG.Proof.AesOcb.Arm.onePub σ₁ σ₂) : RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.block entry) VG.Proof.AesOcb.Arm.TT := by
  obtain ⟨-, q₀, q₁, q₂, q₃, qa⟩ := hq
  have spf := L.spf
  have hw : ∀ {σ : State}, σ.sp = p.SP → VG.Proof.AesOcb.Arm.Perm p σ →
      σ.sp.toNat + 28 ≤ 2 ^ 32 ∧ ∀ r ∈ σ.wr, Region.Disjoint ⟨State.addr σ.sp, 28⟩ r := fun h P =>
    ⟨by rw [h]; omega, fun r hr => by rw [h]; exact P.argw r hr⟩
  refine VG.Proof.AesOcb.Arm.rel_arg [.r0, .r1, .r2, .r3] 28 (fun r hr => ?_) (by rw [h₁, h₂]) (hw h₁ P₁) (hw h₂ P₂)
    (fun k hk => argMem_of (j := 7) (by rw [h₁, h₂]) (by rw [h₁]; omega) qa k (by omega)) VG.Proof.AesOcb.Arm.entry_check
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [q₀, q₁, q₂, q₃]

/-- What the entry and `Offset_0` leave. -/
abbrev EN (p : VG.Proof.AesOcb.Arm.Prm) (σ : State) (c : State) : Prop := ∃ a, VG.Proof.AesOcb.Arm.EntryPost p σ a ∧ VG.Proof.AesOcb.Arm.NonceOut p a c

/-- The entry and `Offset_0`. -/
theorem en_wp {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {s₀ : State} (P : VG.Proof.AesOcb.Arm.Perm p s₀) (A : VG.Proof.AesOcb.Arm.Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.seq (.block entry) nonce) s₀ (VG.Proof.AesOcb.Arm.EN p s₀) :=
  WP.seq (WP.mono (VG.Proof.AesOcb.Arm.entry_wp L P hsp h0 h1 h2 h3 hW) fun a Ea =>
    WP.mono (VG.Proof.AesOcb.Arm.nonce_ok L Ea.env (VG.Proof.AesOcb.Arm.args_W L Ea.frame A) Ea.r4 Ea.r5) fun _ Nc => ⟨a, Ea, Nc⟩)

/-- The entry, `Offset_0` and `HASH`, in two runs with the same public
arguments. -/
theorem pre_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {σ₁ σ₂ : State} (P₁ : VG.Proof.AesOcb.Arm.Perm p σ₁) (P₂ : VG.Proof.AesOcb.Arm.Perm p σ₂) (A₁ : VG.Proof.AesOcb.Arm.Args p σ₁.mem)
    (A₂ : VG.Proof.AesOcb.Arm.Args p σ₂.mem) (hs₁ : σ₁.sp = p.SP) (hs₂ : σ₂.sp = p.SP)
    (h0₁ : σ₁.gpr .r0 = p.K) (h1₁ : σ₁.gpr .r1 = BitVec.ofNat 32 p.R) (h2₁ : σ₁.gpr .r2 = p.N)
    (h3₁ : σ₁.gpr .r3 = BitVec.ofNat 32 p.nl)
    (hW₁ : σ₁.mem.readW (State.addr (σ₁.sp + BitVec.ofNat 32 24)) 32 = p.W)
    (h0₂ : σ₂.gpr .r0 = p.K) (h1₂ : σ₂.gpr .r1 = BitVec.ofNat 32 p.R) (h2₂ : σ₂.gpr .r2 = p.N)
    (h3₂ : σ₂.gpr .r3 = BitVec.ofNat 32 p.nl)
    (hW₂ : σ₂.mem.readW (State.addr (σ₂.sp + BitVec.ofNat 32 24)) 32 = p.W) (hq : VG.Proof.AesOcb.Arm.onePub σ₁ σ₂) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) (.seq (.seq (.block entry) nonce) Impl.AesOcb.Arm.hash) VG.Proof.AesOcb.Arm.TT := by
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.entry_rel L P₁ P₂ hs₁ hs₂ hq) (VG.Proof.AesOcb.Arm.entry_wp L P₁ hs₁ h0₁ h1₁ h2₁ h3₁ hW₁)
    (VG.Proof.AesOcb.Arm.entry_wp L P₂ hs₂ h0₂ h1₂ h2₂ h3₂ hW₂) fun a₁ a₂ E₁ E₂ => VG.Proof.AesOcb.Arm.nonce_rel L E₁.env E₂.env (VG.Proof.AesOcb.Arm.args_W L E₁.frame A₁)
      (VG.Proof.AesOcb.Arm.args_W L E₂.frame A₂) (by rw [E₁.r4, E₂.r4]) (by rw [E₁.r5, E₂.r5]))
    (VG.Proof.AesOcb.Arm.en_wp L P₁ A₁ hs₁ h0₁ h1₁ h2₁ h3₁ hW₁) (VG.Proof.AesOcb.Arm.en_wp L P₂ A₂ hs₂ h0₂ h1₂ h2₂ h3₂ hW₂)
    fun _ _ ⟨a₁, E₁, N₁⟩ ⟨a₂, E₂, N₂⟩ => ?_
  have l0 : ∀ {σ a c : State}, VG.Proof.AesOcb.Arm.EntryPost p σ a → VG.Proof.AesOcb.Arm.NonceOut p a c →
      blockAtMem c.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (VG.Proof.AesOcb.Arm.lstarOf p c.mem) 0 := fun E N => by
    rw [blockAtMem_frame N.frame (by wdisj L), E.l0]
    exact congrArg (Spec.Ocb.lAt · 0) ((VG.Proof.AesOcb.Arm.lstar_mut L (VG.Proof.AesOcb.Arm.nonceR_mut L N.frame)).trans (VG.Proof.AesOcb.Arm.lstar_W L E.frame)).symm
  exact VG.Proof.AesOcb.Arm.hash_rel L N₁.env N₂.env ((VG.Proof.AesOcb.Arm.args_W L E₁.frame A₁).mut L (VG.Proof.AesOcb.Arm.nonceR_mut L N₁.frame))
    ((VG.Proof.AesOcb.Arm.args_W L E₂.frame A₂).mut L (VG.Proof.AesOcb.Arm.nonceR_mut L N₂.frame)) (l0 E₁ N₁) (l0 E₂ N₂)

theorem tagOut_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs []) 24) tagOut h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (VG.Proof.AesOcb.Arm.pubRegs [])) (.block restore)
    h).isSome = true := ⟨_, by taint_decide⟩

/-- What `seal` and `open` know of a run at the entry. -/
structure Run (p : VG.Proof.AesOcb.Arm.Prm) (σ : State) : Prop where
  perm : VG.Proof.AesOcb.Arm.Perm p σ
  args : VG.Proof.AesOcb.Arm.Args p σ.mem
  sp : σ.sp = p.SP
  r0 : σ.gpr .r0 = p.K
  r1 : σ.gpr .r1 = BitVec.ofNat 32 p.R
  r2 : σ.gpr .r2 = p.N
  r3 : σ.gpr .r3 = BitVec.ofNat 32 p.nl
  w : σ.mem.readW (State.addr (σ.sp + BitVec.ofNat 32 24)) 32 = p.W

theorem run_of {σ : State} (P : VG.Proof.AesOcb.Arm.Perm (VG.Proof.AesOcb.Arm.prmOf σ) σ) : VG.Proof.AesOcb.Arm.Run (VG.Proof.AesOcb.Arm.prmOf σ) σ :=
  ⟨P, VG.Proof.AesOcb.Arm.args_of σ, rfl, rfl, (VG.Proof.AesOcb.Arm.ofNat_toNat32' _).symm, rfl, (VG.Proof.AesOcb.Arm.ofNat_toNat32' _).symm, rfl⟩

/-- `vg_aes_ocb_seal`, in two runs with the same public arguments. -/
theorem seal_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {σ₁ σ₂ : State} (R₁ : VG.Proof.AesOcb.Arm.Run p σ₁) (R₂ : VG.Proof.AesOcb.Arm.Run p σ₂) (hq : VG.Proof.AesOcb.Arm.onePub σ₁ σ₂) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) «seal» VG.Proof.AesOcb.Arm.TT := by
  unfold «seal» front
  refine VG.Proof.AesOcb.Arm.rel_assoc5 (RelCT.assoc (RelCT.assoc (VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.pre_rel L R₁.perm R₂.perm R₁.args R₂.args R₁.sp R₂.sp
    R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w hq)
    (WP.assoc' (VG.Proof.AesOcb.Arm.pre_wp' L R₁.perm R₁.args R₁.sp R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w))
    (WP.assoc' (VG.Proof.AesOcb.Arm.pre_wp' L R₂.perm R₂.args R₂.sp R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w)) fun e₁ e₂ P₁ P₂ => ?_)))
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.bodySeal_rel L P₁.env P₂.env P₁.args P₂.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar])
    P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar]))
    (VG.Proof.AesOcb.Arm.bodySeal_ok L P₁.env P₁.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar]))
    (VG.Proof.AesOcb.Arm.bodySeal_ok L P₂.env P₂.args P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar])) fun f₁ f₂ B₁ B₂ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.tag_rel L B₁.env B₂.env (.inl rfl)) (VG.Proof.AesOcb.Arm.tag_ok L B₁.env (.inl rfl)) (VG.Proof.AesOcb.Arm.tag_ok L B₂.env (.inl rfl))
    fun g₁ g₂ T₁ T₂ => ?_
  have A₁ : VG.Proof.AesOcb.Arm.Args p g₁.mem := (P₁.args.mut L (VG.Proof.AesOcb.Arm.bodyR_mut L B₁.frame)).mut L (VG.Proof.AesOcb.Arm.tagR_mut L (.inl (by decide)) T₁.frame)
  have A₂ : VG.Proof.AesOcb.Arm.Args p g₂.mem := (P₂.args.mut L (VG.Proof.AesOcb.Arm.bodyR_mut L B₂.frame)).mut L (VG.Proof.AesOcb.Arm.tagR_mut L (.inl (by decide)) T₂.frame)
  exact VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_envArg L T₁.env T₂.env A₁ A₂ [] (by simp) VG.Proof.AesOcb.Arm.tagOut_check)
    (VG.Proof.AesOcb.Arm.kept_of L T₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L T₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun _ _ K₁ K₂ => VG.Proof.AesOcb.Arm.rel_env K₁.env K₂.env [] (by simp) VG.Proof.AesOcb.Arm.restore_check

theorem recv_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs []) 24) recv h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs []) 24) cmp h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint (VG.Proof.AesOcb.Arm.pubRegs []) 24) mask h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `vg_aes_ocb_open`, in two runs with the same public arguments. -/
theorem open_rel {p : VG.Proof.AesOcb.Arm.Prm} (L : VG.Proof.AesOcb.Arm.Lay p) {σ₁ σ₂ : State} (R₁ : VG.Proof.AesOcb.Arm.Run p σ₁) (R₂ : VG.Proof.AesOcb.Arm.Run p σ₂) (hq : VG.Proof.AesOcb.Arm.onePub σ₁ σ₂) :
    RelCT isa (VG.Proof.AesOcb.Arm.Eq2 σ₁ σ₂) «open» VG.Proof.AesOcb.Arm.TT := by
  unfold «open» front
  refine VG.Proof.AesOcb.Arm.rel_assoc5 (RelCT.assoc (RelCT.assoc (VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.pre_rel L R₁.perm R₂.perm R₁.args R₂.args R₁.sp R₂.sp
    R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w hq)
    (WP.assoc' (VG.Proof.AesOcb.Arm.pre_wp' L R₁.perm R₁.args R₁.sp R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w))
    (WP.assoc' (VG.Proof.AesOcb.Arm.pre_wp' L R₂.perm R₂.args R₂.sp R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w)) fun e₁ e₂ P₁ P₂ => ?_)))
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.bodyOpen_rel L P₁.env P₂.env P₁.args P₂.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar])
    P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar]))
    (VG.Proof.AesOcb.Arm.bodyOpen_ok L P₁.env P₁.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar]))
    (VG.Proof.AesOcb.Arm.bodyOpen_ok L P₂.env P₂.args P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar])) fun f₁ f₂ B₁ B₂ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seq (VG.Proof.AesOcb.Arm.tag_rel L B₁.env B₂.env (.inr rfl)) (VG.Proof.AesOcb.Arm.tag_ok L B₁.env (.inr rfl)) (VG.Proof.AesOcb.Arm.tag_ok L B₂.env (.inr rfl))
    fun g₁ g₂ T₁ T₂ => ?_
  have A₁ : VG.Proof.AesOcb.Arm.Args p g₁.mem :=
    (P₁.args.mut L (VG.Proof.AesOcb.Arm.bodyR_mut L B₁.frame)).mut L (VG.Proof.AesOcb.Arm.tagR_mut L (.inr ⟨by decide, by decide⟩) T₁.frame)
  have A₂ : VG.Proof.AesOcb.Arm.Args p g₂.mem :=
    (P₂.args.mut L (VG.Proof.AesOcb.Arm.bodyR_mut L B₂.frame)).mut L (VG.Proof.AesOcb.Arm.tagR_mut L (.inr ⟨by decide, by decide⟩) T₂.frame)
  refine VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_envArg L T₁.env T₂.env A₁ A₂ [] (by simp) VG.Proof.AesOcb.Arm.recv_check)
    (VG.Proof.AesOcb.Arm.kept_of L T₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L T₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun h₁ h₂ K₁ K₂ => ?_
  refine VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_envArg L K₁.env K₂.env (K₁.args A₁) (K₂.args A₂) [] (by simp) VG.Proof.AesOcb.Arm.cmp_check)
    (VG.Proof.AesOcb.Arm.kept_of L K₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L K₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun i₁ i₂ M₁ M₂ => ?_
  exact VG.Proof.AesOcb.Arm.rel_seqX (VG.Proof.AesOcb.Arm.rel_envArg L M₁.env M₂.env (M₁.args (K₁.args A₁)) (M₂.args (K₂.args A₂)) [] (by simp) VG.Proof.AesOcb.Arm.mask_check)
    (VG.Proof.AesOcb.Arm.kept_of L M₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (VG.Proof.AesOcb.Arm.kept_of L M₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun _ _ N₁ N₂ => VG.Proof.AesOcb.Arm.rel_env N₁.env N₂.env [] (by simp) VG.Proof.AesOcb.Arm.restore_check

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» := by
  refine VG.Proof.AesOcb.Arm.ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have e := VG.Proof.AesOcb.Arm.prm_eq hq
  have R₂ := VG.Proof.AesOcb.Arm.run_of (VG.Proof.AesOcb.Arm.sealPerm h₂)
  rw [e] at R₂
  exact VG.Proof.AesOcb.Arm.seal_rel (VG.Proof.AesOcb.Arm.lay_of h₁.2.2.1) (VG.Proof.AesOcb.Arm.run_of (VG.Proof.AesOcb.Arm.sealPerm h₁)) R₂ hq

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» := by
  refine VG.Proof.AesOcb.Arm.ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have e := VG.Proof.AesOcb.Arm.prm_eq hq.1
  have R₂ := VG.Proof.AesOcb.Arm.run_of (VG.Proof.AesOcb.Arm.openPerm h₂)
  rw [e] at R₂
  exact VG.Proof.AesOcb.Arm.open_rel (VG.Proof.AesOcb.Arm.lay_of h₁.2.2) (VG.Proof.AesOcb.Arm.run_of (VG.Proof.AesOcb.Arm.openPerm h₁)) R₂ hq.1

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Verified`. -/
section

/-!
# AES-OCB on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`), with 8 bytes of stack: each call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` pushes two words.
`Frame.lean` allocates the working space.
-/

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Impl.AesOcb.Arm

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte
nonce, no associated data, no data, a 4-byte tag at `0x3000` and `work` at
0. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { VG.Proof.AesOcb.Arm.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 28⟩], wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesOcb.sealScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesOcb.Arm.seal_wp hs) VG.Proof.AesOcb.Arm.seal_ct (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, VG.Proof.AesOcb.Arm.sealArm, VG.Proof.AesOcb.Arm.sealPre, VG.Proof.AesOcb.Arm.oneLay, VG.Proof.AesOcb.Arm.onePub, VG.Proof.AesOcb.Arm.bel, VG.Proof.AesOcb.Arm.arg, VG.Proof.AesOcb.Arm.args, VG.Proof.AesOcb.Arm.roundsOk, VG.Proof.AesOcb.Arm.ciph, VG.Proof.AesOcb.Arm.lstar, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesOcb.Arm.sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesOcb.openScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesOcb.Arm.open_wp hs) VG.Proof.AesOcb.Arm.open_ct
    { pre := by
        sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, VG.Proof.AesOcb.Arm.openArm, VG.Proof.AesOcb.Arm.openPre, VG.Proof.AesOcb.Arm.oneLay, VG.Proof.AesOcb.Arm.onePub, VG.Proof.AesOcb.Arm.openLeak, VG.Proof.AesOcb.Arm.bel, VG.Proof.AesOcb.Arm.arg, VG.Proof.AesOcb.Arm.args, VG.Proof.AesOcb.Arm.roundsOk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [VG.Proof.AesOcb.Arm.openArm, VG.Proof.AesOcb.Arm.openRes, VG.Proof.AesOcb.Arm.ciph, VG.Proof.AesOcb.Arm.inv, VG.Proof.AesOcb.Arm.lstar, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, VG.Proof.AesOcb.Arm.openArm, VG.Proof.AesOcb.Arm.openPre, VG.Proof.AesOcb.Arm.oneLay, VG.Proof.AesOcb.Arm.onePub, VG.Proof.AesOcb.Arm.openLeak, VG.Proof.AesOcb.Arm.openRes, VG.Proof.AesOcb.Arm.ciph, VG.Proof.AesOcb.Arm.inv, VG.Proof.AesOcb.Arm.lstar, VG.Proof.AesOcb.Arm.bel, VG.Proof.AesOcb.Arm.arg, VG.Proof.AesOcb.Arm.args,
          VG.Proof.AesOcb.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
        · exact a6
      sat := by
        sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, VG.Proof.AesOcb.Arm.openArm, VG.Proof.AesOcb.Arm.openPre, VG.Proof.AesOcb.Arm.oneLay, VG.Proof.AesOcb.Arm.onePub, VG.Proof.AesOcb.Arm.openLeak, VG.Proof.AesOcb.Arm.bel, VG.Proof.AesOcb.Arm.arg, VG.Proof.AesOcb.Arm.args, VG.Proof.AesOcb.Arm.roundsOk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesOcb.Arm.openSat }

end VG.Proof.AesOcb.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.Arm.Frame`. -/
section

/-!
# AES-OCB on ARMv7, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): their working space is their seventh stack
argument, after `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`, so the
frame of 2592 bytes holds a copy of those six words, the address of the
working space, the saved `lr` and the working space. The copies are read
only where the pre- and postconditions read the buffers, and `open`'s leak,
whether it succeeds, reads only its buffers (`Proof/AesOcb/Scratch.lean`).
-/

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Impl.AesOcb.Arm

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { VG.Proof.AesOcb.Arm.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesOcb.Arm.sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»)
      (Spec.Ocb.sealContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre Arm.abi.ptrBits)
    (post := Spec.Ocb.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) VG.Proof.AesOcb.Arm.seal_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _) VG.Proof.AesOcb.Arm.sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { VG.Proof.AesOcb.Arm.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesOcb.Arm.openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Spec.Ocb.openContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre Arm.abi.ptrBits)
    (post := Spec.Ocb.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak Arm.abi.ptrBits))
    (m := 6) VG.Proof.AesOcb.Arm.open_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _) VG.Proof.AesOcb.Arm.openFrameSat_pre
    (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.Arm

end
