module

public import VerifiedGarbage.Impl.AesGcm.Arm.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Loop
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM decryption out of place, by a copy, ARMv7: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against (`toK`), which the shared one implies
(`OpenTo/Verified.lean`), and its proof (`openTo_wp`). It calls an instance
of `vg_aes_gcm_open` as an artifact, with its working space in a frame of
its own, so what the proof needs of it is its shared contract
(`Proof.AesGcm.openRoundsContract`, with 2600 bytes of stack, `OpenFn`).

With `B` the base of the 2648 bytes of stack below the stack pointer
(`sp = B + 2648`), the function allocates its frame of 48 bytes at
`P = B + 2600` (`WP.alloc`), keeps our return address and `r0`–`r3` in it
and lays out the call's six stack arguments (`entered_wp`). It copies the
`len` bytes at `src` to `dst` (`copied_wp`, by `Gather.copySlice_wp`, from
the descriptor that our stack arguments `src` and `len` form), reloads
`r0`–`r3` (`ready_wp`), calls `vg_aes_gcm_open` on `dst` in place
(`called_wp`), which writes only `dst` and the stack below our frame, and
zeroes `dst` if it returned 0 (`after_wp`, `wipe_wp`); then it reloads our
return address (`ret_wp`). Every write is to `dst` or to the stack below
`sp`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.OpenTo

open VG VG.Arm VG.Arm.RegUpd VG.Arm.FrameStack VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Impl.AesGcm.Arm.SealGather (setFp copySlice)
open VG.Proof.AesGcm.Arm (in_left add_ofNat_zero covers_of_mem covers_cons covers_append' covers_prefix covers_nil
  eval_eq' eval_ne' z_cmp0 dec32 z_dec)
open VG.Proof.AesGcm.Arm.Gather (SlicePre Keeps Keeps.gkeeps copySlice_wp gatherRegs add_ofNat_sub_ofNat
  contains_off z_ne0)

/-! ## The arguments and the contract -/

section
variable (s : State)

/-- The arguments `(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad, aad_len, src, len, dst, dst_len, tag, tag_len)`, the last eight on the
stack. -/
abbrev K : BitVec 32 := s.gpr .r0
abbrev Nn : BitVec 32 := s.gpr .r2
abbrev NL : Nat := (s.gpr .r3).toNat
abbrev Ad : BitVec 32 := stackArg s 0
abbrev AL : Nat := (stackArg s 1).toNat
abbrev Src : BitVec 32 := stackArg s 2
abbrev L : Nat := (stackArg s 3).toNat
abbrev Dst : BitVec 32 := stackArg s 4
abbrev Tg : BitVec 32 := stackArg s 6
abbrev TL : Nat := (stackArg s 7).toNat

/-- The regions: the key context, the nonce, the additional data, the
ciphertext, the output, the tag, the stack arguments and the stack below
the stack pointer. -/
abbrev kR : Region := ⟨State.addr (K s), 256⟩
abbrev nR : Region := ⟨State.addr (Nn s), NL s⟩
abbrev aR : Region := ⟨State.addr (Ad s), AL s⟩
abbrev sR : Region := ⟨State.addr (Src s), L s⟩
abbrev dR : Region := ⟨State.addr (Dst s), L s⟩
abbrev tR : Region := ⟨State.addr (Tg s), TL s⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev stkR : Region := ⟨State.addr s.sp - BitVec.ofNat 64 2648, 2648⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (State.addr (K s)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (K s))) (TL s)
    (bytesAt s.mem (State.addr (Nn s)) (NL s)) (bytesAt s.mem (State.addr (Src s)) (L s))
    (bytesAt s.mem (State.addr (Ad s)) (AL s)) (bytesAt s.mem (State.addr (Tg s)) (TL s))

end

/-- What the proof of `vg_aes_gcm_open_to` needs: the layout of its shared
contract, with 2648 bytes of stack, `dst_len` its `len`. -/
structure ToPre (s : State) : Prop where
  w₁ : 2648 ≤ s.sp.toNat
  w₂ : s.sp.toNat + 32 ≤ 2 ^ 32
  rd : s.rd = [kR s, nR s, aR s, sR s, tR s, argR s]
  wr : s.wr = [dR s]
  kd : (kR s).Disjoint (dR s)
  nd : (nR s).Disjoint (dR s)
  ad : (aR s).Disjoint (dR s)
  sd : (sR s).Disjoint (dR s)
  dt : (dR s).Disjoint (tR s)
  da : (dR s).Disjoint (argR s)
  bk : (stkR s).Disjoint (kR s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bs : (stkR s).Disjoint (sR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tR s)
  barg : (stkR s).Disjoint (argR s)
  ok : (K s).toNat + 256 ≤ 2 ^ 32
  on : (Nn s).toNat + NL s ≤ 2 ^ 32
  oa : (Ad s).toNat + AL s ≤ 2 ^ 32
  os : (Src s).toNat + L s ≤ 2 ^ 32
  od : (Dst s).toNat + L s ≤ 2 ^ 32
  ot : (Tg s).toNat + TL s ≤ 2 ^ 32
  hR : (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14

/-- `openToRoundsPost`, for the rounds of `ToPre`, with the result in `r0`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (Dst s)) (L s) = pt
  | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr (Dst s)) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak: whether it succeeds. -/
def toLeak (s : State) : List Nat :=
  if ¬((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) then []
  else [if (res s).isSome = true then 1 else 0]

/-- What two runs agree on: the stack pointer, the arguments and the leak. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ toLeak s₁ = toLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 8, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_open_to`. -/
def toK : Contract isa where
  pre := ToPre
  post := toPost
  pub := toPub

/-! ## The function called -/

/-- An instance of `vg_aes_gcm_open`, by its shared contract, whose frames
use at most the 2600 bytes below the stack pointer that the contract
reserves. -/
structure OpenFn where
  name : String
  code : Prog isa
  verified : Verified Arm.target code (Proof.AesGcm.openRoundsContract Arm.abi 2600)
  depth : armStack code ≤ 2600

/-- What a call of `vg_aes_gcm_open(ctx = r0, rounds = r1, nonce = r2,
nonce_len = r3, aad = [sp], aad_len = [sp + 4], data = [sp + 8],
len = [sp + 12], tag = [sp + 16], tag_len = [sp + 20])` needs. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  let data : Region := ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  let tag : Region := ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩
  let arg : Region := ⟨stackArgAddr s 0, 24⟩
  let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 2600, 2600⟩
  s.rd = [ctx, nonce, aad, tag, arg] ∧ s.wr = [data] ∧
    ctx.Disjoint data ∧ nonce.Disjoint data ∧ aad.Disjoint data ∧ data.Disjoint tag ∧ data.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 32 ∧ 2600 ≤ s.sp.toNat ∧ s.sp.toNat + 24 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)

/-- The shared contract's precondition, from the layout the call gives. -/
theorem openSpec_pre {s : State} (h : callPre s) : (Proof.AesGcm.openRoundsContract Arm.abi 2600).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀
  have a₂₁ := h
  clear h
  sig_pre [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact ⟨a₁₉, a₂₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₂₁⟩

/-- `vg_aes_gcm_open`'s result on the arguments of a call. -/
abbrev callRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0)))
    (stackArg s 5).toNat (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
    (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
    (bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat)

/-- Its postcondition, for rounds of 10, 12 or 14. -/
theorem openSpec_post {s s' : State} (h : (Proof.AesGcm.openRoundsContract Arm.abi 2600).post s s')
    (hR : (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) :
    match callRes s with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 := by
  sig_post [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Proof.AesGcm.openRoundsPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq] at h
  have h' := h hR
  have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
  split
  · rename_i pt heq
    dsimp only [callRes, State.addr] at heq
    rw [heq, e] at h'
    exact h'
  · rename_i heq
    dsimp only [callRes, State.addr] at heq
    rw [heq, e] at h'
    exact h'.1

/-- The public data of a call: whether it succeeds. -/
def callLeak (s : State) : List Nat :=
  if ¬((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) then []
  else [if (callRes s).isSome = true then 1 else 0]

/-- Its public data, from the arguments and the leak. -/
theorem openSpec_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ callLeak s₁ = callLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    ∀ i < 6, stackArg s₁ i = stackArg s₂ i) : (Proof.AesGcm.openRoundsContract Arm.abi 2600).pub s₁ s₂ := by
  obtain ⟨q, l, a₀, a₁, a₂, a₃, a⟩ := h
  sig_pub [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact ⟨q, l, a₀, a₁, a₂, a₃, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide),
    a 4 (by decide), a 5 (by decide)⟩

/-! ## Words of the frame -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 80 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 80) : State.addr (P + BitVec.ofNat 32 d) = State.addr P + BitVec.ofNat 64 d :=
  addr_add (by omega_arith)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 80) (he : e + 4 ≤ 80) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega_arith), aP hP (by omega_arith)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 80) (h : 4 ≤ e) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr P) 32 = m.readW (State.addr P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_ofNat_zero] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 80) (h : 4 ≤ d) :
    (m.writeW (State.addr P) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_ofNat_zero] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

/-- The memory after the entry, at the frame `P`: our return address and
`r0`–`r3` at `P + 24` … `P + 40`, and the six words at `P + 48`, `P + 52`,
`P + 64`, `P + 60`, `P + 72` and `P + 76` (`aad`, `aad_len`, `dst`, `len`,
`tag`, `tag_len`) at `P` … `P + 20`. -/
def eMem (m : Mem) (P : BitVec 32) (lr r0 r1 r2 r3 : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (State.addr (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (State.addr (P + BitVec.ofNat 32 d)) 32
  w (w (w (w (w ((w (w (w (w (w m 24 lr) 28 r0) 32 r1) 36 r2) 40 r3).writeW (State.addr P) (r 48)) 4 (r 52))
    8 (r 64)) 12 (r 60)) 16 (r 72)) 20 (r 76)

theorem entry_ok (a : State) (hP : a.sp.toNat + 80 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 48 → InRegions a.wr (State.addr (a.sp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 48 ≤ d → d + 4 ≤ 80 → InRegions (a.rd ++ a.wr) (State.addr (a.sp + BitVec.ofNat 32 d)) 4) :
    WP isa entry a fun e =>
      e.mem = eMem a.mem a.sp (a.gpr .lr) (a.gpr .r0) (a.gpr .r1) (a.gpr .r2) (a.gpr .r3) ∧
      e.gpr .r0 = a.sp + BitVec.ofNat 32 56 ∧
      e.gpr .r2 = a.mem.readW (State.addr (a.sp + BitVec.ofNat 32 64)) 32 ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r12 → r ≠ .lr → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  have hw0 : InRegions a.wr (State.addr a.sp) 4 := by simpa only [add_ofNat_zero] using hw 0 (by decide)
  refine Gather.WP.split (l₁ := setFp) (l₂ := entryWords) ?_
  refine WP.run ⟨_, by
    arun [setFp, entryWords, hw 24 (by decide), hw 28 (by decide), hw 32 (by decide), hw 36 (by decide),
      hw 40 (by decide), hw0, hw 4 (by decide), hw 8 (by decide), hw 12 (by decide), hw 16 (by decide),
      hw 20 (by decide), hr 48 (by decide) (by decide), hr 52 (by decide) (by decide),
      hr 60 (by decide) (by decide), hr 64 (by decide) (by decide), hr 72 (by decide) (by decide),
      hr 76 (by decide) (by decide), add_ofNat_zero, rdw hP, rdw0 hP, rd0w hP], rfl⟩ fun e he => ?_
  subst he
  exact ⟨rfl, rfl, rfl, fun r h₀ h₂ h₁₂ hl => by simp [gpr_setReg, h₀, h₂, h₁₂, hl], rfl, rfl, rfl⟩

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 80 ≤ 2 ^ 32) (lr r0 r1 r2 r3 : BitVec 32)
include hP

/-- The entry writes only the frame. -/
theorem eMem_frame : Frame [⟨State.addr P, 48⟩] m (eMem m P lr r0 r1 r2 r3) := by
  have c (d : Nat) (hd : d + 4 ≤ 48) : (⟨State.addr P, 48⟩ : Region).Contains (State.addr (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega_arith)]; exact Offset.contains_base _ hd (by omega_arith)
  have c0 : (⟨State.addr P, 48⟩ : Region).Contains (State.addr P) 4 := by simp [Region.Contains]
  have hm := List.mem_singleton_self (⟨State.addr P, 48⟩ : Region)
  exact ((((((((((((Frame.refl _ m).writeW hm _ (c 24 (by decide))).writeW hm _ (c 28 (by decide))).writeW hm _
    (c 32 (by decide))).writeW hm _ (c 36 (by decide))).writeW hm _ (c 40 (by decide))).writeW hm _ c0).writeW hm _
    (c 4 (by decide))).writeW hm _ (c 8 (by decide))).writeW hm _ (c 12 (by decide))).writeW hm _
    (c 16 (by decide))).writeW hm _ (c 20 (by decide)))

/-- The words of the frame after the entry. -/
theorem eMem_words :
    let e := eMem m P lr r0 r1 r2 r3
    let r (m : Mem) (d : Nat) := m.readW (State.addr (P + BitVec.ofNat 32 d)) 32
    e.readW (State.addr P) 32 = r m 48 ∧ r e 4 = r m 52 ∧ r e 8 = r m 64 ∧ r e 12 = r m 60 ∧ r e 16 = r m 72 ∧
      r e 20 = r m 76 ∧ r e 24 = lr ∧ r e 28 = r0 ∧ r e 32 = r1 ∧ r e 36 = r2 ∧ r e 40 = r3 := by
  simp (disch := first | decide | omega_arith) only [eMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end

/-! ## The layout -/

section
variable (s : State)

/-- The frame, the base of the 2648 bytes of stack below the stack pointer,
and the frame as a region. -/
abbrev Pf : BitVec 32 := s.sp - BitVec.ofNat 32 48
abbrev Bs : Addr := State.addr s.sp - BitVec.ofNat 64 2648
abbrev FR : Region := ⟨State.addr (Pf s), 48⟩

/-- The memory after the entry. -/
abbrev eM : Mem := eMem s.mem (Pf s) (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)

/-- The memory once the ciphertext is copied to `dst`. -/
abbrev cM : Mem := writeBytes (eM s) (State.addr (Dst s)) (bytesAt s.mem (State.addr (Src s)) (L s))

end

/-- What `ToPre` gives, with the frame at `Pf s` and the stack below the
stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : ToPre s
  hP : (Pf s).toNat + 80 ≤ 2 ^ 32
  hPn : (Pf s).toNat = s.sp.toNat - 48
  hBn : (Bs s).toNat + 2680 ≤ 2 ^ 32
  hA0 : State.addr (Pf s) = Bs s + BitVec.ofNat 64 2600
  sa : ∀ i, i < 8 → s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 (48 + 4 * i))) 32 = stackArg s i

theorem lay {s : State} (hs : ToPre s) : Lay s := by
  have w₁ := hs.w₁
  have w₂ := hs.w₂
  have hPn : (Pf s).toNat = s.sp.toNat - 48 := sub_toNat' (by omega_arith)
  have hB : Bs s = State.addr (s.sp - BitVec.ofNat 32 2648) := (addr_sub' (by omega_arith)).symm
  have hBn : (Bs s).toNat = s.sp.toNat - 2648 := by
    rw [hB]; simp only [State.addr, BitVec.toNat_setWidth]
    rw [sub_toNat' (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have hA0 : State.addr (Pf s) = Bs s + BitVec.ofNat 64 2600 := by
    rw [addr_sub' (by omega_arith),
      show State.addr s.sp = Bs s + BitVec.ofNat 64 2648 from (BitVec.sub_add_cancel _ _).symm,
      add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨hs, by omega_arith, hPn, by omega_arith, hA0, fun i hi => ?_⟩
  show _ = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2648) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2648⟩ :=
  Offset.sub_base _ h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA {d : Nat} (hd : d < 80) : State.addr (Pf s + BitVec.ofNat 32 d) = Bs s + BitVec.ofNat 64 (2600 + d) := by
  rw [aP h.hP hd, h.hA0, Offset.add_ofNat_add_ofNat]

theorem fr_sub : (FR s).Sub ⟨Bs s, 2648⟩ := by
  show Region.Sub ⟨State.addr (Pf s), 48⟩ _; rw [h.hA0]; exact stk_sub s 2600 48 (by decide)

theorem argIn : argR s ∈ s.rd := by rw [h.pre.rd]; simp

omit h in
theorem hArg : argR s = ⟨Bs s + BitVec.ofNat 64 2648, 32⟩ := by
  show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), 32⟩ : Region) = _
  rw [Nat.mul_zero, add_ofNat_zero, BitVec.sub_add_cancel]

/-- The words of the stack arguments are readable. -/
theorem inArg (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 4 ≤ 80) (rs : List Region) :
    InRegions (s.rd ++ rs) (State.addr (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_append_left _ h.argIn, by
    rw [hArg, h.hA (by omega_arith)]; exact contains_off _ (by omega_arith) (by omega_arith) (by omega_arith)⟩

/-- The frame's words are writable. -/
theorem inFr (d : Nat) (h₂ : d + 4 ≤ 48) (rs : List Region) :
    InRegions (FR s :: rs) (State.addr (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_cons_self .., by rw [aP h.hP (by omega_arith)]; exact Offset.contains_base _ h₂ (by omega_arith)⟩

theorem sa' (i d : Nat) (hi : i < 8) (hd : d = 48 + 4 * i) :
    s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = stackArg s i := by
  subst hd; exact h.sa i hi

theorem eM_frame : Frame [FR s] s.mem (eM s) := eMem_frame h.hP _ _ _ _ _

/-- A word above the frame, after the entry. -/
theorem eAbove (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 4 ≤ 80) :
    (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
  refine h.eM_frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint ⟨State.addr (Pf s + BitVec.ofNat 32 d), 4⟩ ⟨State.addr (Pf s), 48⟩
  rw [h.hA (by omega_arith), h.hA0]
  exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by have := h.hBn; omega_arith)

/-- The bytes at `src`, after the entry. -/
theorem srcE : bytesAt (eM s) (State.addr (Src s)) (L s) = bytesAt s.mem (State.addr (Src s)) (L s) :=
  Proof.Cmac.bytesAt_frame h.eM_frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bs.symm.sub_right h.fr_sub) (by have := h.pre.os; omega_arith)

omit h in
theorem hlen : (bytesAt s.mem (State.addr (Src s)) (L s)).length = L s := Proof.Cmac.bytesAt_length _ _ _

omit h in
theorem frame_cM : Frame [dR s] (eM s) (cM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Lay.hlen, Nat.le_refl]

/-- The words of the stack, from the frame up to our arguments, are apart from `dst`. -/
theorem dsep (d : Nat) (hd : d + 4 ≤ 2648 ∨ (2648 ≤ d ∧ d + 4 ≤ 2680)) :
    (⟨Bs s + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint (dR s) := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact h.pre.bd.sub_left (stk_sub s d 4 hd)
  · have da := h.pre.da
    rw [hArg] at da
    exact (da.sub_right (Offset.sub _ h₁ (by omega_arith))).symm

/-- A word of the frame or above it, once the ciphertext is copied. -/
theorem cWord (d : Nat) (hd : d + 4 ≤ 48 ∨ (48 ≤ d ∧ d + 4 ≤ 80)) :
    (cM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
  rw [h.hA (by omega_arith)]
  refine Frame.readW Lay.frame_cM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact h.dsep _ (by omega_arith)

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  r0 : e.gpr .r0 = Pf s + BitVec.ofNat 32 56
  r2 : e.gpr .r2 = Dst s
  gpr : ∀ r, r ∉ gatherRegs → e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa entry (allocated 48 s) (Entered s) := by
  refine WP.mono (entry_ok (allocated 48 s) h.hP (fun d hd => h.inFr d hd _)
      (fun d h₁ h₂ => h.inArg d h₁ h₂ _)) fun e ⟨me, r0e, r2e, ge, spe, rde, wre⟩ => ?_
  refine ⟨me, r0e, r2e.trans (h.sa' 4 64 (by decide) rfl), fun r hr => ?_, spe, rde, wre⟩
  simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h₀, -, h₂, -, h₁₂, hl⟩ := hr
  exact ge r h₀ h₂ h₁₂ hl

theorem a60 (P : BitVec 32) : P + BitVec.ofNat 32 56 + BitVec.ofNat 32 4 = P + BitVec.ofNat 32 60 := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The copy's precondition after the entry: the descriptor is our stack
arguments `src` and `len`. -/
theorem slicePre_of {s e : State} (h : Lay s) (he : Entered s e) :
    SlicePre e (Pf s + BitVec.ofNat 32 56) (Src s) (Dst s) (L s) := by
  have hin (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 4 ≤ 80) :
      InRegions (e.rd ++ e.wr) (State.addr (Pf s + BitVec.ofNat 32 d)) 4 := by
    rw [he.rd, he.wr]; exact h.inArg d h₁ h₂ _
  have w (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 4 ≤ 80) :
      e.mem.readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [he.mem]; exact h.eAbove d h₁ h₂
  exact { r0 := he.r0
          r2 := he.r2
          d0 := hin 56 (by decide) (by decide)
          d4 := by rw [a60]; exact hin 60 (by decide) (by decide)
          w0 := (w 56 (by decide) (by decide)).trans (h.sa' 2 56 (by decide) rfl)
          w4 := by
            rw [a60, w 60 (by decide) (by decide), h.sa' 3 60 (by decide) rfl, BitVec.ofNat_toNat,
              BitVec.setWidth_eq]
          lt := (stackArg s 3).isLt
          fitS := h.pre.os
          fitD := h.pre.od
          rd := covers_of_mem (List.mem_append_left _ (by rw [he.rd, h.pre.rd]; simp))
          wr := fun _ => covers_of_mem (by rw [he.wr, h.pre.wr]; simp)
          disj := h.pre.sd
          dd := by rw [a60, h.hA (by decide)]; exact h.dsep 2660 (.inr ⟨by decide, by decide⟩) }

/-- After the copy. -/
structure Copied (s c : State) : Prop where
  mem : c.mem = cM s
  gpr : ∀ r, r ∉ gatherRegs → c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem copied_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa copySlice e (Copied s) := by
  refine WP.mono (copySlice_wp e (slicePre_of h he)) fun c ⟨mc, _, kc⟩ => ?_
  rw [he.mem, h.srcE] at mc
  exact ⟨mc, fun r hr => (kc.gkeeps.gpr r hr).trans (he.gpr r hr), kc.sp.trans he.sp, kc.rd.trans he.rd,
    kc.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = cM s
  r0 : c.gpr .r0 = s.gpr .r0
  r1 : c.gpr .r1 = s.gpr .r1
  r2 : c.gpr .r2 = s.gpr .r2
  r3 : c.gpr .r3 = s.gpr .r3
  gpr : ∀ r, r ∉ gatherRegs → c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Copied s g) : WP isa callArgs g (Ready s) := by
  have hr (d : Nat) (hd : d + 4 ≤ 48) : InRegions (g.rd ++ g.wr) (State.addr (g.sp + BitVec.ofNat 32 d)) 4 := by
    rw [hg.sp, hg.wr]; exact in_left (h.inFr d hd _)
  refine Gather.WP.split (l₁ := setFp) (l₂ := argWords) ?_
  refine WP.run ⟨_, by
    arun [setFp, argWords, add_ofNat_zero, hr 28 (by decide), hr 32 (by decide), hr 36 (by decide),
      hr 40 (by decide)], rfl⟩ fun c hc => ?_
  subst hc
  obtain ⟨-, -, -, -, -, -, -, w28, w32, w36, w40⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
  have rd (d : Nat) (hd : d + 4 ≤ 48) : g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 d)) 32 =
      (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [hg.mem, hg.sp, h.cWord d (.inl hd)]
  refine ⟨hg.mem, ?_, ?_, ?_, ?_, fun r hr => ?_, hg.sp, hg.rd, hg.wr⟩
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 28 (by decide)]; exact w28
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 32 (by decide)]; exact w32
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 36 (by decide)]; exact w36
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 40 (by decide)]; exact w40
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₀, h₁, h₂, h₃, h₁₂, hl⟩ := hr
    simp only [gpr_setReg, h₀, h₁, h₂, h₃, h₁₂, ↓reduceIte]
    exact hg.gpr r (by simp [gatherRegs, h₀, h₁, h₂, h₃, h₁₂, hl])

/-- The callee's stack arguments: words of our frame. -/
theorem Ready.word {s c : State} (hc : Ready s c) (rd' wr' : List Region) (i : Nat) :
    stackArg ((c.callEntry).withRegions rd' wr') i = (cM s).readW (State.addr (Pf s + BitVec.ofNat 32 (4 * i))) 32 := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, hc.mem, hc.sp]

theorem Ready.args {s c : State} (h : Lay s) (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    stackArg c' 0 = Ad s ∧ stackArg c' 1 = stackArg s 1 ∧ stackArg c' 2 = Dst s ∧ stackArg c' 3 = stackArg s 3 ∧
      stackArg c' 4 = Tg s ∧ stackArg c' 5 = stackArg s 7 := by
  obtain ⟨w0, w4, w8, w12, w16, w20, -⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
  simp only [hc.word]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_zero, h.cWord 0 (.inl (by decide)), add_ofNat_zero]; exact w0.trans (h.sa' 0 48 (by decide) rfl)
  · rw [h.cWord 4 (.inl (by decide))]; exact w4.trans (h.sa' 1 52 (by decide) rfl)
  · rw [h.cWord 8 (.inl (by decide))]; exact w8.trans (h.sa' 4 64 (by decide) rfl)
  · rw [h.cWord 12 (.inl (by decide))]; exact w12.trans (h.sa' 3 60 (by decide) rfl)
  · rw [h.cWord 16 (.inl (by decide))]; exact w16.trans (h.sa' 6 72 (by decide) rfl)
  · rw [h.cWord 20 (.inl (by decide))]; exact w20.trans (h.sa' 7 76 (by decide) rfl)

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    c'.gpr .r0 = s.gpr .r0 ∧ c'.gpr .r1 = s.gpr .r1 ∧ c'.gpr .r2 = s.gpr .r2 ∧ c'.gpr .r3 = s.gpr .r3 := by
  simp only [State.withRegions_gpr]
  exact ⟨by rw [c.callEntry_gpr (by decide), hc.r0], by rw [c.callEntry_gpr (by decide), hc.r1],
    by rw [c.callEntry_gpr (by decide), hc.r2], by rw [c.callEntry_gpr (by decide), hc.r3]⟩

section
variable (s : State)

/-- The regions the call of `vg_aes_gcm_open` reads and writes: its stack
arguments are the first 24 bytes of our frame. -/
abbrev rdC : List Region := [kR s, nR s, aR s, tR s, ⟨Bs s + BitVec.ofNat 64 2600, 24⟩]
abbrev wrC : List Region := [dR s]

/-- The call's state, with its permissions. -/
abbrev xS (c : State) : State := c.callEntry.withRegions (rdC s) (wrC s)

end

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre (xS s c) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have pre := h.pre
  obtain ⟨c0, c1, c2, c3⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hc.args h (rdC s) (wrC s)
  have sad0 : stackArgAddr (xS s c) 0 = Bs s + BitVec.ofNat 64 2600 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp, Nat.mul_zero, add_ofNat_zero, h.hA0]
  have hPn := h.hPn
  have hP := h.hP
  have w₁ := pre.w₁
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
      c0, c1, c2, c3, a0, a1, a2, a3, a4, a5, sad0, hc.sp, h.hA0, BitVec.add_sub_cancel]
    have stkArg : (⟨Bs s, 2600⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 2600, 24⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 2600) (e := 2600) (k := 24) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    refine ⟨trivial, trivial, pre.kd, pre.nd, pre.ad, pre.dt, (pre.bd.sub_left (stk_sub s 2600 24 (by decide))).symm,
      pre.bk.sub_left (Region.sub_prefix (by decide)), pre.bn.sub_left (Region.sub_prefix (by decide)),
      pre.ba.sub_left (Region.sub_prefix (by decide)), pre.bd.sub_left (Region.sub_prefix (by decide)),
      pre.bt.sub_left (Region.sub_prefix (by decide)), stkArg,
      pre.ok, pre.on, pre.oa, pre.od, pre.ot, by omega_arith, by omega_arith, pre.hR⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s, tR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem (List.mem_append_left _ ?_)
      rw [hc.rd, pre.rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> simp
    have hfr : Covers [⟨Bs s + BitVec.ofNat 64 2600, 48⟩] (c.rd ++ c.wr) := by
      rw [← h.hA0]; exact covers_of_mem (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hw' : Covers [dR s] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp))
    exact covers_append' (covers_cons (inRd (r := kR s) (by simp)) (covers_cons (inRd (r := nR s) (by simp))
      (covers_cons (inRd (r := aR s) (by simp)) (covers_cons (inRd (r := tR s) (by simp))
      (covers_cons (covers_prefix hfr (by decide)) covers_nil))))) (covers_cons hw' covers_nil)
  · rw [hc.wr, pre.wr]
    exact covers_cons (covers_of_mem (by simp)) covers_nil

/-- The call's result, on the call's state. -/
theorem Ready.xres {s c : State} (h : Lay s) (hc : Ready s c) : callRes (xS s c) = res s := by
  have pre := h.pre
  obtain ⟨c0, c1, c2, c3⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hc.args h (rdC s) (wrC s)
  have hm : (xS s c).mem = cM s := by
    simp only [State.withRegions_mem, State.callEntry_mem, hc.mem]
  have hfc : Frame [FR s, dR s] s.mem (cM s) :=
    (h.eM_frame.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      (Lay.frame_cM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
  have apart {r : Region} (h₁ : (⟨Bs s, 2648⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h₁.symm.sub_right h.fr_sub
    · exact h₂
  obtain ⟨hc', hh⟩ := Proof.AesGcm.ctx_frame hfc (apart pre.bk pre.kd) pre.hR
  have hn : bytesAt (cM s) (State.addr (Nn s)) (NL s) = bytesAt s.mem (State.addr (Nn s)) (NL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bn pre.nd) (by have := pre.on; omega_arith)
  have ha : bytesAt (cM s) (State.addr (Ad s)) (AL s) = bytesAt s.mem (State.addr (Ad s)) (AL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.ba pre.ad) (by have := pre.oa; omega_arith)
  have ht : bytesAt (cM s) (State.addr (Tg s)) (TL s) = bytesAt s.mem (State.addr (Tg s)) (TL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bt pre.dt.symm) (by have := pre.ot; omega_arith)
  have hd : bytesAt (cM s) (State.addr (Dst s)) (L s) = bytesAt s.mem (State.addr (Src s)) (L s) := by
    have := Proof.AesGcm.bytesAt_writeBytes_self (eM s) (State.addr (Dst s))
      (bytesAt s.mem (State.addr (Src s)) (L s))
      (by rw [Lay.hlen]; show (stackArg s 3).toNat < _; have := (stackArg s 3).isLt; omega_arith)
    rwa [Lay.hlen] at this
  simp only [callRes, hm, c0, c1, c2, c3, a0, a1, a2, a3, a4, a5]
  rw [hc', hh, hn, hd, ha, ht]

/-- What the call leaves of `dst` and `r0`: `vg_aes_gcm_open`'s result. -/
def Out (s : State) (e : BitVec 32) (m : Mem) : Prop :=
  match res s with
  | some pt => e = 1 ∧ bytesAt m (State.addr (Dst s)) (L s) = pt
  | none => e = 0

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.readW (State.addr (Pf s + BitVec.ofNat 32 24)) 32 = s.gpr .lr
  a3 : z.mem.readW (State.addr (Pf s + BitVec.ofNat 32 60)) 32 = stackArg s 3
  a4 : z.mem.readW (State.addr (Pf s + BitVec.ofNat 32 64)) 32 = stackArg s 4
  out : Out s (z.gpr .r0) z.mem
  gpr : ∀ r ∈ preserved, r ≠ .lr → z.gpr r = s.gpr r
  sp : z.sp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem Called.congr {s z t : State} (hz : Called s z) (hm : t.mem = z.mem) (hg : ∀ r, t.gpr r = z.gpr r)
    (hsp : t.sp = z.sp) (hrd : t.rd = z.rd) (hwr : t.wr = z.wr) : Called s t :=
  ⟨by rw [hm]; exact hz.ra, by rw [hm]; exact hz.a3, by rw [hm]; exact hz.a4, by rw [hm, hg]; exact hz.out,
    fun r hr hl => by rw [hg]; exact hz.gpr r hr hl, hsp.trans hz.sp, hrd.trans hz.rd, hwr.trans hz.wr⟩

theorem called_wp (F : OpenFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call F.name F.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hc.args h (rdC s) (wrC s)
  have hdep := F.depth
  have hPn := h.hPn
  have hBn := h.hBn
  have w₁ := h.pre.w₁
  refine WP.callF (n := F.name) F.verified.1 (openSpec_pre hcp) hcov hw (by rw [hc.sp]; omega_arith)
    fun s' rd' wr' sp' fr' pres' post' => ?_
  have hpost := openSpec_post post' (by
    simp only [State.withRegions_gpr] at c1 ⊢; rw [c1]; exact h.pre.hR)
  rw [hc.xres h, a2, a3] at hpost
  -- What the call kept: our frame and our arguments.
  have kept (d : Nat) (h₁ : 2600 ≤ d) (h₂ : d + 4 ≤ 2648 ∨ (2648 ≤ d ∧ d + 4 ≤ 2680)) :
      s'.mem.readW (Bs s + BitVec.ofNat 64 d) 32 = c.mem.readW (Bs s + BitVec.ofNat 64 d) 32 := by
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dsep d h₂
    · simp only [belowA, hc.sp]
      rw [addr_sub' (by omega_arith), h.hA0, add_ofNat_sub_ofNat _ (show armStack F.code ≤ 2600 by omega_arith)]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  have word (d : Nat) (hd : (24 ≤ d ∧ d + 4 ≤ 48) ∨ (48 ≤ d ∧ d + 4 ≤ 80)) :
      s'.mem.readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 =
        (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [← h.cWord d (by omega_arith), ← hc.mem, h.hA (by omega_arith), kept _ (by omega_arith) (by omega_arith)]
  obtain ⟨-, -, -, -, -, -, w24, -⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
  have hpres : ∀ r ∈ preserved, r ≠ .lr → r ∉ gatherRegs := by decide
  refine ⟨(word 24 (.inl ⟨by decide, by decide⟩)).trans w24, ?_, ?_, hpost, fun r hr hl => ?_,
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr⟩
  · rw [word 60 (.inr ⟨by decide, by decide⟩), h.eAbove 60 (by decide) (by decide)]
    exact h.sa' 3 60 (by decide) rfl
  · rw [word 64 (.inr ⟨by decide, by decide⟩), h.eAbove 64 (by decide) (by decide)]
    exact h.sa' 4 64 (by decide) rfl
  · rw [pres' r hr hl, hc.gpr r (hpres r hr hl)]

/-! ## After the call -/

/-- `cmp r0, #0`: whether the call returned 0. -/
theorem cmp_ok (z : State) : WP isa (.block [.cmp .r0 (imm 0)]) z fun t =>
    t.mem = z.mem ∧ (∀ r, t.gpr r = z.gpr r) ∧ t.sp = z.sp ∧ t.z = (z.gpr .r0 == 0) ∧ t.rd = z.rd ∧
      t.wr = z.wr := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun t ht => ?_
  subst ht
  exact ⟨rfl, fun _ => rfl, rfl, by simp only [z_subFlags]; rw [BitVec.sub_zero], rfl, rfl⟩

/-- One step of the wipe: the byte at `D + i` zeroed. -/
theorem zeroStep_ok (t : State) {D : BitVec 32} {i : Nat} (hd : t.gpr .r1 = D + BitVec.ofNat 32 i)
    (h0 : t.gpr .r3 = 0) (w : InRegions t.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ t', runBlock isa [.strb .r3 .r1 0, addI .r1 .r1 1, .subs .r2 .r2 (imm 1)] t = some t' ∧
      t'.mem = t.mem.writeW (State.addr (D + BitVec.ofNat 32 i)) (0 : BitVec 8) ∧
      t'.gpr .r1 = D + BitVec.ofNat 32 (i + 1) ∧ t'.gpr .r2 = t.gpr .r2 - BitVec.ofNat 32 1 ∧
      t'.z = (t.gpr .r2 - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  refine ⟨_, by arun [hd, add_ofNat_zero, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, Proof.AesGcm.Arm.mem_store, h0]; rfl
  · simp [gpr_setReg, hd, Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp [gpr_setReg]
  · simp [z_setReg, gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `r1 = D`, `r2 = n` and
`r3 = 0`. -/
theorem wipeLoop_wp (u : State) {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32)
    (h₁ : u.gpr .r1 = D) (h₂ : u.gpr .r2 = BitVec.ofNat 32 n) (h₀ : u.gpr .r3 = 0)
    (hw : Covers [⟨State.addr D, n⟩] u.wr) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem (State.addr D) n ∧
      Frame [⟨State.addr D, n⟩] u.mem u'.mem ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp := by
  unfold wipeLoop
  have cmp : WP isa (.block [.cmp .r2 (imm 0)]) u fun t => t = subFlags u (u.gpr .r2) (BitVec.ofNat 32 0) :=
    WP.run ⟨_, by arun [], rfl⟩ fun _ h => h.symm
  refine WP.seq (WP.mono cmp fun t ht => ?_)
  subst ht
  have tz : (subFlags u (u.gpr .r2) (BitVec.ofNat 32 0)).z = decide (n = 0) := by
    rw [z_subFlags, h₂]; exact z_ne0 hn
  refine WP.ite (decide (n = 0)) (eval_eq' tz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, fun r _ _ => rfl, rfl, rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (body := .block [.strb .r3 .r1 0, addI .r1 .r1 1, .subs .r2 .r2 (imm 1)]) (c := .ne)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .r1 = D + BitVec.ofNat 32 i ∧
        v.gpr .r2 = BitVec.ofNat 32 (n - i) ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp ∧ Frame [⟨State.addr D, n⟩] u.mem v.mem ∧
        Proof.Zeroize.Prefix v.mem (State.addr D) i) ?_ (n - 0) _
      ⟨0, rfl, by omega, by rw [gpr_subFlags, h₁, add_ofNat_zero], by rw [gpr_subFlags, h₂, Nat.sub_zero],
        fun r _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, r1, r2, gv, rdv, wrv, spv, fv, pv⟩
    have aD : State.addr (D + BitVec.ofNat 32 i) = State.addr D + BitVec.ofNat 64 i := addr_add (by omega)
    have hcn : (⟨State.addr D, n⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have win : InRegions v.wr (State.addr (D + BitVec.ofNat 32 i)) 1 := by
      rw [wrv, aD]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩
    obtain ⟨v', run', mem', r1', r2', z', g', rd', wr', sp'⟩ :=
      zeroStep_ok v r1 (by rw [gv _ (by decide) (by decide), h₀]) win
    refine WP.of_runBlock ⟨v', run', ?_⟩
    have f' : Frame [⟨State.addr D, n⟩] u.mem v'.mem := by
      rw [mem', aD]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    have p' : Proof.Zeroize.Prefix v'.mem (State.addr D) (i + 1) := by
      rw [mem', aD]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega)
    have g'' : ∀ r, r ≠ .r1 → r ≠ .r2 → v'.gpr r = u.gpr r := fun r a b => by rw [g' r a b, gv r a b]
    have hz : v'.z = decide (i + 1 = n) := by rw [z', r2, dec32 hi hn, z_dec hi hn]
    have ev : isa.eval .ne v' = some !decide (i + 1 = n) := eval_ne' hz
    by_cases he : i + 1 = n
    · left
      exact ⟨by rw [ev]; simp [he], by rw [← he]; exact p', f', g'', rd'.trans rdv, wr'.trans wrv,
        sp'.trans spv⟩
    · right
      exact ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r1',
        by rw [r2', r2, dec32 hi hn], g'', rd'.trans rdv, wr'.trans wrv, sp'.trans spv, f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- After `wipeArgs`: `dst` in `r1`, `len` in `r2` and zero in `r3`. -/
structure WArgs (s z a : State) : Prop where
  r1 : a.gpr .r1 = Dst s
  r2 : a.gpr .r2 = BitVec.ofNat 32 (L s)
  r3 : a.gpr .r3 = 0
  gpr : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → a.gpr r = z.gpr r
  mem : a.mem = z.mem
  sp : a.sp = z.sp
  rd : a.rd = z.rd
  wr : a.wr = z.wr

theorem wipeArgs_wp {s z : State} (h : Lay s) (hz : Called s z) :
    WP isa (.seq (.block setFp) (.block wipeArgs)) z (WArgs s z) := by
  have hr (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 4 ≤ 80) :
      InRegions (z.rd ++ z.wr) (State.addr (z.sp + BitVec.ofNat 32 d)) 4 := by
    rw [hz.sp, hz.rd, hz.wr]; exact h.inArg d h₁ h₂ _
  refine Gather.WP.split (l₁ := setFp) (l₂ := wipeArgs) ?_
  refine WP.run ⟨_, by
    arun [setFp, wipeArgs, add_ofNat_zero, hr 60 (by decide) (by decide), hr 64 (by decide) (by decide)], rfl⟩
    fun a ha => ?_
  subst ha
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ h₁₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; rw [hz.sp]; exact hz.a4
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; rw [hz.sp, hz.a3, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; rfl
  · simp [gpr_setReg, h₁, h₂, h₃, h₁₂]

/-- Where `after` leaves the state: what follows the call, with `dst` and
`r0` as `toPost` has them. -/
structure Done (s u : State) : Prop where
  post : toPost s u
  ra : u.mem.readW (State.addr (Pf s + BitVec.ofNat 32 24)) 32 = s.gpr .lr
  gpr : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = s.gpr r
  sp : u.sp = Pf s
  rd : u.rd = s.rd
  wr : u.wr = FR s :: s.wr

/-- When the call failed: `dst` zeroed. -/
theorem wipe_wp {s z : State} (h : Lay s) (hz : Called s z) (hres : res s = none) : WP isa wipe z (Done s) := by
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun a ha => ?_)
  have hw : Covers [⟨State.addr (Dst s), L s⟩] a.wr := by
    rw [ha.wr, hz.wr, h.pre.wr]; exact covers_of_mem (by simp)
  refine WP.mono (wipeLoop_wp a (stackArg s 3).isLt h.pre.od ha.r1 ha.r2 ha.r3 hw)
    fun u ⟨pz, fu, gu, rdu, wru, spu⟩ => ?_
  have g' : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → u.gpr r = z.gpr r := fun r a b c d => by
    rw [gu r a b, ha.gpr r a b c d]
  have keep : u.mem.readW (State.addr (Pf s + BitVec.ofNat 32 24)) 32 =
      z.mem.readW (State.addr (Pf s + BitVec.ofNat 32 24)) 32 := by
    rw [← ha.mem, h.hA (by decide)]
    refine fu.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.dsep _ (.inl (by decide))
  have hpres : ∀ r ∈ preserved, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by decide
  have o := hz.out
  unfold Out at o
  rw [hres] at o
  refine ⟨?_, keep.trans hz.ra, fun r hr hl => ?_, spu.trans (ha.sp.trans hz.sp), by rw [rdu, ha.rd, hz.rd],
    by rw [wru, ha.wr, hz.wr]⟩
  · show match res s with | some pt => _ | none => _
    rw [hres]
    exact ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide)]; exact o, bytesAt_zeros pz⟩
  · obtain ⟨a₁, a₂, a₃, a₄⟩ := hpres r hr
    rw [g' r a₁ a₂ a₃ a₄]; exact hz.gpr r hr hl

/-- After the call: `dst` zeroed if it failed. -/
theorem after_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa after z (Done s) := by
  unfold after
  refine WP.seq (WP.mono (cmp_ok z) fun t ⟨tm, tg, tsp, tz, trd, twr⟩ => ?_)
  have ht := hz.congr tm tg tsp trd twr
  have o := ht.out
  unfold Out at o
  cases hr : res s with
  | none =>
    rw [hr] at o
    exact WP.ite true (eval_eq' (by rw [tz, ← tg, o]; rfl)) (fun _ => wipe_wp h ht hr)
      (fun h' => absurd h' (by decide))
  | some pt =>
    rw [hr] at o
    refine WP.ite false (eval_eq' (by rw [tz, ← tg, o.1]; rfl)) (fun h' => absurd h' (by decide))
      (fun _ => WP.block_nil ⟨?_, ht.ra, ht.gpr, ht.sp, ht.rd, ht.wr⟩)
    show match res s with | some pt => _ | none => _
    rw [hr]
    exact o

/-- Our return address back in `lr`, and the frame freed. -/
theorem ret_wp {s u : State} (h : Lay s) (hu : Done s u) :
    WP isa OpenTo.ret u fun z => abiPreserved s (freed 48 z) ∧ toPost s (freed 48 z) := by
  have hr : InRegions (u.rd ++ u.wr) (State.addr (u.sp + BitVec.ofNat 32 24)) 4 := by
    rw [hu.sp, hu.wr]; exact in_left (h.inFr 24 (by decide) _)
  refine Gather.WP.split (l₁ := setFp) (l₂ := [Instr.ldr .lr .r12 24]) ?_
  refine WP.run ⟨_, by arun [setFp, add_ofNat_zero, hr], rfl⟩ fun z hz => ?_
  subst hz
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have h12 : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    simp only [freed, gpr_setReg, h12, ↓reduceIte]
    by_cases hl : r = .lr
    · subst hl; simp only [↓reduceIte]; rw [hu.sp]; exact hu.ra
    · simp only [hl, ↓reduceIte]; exact hu.gpr r hr hl
  · simp only [freed, sp_setReg, hu.sp]
    exact BitVec.sub_add_cancel _ _
  · have p := hu.post
    show match res s with | some pt => _ | none => _
    revert p
    show (match res s with | some pt => _ | none => _) → _
    cases res s with
    | some pt => intro p; simpa [freed, gpr_setReg, mem_setReg] using p
    | none => intro p; simpa [freed, gpr_setReg, mem_setReg] using p

theorem openTo_wp (F : OpenFn) {s : State} (hs : ToPre s) :
    WP isa (openTo F.name F.code) s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  have w₁ := hs.w₁
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (copied_wp h he) fun c hc => ?_)
  refine WP.seq (WP.mono (ready_wp h hc) fun r hr => ?_)
  refine WP.seq (WP.mono (called_wp F h hr) fun z hz => ?_)
  refine WP.seq (WP.mono (after_wp h hz) fun u hu => ?_)
  exact ret_wp h hu

end VG.Proof.AesGcm.Arm.OpenTo
