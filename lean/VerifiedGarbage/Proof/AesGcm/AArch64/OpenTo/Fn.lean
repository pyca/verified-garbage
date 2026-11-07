module

public import VerifiedGarbage.Impl.AesGcm.AArch64.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Copy
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.Cmac.Spec

/-!
# AES-GCM decryption out of place, by a copy, AArch64: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against (`toK`), which the shared one implies
(`OpenTo/Verified.lean`), and its proof (`openTo_wp`). It calls an
implementation of `vg_aes_gcm_open` as an artifact, with its working space in
a frame of its own, so what the proof needs of it is its shared contract
(`Proof.AesGcm.openRoundsContract`, with 2592 bytes of stack, `OpenFn`).

With `B` the base of the 2624 bytes of stack below the stack pointer
(`sp = B + 2624`), the function allocates its frame of 32 bytes at
`P = B + 2592`: `tag` and `tag_len`, the call's stack arguments, at `P` and
`P + 8`, and our return address at `P + 16` (`entered_wp`). It copies the
`len` bytes at `src` to `dst` (`copied_wp`, by `Gather.copySlice_wp`), puts
`dst` in `x6` (`ready_wp`), calls `vg_aes_gcm_open` on `dst` in place
(`called_wp`), which writes only `dst` and the stack below `P`, keeping our
frame, and zeroes `dst` if it returned 0 (`after_ok`, `wipe_wp`). Every
write is to `dst` or to the stack below `sp`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.OpenTo

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.AesGcm.AArch64 (bytesAt_frame covers_of_mem covers_cons covers_append covers_prefix covers_nil)
open VG.Proof.AesGcm.AArch64.Gather (SlicePre Keeps copyRegs copySlice_wp add_ofNat_sub_ofNat contains_off ldrSp_ok)
open VG.Impl.AesGcm.AArch64.SealGather (copySlice)

/-! ## The arguments and the contract -/

section
variable (s : State)

/-- The arguments: `(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3,
aad = x4, aad_len = x5, src = x6, len = x7, dst = [sp], dst_len = [sp + 8],
tag = [sp + 16], tag_len = [sp + 24])`. -/
abbrev K : Addr := s.gpr .x0
abbrev R : Nat := (s.gpr .x1).toNat
abbrev Nn : Addr := s.gpr .x2
abbrev NL : Nat := (s.gpr .x3).toNat
abbrev Ad : Addr := s.gpr .x4
abbrev AL : Nat := (s.gpr .x5).toNat
abbrev Src : Addr := s.gpr .x6
abbrev L : Nat := (s.gpr .x7).toNat
abbrev Dst : Addr := stackArg s 0
abbrev Tg : Addr := stackArg s 2
abbrev TL : Nat := (stackArg s 3).toNat

/-- The regions: the key context, the nonce, the additional data, the
ciphertext, the output, the tag, the stack arguments and the stack below the
stack pointer. -/
abbrev kR : Region := ⟨K s, 256⟩
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev sR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tR : Region := ⟨Tg s, TL s⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 2624, 2624⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (K s) (R s)) (ctxH s.mem (K s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-- What the proof of `vg_aes_gcm_open_to` needs: the layout of its shared
contract, with 2624 bytes of stack, `dst_len` its `len`. -/
structure ToPre (s : State) : Prop where
  w₁ : 2624 ≤ s.sp.toNat
  w₂ : s.sp.toNat + 32 ≤ 2 ^ 64
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
  ok : (K s).toNat + 256 ≤ 2 ^ 64
  on : (Nn s).toNat + NL s ≤ 2 ^ 64
  oa : (Ad s).toNat + AL s ≤ 2 ^ 64
  os : (Src s).toNat + L s ≤ 2 ^ 64
  od : (Dst s).toNat + L s ≤ 2 ^ 64
  ot : (Tg s).toNat + TL s ≤ 2 ^ 64
  hR : R s = 10 ∨ R s = 12 ∨ R s = 14
  dl : (stackArg s 1).toNat = L s

/-- `openToRoundsPost`, for the rounds of `ToPre`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (Dst s) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak: whether it succeeds. -/
def toLeak (s : State) : List Nat :=
  if ¬(R s = 10 ∨ R s = 12 ∨ R s = 14) then [] else [if (res s).isSome = true then 1 else 0]

/-- What two runs agree on: the arguments and the leak. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ toLeak s₁ = toLeak s₂ ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    stackArg s₁ 3 = stackArg s₂ 3

/-- `vg_aes_gcm_open_to`. -/
def toK : Contract isa where
  pre := ToPre
  post := toPost
  pub := toPub

/-! ## The function called -/

/-- An implementation of `vg_aes_gcm_open`, by its shared contract
(`Proof.AesGcm.openRoundsContract`, with 2592 bytes of stack), whose frames use
at most those. -/
structure OpenFn where
  fn : Fn
  verified : Verified AArch64.target fn.code (Proof.AesGcm.openRoundsContract AArch64.abi 2592)
  depth : 16 * fn.code.aarch64Depth ≤ 2592

/-- The shared contract's precondition, as the call lays it out. -/
def callPre (s : State) : Prop :=
  2592 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 64 ∧
    s.rd = [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArgAddr s 0, 16⟩] ∧
    s.wr = [⟨s.gpr .x6, (s.gpr .x7).toNat⟩] ∧
    (⟨s.gpr .x0, 256⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∧
    (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x0, 256⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩ ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem openSpec_pre {s : State} (h : callPre s) : (Proof.AesGcm.openRoundsContract AArch64.abi 2592).pre s := by
  sig_pre [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, AArch64.abi, AArch64.argRegs,
    stackArgs_two, List.append_eq, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, AArch64.abi, AArch64.argRegs, List.getD,
    List.range, List.range.loop]
  exact h

/-- `vg_aes_gcm_open`'s result on the arguments of a call. -/
abbrev callRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

theorem openSpec_post {s s' : State} (h : (Proof.AesGcm.openRoundsContract AArch64.abi 2592).post s s')
    (hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) :
    match callRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat := by
  sig_post [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Proof.AesGcm.openRoundsPost, AArch64.abi,
    AArch64.argRegs, stackArgs_two, List.append_eq, List.range, List.range.loop] at h
  exact h hR

/-- The public data of a call: its arguments, and whether it succeeds. -/
def callLeak (s : State) : List Nat :=
  if ¬((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) then []
  else [if (callRes s).isSome = true then 1 else 0]

theorem openSpec_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ callLeak s₁ = callLeak s₂ ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧
    s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧
    s₁.gpr .x7 = s₂.gpr .x7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1) :
    (Proof.AesGcm.openRoundsContract AArch64.abi 2592).pub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs,
    stackArgs_two, List.append_eq, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs,
    List.range, List.range.loop]
  exact h

/-! ## Steps -/

/-- The entry, in the frame at `P`: our return address at `P + 16`, the
stack arguments at `P + 48` and `P + 56` (`tag`, `tag_len`) at `P` and
`P + 8`, the one at `P + 32` (`dst`) in `x11`, and `x6` and `x7` in `x12`
and `x13`. -/
theorem entry_ok (a : State) {P : Addr} (hsp : a.sp = P)
    (w₁₆ : InRegions a.wr (P + BitVec.ofNat 64 16) 8) (w₀ : InRegions a.wr P 8)
    (w₈ : InRegions a.wr (P + BitVec.ofNat 64 8) 8)
    (r₄₈ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 48) 8)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8)
    (r₃₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 32) 8) :
    WP isa (.block entry) a fun e =>
      e.mem = ((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).write P 8
        ((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).read (P + BitVec.ofNat 64 48) 8)).write
          (P + BitVec.ofNat 64 8) 8
          (((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).write P 8
            ((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).read (P + BitVec.ofNat 64 48) 8)).read
              (P + BitVec.ofNat 64 56) 8) ∧
      e.gpr .x11 = e.mem.read (P + BitVec.ofNat 64 32) 8 ∧ e.gpr .x12 = a.gpr .x6 ∧ e.gpr .x13 = a.gpr .x7 ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x16 → r ≠ .x17 → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧
      e.rd = a.rd ∧ e.wr = a.wr := by
  subst hsp
  have e₀ : a.sp + BitVec.ofNat 64 0 = a.sp := BitVec.add_zero _
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [entry, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some,
      Option.map_some, BitVec.setWidth_eq, e₀, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul,
      Nat.reduceMod, and_self, w₁₆, w₀, w₈, r₄₈, r₅₆, r₃₂]; rfl, rfl⟩ fun e he => ?_
  subst he
  refine ⟨rfl, by simp [State.write], by simp [State.write], by simp [State.write],
    fun r h₁ h₂ h₃ h₄ h₅ => by simp [State.write, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl⟩

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 2624 bytes of stack below the stack pointer, and our frame. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 2624
abbrev P : Addr := Bs s + BitVec.ofNat 64 2592
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 2592, 32⟩

/-- The memory after the entry: the return address at `P + 16`, `tag` at
`P` and `tag_len` at `P + 8`. -/
abbrev eMem : Mem :=
  ((s.mem.write (Bs s + BitVec.ofNat 64 2608) 8 (s.gpr .x30)).write (Bs s + BitVec.ofNat 64 2592) 8 (Tg s)).write
    (Bs s + BitVec.ofNat 64 2600) 8 (stackArg s 3)

/-- The memory once the ciphertext is copied to `dst`. -/
abbrev cMem : Mem := writeBytes (eMem s) (Dst s) (bytesAt s.mem (Src s) (L s))

/-- The regions the call of `vg_aes_gcm_open` reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, tR s, ⟨P s, 16⟩]
abbrev wrC : List Region := [dR s]

end

/-- What `ToPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : ToPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 2624
  hBn : (Bs s).toNat + 2656 ≤ 2 ^ 64
  hargR : argR s = ⟨Bs s + BitVec.ofNat 64 2624, 32⟩

theorem stackArgAddr_eq (s : State) {B : Addr} (hB : s.sp = B + BitVec.ofNat 64 2624) (i : Nat) :
    stackArgAddr s i = B + BitVec.ofNat 64 (2624 + 8 * i) := by
  rw [stackArgAddr, hB, Offset.add_ofNat_add_ofNat]

theorem lay {s : State} (hs : ToPre s) : Lay s := by
  have hB : s.sp = Bs s + BitVec.ofNat 64 2624 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 2656 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    have := hs.w₁
    have := hs.w₂
    omega_arith
  exact ⟨hs, hB, hBn, by simp only [argR, stackArgAddr_eq s hB, Nat.mul_zero, Nat.add_zero]⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2624) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2624⟩ :=
  Offset.sub_base _ h'

theorem stkR_eq (s : State) : stkR s = ⟨Bs s, 2624⟩ := rfl

theorem frame_eMem (s : State) : Frame [FR s] s.mem (eMem s) :=
  (((Frame.refl _ _).write (List.mem_singleton_self _) _
    (contains_off _ (by decide) (by decide) (by decide))).write (List.mem_singleton_self _) _
    (contains_off _ (Nat.le_refl _) (by decide) (by decide))).write (List.mem_singleton_self _) _
    (contains_off _ (by decide) (by decide) (by decide))

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (2624 + 8 * i) := stackArgAddr_eq s h.hB i

theorem argIn : argR s ∈ s.rd := by rw [h.pre.rd]; simp

theorem inArg (d : Nat) (h₁ : 2624 ≤ d) (h₂ : d + 8 ≤ 2656) (rs : List Region) :
    InRegions (s.rd ++ rs) (Bs s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_append_left _ h.argIn, by rw [h.hargR]; exact contains_off _ h₁ (by omega_arith) (by omega_arith)⟩

theorem sa (i : Nat) : s.mem.read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.hA]; rfl

theorem sep (d e : Nat) (h₁ : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2656) (he : e + 8 ≤ 2656) :
    Mem.Sep (Bs s + BitVec.ofNat 64 d) 8 (Bs s + BitVec.ofNat 64 e) 8 :=
  Offset.sep _ h₁ (by have := h.hBn; omega_arith) (by have := h.hBn; omega_arith)

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 2624⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 2592 32 (by decide) x hc)

theorem eArg (i : Nat) (hi : i < 4) :
    (eMem s).read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [Mem.read_write_sep (h.sep _ 2600 (by omega_arith) (by omega_arith) (by decide)) (by decide),
    Mem.read_write_sep (h.sep _ 2592 (by omega_arith) (by omega_arith) (by decide)) (by decide),
    Mem.read_write_sep (h.sep _ 2608 (by omega_arith) (by omega_arith) (by decide)) (by decide)]
  exact h.sa i

/-- The bytes at `src`, after the entry. -/
theorem srcE : bytesAt (eMem s) (Src s) (L s) = bytesAt s.mem (Src s) (L s) :=
  bytesAt_frame (frame_eMem s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bs.symm.sub_right (stk_sub s 2592 32 (by decide))) (by have := h.pre.os; omega_arith)

omit h in
theorem hlen : (bytesAt s.mem (Src s) (L s)).length = L s := Proof.Cmac.bytesAt_length _ _ _

omit h in
theorem frame_cMem : Frame [dR s] (eMem s) (cMem s) :=
  writeBytes_frame _ _ _ (by rw [Lay.hlen]; exact Region.contains_self _ _)

/-- A doubleword of the stack, once the ciphertext is copied. -/
theorem cFrame (d : Nat) (hd' : d + 8 ≤ 2624) :
    (cMem s).read (Bs s + BitVec.ofNat 64 d) 8 = (eMem s).read (Bs s + BitVec.ofNat 64 d) 8 :=
  Frame.read Lay.frame_cMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.symm.sub_right (stk_sub s d 8 hd') |>.symm) (by decide)

theorem cArg (i : Nat) (hi : i < 4) :
    (cMem s).read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.eArg i hi]
  refine Frame.read Lay.frame_cMem (contains_off _ (Nat.le_refl _) (Nat.le_refl _) (by omega_arith)) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  have da := h.pre.da
  rw [h.hargR] at da
  exact (da.sub_right (Offset.sub _ (show 2624 ≤ 2624 + 8 * i by omega_arith) (by omega_arith))).symm

omit h in
/-- The memory the call finds, changed since the entry only in the frame and at `dst`. -/
theorem frame_cMem' : Frame [FR s, dR s] s.mem (cMem s) :=
  ((frame_eMem s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
    (Lay.frame_cMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))

omit h in
/-- The regions apart from both the frame and `dst`. -/
theorem apart {r : Region} (h₁ : (stkR s).Disjoint r) (h₂ : r.Disjoint (dR s)) :
    ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact h₁.symm.sub_right (stk_sub s 2592 32 (by decide))
  · exact h₂

/-- The call's result is `res`. -/
theorem cRes {m : Mem} (hf : Frame [FR s, dR s] s.mem m)
    (hd : bytesAt m (Dst s) (L s) = bytesAt s.mem (Src s) (L s)) :
    openResult (ctxCiph m (K s) (R s)) (ctxH m (K s)) (TL s) (bytesAt m (Nn s) (NL s))
      (bytesAt m (Dst s) (L s)) (bytesAt m (Ad s) (AL s)) (bytesAt m (Tg s) (TL s)) = res s := by
  obtain ⟨hc, hh⟩ := Proof.AesGcm.ctx_frame hf (Lay.apart h.pre.bk h.pre.kd) h.pre.hR
  have hn : bytesAt m (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
    bytesAt_frame hf (Lay.apart h.pre.bn h.pre.nd) (by have := h.pre.on; omega_arith)
  have ha : bytesAt m (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
    bytesAt_frame hf (Lay.apart h.pre.ba h.pre.ad) (by have := h.pre.oa; omega_arith)
  have ht : bytesAt m (Tg s) (TL s) = bytesAt s.mem (Tg s) (TL s) :=
    bytesAt_frame hf (Lay.apart h.pre.bt h.pre.dt.symm) (by have := h.pre.ot; omega_arith)
  rw [hc, hh, hn, ha, ht, hd]

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  x11 : e.gpr .x11 = Dst s
  x12 : e.gpr .x12 = Src s
  x13 : e.gpr .x13 = s.gpr .x7
  gpr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x16 → r ≠ .x17 → e.gpr r = s.gpr r
  sp : e.sp = P s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (e.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem allocated_sp {s : State} (h : Lay s) : (allocated 32 s).sp = P s := by
  show s.sp - BitVec.ofNat 64 32 = _
  rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]

theorem allocated_wr {s : State} (h : Lay s) : (allocated 32 s).wr = FR s :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr : List Region) = _
  rw [show s.sp - BitVec.ofNat 64 32 = _ from allocated_sp h]

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 32 s) (Entered s) := by
  have asp := allocated_sp h
  have awr := allocated_wr h
  have inFr (d : Nat) (hd : d + 8 ≤ 32) : InRegions (allocated 32 s).wr (P s + BitVec.ofNat 64 d) 8 :=
    ⟨_, by rw [awr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inArg (d : Nat) (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 64) :
      InRegions ((allocated 32 s).rd ++ (allocated 32 s).wr) (P s + BitVec.ofNat 64 d) 8 := by
    rw [Offset.add_ofNat_add_ofNat]
    exact h.inArg (2592 + d) (by omega_arith) (by omega_arith) _
  refine WP.mono (WP.preservedV (entry_ok (allocated 32 s) asp (inFr 16 (by decide))
      ⟨_, by rw [awr]; exact List.mem_cons_self .., by simp [Region.Contains]⟩ (inFr 8 (by decide))
      (inArg 48 (by decide) (by decide)) (inArg 56 (by decide) (by decide)) (inArg 32 (by decide) (by decide)))
      (by lit_decide))
    fun e ⟨⟨me, x11e, x12e, x13e, ge, spe, rde, wre⟩, ve⟩ => ?_
  simp only [Offset.add_ofNat_add_ofNat, Nat.reduceAdd] at me x11e
  change e.mem = ((s.mem.write _ 8 (s.gpr .x30)).write _ 8 ((s.mem.write _ 8 (s.gpr .x30)).read _ 8)).write _ 8
    (((s.mem.write _ 8 (s.gpr .x30)).write _ 8 ((s.mem.write _ 8 (s.gpr .x30)).read _ 8)).read _ 8) at me
  rw [Mem.read_write_sep (h.sep 2640 2608 (by decide) (by decide) (by decide)) (by decide), h.sa 2,
    Mem.read_write_sep (h.sep 2648 2592 (by decide) (by decide) (by decide)) (by decide),
    Mem.read_write_sep (h.sep 2648 2608 (by decide) (by decide) (by decide)) (by decide), h.sa 3] at me
  refine ⟨me, ?_, x12e, x13e, ge, by rw [spe, asp], rde, by rw [wre, awr], ve⟩
  rw [x11e, me]
  exact h.eArg 0 (by decide)

/-- After the copy. -/
structure Copied (s c : State) : Prop where
  mem : c.mem = cMem s
  gpr : ∀ r, r ∉ copyRegs → r ≠ .x16 → r ≠ .x17 → c.gpr r = s.gpr r
  sp : c.sp = P s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (c.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem copied_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa copySlice e (Copied s) := by
  have hp : SlicePre e (Src s) (Dst s) (L s) :=
    ⟨he.x12, he.x11, by rw [he.x13, BitVec.ofNat_toNat, BitVec.setWidth_eq], (s.gpr .x7).isLt,
      covers_of_mem (List.mem_append_left _ (by rw [he.rd, h.pre.rd]; simp)),
      covers_of_mem (by rw [he.wr, h.pre.wr]; simp), h.pre.sd⟩
  refine WP.mono (WP.preservedV (copySlice_wp e hp) (by lit_decide)) fun c ⟨⟨mc, _, kc⟩, vc⟩ => ?_
  rw [he.mem, h.srcE] at mc
  have hpres : ∀ r, r ∉ copyRegs → r ≠ .x16 → r ≠ .x17 → r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 := by
    intro r hr _ _; simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
  exact ⟨mc, fun r hr h₁₆ h₁₇ => by
      obtain ⟨h₁₁, h₁₂, h₁₃⟩ := hpres r hr h₁₆ h₁₇
      rw [kc.gpr r hr, he.gpr r h₁₁ h₁₂ h₁₃ h₁₆ h₁₇],
    kc.sp.trans he.sp, kc.rd.trans he.rd, kc.wr.trans he.wr, fun r hr => (vc r hr).trans (he.v r hr)⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = cMem s
  x6 : c.gpr .x6 = Dst s
  gpr : ∀ r, r ≠ .x6 → r ∉ copyRegs → r ≠ .x16 → r ≠ .x17 → c.gpr r = s.gpr r
  sp : c.sp = P s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (c.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem ready_wp {s c : State} (h : Lay s) (hc : Copied s c) : WP isa (.block callArgs) c (Ready s) := by
  refine WP.mono (ldrSp_ok (t := .x6) c (by decide)
      (by rw [hc.sp, Offset.add_ofNat_add_ofNat, hc.rd, hc.wr]; exact h.inArg 2624 (by decide) (by decide) _))
    fun r ⟨x6r, gr, mr, spr, rdr, wrr, vr⟩ => ?_
  rw [hc.sp, Offset.add_ofNat_add_ofNat, hc.mem] at x6r
  exact ⟨mr.trans hc.mem, x6r.trans (h.cArg 0 (by decide)),
    fun r' h₆ hr h₁₆ h₁₇ => (gr r' h₆).trans (hc.gpr r' hr h₁₆ h₁₇), spr.trans hc.sp, rdr.trans hc.rd,
    wrr.trans hc.wr, fun r' hr' => by rw [vr]; exact hc.v r' hr'⟩

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .x0 = s.gpr .x0 ∧ c.callEntry.gpr .x1 = s.gpr .x1 ∧ c.callEntry.gpr .x2 = s.gpr .x2 ∧
      c.callEntry.gpr .x3 = s.gpr .x3 ∧ c.callEntry.gpr .x4 = s.gpr .x4 ∧ c.callEntry.gpr .x5 = s.gpr .x5 ∧
      c.callEntry.gpr .x6 = Dst s ∧ c.callEntry.gpr .x7 = s.gpr .x7 := by
  have cg (r : Reg) (h₀ : r ∉ linkRegs) (h₆ : r ≠ .x6) (hr : r ∉ copyRegs) (h₁₆ : r ≠ .x16)
      (h₁₇ : r ≠ .x17) : c.callEntry.gpr r = s.gpr r := by
    rw [c.callEntry_gpr h₀, hc.gpr r h₆ hr h₁₆ h₁₇]
  exact ⟨cg _ (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [c.callEntry_gpr (by decide), hc.x6],
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- `tag` and `tag_len`, the call's stack arguments. -/
theorem Ready.stackArgs {s c : State} (h : Lay s) (hc : Ready s c) (rd' wr' : List Region) :
    stackArg ((c.callEntry).withRegions rd' wr') 0 = Tg s ∧
      stackArg ((c.callEntry).withRegions rd' wr') 1 = stackArg s 3 := by
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  have c₀ : c.mem.read (P s) 8 = Tg s := by
    rw [hc.mem, hP, h.cFrame 2592 (by decide),
      Mem.read_write_sep (h.sep 2592 2600 (by decide) (by decide) (by decide)) (by decide)]
    exact read_write_self _ _ _
  have c₈ : c.mem.read (P s + BitVec.ofNat 64 8) 8 = stackArg s 3 := by
    rw [hc.mem, hP, Offset.add_ofNat_add_ofNat, h.cFrame 2600 (by decide)]
    exact read_write_self _ _ _
  refine ⟨?_, ?_⟩
  · rw [← c₀, ← hc.sp]; simp [stackArg, stackArgAddr, Mem.readW]
  · rw [← c₈, ← hc.sp]; simp [stackArg, stackArgAddr, Mem.readW]

/-- The call's state, with its permissions. -/
abbrev xS (s c : State) : State := c.callEntry.withRegions (rdC s) (wrC s)

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre (xS s c) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have pre := h.pre
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  obtain ⟨sa0, sa1⟩ := hc.stackArgs h (rdC s) (wrC s)
  have dl := pre.dl
  have sad0 : stackArgAddr (xS s c) 0 = P s := by simp [stackArgAddr, hc.sp]
  have hPn : (P s).toNat = (Bs s).toNat + 2592 := by
    have := h.hBn
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  have hPsub : P s - BitVec.ofNat 64 2592 = Bs s := by rw [add_ofNat_sub_ofNat _ (by decide), Nat.sub_self,
    BitVec.add_zero]
  have stkArg : (⟨Bs s, 2592⟩ : Region).Disjoint ⟨P s, 16⟩ := by
    have := Offset.disjoint (Bs s) (d := 0) (n := 2592) (e := 2592) (k := 16) (.inl (by decide)) (by decide)
      (by decide)
    rwa [BitVec.add_zero] at this
  have stkR' : stkR s = ⟨Bs s, 2624⟩ := rfl
  have bsub (r : Region) (hr : (stkR s).Disjoint r) : (⟨Bs s, 2592⟩ : Region).Disjoint r :=
    (by rw [stkR'] at hr; exact hr.sub_left (Region.sub_prefix (by decide)))
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c0, c1, c2, c3, c4, c5, c6, c7, sa0, sa1, sad0, hc.sp, hPsub]
    refine ⟨by omega_arith, by have := h.hBn; omega_arith, trivial, trivial, pre.kd, pre.nd, pre.ad, pre.dt,
      (h.pre.bd.sub_left (stk_sub s 2592 16 (by decide))).symm,
      bsub _ pre.bk, bsub _ pre.bn, bsub _ pre.ba, bsub _ pre.bd, bsub _ pre.bt, stkArg,
      pre.ok, pre.on, pre.oa, pre.od, pre.ot, pre.hR⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s, tR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem (List.mem_append_left _ ?_)
      rw [hc.rd, pre.rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> simp
    have hfr : Covers [FR s] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hw' : Covers [dR s] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp))
    exact covers_append (covers_cons (inRd (r := kR s) (by simp)) (covers_cons (inRd (r := nR s) (by simp))
      (covers_cons (inRd (r := aR s) (by simp)) (covers_cons (inRd (r := tR s) (by simp))
        (covers_cons (covers_prefix hfr (by decide)) covers_nil)))))
      (covers_cons hw' covers_nil)
  · rw [hc.wr, pre.wr]
    exact covers_cons (covers_of_mem (by simp)) covers_nil

/-- The call's result, on the call's state. -/
theorem Ready.xres {s c : State} (h : Lay s) (hc : Ready s c) : callRes (xS s c) = res s := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  obtain ⟨sa0, sa1⟩ := hc.stackArgs h (rdC s) (wrC s)
  have hd : bytesAt (cMem s) (Dst s) (L s) = bytesAt s.mem (Src s) (L s) := by
    have := Proof.AesGcm.bytesAt_writeBytes_self (eMem s) (Dst s) (bytesAt s.mem (Src s) (L s))
      (by rw [Lay.hlen]; exact (s.gpr .x7).isLt)
    rwa [Lay.hlen] at this
  simp only [callRes, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, c4, c5,
    c6, c7, sa0, sa1, hc.mem]
  exact h.cRes Lay.frame_cMem' hd

/-- After the call. -/
structure Called (s z : State) : Prop where
  fr : Frame [dR s, ⟨Bs s, 2592⟩] (cMem s) z.mem
  ra : z.mem.read (P s + BitVec.ofNat 64 16) 8 = s.gpr .x30
  out : match res s with
    | some pt => (z.gpr .x0).setWidth 32 = 1 ∧ bytesAt z.mem (Dst s) (L s) = pt
    | none => (z.gpr .x0).setWidth 32 = 0
  gpr : ∀ r ∈ preserved, r ≠ .x30 → z.gpr r = s.gpr r
  sp : z.sp = P s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem called_wp (F : OpenFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call F.fn.name F.fn.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  have hdep := F.depth
  refine WP.callFV (name := F.fn.name) F.verified.1 (openSpec_pre hcp) hcov hw
    (fun s' rd' wr' sp' fr' pres' presV' post' => ?_) (by omega_arith)
  have hpost := openSpec_post post' (by simp only [State.withRegions_gpr, c1]; exact h.pre.hR)
  rw [hc.xres h] at hpost
  have hpres : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x6 ∧ r ∉ copyRegs ∧ r ≠ .x16 ∧ r ≠ .x17 := by decide
  -- What the call wrote: `dst` and the stack below our frame.
  have frc : Frame [dR s, ⟨Bs s, 2592⟩] (cMem s) s'.mem := by
    rw [← hc.mem]
    refine fr'.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dR s, by simp, fun _ h => h⟩
    · refine ⟨⟨Bs s, 2592⟩, by simp, ?_⟩
      simp only [below, hc.sp, show P s = Bs s + BitVec.ofNat 64 2592 from rfl,
        add_ofNat_sub_ofNat _ (show 16 * F.fn.code.aarch64Depth ≤ 2592 by omega_arith)]
      exact Offset.sub_base _ (by omega_arith)
  -- The return address, from the frame, which the call kept.
  have ra : s'.mem.read (P s + BitVec.ofNat 64 16) 8 = s.gpr .x30 := by
    have e : c.mem.read (P s + BitVec.ofNat 64 16) 8 = s.gpr .x30 := by
      rw [hc.mem, show P s = Bs s + BitVec.ofNat 64 2592 from rfl, Offset.add_ofNat_add_ofNat,
        h.cFrame 2608 (by decide),
        Mem.read_write_sep (h.sep 2608 2600 (by decide) (by decide) (by decide)) (by decide),
        Mem.read_write_sep (h.sep 2608 2592 (by decide) (by decide) (by decide)) (by decide)]
      exact read_write_self _ _ _
    rw [← e]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [show P s + BitVec.ofNat 64 16 = Bs s + BitVec.ofNat 64 2608 by
        rw [show P s = Bs s + BitVec.ofNat 64 2592 from rfl, Offset.add_ofNat_add_ofNat]]
      exact h.pre.bd.symm.sub_right (stk_sub s 2608 8 (by decide)) |>.symm
    · simp only [below, hc.sp, show P s = Bs s + BitVec.ofNat 64 2592 from rfl,
        add_ofNat_sub_ofNat _ (show 16 * F.fn.code.aarch64Depth ≤ 2592 by omega_arith),
        Offset.add_ofNat_add_ofNat]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by decide) (by have := h.hBn; omega_arith)
  refine ⟨frc, ra, ?_, fun r hr h30 => by
      obtain ⟨h₆, hcr, h₁₆, h₁₇⟩ := hpres r hr h30
      rw [pres' r hr h30, hc.gpr r h₆ hcr h₁₆ h₁₇],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr, fun r hr => (presV' r hr).trans (hc.v r hr)⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, c6, c7] at hpost
  revert hpost
  cases res s with
  | some pt => exact id
  | none => exact fun hp => hp.1

/-! ## After the call -/

/-- One step of the wipe: the byte at `D + j` zeroed. -/
theorem zeroStep_ok (u : State) {D : Addr} {j : Nat} (h9 : u.gpr .x9 = D + BitVec.ofNat 64 j)
    (h11 : u.gpr .x11 = 0) (w : InRegions u.wr (D + BitVec.ofNat 64 j) 1) :
    ∃ u', runBlock isa [.strb .x11 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1] u = some u' ∧
      u'.mem = u.mem.write (D + BitVec.ofNat 64 j) 1 (0 : BitVec (8 * 1)) ∧
      u'.gpr .x9 = D + BitVec.ofNat 64 (j + 1) ∧
      u'.gpr .x10 = u.gpr .x10 - 1 ∧ (∀ r, r ≠ .x9 → r ≠ .x10 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.v = u.v := by
  have ha : u.gpr .x9 + BitVec.ofNat 64 0 = D + BitVec.ofNat 64 j := by rw [BitVec.add_zero, h9]
  let u₁ : State :=
    { u with mem := (u.mem.write (D + BitVec.ofNat 64 j) 1 (BitVec.setWidth 8 (BitVec.setWidth 32 (u.gpr .x11)))) }
  refine ⟨(u₁.write .x .x9 (u.gpr .x9 + BitVec.ofNat 64 1)).write .x .x10 (u.gpr .x10 - BitVec.ofNat 64 1), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some, Option.map_some,
      BitVec.setWidth_eq, ha, w, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self,
      Nat.mod_one, true_and, u₁], ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [State.write, u₁, h11]; rfl
  · simp [State.write, u₁, h9, BitVec.add_assoc, BitVec.ofNat_add]
  · simp [State.write, u₁]
  · intro r h₁ h₂; simp [State.write, u₁, h₁, h₂]

theorem ofNat64_sub_one {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `x9 = D`, `x10 = n` and
`x11 = 0`. -/
theorem wipeLoop_wp (u : State) {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (h9 : u.gpr .x9 = D)
    (h10 : u.gpr .x10 = BitVec.ofNat 64 n) (h11 : u.gpr .x11 = 0) (hw : Covers [⟨D, n⟩] u.wr)
    (hD : D.toNat + n ≤ 2 ^ 64) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem D n ∧ Frame [⟨D, n⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      u'.v = u.v := by
  unfold wipeLoop
  refine WP.ite (decide (n = 0)) (Proof.AesGcm.AArch64.eval_zero h10 hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl, rfl,
      rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧ t.gpr .x11 = 0 ∧
      t.gpr .x9 = D + BitVec.ofNat 64 j ∧ t.gpr .x10 = BitVec.ofNat 64 (n - j) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = u.gpr r) ∧ t.sp = u.sp ∧ t.rd = u.rd ∧ t.wr = u.wr ∧ t.v = u.v ∧
      Frame [⟨D, n⟩] u.mem t.mem ∧ Proof.Zeroize.Prefix t.mem D j) ?_ n u
      ⟨0, by omega, by omega, h11, by rw [h9]; exact (BitVec.add_zero _).symm, by rw [h10, Nat.sub_zero], fun _ _ _ => rfl,
        rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    intro rem t ⟨j, hj, hr, e11, e9, e10, ho, esp, erd, ewr, ev, hf', hpz⟩
    have hc : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 j) 1 := Offset.contains_base _ (by omega) (by omega)
    have hin : InRegions t.wr (D + BitVec.ofNat 64 j) 1 := by
      rw [ewr]; exact hw _ _ ⟨_, List.mem_singleton_self _, hc⟩
    obtain ⟨t', run, m', x9', x10', o', sp', rd', wr', v'⟩ := zeroStep_ok t e9 e11 hin
    refine WP.of_runBlock ⟨t', run, ?_⟩
    have hsub : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
      rw [ofNat64_sub_one (by omega) (by omega), Nat.sub_sub]
    rw [e10, hsub] at x10'
    have f'' : Frame [⟨D, n⟩] u.mem t'.mem := by
      rw [m']; exact hf'.write (List.mem_singleton_self _) _ hc
    have p' : Proof.Zeroize.Prefix t'.mem D (j + 1) := by
      rw [m']; exact Proof.Zeroize.prefix_write hpz (by omega)
    have o'' : ∀ r, r ≠ .x9 → r ≠ .x10 → t'.gpr r = u.gpr r := fun r a b => by rw [o' r a b, ho r a b]
    by_cases he : j + 1 = n
    · left
      refine ⟨by rw [Proof.AesGcm.AArch64.eval_nonzero x10' (by omega)]; simp only [Option.some.injEq]; simp; omega,
        by rw [← he]; exact p', f'', o'', sp'.trans esp, rd'.trans erd, wr'.trans ewr, v'.trans ev⟩
    · right
      refine ⟨by rw [Proof.AesGcm.AArch64.eval_nonzero x10' (by omega)]; simp only [Option.some.injEq]; simp; omega,
        n - (j + 1), by omega, j + 1, by omega, rfl, by rw [o' _ (by decide) (by decide), e11],
        x9', x10', o'', sp'.trans esp, rd'.trans erd, wr'.trans ewr, v'.trans ev, f'', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- `wipeArgs`: the stack arguments at `sp + 32` and `sp + 40` into `x9` and
`x10`, and zero into `x11`. -/
theorem wipeArgs_ok (a : State) (r₃₂ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 32) 8)
    (r₄₀ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 40) 8) :
    WP isa (.block wipeArgs) a fun e => e.gpr .x9 = a.mem.read (a.sp + BitVec.ofNat 64 32) 8 ∧
      e.gpr .x10 = a.mem.read (a.sp + BitVec.ofNat 64 40) 8 ∧ e.gpr .x11 = 0 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.sp = a.sp ∧
      e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [wipeArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
      Option.map_some, BitVec.setWidth_eq, r₃₂, r₄₀, and_self, ite_true, Nat.reduceLT, Nat.reduceMod,
      Nat.reduceMul, Option.bind_some, gpr_write, mem_write, rd_write, wr_write, sp_write]; rfl, rfl⟩ fun e he => ?_
  subst he
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], fun r h₁ h₂ h₃ => by
    simp [State.write, h₁, h₂, h₃], rfl, rfl, rfl, rfl, rfl⟩

/-- Where the wipe leaves the state: what follows the call, with `dst`
as `toPost` has it. -/
structure Done (s u : State) : Prop where
  post : toPost s u
  ra : u.mem.read (P s + BitVec.ofNat 64 16) 8 = s.gpr .x30
  gpr : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r
  sp : u.sp = P s
  rd : u.rd = s.rd
  wr : u.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- A stack argument, after the call. -/
theorem Called.arg {s z : State} (h : Lay s) (hz : Called s z) (i : Nat) (hi : i < 4) :
    z.mem.read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.cArg i hi]
  refine Frame.read hz.fr (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  have da := h.pre.da
  rw [h.hargR] at da
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (da.sub_right (Offset.sub _ (show 2624 ≤ 2624 + 8 * i by omega_arith) (by omega_arith))).symm
  · have := Offset.disjoint (Bs s) (d := 2624 + 8 * i) (n := 8) (e := 0) (k := 2592) (.inr (by omega_arith))
      (by omega_arith) (by have := h.hBn; omega_arith)
    rwa [BitVec.add_zero] at this

/-- After `wipeArgs`: `dst` in `x9`, `len` in `x10` and zero in `x11`. -/
structure WArgs (s z a : State) : Prop where
  x9 : a.gpr .x9 = Dst s
  x10 : a.gpr .x10 = BitVec.ofNat 64 (L s)
  x11 : a.gpr .x11 = 0
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → a.gpr r = z.gpr r
  mem : a.mem = z.mem
  sp : a.sp = z.sp
  rd : a.rd = z.rd
  wr : a.wr = z.wr
  v : a.v = z.v

theorem wipeArgs_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa (.block wipeArgs) z (WArgs s z) := by
  have pre := h.pre
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  have inA (d : Nat) (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 64) :
      InRegions (z.rd ++ z.wr) (z.sp + BitVec.ofNat 64 d) 8 := by
    rw [hz.sp, hP, Offset.add_ofNat_add_ofNat, hz.rd]
    exact h.inArg (2592 + d) (by omega_arith) (by omega_arith) _
  refine WP.mono (wipeArgs_ok z (inA 32 (by decide) (by decide)) (inA 40 (by decide) (by decide)))
    fun a ⟨x9a, x10a, x11a, ga, ma, spa, rda, wra, va⟩ => ?_
  rw [hz.sp, hP, Offset.add_ofNat_add_ofNat,
    show Bs s + BitVec.ofNat 64 (2592 + 32) = Bs s + BitVec.ofNat 64 (2624 + 8 * 0) from rfl,
    hz.arg h 0 (by decide)] at x9a
  rw [hz.sp, hP, Offset.add_ofNat_add_ofNat,
    show Bs s + BitVec.ofNat 64 (2592 + 40) = Bs s + BitVec.ofNat 64 (2624 + 8 * 1) from rfl,
    hz.arg h 1 (by decide)] at x10a
  have hL : stackArg s 1 = BitVec.ofNat 64 (L s) := by
    apply BitVec.eq_of_toNat_eq; rw [pre.dl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s.gpr .x7).isLt]
  rw [hL] at x10a
  exact ⟨x9a, x10a, x11a, ga, ma, spa, rda, wra, va⟩

/-- When the call failed: `dst` zeroed. -/
theorem wipe_wp {s z : State} (h : Lay s) (hz : Called s z) (hres : res s = none) :
    WP isa wipe z (Done s) := by
  have pre := h.pre
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  have x0 : (z.gpr .x0).setWidth 32 = 0 := by have := hz.out; rw [hres] at this; exact this
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun a ha => ?_)
  have hw : Covers [⟨Dst s, L s⟩] a.wr := by
    rw [ha.wr, hz.wr, pre.wr]; exact covers_cons (covers_of_mem (by simp)) covers_nil
  refine WP.mono (wipeLoop_wp a (s.gpr .x7).isLt ha.x9 ha.x10 ha.x11 hw pre.od)
    fun u ⟨pz, fu, gu, spu, rdu, wru, vu⟩ => ?_
  have g' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → u.gpr r = z.gpr r := fun r a b c => by
    rw [gu r a b, ha.gpr r a b c]
  refine ⟨?_, ?_, fun r hr h30 => ?_, by rw [spu, ha.sp, hz.sp], by rw [rdu, ha.rd, hz.rd],
    by rw [wru, ha.wr, hz.wr], fun r hr => by rw [vu, ha.v]; exact hz.v r hr⟩
  · show match res s with | some pt => _ | none => _
    rw [hres]
    exact ⟨by rw [g' _ (by decide) (by decide) (by decide)]; exact x0, bytesAt_zeros pz⟩
  · rw [← hz.ra, ← ha.mem]
    refine Frame.read fu (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [hP, Offset.add_ofNat_add_ofNat]
    exact (pre.bd.symm.sub_right (stk_sub s 2608 8 (by decide))).symm
  · have hp' : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    have := hp' r hr
    rw [g' r this.1 this.2.1 this.2.2]; exact hz.gpr r hr h30

/-- After the call: `dst` zeroed if it failed. -/
theorem after_ok {s z : State} (h : Lay s) (hz : Called s z) : WP isa after z (Done s) := by
  unfold after
  have hdone : res s ≠ none → Done s z := fun hn => by
    obtain ⟨pt, hpt⟩ := Option.ne_none_iff_exists'.mp hn
    have o := hz.out
    rw [hpt] at o
    refine ⟨?_, hz.ra, hz.gpr, hz.sp, hz.rd, hz.wr, hz.v⟩
    show match res s with | some pt => _ | none => _
    rw [hpt]; exact o
  cases hr : res s with
  | none =>
    have x0 : (z.gpr .x0).setWidth 32 = 0 := by have := hz.out; rw [hr] at this; exact this
    exact WP.ite true (by show some (_ == _) = _; rw [show z.read .w .x0 = 0 from x0]; rfl)
      (fun _ => wipe_wp h hz hr) (fun h' => absurd h' (by decide))
  | some pt =>
    have x0 : (z.gpr .x0).setWidth 32 = 1 := by have := hz.out; rw [hr] at this; exact this.1
    exact WP.ite false (by show some (_ == _) = _; rw [show z.read .w .x0 = 1 from x0]; rfl)
      (fun h' => absurd h' (by decide)) (fun _ => WP.block_nil (hdone (by rw [hr]; simp)))

/-- Our return address back in `x30`, and the frame freed. -/
theorem ret_wp {s u : State} (h : Lay s) (hu : Done s u) :
    WP isa (.block [.ldrSp .x30 16]) u fun z => abiPreserved s (freed 32 z) ∧ toPost s (freed 32 z) := by
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  refine WP.mono (ldrSp_ok (t := .x30) (k := 16) u (by decide) ?_) fun z ⟨x30z, gz, mz, spz, rdz, wrz, vz⟩ => ?_
  · rw [hu.sp, hu.rd, hu.wr, hP, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), contains_off _ (by decide) (by decide) (by decide)⟩
  rw [hu.sp, hu.ra] at x30z
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · show z.gpr r = s.gpr r
    by_cases h30 : r = .x30
    · subst h30; exact x30z
    · rw [gz r h30, hu.gpr r hr h30]
  · show z.sp + BitVec.ofNat 64 32 = s.sp
    rw [spz, hu.sp, hP, Offset.add_ofNat_add_ofNat, h.hB]
  · show (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
    rw [vz]; exact hu.v r hr
  · have p := hu.post
    show match res s with | some pt => _ | none => _
    revert p
    show (match res s with | some pt => _ | none => _) → _
    cases res s with
    | some pt => intro p; exact ⟨by show (z.gpr .x0).setWidth 32 = _; rw [gz _ (by decide)]; exact p.1,
        by show bytesAt z.mem _ _ = _; rw [mz]; exact p.2⟩
    | none => intro p; exact ⟨by show (z.gpr .x0).setWidth 32 = _; rw [gz _ (by decide)]; exact p.1,
        by show bytesAt z.mem _ _ = _; rw [mz]; exact p.2⟩

theorem openTo_wp (F : OpenFn) {s : State} (hs : ToPre s) :
    WP isa (openTo F.fn) s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hs.w₁; omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (copied_wp h he) fun c hc => ?_)
  refine WP.seq (WP.mono (ready_wp h hc) fun r hr => ?_)
  refine WP.seq (WP.mono (called_wp F h hr) fun z hz => ?_)
  exact WP.seq (WP.mono (after_ok h hz) fun u hu => ret_wp h hu)

end VG.Proof.AesGcm.AArch64.OpenTo
