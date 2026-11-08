module

public import VerifiedGarbage.Impl.AesGcm.AArch64.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Copy
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.Cmac.Spec

/-!
# AES-GCM decryption out of place, by a copy, AArch64: the function

Untrusted: everything here is checked by Lean. The contract the proofs of
`vg_aes_gcm_open_to` and `vg_aes_gcm_open_to_with_powers` are written against
(`toK S`), which their shared ones imply (`OpenTo/Verified.lean`), and its
proof (`openTo_wp`), for the shape `S` of the function they call: the number
of its stack arguments (`tag`, `tag_len`, and for
`vg_aes_gcm_open_with_powers`, `pw`), the buffers those after `tag_len` point
to, what it needs of them (`Shape.X`, the powers of the key context's hash
subkey), and its contract with 2592 bytes of stack, as the call lays it out
(`callPre`, `callPost`, `callPub`). It calls an implementation of that
function as an artifact, with its working space in a frame of its own, so
what the proof needs of it is that contract (`OpenFn`). The instances are
`openShape` (`vg_aes_gcm_open`, by `Proof.AesGcm.openRoundsContract`) and
`pwShape` (`vg_aes_gcm_open_with_powers`, by
`Proof.AesGcm.openWithPowersRoundsContract`).

With `B` the base of the 2624 bytes of stack below the stack pointer
(`sp = B + 2624`), the function allocates its frame of 32 bytes at
`P = B + 2592`: the call's `n` stack arguments, our stack arguments `2`, …,
`n + 1`, at `P`, `P + 8`, …, and our return address at `P + 8 n`
(`entered_wp`). It copies the `len` bytes at `src` to `dst` (`copied_wp`, by
`Gather.copySlice_wp`), puts `dst` in `x6` (`ready_wp`), calls the function
on `dst` in place (`called_wp`), which writes only `dst` and the stack below
`P`, keeping our frame, and zeroes `dst` if it returned 0 (`after_ok`,
`wipe_wp`). Every write is to `dst` or to the stack below `sp`.
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

/-! ## The arguments -/

section
variable (s : State)

/-- The arguments: `(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3,
aad = x4, aad_len = x5, src = x6, len = x7, dst = [sp], dst_len = [sp + 8],
tag = [sp + 16], tag_len = [sp + 24], …)`. -/
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

/-- Our stack arguments after `tag_len`, for a call with `n` stack arguments. -/
abbrev ourX (n : Nat) : List Addr := (List.range (n - 2)).map fun i => stackArg s (4 + i)

/-- The regions: the key context, the nonce, the additional data, the
ciphertext, the output, the tag, the stack arguments (for a call with `n`)
and the stack below the stack pointer. -/
abbrev kR : Region := ⟨K s, 256⟩
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev sR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tR : Region := ⟨Tg s, TL s⟩
abbrev argR (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * (n + 2)⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 2624, 2624⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (K s) (R s)) (ctxH s.mem (K s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-! ## The function called -/

/-- The call's stack arguments after `tag_len`, of `n`. -/
abbrev callX (n : Nat) (s : State) : List Addr := (List.range (n - 2)).map fun i => stackArg s (2 + i)

/-- The precondition of the function called, as the call lays it out, with
`n` stack arguments, those after `tag_len` pointing to the buffers `xR`,
which hold `X`. -/
def callPre (n : Nat) (xR : List Addr → List Region) (X : Mem → Addr → List Addr → Prop) (s : State) : Prop :=
  2592 ≤ s.sp.toNat ∧ s.sp.toNat + 8 * n ≤ 2 ^ 64 ∧
    s.rd = [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩] ++ xR (callX n s) ++ [⟨stackArgAddr s 0, 8 * n⟩] ∧
    s.wr = [⟨s.gpr .x6, (s.gpr .x7).toNat⟩] ∧
    (⟨s.gpr .x0, 256⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∧
    (∀ r ∈ xR (callX n s), (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint r) ∧
    (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 8 * n⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x0, 256⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∧
    (∀ r ∈ xR (callX n s), (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint r) ∧
    (⟨s.sp - BitVec.ofNat 64 2592, 2592⟩ : Region).Disjoint ⟨stackArgAddr s 0, 8 * n⟩ ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (∀ r ∈ xR (callX n s), r.base.toNat + r.len ≤ 2 ^ 64) ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) ∧
    X s.mem (s.gpr .x0) (callX n s)

/-- `vg_aes_gcm_open`'s result on the arguments of a call. -/
abbrev callRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- The postcondition of the function called: the plaintext and 1, or 0 and
the ciphertext. -/
def callPost (s s' : State) : Prop :=
  match callRes s with
  | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧
      bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat

/-- The public data of a call: whether it succeeds. -/
def callLeak (s : State) : List Nat :=
  if ¬((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) then []
  else [if (callRes s).isSome = true then 1 else 0]

/-- What two calls agree on: their arguments, with `n` on the stack, and
whether they succeed. -/
def callPub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ callLeak s₁ = callLeak s₂ ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧
    s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧
    s₁.gpr .x7 = s₂.gpr .x7 ∧ ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- What the instances differ in: the function called, an implementation of
`vg_aes_gcm_open` or of an instance of it, with its contract with 2592 bytes
of stack (`C`), which follows from the call's layout (`pre`, `post`, `pub`):
its `n` stack arguments, those after `tag_len` pointing to the buffers `xR`,
which both functions only read, and what it needs of them (`X`), which
writes elsewhere keep. -/
structure Shape where
  n : Nat
  hn : n = 2 ∨ n = 3
  xR : List Addr → List Region
  X : Mem → Addr → List Addr → Prop
  X_frame : ∀ {m m' : Mem} {ctx : Addr} {ps : List Addr} {rs : List Region}, Frame rs m m' →
    (∀ r ∈ rs, (⟨ctx, 256⟩ : Region).Disjoint r) → (∀ x ∈ xR ps, ∀ r ∈ rs, x.Disjoint r) →
    (∀ x ∈ xR ps, x.base.toNat + x.len ≤ 2 ^ 64) → X m ctx ps → X m' ctx ps
  C : Contract isa
  pre : ∀ {s}, callPre n xR X s → C.pre s
  post : ∀ {s s'}, C.post s s' →
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) → callPost s s'
  pub : ∀ {s₁ s₂}, callPub n s₁ s₂ → C.pub s₁ s₂

theorem Shape.two_le (S : Shape) : 2 ≤ S.n := by rcases S.hn with h | h <;> omega
theorem Shape.le_three (S : Shape) : S.n ≤ 3 := by rcases S.hn with h | h <;> omega

/-- An implementation of the function called, by its contract, whose frames
use at most its 2592 bytes of stack. -/
structure OpenFn (S : Shape) where
  fn : Fn
  verified : Verified AArch64.target fn.code S.C
  depth : 16 * fn.code.aarch64Depth ≤ 2592

/-! ## The contract -/

/-- What the proof of `openTo` needs: the layout of its shared contract,
with 2624 bytes of stack, `dst_len` its `len`, our stack arguments after
`tag_len` pointing to the buffers `S.xR`, which hold `S.X`. -/
structure ToPre (S : Shape) (s : State) : Prop where
  w₁ : 2624 ≤ s.sp.toNat
  w₂ : s.sp.toNat + 8 * (S.n + 2) ≤ 2 ^ 64
  rd : s.rd = [kR s, nR s, aR s, sR s, tR s] ++ S.xR (ourX s S.n) ++ [argR s S.n]
  wr : s.wr = [dR s]
  kd : (kR s).Disjoint (dR s)
  nd : (nR s).Disjoint (dR s)
  ad : (aR s).Disjoint (dR s)
  sd : (sR s).Disjoint (dR s)
  dt : (dR s).Disjoint (tR s)
  dx : ∀ r ∈ S.xR (ourX s S.n), (dR s).Disjoint r
  da : (dR s).Disjoint (argR s S.n)
  bk : (stkR s).Disjoint (kR s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bs : (stkR s).Disjoint (sR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tR s)
  bx : ∀ r ∈ S.xR (ourX s S.n), (stkR s).Disjoint r
  barg : (stkR s).Disjoint (argR s S.n)
  ok : (K s).toNat + 256 ≤ 2 ^ 64
  on : (Nn s).toNat + NL s ≤ 2 ^ 64
  oa : (Ad s).toNat + AL s ≤ 2 ^ 64
  os : (Src s).toNat + L s ≤ 2 ^ 64
  od : (Dst s).toNat + L s ≤ 2 ^ 64
  ot : (Tg s).toNat + TL s ≤ 2 ^ 64
  ox : ∀ r ∈ S.xR (ourX s S.n), r.base.toNat + r.len ≤ 2 ^ 64
  hR : R s = 10 ∨ R s = 12 ∨ R s = 14
  dl : (stackArg s 1).toNat = L s
  X : S.X s.mem (K s) (ourX s S.n)

/-- `openToRoundsPost`, for the rounds of `ToPre`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (Dst s) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak: whether it succeeds. -/
def toLeak (s : State) : List Nat :=
  if ¬(R s = 10 ∨ R s = 12 ∨ R s = 14) then [] else [if (res s).isSome = true then 1 else 0]

/-- What two runs agree on: the arguments, with `n + 2` on the stack, and the leak. -/
def toPub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ toLeak s₁ = toLeak s₂ ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    ∀ i < n + 2, stackArg s₁ i = stackArg s₂ i

/-- `openTo`, calling a function of shape `S`. -/
def toK (S : Shape) : Contract isa where
  pre := ToPre S
  post := toPost
  pub := toPub S.n

/-! ## Steps -/

theorem frameBytes_eq {n : Nat} (hn : n = 2 ∨ n = 3) : frameBytes n = 32 := by
  rcases hn with rfl | rfl <;> rfl

theorem callArgs_eq {n : Nat} (hn : n = 2 ∨ n = 3) : callArgs n = [.ldrSp .x6 32] := by
  unfold callArgs; rw [frameBytes_eq hn]

theorem wipeArgs_eq {n : Nat} (hn : n = 2 ∨ n = 3) :
    wipeArgs n = [.ldrSp .x9 32, .ldrSp .x10 40, .movz .x .x11 0 0] := by
  unfold wipeArgs; rw [frameBytes_eq hn]

/-- The start of the entry: `sp` in `x16`, and our return address at `sp + k`. -/
theorem head_ok (a : State) {k : Nat} (hk₁ : k % 8 = 0) (hk₂ : k < 32768)
    (w : InRegions a.wr (a.sp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.addSp .x16 0, .str .x .x30 .x16 k]) a fun e =>
      e.mem = a.mem.write (a.sp + BitVec.ofNat 64 k) 8 (a.gpr .x30) ∧ e.gpr .x16 = a.sp ∧
      (∀ r, r ≠ .x16 → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧ e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  have e₀ : a.sp + BitVec.ofNat 64 0 = a.sp := BitVec.add_zero _
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some,
      Option.map_some, BitVec.setWidth_eq, e₀, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul,
      Nat.reduceMod, and_self, hk₁, hk₂, w]; rfl, rfl⟩ fun e he => ?_
  subst he
  exact ⟨rfl, by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

/-- One copy of the entry: the doubleword at `sp + o` to `x16 + k`, through `x17`. -/
theorem copyStep_ok (t : State) {o k : Nat} (ho₁ : o % 8 = 0) (ho₂ : o < 32768) (hk₁ : k % 8 = 0)
    (hk₂ : k < 32768) (r : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 o) 8)
    (w : InRegions t.wr (t.gpr .x16 + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.ldrSp .x17 o, .str .x .x17 .x16 k]) t fun u =>
      u.mem = t.mem.write (t.gpr .x16 + BitVec.ofNat 64 k) 8 (t.mem.read (t.sp + BitVec.ofNat 64 o) 8) ∧
      (∀ r, r ≠ .x17 → u.gpr r = t.gpr r) ∧ u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.v = t.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some,
      Option.map_some, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul,
      Nat.reduceMod, and_self, ho₁, ho₂, hk₁, hk₂, r, w]; rfl, rfl⟩ fun u hu => ?_
  subst hu
  exact ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

/-- The end of the entry: the doubleword at `sp + o` in `x11`, `x6` in `x12`
and `x7` in `x13`. -/
theorem tail_ok (a : State) {o : Nat} (ho₁ : o % 8 = 0) (ho₂ : o < 32768)
    (r : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 o) 8) :
    WP isa (.block [.ldrSp .x11 o, .addImm .x .x12 .x6 0, .addImm .x .x13 .x7 0]) a fun e =>
      e.gpr .x11 = a.mem.read (a.sp + BitVec.ofNat 64 o) 8 ∧ e.gpr .x12 = a.gpr .x6 ∧
      e.gpr .x13 = a.gpr .x7 ∧ (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → e.gpr r = a.gpr r) ∧
      e.mem = a.mem ∧ e.sp = a.sp ∧ e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some, Option.map_some,
      BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self,
      ho₁, ho₂, r]; rfl, rfl⟩ fun e he => ?_
  subst he
  exact ⟨by simp [State.write], by simp [State.write], by simp [State.write],
    fun r h₁ h₂ h₃ => by simp [State.write, h₁, h₂, h₃], rfl, rfl, rfl, rfl, rfl⟩

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 2624 bytes of stack below the stack pointer, and our frame. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 2624
abbrev P : Addr := Bs s + BitVec.ofNat 64 2592
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 2592, 32⟩

end

/-- The memory once the entry has stored our return address at `P + 8 n`
and the first `k` of the call's `n` stack arguments at `P + 8 j`. -/
def argsMem (n : Nat) (s : State) : Nat → Mem
  | 0 => s.mem.write (Bs s + BitVec.ofNat 64 (2592 + 8 * n)) 8 (s.gpr .x30)
  | k + 1 => (argsMem n s k).write (Bs s + BitVec.ofNat 64 (2592 + 8 * k)) 8 (stackArg s (2 + k))

section
variable (S : Shape) (s : State)

/-- The memory after the entry. -/
abbrev eMem : Mem := argsMem S.n s S.n

/-- The memory once the ciphertext is copied to `dst`. -/
abbrev cMem : Mem := writeBytes (eMem S s) (Dst s) (bytesAt s.mem (Src s) (L s))

/-- The regions the call reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, tR s] ++ S.xR (ourX s S.n) ++ [⟨P s, 8 * S.n⟩]
abbrev wrC : List Region := [dR s]

end

/-- What `ToPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (S : Shape) (s : State) : Prop where
  pre : ToPre S s
  hB : s.sp = Bs s + BitVec.ofNat 64 2624
  hBn : (Bs s).toNat + 2656 ≤ 2 ^ 64
  hBx : (Bs s).toNat + 2624 + 8 * (S.n + 2) ≤ 2 ^ 64
  hargR : argR s S.n = ⟨Bs s + BitVec.ofNat 64 2624, 8 * (S.n + 2)⟩

theorem stackArgAddr_eq (s : State) {B : Addr} (hB : s.sp = B + BitVec.ofNat 64 2624) (i : Nat) :
    stackArgAddr s i = B + BitVec.ofNat 64 (2624 + 8 * i) := by
  rw [stackArgAddr, hB, Offset.add_ofNat_add_ofNat]

theorem lay {S : Shape} {s : State} (hs : ToPre S s) : Lay S s := by
  have hB : s.sp = Bs s + BitVec.ofNat 64 2624 := (BitVec.sub_add_cancel s.sp _).symm
  have hBx : (Bs s).toNat + 2624 + 8 * (S.n + 2) ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    have := hs.w₁
    have := hs.w₂
    omega_arith
  have := S.two_le
  exact ⟨hs, hB, by omega, hBx, by simp only [argR, stackArgAddr_eq s hB, Nat.mul_zero, Nat.add_zero]⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2624) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2624⟩ :=
  Offset.sub_base _ h'

theorem stkR_eq (s : State) : stkR s = ⟨Bs s, 2624⟩ := rfl

/-- The entry writes only our frame. -/
theorem frame_argsMem (s : State) {n : Nat} (hn : n ≤ 3) : ∀ k ≤ n, Frame [FR s] s.mem (argsMem n s k)
  | 0, _ => (Frame.refl _ _).write (List.mem_singleton_self _) _
      (contains_off _ (by omega) (by omega) (by omega))
  | k + 1, hk => (frame_argsMem s hn k (by omega)).write (List.mem_singleton_self _) _
      (contains_off _ (by omega) (by omega) (by omega))

theorem frame_eMem (S : Shape) (s : State) : Frame [FR s] s.mem (eMem S s) :=
  frame_argsMem s S.le_three _ (Nat.le_refl _)

namespace Lay

variable {S : Shape} {s : State} (h : Lay S s)
include h

theorem hA (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (2624 + 8 * i) := stackArgAddr_eq s h.hB i

theorem argIn : argR s S.n ∈ s.rd := by rw [h.pre.rd]; simp

theorem inArgX (d : Nat) (h₁ : 2624 ≤ d) (h₂ : d + 8 ≤ 2624 + 8 * (S.n + 2)) (rs : List Region) :
    InRegions (s.rd ++ rs) (Bs s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_append_left _ h.argIn, by
    rw [h.hargR]; exact contains_off _ h₁ (by omega_arith) (by have := h.hBx; omega_arith)⟩

theorem inArg (d : Nat) (h₁ : 2624 ≤ d) (h₂ : d + 8 ≤ 2656) (rs : List Region) :
    InRegions (s.rd ++ rs) (Bs s + BitVec.ofNat 64 d) 8 :=
  h.inArgX d h₁ (by have := S.two_le; omega_arith) rs

theorem sa (i : Nat) : s.mem.read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.hA]; rfl

theorem sep (d e : Nat) (h₁ : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2656) (he : e + 8 ≤ 2656) :
    Mem.Sep (Bs s + BitVec.ofNat 64 d) 8 (Bs s + BitVec.ofNat 64 e) 8 :=
  Offset.sep _ h₁ (by have := h.hBn; omega_arith) (by have := h.hBn; omega_arith)

/-- Our stack arguments, after any part of the entry. -/
theorem argsArg {k : Nat} (hk : k ≤ S.n) {i : Nat} (hi : i < S.n + 2) :
    (argsMem S.n s k).read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.sa i]
  refine Frame.read (frame_argsMem s S.le_three k hk) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (.inr (by omega_arith)) (by have := h.hBx; omega_arith)
    (by have := h.hBn; omega_arith)

/-- The call's stack arguments the entry has stored. -/
theorem argsSlot {k : Nat} (hk : k ≤ S.n) {j : Nat} (hj : j < k) :
    (argsMem S.n s k).read (Bs s + BitVec.ofNat 64 (2592 + 8 * j)) 8 = stackArg s (2 + j) := by
  have := S.le_three
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [argsMem]
    by_cases hjk : j = k
    · subst hjk; exact read_write_self _ _ _
    · rw [Mem.read_write_sep (h.sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact ih (by omega) (by omega)

/-- Our return address, after any part of the entry. -/
theorem argsRa {k : Nat} (hk : k ≤ S.n) :
    (argsMem S.n s k).read (Bs s + BitVec.ofNat 64 (2592 + 8 * S.n)) 8 = s.gpr .x30 := by
  have := S.le_three
  induction k with
  | zero => exact read_write_self _ _ _
  | succ k ih =>
    simp only [argsMem]
    rw [Mem.read_write_sep (h.sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact ih (by omega)

/-- The bytes at `src`, after the entry. -/
theorem srcE : bytesAt (eMem S s) (Src s) (L s) = bytesAt s.mem (Src s) (L s) :=
  bytesAt_frame (frame_eMem S s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bs.symm.sub_right (stk_sub s 2592 32 (by decide))) (by have := h.pre.os; omega_arith)

omit h in
theorem hlen : (bytesAt s.mem (Src s) (L s)).length = L s := Proof.Cmac.bytesAt_length _ _ _

omit h in
theorem frame_cMem : Frame [dR s] (eMem S s) (cMem S s) :=
  writeBytes_frame _ _ _ (by rw [Lay.hlen]; exact Region.contains_self _ _)

/-- A doubleword of the stack, once the ciphertext is copied. -/
theorem cFrame (d : Nat) (hd' : d + 8 ≤ 2624) :
    (cMem S s).read (Bs s + BitVec.ofNat 64 d) 8 = (eMem S s).read (Bs s + BitVec.ofNat 64 d) 8 :=
  Frame.read Lay.frame_cMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.symm.sub_right (stk_sub s d 8 hd') |>.symm) (by decide)

theorem cArg (i : Nat) (hi : i < S.n + 2) :
    (cMem S s).read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.argsArg (Nat.le_refl _) hi]
  refine Frame.read Lay.frame_cMem (contains_off _ (Nat.le_refl _) (Nat.le_refl _) (by omega_arith)) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  have da := h.pre.da
  rw [h.hargR] at da
  exact (da.sub_right (Offset.sub _ (show 2624 ≤ 2624 + 8 * i by omega_arith) (by omega_arith))).symm

omit h in
/-- The memory the call finds, changed since the entry only in the frame and at `dst`. -/
theorem frame_cMem' : Frame [FR s, dR s] s.mem (cMem S s) :=
  ((frame_eMem S s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
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

/-- What the call needs of the buffers after `tag_len`, on the memory it finds. -/
theorem cX : S.X (cMem S s) (K s) (ourX s S.n) :=
  S.X_frame Lay.frame_cMem' (Lay.apart h.pre.bk h.pre.kd)
    (fun x hx => Lay.apart (h.pre.bx x hx) (h.pre.dx x hx).symm) h.pre.ox h.pre.X

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (S : Shape) (s e : State) : Prop where
  mem : e.mem = eMem S s
  x11 : e.gpr .x11 = Dst s
  x12 : e.gpr .x12 = Src s
  x13 : e.gpr .x13 = s.gpr .x7
  gpr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x16 → r ≠ .x17 → e.gpr r = s.gpr r
  sp : e.sp = P s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (e.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem allocated_sp {S : Shape} {s : State} (h : Lay S s) : (allocated 32 s).sp = P s := by
  show s.sp - BitVec.ofNat 64 32 = _
  rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]

theorem allocated_wr {S : Shape} {s : State} (h : Lay S s) : (allocated 32 s).wr = FR s :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr : List Region) = _
  rw [show s.sp - BitVec.ofNat 64 32 = _ from allocated_sp h]

/-- The state as the entry's copies leave it, after `k` of them. -/
def Copying (S : Shape) (s : State) (k : Nat) (t : State) : Prop :=
  t.mem = argsMem S.n s k ∧ t.gpr .x16 = P s ∧ t.sp = P s ∧
    (∀ r, r ≠ .x16 → r ≠ .x17 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = FR s :: s.wr ∧ t.v = s.v

theorem copying_step {S : Shape} {s : State} (h : Lay S s) (k : Nat) (t : State) (hk : k < S.n)
    (ht : Copying S s k t) :
    WP isa (.block [.ldrSp .x17 (32 + 16 + 8 * k), .str .x .x17 .x16 (8 * k)]) t (Copying S s (k + 1)) := by
  obtain ⟨mt, x16t, spt, gt, rdt, wrt, vt⟩ := ht
  have := S.le_three
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  refine WP.mono (copyStep_ok t (o := 32 + 16 + 8 * k) (k := 8 * k) (by omega) (by omega) (by omega) (by omega)
    ?_ ?_) fun u ⟨mu, gu, spu, rdu, wru, vu⟩ => ?_
  · rw [spt, rdt, hP, Offset.add_ofNat_add_ofNat]
    exact h.inArgX _ (by omega) (by omega) _
  · rw [x16t, wrt, hP, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_cons_self .., contains_off _ (by omega) (by omega) (by omega)⟩
  refine ⟨?_, by rw [gu _ (by decide), x16t], spu.trans spt,
    fun r h₁₆ h₁₇ => by rw [gu r h₁₇, gt r h₁₆ h₁₇], rdu.trans rdt, wru.trans wrt, vu.trans vt⟩
  rw [mu, mt, x16t, spt, hP, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    show 2592 + (32 + 16 + 8 * k) = 2624 + 8 * (2 + k) by omega, h.argsArg (by omega) (by omega)]
  rfl

theorem entered_wp {S : Shape} {s : State} (h : Lay S s) :
    WP isa (.block (entry S.n)) (allocated 32 s) (Entered S s) := by
  have asp := allocated_sp h
  have awr := allocated_wr h
  have := S.le_three
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  unfold entry copyArgs
  rw [frameBytes_eq S.hn, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (head_ok _ (k := 8 * S.n) (by omega) (by omega) ?_) fun a ⟨ma, x16a, ga, spa, rda, wra, va⟩ => ?_
  · rw [awr, asp]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (wp_range_flatMap (Copying S s) (N := S.n) (fun k t hk ht => copying_step h k t hk ht) S.n
    (Nat.le_refl _) a ⟨?_, by rw [x16a, asp], by rw [spa, asp], fun r h₁₆ _ => by rw [ga r h₁₆]; rfl,
      rda, by rw [wra, awr], va⟩) fun t ⟨mt, _, spt, gt, rdt, wrt, vt⟩ => ?_
  · rw [ma, asp, hP, Offset.add_ofNat_add_ofNat]; rfl
  refine WP.mono (tail_ok t (o := 32) (by decide) (by decide) ?_)
    fun e ⟨x11e, x12e, x13e, ge, me, spe, rde, wre, ve⟩ => ?_
  · rw [spt, rdt, hP, Offset.add_ofNat_add_ofNat]
    exact h.inArg _ (by decide) (by decide) _
  refine ⟨me.trans mt, ?_, by rw [x12e, gt _ (by decide) (by decide)], by rw [x13e, gt _ (by decide) (by decide)],
    fun r h₁₁ h₁₂ h₁₃ h₁₆ h₁₇ => by rw [ge r h₁₁ h₁₂ h₁₃, gt r h₁₆ h₁₇], spe.trans spt, rde.trans rdt,
    wre.trans wrt, fun r _ => by rw [ve, vt]⟩
  rw [x11e, spt, mt, hP, Offset.add_ofNat_add_ofNat]
  exact h.argsArg (Nat.le_refl _) (i := 0) (by omega)

/-- After the copy. -/
structure Copied (S : Shape) (s c : State) : Prop where
  mem : c.mem = cMem S s
  gpr : ∀ r, r ∉ copyRegs → r ≠ .x16 → r ≠ .x17 → c.gpr r = s.gpr r
  sp : c.sp = P s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (c.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem copied_wp {S : Shape} {s e : State} (h : Lay S s) (he : Entered S s e) : WP isa copySlice e (Copied S s) := by
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
structure Ready (S : Shape) (s c : State) : Prop where
  mem : c.mem = cMem S s
  x6 : c.gpr .x6 = Dst s
  gpr : ∀ r, r ≠ .x6 → r ∉ copyRegs → r ≠ .x16 → r ≠ .x17 → c.gpr r = s.gpr r
  sp : c.sp = P s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (c.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem ready_wp {S : Shape} {s c : State} (h : Lay S s) (hc : Copied S s c) :
    WP isa (.block (callArgs S.n)) c (Ready S s) := by
  rw [callArgs_eq S.hn]
  refine WP.mono (ldrSp_ok (t := .x6) c (by decide)
      (by rw [hc.sp, Offset.add_ofNat_add_ofNat, hc.rd, hc.wr]; exact h.inArg 2624 (by decide) (by decide) _))
    fun r ⟨x6r, gr, mr, spr, rdr, wrr, vr⟩ => ?_
  rw [hc.sp, Offset.add_ofNat_add_ofNat, hc.mem] at x6r
  exact ⟨mr.trans hc.mem, x6r.trans (h.cArg 0 (by have := S.two_le; omega)),
    fun r' h₆ hr h₁₆ h₁₇ => (gr r' h₆).trans (hc.gpr r' hr h₁₆ h₁₇), spr.trans hc.sp, rdr.trans hc.rd,
    wrr.trans hc.wr, fun r' hr' => by rw [vr]; exact hc.v r' hr'⟩

/-- The registers at the call. -/
theorem Ready.callGpr {S : Shape} {s c : State} (hc : Ready S s c) :
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

/-- The call's stack arguments: our stack arguments after `dst_len`. -/
theorem Ready.stackArgs {S : Shape} {s c : State} (h : Lay S s) (hc : Ready S s c) (rd' wr' : List Region)
    {i : Nat} (hi : i < S.n) : stackArg ((c.callEntry).withRegions rd' wr') i = stackArg s (2 + i) := by
  have := S.le_three
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  have c₀ : c.mem.read (P s + BitVec.ofNat 64 (8 * i)) 8 = stackArg s (2 + i) := by
    rw [hc.mem, hP, Offset.add_ofNat_add_ofNat, h.cFrame _ (by omega)]
    exact h.argsSlot (Nat.le_refl _) hi
  rw [← c₀, ← hc.sp]; simp [stackArg, stackArgAddr, Mem.readW]

/-- The call's state, with its permissions. -/
abbrev xS (S : Shape) (s c : State) : State := c.callEntry.withRegions (rdC S s) (wrC s)

/-- The call's stack arguments after `tag_len`: ours. -/
theorem Ready.callX {S : Shape} {s c : State} (h : Lay S s) (hc : Ready S s c) :
    callX S.n (xS S s c) = ourX s S.n :=
  List.map_congr_left fun i hi => by
    have := List.mem_range.mp hi
    rw [hc.stackArgs h _ _ (by omega)]
    exact congrArg (stackArg s) (by omega)

/-- What the call needs. -/
theorem Ready.call {S : Shape} {s c : State} (h : Lay S s) (hc : Ready S s c) :
    callPre S.n S.xR S.X (xS S s c) ∧ Covers (rdC S s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have pre := h.pre
  have := S.le_three
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  have sa0 := hc.stackArgs h (rdC S s) (wrC s) (i := 0) (by have := S.two_le; omega)
  have sa1 := hc.stackArgs h (rdC S s) (wrC s) (i := 1) (by have := S.two_le; omega)
  have cx := hc.callX h
  have dl := pre.dl
  have sad0 : stackArgAddr (xS S s c) 0 = P s := by simp [stackArgAddr, hc.sp]
  have hPn : (P s).toNat = (Bs s).toNat + 2592 := by
    have := h.hBn
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  have hPsub : P s - BitVec.ofNat 64 2592 = Bs s := by rw [add_ofNat_sub_ofNat _ (by decide), Nat.sub_self,
    BitVec.add_zero]
  have stkArg : (⟨Bs s, 2592⟩ : Region).Disjoint ⟨P s, 8 * S.n⟩ := by
    have := Offset.disjoint (Bs s) (d := 0) (n := 2592) (e := 2592) (k := 8 * S.n) (.inl (by decide)) (by decide)
      (by omega)
    rwa [BitVec.add_zero] at this
  have stkR' : stkR s = ⟨Bs s, 2624⟩ := rfl
  have bsub (r : Region) (hr : (stkR s).Disjoint r) : (⟨Bs s, 2592⟩ : Region).Disjoint r :=
    (by rw [stkR'] at hr; exact hr.sub_left (Region.sub_prefix (by decide)))
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.withRegions_mem, State.callEntry_sp, State.callEntry_mem, c0, c1, c2, c3, c4, c5, c6, c7,
      Nat.add_zero, sa0, sa1, sad0, hc.sp, hPsub, cx, hc.mem]
    refine ⟨by omega_arith, by have := h.hBn; omega_arith, trivial, trivial, pre.kd, pre.nd, pre.ad, pre.dt, pre.dx,
      (h.pre.bd.sub_left (stk_sub s 2592 (8 * S.n) (by omega))).symm,
      bsub _ pre.bk, bsub _ pre.bn, bsub _ pre.ba, bsub _ pre.bd, bsub _ pre.bt,
      fun r hr => bsub _ (pre.bx r hr), stkArg, pre.ok, pre.on, pre.oa, pre.od, pre.ot, pre.ox, pre.hR, h.cX⟩
  · have inRd {r : Region} (h' : r ∈ s.rd) : Covers [r] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_left _ (by rw [hc.rd]; exact h'))
    have hx : Covers (S.xR (ourX s S.n)) (c.rd ++ c.wr) := fun a k ⟨x, hx, hc'⟩ =>
      inRd (r := x) (by rw [pre.rd]; simp [hx]) a k ⟨x, List.mem_singleton_self _, hc'⟩
    have hfr : Covers [FR s] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hw' : Covers [dR s] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp))
    exact covers_append (covers_append (covers_append (covers_cons (inRd (r := kR s) (by rw [pre.rd]; simp))
      (covers_cons (inRd (r := nR s) (by rw [pre.rd]; simp))
      (covers_cons (inRd (r := aR s) (by rw [pre.rd]; simp)) (covers_cons (inRd (r := tR s) (by rw [pre.rd]; simp))
        covers_nil)))) hx) (covers_cons (covers_prefix hfr (by omega)) covers_nil))
      (covers_cons hw' covers_nil)
  · rw [hc.wr, pre.wr]
    exact covers_cons (covers_of_mem (by simp)) covers_nil

/-- The call's result, on the call's state. -/
theorem Ready.xres {S : Shape} {s c : State} (h : Lay S s) (hc : Ready S s c) : callRes (xS S s c) = res s := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  have sa0 := hc.stackArgs h (rdC S s) (wrC s) (i := 0) (by have := S.two_le; omega)
  have sa1 := hc.stackArgs h (rdC S s) (wrC s) (i := 1) (by have := S.two_le; omega)
  have hd : bytesAt (cMem S s) (Dst s) (L s) = bytesAt s.mem (Src s) (L s) := by
    have := Proof.AesGcm.bytesAt_writeBytes_self (eMem S s) (Dst s) (bytesAt s.mem (Src s) (L s))
      (by rw [Lay.hlen]; exact (s.gpr .x7).isLt)
    rwa [Lay.hlen] at this
  simp only [callRes, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, c4, c5,
    c6, c7, sa0, sa1, hc.mem]
  exact h.cRes Lay.frame_cMem' hd

/-- After the call. -/
structure Called (S : Shape) (s z : State) : Prop where
  fr : Frame [dR s, ⟨Bs s, 2592⟩] (cMem S s) z.mem
  ra : z.mem.read (P s + BitVec.ofNat 64 (8 * S.n)) 8 = s.gpr .x30
  out : match res s with
    | some pt => (z.gpr .x0).setWidth 32 = 1 ∧ bytesAt z.mem (Dst s) (L s) = pt
    | none => (z.gpr .x0).setWidth 32 = 0
  gpr : ∀ r ∈ preserved, r ≠ .x30 → z.gpr r = s.gpr r
  sp : z.sp = P s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem called_wp {S : Shape} (F : OpenFn S) {s c : State} (h : Lay S s) (hc : Ready S s c) :
    WP isa (.call F.fn.name F.fn.code) c (Called S s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  have hdep := F.depth
  have := S.le_three
  refine WP.callFV (name := F.fn.name) F.verified.1 (S.pre hcp) hcov hw
    (fun s' rd' wr' sp' fr' pres' presV' post' => ?_) (by omega_arith)
  have hpost := S.post post' (by simp only [State.withRegions_gpr, c1]; exact h.pre.hR)
  unfold callPost at hpost
  rw [hc.xres h] at hpost
  have hpres : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x6 ∧ r ∉ copyRegs ∧ r ≠ .x16 ∧ r ≠ .x17 := by decide
  -- What the call wrote: `dst` and the stack below our frame.
  have frc : Frame [dR s, ⟨Bs s, 2592⟩] (cMem S s) s'.mem := by
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
  have ra : s'.mem.read (P s + BitVec.ofNat 64 (8 * S.n)) 8 = s.gpr .x30 := by
    have e : c.mem.read (P s + BitVec.ofNat 64 (8 * S.n)) 8 = s.gpr .x30 := by
      rw [hc.mem, show P s = Bs s + BitVec.ofNat 64 2592 from rfl, Offset.add_ofNat_add_ofNat,
        h.cFrame _ (by omega)]
      exact h.argsRa (Nat.le_refl _)
    rw [← e]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [show P s + BitVec.ofNat 64 (8 * S.n) = Bs s + BitVec.ofNat 64 (2592 + 8 * S.n) by
        rw [show P s = Bs s + BitVec.ofNat 64 2592 from rfl, Offset.add_ofNat_add_ofNat]]
      exact h.pre.bd.symm.sub_right (stk_sub s _ 8 (by omega)) |>.symm
    · simp only [below, hc.sp, show P s = Bs s + BitVec.ofNat 64 2592 from rfl,
        add_ofNat_sub_ofNat _ (show 16 * F.fn.code.aarch64Depth ≤ 2592 by omega_arith),
        Offset.add_ofNat_add_ofNat]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega) (by have := h.hBn; omega_arith)
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

/-- `wipeArgs`: the stack arguments at `sp + 32` and `sp + 40` into `x9` and
`x10`, and zero into `x11`. -/
theorem wipeArgs_ok (a : State) (r₃₂ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 32) 8)
    (r₄₀ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 40) 8) :
    WP isa (.block [.ldrSp .x9 32, .ldrSp .x10 40, .movz .x .x11 0 0]) a fun e =>
      e.gpr .x9 = a.mem.read (a.sp + BitVec.ofNat 64 32) 8 ∧
      e.gpr .x10 = a.mem.read (a.sp + BitVec.ofNat 64 40) 8 ∧ e.gpr .x11 = 0 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.sp = a.sp ∧
      e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
      Option.map_some, BitVec.setWidth_eq, r₃₂, r₄₀, and_self, ite_true, Nat.reduceLT, Nat.reduceMod,
      Nat.reduceMul, Option.bind_some, gpr_write, mem_write, rd_write, wr_write, sp_write]; rfl, rfl⟩ fun e he => ?_
  subst he
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], fun r h₁ h₂ h₃ => by
    simp [State.write, h₁, h₂, h₃], rfl, rfl, rfl, rfl, rfl⟩

/-- Where the wipe leaves the state: what follows the call, with `dst`
as `toPost` has it. -/
structure Done (S : Shape) (s u : State) : Prop where
  post : toPost s u
  ra : u.mem.read (P s + BitVec.ofNat 64 (8 * S.n)) 8 = s.gpr .x30
  gpr : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r
  sp : u.sp = P s
  rd : u.rd = s.rd
  wr : u.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- A stack argument, after the call. -/
theorem Called.arg {S : Shape} {s z : State} (h : Lay S s) (hz : Called S s z) (i : Nat) (hi : i < 4) :
    z.mem.read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  have := S.two_le
  rw [← h.cArg i (by omega)]
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

theorem wipeArgs_wp {S : Shape} {s z : State} (h : Lay S s) (hz : Called S s z) :
    WP isa (.block (wipeArgs S.n)) z (WArgs s z) := by
  have pre := h.pre
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  have inA (d : Nat) (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 64) :
      InRegions (z.rd ++ z.wr) (z.sp + BitVec.ofNat 64 d) 8 := by
    rw [hz.sp, hP, Offset.add_ofNat_add_ofNat, hz.rd]
    exact h.inArg (2592 + d) (by omega_arith) (by omega_arith) _
  rw [wipeArgs_eq S.hn]
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
theorem wipe_wp {S : Shape} {s z : State} (h : Lay S s) (hz : Called S s z) (hres : res s = none) :
    WP isa (wipe S.n) z (Done S s) := by
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
    have := S.le_three
    rw [hP, Offset.add_ofNat_add_ofNat]
    exact (pre.bd.symm.sub_right (stk_sub s _ 8 (by omega))).symm
  · have hp' : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    have := hp' r hr
    rw [g' r this.1 this.2.1 this.2.2]; exact hz.gpr r hr h30

/-- After the call: `dst` zeroed if it failed. -/
theorem after_ok {S : Shape} {s z : State} (h : Lay S s) (hz : Called S s z) : WP isa (after S.n) z (Done S s) := by
  unfold after
  have hdone : res s ≠ none → Done S s z := fun hn => by
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
theorem ret_wp {S : Shape} {s u : State} (h : Lay S s) (hu : Done S s u) :
    WP isa (.block (ret S.n)) u fun z => abiPreserved s (freed 32 z) ∧ toPost s (freed 32 z) := by
  have hP : P s = Bs s + BitVec.ofNat 64 2592 := rfl
  have := S.le_three
  refine WP.mono (ldrSp_ok (t := .x30) (k := 8 * S.n) u ⟨by omega, by omega⟩ ?_)
    fun z ⟨x30z, gz, mz, spz, rdz, wrz, vz⟩ => ?_
  · rw [hu.sp, hu.rd, hu.wr, hP, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), contains_off _ (by omega) (by omega) (by omega)⟩
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

theorem openTo_wp {S : Shape} (F : OpenFn S) {s : State} (hs : ToPre S s) :
    WP isa (openTo S.n F.fn) s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  unfold openTo
  rw [frameBytes_eq S.hn]
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hs.w₁; omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (copied_wp h he) fun c hc => ?_)
  refine WP.seq (WP.mono (ready_wp h hc) fun r hr => ?_)
  refine WP.seq (WP.mono (called_wp F h hr) fun z hz => ?_)
  exact WP.seq (WP.mono (after_ok h hz) fun u hu => ret_wp h hu)

/-! ## The instances -/

/-- `vg_aes_gcm_open`'s contract with 2592 bytes of stack, as the call lays it out. -/
theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem openSpec_pre {s : State} (h : callPre 2 (fun _ => []) (fun _ _ _ => True) s) :
    (Proof.AesGcm.openRoundsContract AArch64.abi 2592).pre s := by
  sig_pre [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, AArch64.abi, AArch64.argRegs,
    stackArgs_two, List.append_eq, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, AArch64.abi, AArch64.argRegs, List.getD,
    List.range, List.range.loop]
  obtain ⟨w₁, w₂, rd, wr, kd, nd, ad, dt, -, da, bk, bn, ba, bd, bt, -, barg, ok, on, oa, od, ot, -, hR, -⟩ := h
  exact ⟨w₁, w₂, rd, wr, kd, nd, ad, dt, da, bk, bn, ba, bd, bt, barg, ok, on, oa, od, ot, hR⟩

theorem openSpec_post {s s' : State} (h : (Proof.AesGcm.openRoundsContract AArch64.abi 2592).post s s')
    (hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) : callPost s s' := by
  sig_post [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Proof.AesGcm.openRoundsPost, AArch64.abi,
    AArch64.argRegs, stackArgs_two, List.append_eq, List.range, List.range.loop] at h
  exact h hR

theorem openSpec_pub {s₁ s₂ : State} (h : callPub 2 s₁ s₂) :
    (Proof.AesGcm.openRoundsContract AArch64.abi 2592).pub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs,
    stackArgs_two, List.append_eq, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs,
    List.range, List.range.loop]
  obtain ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a⟩ := h
  exact ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a 0 (by decide), a 1 (by decide)⟩

/-- `vg_aes_gcm_open`: `tag` and `tag_len` on the stack, by
`Proof.AesGcm.openRoundsContract`. -/
def openShape : Shape where
  n := 2
  hn := .inl rfl
  xR _ := []
  X _ _ _ := True
  X_frame _ _ _ _ h := h
  C := Proof.AesGcm.openRoundsContract AArch64.abi 2592
  pre := openSpec_pre
  post := openSpec_post
  pub := openSpec_pub

/-- The powers' buffers `pw`. -/
def pwR (ps : List Addr) : List Region := ps.map fun p => ⟨p, 128⟩

/-- The powers of the key context's hash subkey at each `pw`. -/
def pwX (m : Mem) (ctx : Addr) (ps : List Addr) : Prop := ∀ p ∈ ps, Spec.Gcm.Powers8Repr m p (ctxH m ctx)

theorem pwX_frame {m m' : Mem} {ctx : Addr} {ps : List Addr} {rs : List Region} (hf : Frame rs m m')
    (hk : ∀ r ∈ rs, (⟨ctx, 256⟩ : Region).Disjoint r) (hx : ∀ x ∈ pwR ps, ∀ r ∈ rs, x.Disjoint r)
    (_ : ∀ x ∈ pwR ps, x.base.toNat + x.len ≤ 2 ^ 64) (h : pwX m ctx ps) : pwX m' ctx ps := by
  intro p hp
  rw [(Proof.AesGcm.ctx_frame hf hk (R := 10) (.inl rfl)).2]
  exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := ⟨p, 128⟩)
    (hx _ (List.mem_map_of_mem hp)) (show 128 ≤ 2 ^ 64 by decide) hi) (h p hp)

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem pwSpec_pre {s : State} (h : callPre 3 pwR pwX s) :
    (Proof.AesGcm.openWithPowersRoundsContract AArch64.abi 2592).pre s := by
  sig_pre [Proof.AesGcm.openWithPowersRoundsContract, Spec.Gcm.openWithPowersSig, Spec.Gcm.openWithPowersPre,
    Spec.Gcm.openSig, Spec.Gcm.withPowersParam, Spec.Gcm.openPre, AArch64.abi, AArch64.argRegs,
    stackArgs_three, List.append_eq, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openWithPowersRoundsContract, Spec.Gcm.openWithPowersSig, Spec.Gcm.openSig,
    Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs, List.getD, List.range, List.range.loop]
  simp only [callPre, callX, pwR, pwX, Nat.reduceSub, List.range_one, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, Nat.add_zero, List.cons_append, List.nil_append] at h
  obtain ⟨w₁, w₂, rd, wr, kd, nd, ad, dt, dp, da, bk, bn, ba, bd, bt, bp, barg, ok, on, oa, od, ot, op, hR, rep⟩ := h
  exact ⟨w₁, w₂, rd, wr, kd, nd, ad, dt, dp, da, bk, bn, ba, bd, bt, bp, barg, ok, on, oa, od, ot, op, hR, rep⟩

theorem pwSpec_post {s s' : State} (h : (Proof.AesGcm.openWithPowersRoundsContract AArch64.abi 2592).post s s')
    (hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) : callPost s s' := by
  sig_post [Proof.AesGcm.openWithPowersRoundsContract, Spec.Gcm.openWithPowersSig, Spec.Gcm.openSig,
    Spec.Gcm.withPowersParam, Proof.AesGcm.openWithPowersRoundsPost, Proof.AesGcm.openRoundsPost, AArch64.abi,
    AArch64.argRegs, stackArgs_three, List.append_eq, List.range, List.range.loop] at h
  exact h hR

theorem pwSpec_pub {s₁ s₂ : State} (h : callPub 3 s₁ s₂) :
    (Proof.AesGcm.openWithPowersRoundsContract AArch64.abi 2592).pub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openWithPowersRoundsContract, Spec.Gcm.openWithPowersSig, Spec.Gcm.openSig,
    Spec.Gcm.withPowersParam, Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs,
    stackArgs_three, List.append_eq, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openWithPowersRoundsContract, Spec.Gcm.openWithPowersSig, Spec.Gcm.openSig,
    Spec.Gcm.withPowersParam, Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, AArch64.abi, AArch64.argRegs,
    List.range, List.range.loop]
  obtain ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a⟩ := h
  exact ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a 0 (by decide), a 1 (by decide), a 2 (by decide)⟩

/-- `vg_aes_gcm_open_with_powers`: `tag`, `tag_len` and `pw` on the stack,
with the powers of the key context's hash subkey at `pw`, by
`Proof.AesGcm.openWithPowersRoundsContract`. -/
def pwShape : Shape where
  n := 3
  hn := .inr rfl
  xR := pwR
  X := pwX
  X_frame := pwX_frame
  C := Proof.AesGcm.openWithPowersRoundsContract AArch64.abi 2592
  pre := pwSpec_pre
  post := pwSpec_post
  pub := pwSpec_pub

end VG.Proof.AesGcm.AArch64.OpenTo
