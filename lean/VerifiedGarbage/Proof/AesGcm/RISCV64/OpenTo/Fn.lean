module

public import VerifiedGarbage.Impl.AesGcm.RISCV64.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesGcm.RISCV64.Gather.Fn
import VerifiedGarbage.Proof.Gather.RISCV64.Loop
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-!
# AES-GCM decryption out of place, by a copy, RISC-V: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against (`toK`), which the shared one implies
(`OpenTo/Verified.lean`), and its proof (`openTo_wp`). It calls
`vg_aes_gcm_open` in its frame (`openCode`) by its shared contract
(`Proof.AesGcm.openRoundsContract`, with 4640 bytes of stack, `OpenOk`).

With `Bs` the base of the 4672 bytes of stack below the stack pointer
(`sp = Bs + 4672`), the function allocates its frame of 32 bytes at
`Pf = Bs + 4640` (`WP.alloc`), keeps our return address in it at `Pf + 16`,
and lays out the call's two stack arguments at `Pf` and `Pf + 8`
(`entered_wp`). It copies the `len` bytes at `src` to `dst` (`copied_wp`,
`Gather.RISCV64.copySlice` by `copyLoop_adv`), loads `dst` for the call
(`ready_wp`), calls `vg_aes_gcm_open` on `dst` in place (`called_wp`), which
writes only `dst` and the stack below our frame, and zeroes `dst` if it
returned 0 (`after_wp`, `wipe_wp`); then it reloads our return address
(`ret_wp`). Every write is to `dst` or to the stack below `sp`. As on
PPC64LE (`Proof/AesGcm/PPC64LE/OpenTo/Fn.lean`), with the layout of
`vg_aes_gcm_seal_gather` (`Gather/Fn.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.RISCV64.OpenTo

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesGcm.RISCV64.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.AesGcm.RISCV64.Gather (covers_mem contains_pre)

/-! ## The arguments and the contract -/

section
variable (s : State)

/-- The arguments `(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3,
aad = a4, aad_len = a5, src = a6, len = a7, dst, dst_len, tag, tag_len)`,
the last four in memory. -/
abbrev C : Addr := s.gpr .a0
abbrev Rn : Nat := (s.gpr .a1).toNat
abbrev Nn : Addr := s.gpr .a2
abbrev NL : Nat := (s.gpr .a3).toNat
abbrev Ad : Addr := s.gpr .a4
abbrev AL : Nat := (s.gpr .a5).toNat
abbrev Src : Addr := s.gpr .a6
abbrev L : Nat := (s.gpr .a7).toNat
abbrev Dst : Addr := stackArg s 0
abbrev Tg : Addr := stackArg s 2
abbrev TL : Nat := (stackArg s 3).toNat

/-- The regions: the key context, the nonce, the additional data, the
ciphertext, the output, the tag, the stack arguments and the stack below
the stack pointer. -/
abbrev kR : Region := ⟨C s, 256⟩
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev sR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tR : Region := ⟨Tg s, TL s⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 4672, 4672⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (C s) (Rn s)) (ctxH s.mem (C s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-- What the proof of `vg_aes_gcm_open_to` needs: the layout of its shared
contract, with 4672 bytes of stack, `dst_len` its `len`. -/
structure ToPre (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  w₁ : 4672 ≤ s.sp.toNat
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
  ok : (C s).toNat + 256 ≤ 2 ^ 64
  on : (Nn s).toNat + NL s ≤ 2 ^ 64
  oa : (Ad s).toNat + AL s ≤ 2 ^ 64
  os : (Src s).toNat + L s ≤ 2 ^ 64
  od : (Dst s).toNat + L s ≤ 2 ^ 64
  ot : (Tg s).toNat + TL s ≤ 2 ^ 64
  hR : Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14
  dl : (stackArg s 1).toNat = L s
  ca : (C s).toNat % 8 = 0

/-- `openToRoundsPost`, for the rounds of `ToPre`, with the result in `a0`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
  | none => (s'.gpr .a0).setWidth 32 = 0 ∧ bytesAt s'.mem (Dst s) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak: whether it succeeds. -/
def toLeak (s : State) : List Nat :=
  if ¬(Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14) then [] else [if (res s).isSome = true then 1 else 0]

/-- What two runs agree on: the stack pointer, the arguments and the leak. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ toLeak s₁ = toLeak s₂ ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ ∀ i < 4, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_open_to`. -/
def toK : Contract isa where
  pre := ToPre
  post := toPost
  pub := toPub

/-! ## The function called -/

/-- The correctness of `vg_aes_gcm_open`, in its frame, by its shared contract. -/
abbrev OpenOk : Prop :=
  ∀ s, (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).pre s →
    ∃ t s', Exec isa openCode s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).post s s'

/-- The frame of `vg_aes_gcm_open` uses the 4640 bytes of stack its
contract reserves. -/
theorem open_sdepth : sdepth openCode = 4640 := by
  decide +kernel

/-- What a call of `vg_aes_gcm_open(ctx = a0, rounds = a1, nonce = a2,
nonce_len = a3, aad = a4, aad_len = a5, data = a6, len = a7, tag, tag_len)`
needs, `tag` and `tag_len` its stack arguments. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let arg : Region := ⟨stackArgAddr s 0, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 4640, 4640⟩
  s.rd = [ctx, nonce, aad, tag, arg] ∧ s.wr = [data] ∧
    ctx.Disjoint data ∧ nonce.Disjoint data ∧ aad.Disjoint data ∧ data.Disjoint tag ∧ data.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 4640 ≤ s.sp.toNat ∧
    s.sp.toNat + 16 ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧ (s.gpr .a0).toNat % 8 = 0

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

/-- The shared contract's precondition, from the layout the call gives. -/
theorem openSpec_pre {s : State} (h : callPre s) : (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃⟩ := h
  sig_pre [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, RISCV64.abi, RISCV64.argRegs,
    stackArgs_two, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, RISCV64.abi, RISCV64.argRegs,
    List.getD, stackArgs_two, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

/-- `vg_aes_gcm_open`'s result on the arguments of a call. -/
abbrev callRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxH s.mem (s.gpr .a0)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- Its postcondition, for rounds of 10, 12 or 14. -/
theorem openSpec_post {s s' : State} (h : (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).post s s')
    (hR : (s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) :
    match callRes s with
    | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat = pt
    | none => (s'.gpr .a0).setWidth 32 = 0 := by
  sig_post [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Proof.AesGcm.openRoundsPost, RISCV64.abi,
    RISCV64.argRegs, stackArgs_two, List.range, List.range.loop] at h
  have h' := h hR
  split
  · rename_i pt heq
    dsimp only [callRes] at heq
    rw [heq] at h'
    exact h'
  · rename_i heq
    dsimp only [callRes] at heq
    rw [heq] at h'
    exact h'.1

/-- The public data of a call: whether it succeeds. -/
def callLeak (s : State) : List Nat :=
  if ¬((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) then []
  else [if (callRes s).isSome = true then 1 else 0]

/-- Its public data, from the arguments and the leak. -/
theorem openSpec_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ callLeak s₁ = callLeak s₂ ∧
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
    s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
    s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1) :
    (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).pub s₁ s₂ := by
  obtain ⟨q, l, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, b₀, b₁⟩ := h
  sig_pub [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, RISCV64.abi, RISCV64.argRegs,
    stackArgs_two, List.range, List.range.loop]
  exact ⟨q, l, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, b₀, b₁⟩

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 4672 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 4672

/-- Our frame: the stack pointer in it, which is where the call's first
stack argument, `tag`, is. -/
abbrev Pf : Addr := Bs s + BitVec.ofNat 64 4640

/-- The doubleword at offset `a` of the frame. -/
abbrev fa (a : Nat) : Addr := Bs s + BitVec.ofNat 64 (4640 + a)

/-- Our stack argument `i`. -/
abbrev sa (i : Nat) : Addr := Bs s + BitVec.ofNat 64 (4672 + 8 * i)

/-- The frame. -/
abbrev FA : Region := ⟨Pf s, 32⟩

/-- The memory after the entry: our return address at `Pf + 16`, and `tag`
and `tag_len` at `Pf` and `Pf + 8`, for the call. -/
abbrev eMem0 : Mem := s.mem.writeW (fa s 16) (s.gpr .ra)

abbrev eMem1 : Mem := (eMem0 s).writeW (Pf s) (Tg s)

abbrev eMem : Mem := (eMem1 s).writeW (fa s 8) (stackArg s 3)

/-- The memory once the ciphertext is copied to `dst`. -/
abbrev cMem : Mem := writeBytes (eMem s) (Dst s) (bytesAt s.mem (Src s) (L s))

/-- The regions the call of `vg_aes_gcm_open` reads and writes: its stack
arguments are at `Pf`. -/
abbrev rdC : List Region := [kR s, nR s, aR s, tR s, ⟨Pf s, 16⟩]
abbrev wrC : List Region := [dR s]

end

/-- What `ToPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : ToPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 4672
  hBn : (Bs s).toNat + 4704 ≤ 2 ^ 64
  hargR : argR s = ⟨Bs s + BitVec.ofNat 64 4672, 32⟩

theorem lay {s : State} (hs : ToPre s) : Lay s := by
  have w₁ := hs.w₁
  have w₂ := hs.w₂
  have hB : s.sp = Bs s + BitVec.ofNat 64 4672 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 4704 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega_arith
  refine ⟨hs, hB, hBn, ?_⟩
  show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 32⟩ : Region) = ⟨Bs s + BitVec.ofNat 64 4672, 32⟩
  rw [← hB]; simp

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 4672) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 4672⟩ :=
  Offset.sub_base _ h'

theorem fa_in (s : State) {a : Nat} (ha : a + 8 ≤ 32) : (FA s).Contains (fa s a) 8 :=
  Offset.contains (Bs s) (by omega) (by omega) (by omega)

theorem pf_in (s : State) : (FA s).Contains (Pf s) 8 := contains_pre (by decide)

theorem frame_eMem0 (s : State) : Frame [FA s] s.mem (eMem0 s) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fa_in s (by decide))

theorem frame_eMem1 (s : State) : Frame [FA s] s.mem (eMem1 s) :=
  (frame_eMem0 s).writeW (List.mem_singleton_self _) _ (pf_in s)

theorem frame_eMem (s : State) : Frame [FA s] s.mem (eMem s) :=
  (frame_eMem1 s).writeW (List.mem_singleton_self _) _ (fa_in s (by decide))

/-- A doubleword of the stack, after a write to another. -/
theorem rd_sep (s : State) (m : Mem) (v : BitVec 64) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 4704)
    (hb : b + 8 ≤ 4704) :
    (m.writeW (Bs s + BitVec.ofNat 64 b) v).readW (Bs s + BitVec.ofNat 64 a) 64 =
      m.readW (Bs s + BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep (Bs s) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

/-- The words of the frame after the entry. -/
structure Slots (s : State) (m : Mem) : Prop where
  ra : m.readW (fa s 16) 64 = s.gpr .ra
  tg : m.readW (Pf s) 64 = Tg s
  tl : m.readW (fa s 8) 64 = stackArg s 3

theorem slots_eMem (s : State) : Slots s (eMem s) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := omega_arith) only [eMem, eMem1, eMem0, fa, Pf, rd_sep, Mem.readW_writeW_self64]

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem bs_toNat : (Bs s).toNat = s.sp.toNat - 4672 := by
  have e := congrArg BitVec.toNat h.hB
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
  have := h.hBn
  omega

theorem off_toNat {k : Nat} (hk : k < 4704) : (Bs s + BitVec.ofNat 64 k).toNat = (Bs s).toNat + k := by
  have := h.hBn
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem al8 {k : Nat} (hk : k < 4704) (h8 : k % 8 = 0) : (Bs s + BitVec.ofNat 64 k).toNat % 8 = 0 := by
  rw [h.off_toNat hk, h.bs_toNat]; have := h.pre.al; have := h.pre.w₁; omega

theorem pf_eq : s.sp - BitVec.ofNat 64 32 = Pf s := by
  rw [h.hB, Offset.add_ofNat_sub _ (by decide)]

theorem argIn : argR s ∈ s.rd := by rw [h.pre.rd]; simp

/-- Our stack argument `i`, from its address in our frame's terms. -/
theorem sa_eq {i : Nat} : stackArg s i = s.mem.readW (sa s i) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (8 * i)) 64 = _
  rw [h.hB, Offset.add_add]

theorem sa_in {i : Nat} (hi : i < 4) (u : State) (hrd : u.rd = s.rd) :
    InRegions (u.rd ++ u.wr) (sa s i) 8 :=
  ⟨_, List.mem_append_left _ (by rw [hrd]; exact h.argIn), by
    rw [h.hargR]
    exact Offset.contains (Bs s) (by omega_arith) (by omega_arith) (by have := h.hBn; omega_arith)⟩

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 4672⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 4640 32 (by decide) x hc)

/-- Our stack arguments are apart from the frame. -/
theorem sa_fa {i : Nat} (hi : i < 4) : ∀ r ∈ [FA s], (⟨sa s i, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (.inr (by omega_arith)) (by have := h.hBn; omega_arith)
    (by have := h.hBn; omega_arith)

/-- Our stack arguments, during and after the entry. -/
theorem e0Arg {i : Nat} (hi : i < 4) : (eMem0 s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem0 s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

theorem e1Arg {i : Nat} (hi : i < 4) : (eMem1 s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem1 s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

theorem eArg {i : Nat} (hi : i < 4) : (eMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

/-- The bytes at `src`, after the entry. -/
theorem srcE : bytesAt (eMem s) (Src s) (L s) = bytesAt s.mem (Src s) (L s) :=
  Proof.Cmac.bytesAt_frame (frame_eMem s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bs.symm.sub_right (stk_sub s 4640 32 (by decide))) (Nat.le_of_lt (s.gpr .a7).isLt)

omit h in
theorem hlen : (bytesAt s.mem (Src s) (L s)).length = L s := Proof.Cmac.bytesAt_length _ _ _

omit h in
theorem frame_cMem : Frame [dR s] (eMem s) (cMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Lay.hlen, Nat.le_refl]

/-- A doubleword of the stack below the stack pointer, once the ciphertext
is copied. -/
theorem cKeep {x : Addr} (hx : (⟨x, 8⟩ : Region).Sub ⟨Bs s, 4672⟩) :
    (cMem s).readW x 64 = (eMem s).readW x 64 :=
  Frame.readW Lay.frame_cMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.sub_left hx) (by decide)

theorem slots_cMem : Slots s (cMem s) := by
  have e := slots_eMem s
  exact ⟨(h.cKeep (stk_sub s _ _ (by decide))).trans e.ra, (h.cKeep (stk_sub s _ _ (by decide))).trans e.tg,
    (h.cKeep (stk_sub s _ _ (by decide))).trans e.tl⟩

/-- Our stack arguments are apart from `dst`. -/
theorem sa_dR {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Disjoint (dR s) := by
  have da := h.pre.da
  rw [h.hargR] at da
  exact da.symm.sub_left (Offset.sub _ (by omega_arith) (by omega_arith))

/-- Our stack arguments, once the ciphertext is copied. -/
theorem cArg {i : Nat} (hi : i < 4) : (cMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW Lay.frame_cMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.sa_dR hi) (by decide), h.eArg hi]

/-- `dst_len` is `len`. -/
theorem dstLen : stackArg s 1 = s.gpr .a7 := BitVec.eq_of_toNat_eq h.pre.dl

end Lay

/-! ## The phases -/

/-- The registers the entry and the copy write. -/
abbrev kregs : List Reg := [.t0, .t1, .t2, .a6]

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  t0 : e.gpr .t0 = Src s
  t1 : e.gpr .t1 = s.gpr .a7
  a6 : e.gpr .a6 = Dst s
  gpr : ∀ r, r ∉ kregs → e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FA s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocd 32 s) (Entered s) := by
  have asp : (allocd 32 s).sp = Pf s := h.pf_eq
  have awr : (allocd 32 s).wr = FA s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr : List Region) = _
    rw [h.pf_eq]
  have ag (r : Reg) : (allocd 32 s).gpr r = s.gpr r := rfl
  have ard : (allocd 32 s).rd = s.rd := rfl
  have amem : (allocd 32 s).mem = s.mem := rfl
  have fin {a : Nat} (ha : a + 8 ≤ 32) (u : State) (hw : u.wr = FA s :: s.wr) : InRegions u.wr (fa s a) 8 :=
    ⟨_, by rw [hw]; exact List.mem_cons_self .., fa_in s ha⟩
  unfold entry
  simp only [Impl.AesGcm.RISCV64.mov]
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .t0 = Pf s := by rw [v₁.gpr, asp, BitVec.add_zero]
  have w₁ : u₁.wr = FA s :: s.wr := by rw [v₁.wr, awr]
  refine wp_sd (a := fa s 16) (by decide) (by rw [p₁, Offset.add_add]) (h.al8 (by decide) (by decide))
    (fin (by decide) _ w₁) fun u₂ v₂ => ?_
  have m₂ : u₂.mem = eMem0 s := by rw [v₂.mem, v₁.other _ (by decide), v₁.mem, amem, ag]
  have p₂ : u₂.gpr .t0 = Pf s := by rw [v₂.gpr, p₁]
  have w₂ : u₂.wr = FA s :: s.wr := by rw [v₂.wr, w₁]
  have r₂ : u₂.rd = s.rd := by rw [v₂.rd, v₁.rd, ard]
  refine wp_ld (a := sa s 2) (by decide) (by rw [p₂, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ r₂) fun u₃ v₃ => ?_
  have t₃ : u₃.gpr .t1 = Tg s := by rw [v₃.gpr, m₂, h.e0Arg (by decide)]
  refine wp_sd (a := Pf s) (by decide) (by rw [v₃.other _ (by decide), p₂, BitVec.add_zero])
    (h.al8 (by decide) (by decide)) ⟨_, by rw [v₃.wr, w₂]; exact List.mem_cons_self .., pf_in s⟩
    fun u₄ v₄ => ?_
  have m₄ : u₄.mem = eMem1 s := by rw [v₄.mem, t₃, v₃.mem, m₂]
  have p₄ : u₄.gpr .t0 = Pf s := by rw [v₄.gpr, v₃.other _ (by decide), p₂]
  have w₄ : u₄.wr = FA s :: s.wr := by rw [v₄.wr, v₃.wr, w₂]
  have r₄ : u₄.rd = s.rd := by rw [v₄.rd, v₃.rd, r₂]
  refine wp_ld (a := sa s 3) (by decide) (by rw [p₄, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ r₄) fun u₅ v₅ => ?_
  have t₅ : u₅.gpr .t1 = stackArg s 3 := by rw [v₅.gpr, m₄, h.e1Arg (by decide)]
  refine wp_sd (a := fa s 8) (by decide) (by rw [v₅.other _ (by decide), p₄, Offset.add_add])
    (h.al8 (by decide) (by decide)) (fin (by decide) _ (by rw [v₅.wr, w₄])) fun u₆ v₆ => ?_
  have m₆ : u₆.mem = eMem s := by rw [v₆.mem, t₅, v₅.mem, m₄]
  have p₆ : u₆.gpr .t0 = Pf s := by rw [v₆.gpr, v₅.other _ (by decide), p₄]
  have r₆ : u₆.rd = s.rd := by rw [v₆.rd, v₅.rd, r₄]
  refine wp_ld (a := sa s 0) (by decide) (by rw [p₆, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ r₆) fun u₇ v₇ => ?_
  refine wp_mv fun u₈ v₈ => wp_mv fun u₉ v₉ => wp_mv fun u₁₀ v₁₀ => WP.block_nil ?_
  -- What the stores kept: every register but `t0` and `t1`.
  have g₆ (r : Reg) (h0 : r ≠ .t0) (h1 : r ≠ .t1) : u₆.gpr r = s.gpr r := by
    rw [v₆.gpr, v₅.other r h1, v₄.gpr, v₃.other r h1, v₂.gpr, v₁.other r h0, ag]
  refine ⟨by rw [v₁₀.mem, v₉.mem, v₈.mem, v₇.mem, m₆], ?_, ?_, ?_, fun r hr => ?_,
    by rw [v₁₀.sp, v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp],
    by rw [v₁₀.rd, v₉.rd, v₈.rd, v₇.rd, r₆],
    by rw [v₁₀.wr, v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, w₄]⟩
  · rw [v₁₀.other _ (by decide), v₉.other _ (by decide), v₈.gpr, v₇.other _ (by decide),
      g₆ _ (by decide) (by decide)]
  · rw [v₁₀.gpr, v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide),
      g₆ _ (by decide) (by decide)]
  · rw [v₁₀.other _ (by decide), v₉.gpr, v₈.other _ (by decide), v₇.gpr, m₆, h.eArg (by decide)]
  · simp only [kregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, -, h6⟩ := hr
    rw [v₁₀.other _ h1, v₉.other _ h6, v₈.other _ h0, v₇.other _ h1, g₆ r h0 h1]

/-- After the copy. -/
structure Copied (s c : State) : Prop where
  mem : c.mem = cMem s
  gpr : ∀ r, r ∉ kregs → c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FA s :: s.wr

theorem copied_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.Gather.RISCV64.copySlice e (Copied s) := by
  have hL : L s < 2 ^ 64 := (s.gpr .a7).isLt
  have ht1 : e.gpr .t1 = BitVec.ofNat 64 (L s) := by rw [he.t1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hk : ∀ r, r ∉ kregs → r ∉ [.t2, .t0, .a6, .t1] := fun r hr hm => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide)
  unfold Impl.Gather.RISCV64.copySlice
  refine WP.ite (decide (L s = 0)) (eval_zero_ofNat e .t1 hL ht1) (fun ht => ?_) (fun hf => ?_)
  · have h0 : L s = 0 := by simpa using ht
    refine WP.block_nil ⟨?_, he.gpr, he.sp, he.rd, he.wr⟩
    rw [he.mem, cMem, h0]
    simp [bytesAt, writeBytes_nil]
  · have h0 : L s ≠ 0 := by simpa using hf
    have hr : ∀ i < L s, InRegions (e.rd ++ e.wr) (e.gpr .t0 + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨sR s, List.mem_append_left _ (by rw [he.rd, h.pre.rd]; simp),
        by rw [he.t0]; exact Offset.contains_base _ (by omega) (by omega)⟩
    have hw : ∀ i < L s, InRegions e.wr (e.gpr .a6 + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨dR s, by rw [he.wr, h.pre.wr]; simp, by rw [he.a6]; exact Offset.contains_base _ (by omega) (by omega)⟩
    have hsep : Mem.Sep (e.gpr .a6) (L s) (e.gpr .t0) (L s) := fun x h₁ h₂ => by
      rw [he.a6] at h₁; rw [he.t0] at h₂
      exact h.pre.sd x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
    refine (WP.rdwr (copyLoop_adv (tmp := .t2) (src := .t0) (dst := .a6) (cnt := .t1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) e (Nat.pos_of_ne_zero h0) hL ht1 hr hw hsep)).mono
      fun c ⟨⟨c₂, f₂, k₂, _⟩, rd₂, wr₂, sp₂⟩ => ⟨?_, fun r hr => (k₂.gpr (hk r hr)).trans (he.gpr r hr),
        sp₂.trans he.sp, rd₂.trans he.rd, wr₂.trans he.wr⟩
    rw [he.a6, he.t0] at c₂; rw [he.a6] at f₂
    rw [Gather.RISCV64.mem_of_copy c₂ f₂, he.mem, h.srcE]

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = cMem s
  a6 : c.gpr .a6 = Dst s
  gpr : ∀ r, r ∉ kregs → c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FA s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Copied s g) : WP isa (.block callArgs) g (Ready s) := by
  unfold callArgs
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .t0 = Pf s := by rw [v₁.gpr, hg.sp, BitVec.add_zero]
  refine wp_ld (a := sa s 0) (by decide) (by rw [p₁, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ (by rw [v₁.rd, hg.rd])) fun u₂ v₂ => WP.block_nil ?_
  refine ⟨by rw [v₂.mem, v₁.mem, hg.mem], by rw [v₂.gpr, v₁.mem, hg.mem, h.cArg (by decide)], fun r hr => ?_,
    by rw [v₂.sp, v₁.sp, hg.sp], by rw [v₂.rd, v₁.rd, hg.rd], by rw [v₂.wr, v₁.wr, hg.wr]⟩
  simp only [kregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [v₂.other _ hr.2.2.2, v₁.other _ hr.1, hg.gpr r (by simp [kregs]; exact hr)]

section
variable (s : State)

/-- The call's state, with its permissions. -/
abbrev xS (c : State) : State := c.callEntry.withRegions (rdC s) (wrC s)

end

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    c'.gpr .a0 = C s ∧ c'.gpr .a1 = s.gpr .a1 ∧ c'.gpr .a2 = Nn s ∧ c'.gpr .a3 = s.gpr .a3 ∧
      c'.gpr .a4 = Ad s ∧ c'.gpr .a5 = s.gpr .a5 ∧ c'.gpr .a6 = Dst s ∧ c'.gpr .a7 = s.gpr .a7 := by
  simp only [State.withRegions_gpr]
  exact ⟨by rw [c.callEntry_gpr (by decide), hc.gpr _ (by decide)],
    by rw [c.callEntry_gpr (by decide), hc.gpr _ (by decide)],
    by rw [c.callEntry_gpr (by decide), hc.gpr _ (by decide)],
    by rw [c.callEntry_gpr (by decide), hc.gpr _ (by decide)],
    by rw [c.callEntry_gpr (by decide), hc.gpr _ (by decide)],
    by rw [c.callEntry_gpr (by decide), hc.gpr _ (by decide)],
    by rw [c.callEntry_gpr (by decide), hc.a6],
    by rw [c.callEntry_gpr (by decide), hc.gpr _ (by decide)]⟩

theorem pf_sub (s : State) : Pf s - BitVec.ofNat 64 4640 = Bs s := BitVec.add_sub_cancel _ _

/-- The call's stack arguments, in its own terms. -/
theorem Ready.argAddr {s c : State} (hc : Ready s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 0 = Pf s := by
  show c.sp + BitVec.ofNat 64 (8 * 0) = _
  rw [hc.sp, Nat.mul_zero, BitVec.add_zero]

theorem Ready.args {s c : State} (h : Lay s) (hc : Ready s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 0 = Tg s ∧
      stackArg ((c.callEntry).withRegions rd wr) 1 = stackArg s 3 := by
  have sl := h.slots_cMem
  constructor
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [hc.sp, hc.mem, Nat.mul_zero, BitVec.add_zero]; exact sl.tg
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [hc.sp, hc.mem, Offset.add_add]; exact sl.tl

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre (xS s c) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have pre := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1⟩ := hc.args h (rdC s) (wrC s)
  have hBn := h.hBn
  have hb := h.bs_toNat
  have hP := h.off_toNat (k := 4640) (by decide)
  have aS : (⟨Pf s, 16⟩ : Region).Sub ⟨Bs s, 4672⟩ := stk_sub s 4640 16 (by decide)
  have al := pre.al
  have w₁ := pre.w₁
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c3, c4, c5, c6, c7, c8, c9, c10, a0, a1, hc.sp, pf_sub, hc.argAddr]
    refine ⟨trivial, trivial, pre.kd, pre.nd, pre.ad, pre.dt, pre.bd.symm.sub_right aS,
      pre.bk.sub_left (Region.sub_prefix (by decide)), pre.bn.sub_left (Region.sub_prefix (by decide)),
      pre.ba.sub_left (Region.sub_prefix (by decide)), pre.bd.sub_left (Region.sub_prefix (by decide)),
      pre.bt.sub_left (Region.sub_prefix (by decide)), (Offset.disjoint_base _ (by decide) (by omega_arith)).symm,
      pre.ok, pre.on, pre.oa, pre.od, pre.ot, by rw [hP]; omega_arith, by rw [hP]; omega_arith,
      by rw [hP]; omega_arith, pre.hR, pre.ca⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨FA s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 0,
        (BitVec.add_zero _).symm, by show 0 + 16 ≤ 32; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
  · refine covers_mem fun r hr => ?_
    rw [hc.wr, pre.wr]
    exact List.mem_cons_of_mem _ hr

/-- The call's result, on the call's state. -/
theorem Ready.xres {s c : State} (h : Lay s) (hc : Ready s c) : callRes (xS s c) = res s := by
  have pre := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1⟩ := hc.args h (rdC s) (wrC s)
  have hm : (xS s c).mem = cMem s := by
    simp only [State.withRegions_mem, State.callEntry_mem, hc.mem]
  have hfc : Frame [FA s, dR s] s.mem (cMem s) :=
    ((frame_eMem s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      (Lay.frame_cMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
  have apart {r : Region} (h₁ : (⟨Bs s, 4672⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FA s, dR s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h₁.symm.sub_right (stk_sub s 4640 32 (by decide))
    · exact h₂
  obtain ⟨hc', hh⟩ := Proof.AesGcm.ctx_frame hfc (apart pre.bk pre.kd) pre.hR
  have hn : bytesAt (cMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bn pre.nd) (Nat.le_of_lt (s.gpr .a3).isLt)
  have ha : bytesAt (cMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.ba pre.ad) (Nat.le_of_lt (s.gpr .a5).isLt)
  have ht : bytesAt (cMem s) (Tg s) (TL s) = bytesAt s.mem (Tg s) (TL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bt pre.dt.symm) (Nat.le_of_lt (stackArg s 3).isLt)
  have hd : bytesAt (cMem s) (Dst s) (L s) = bytesAt s.mem (Src s) (L s) := by
    have := Proof.AesGcm.bytesAt_writeBytes_self (eMem s) (Dst s) (bytesAt s.mem (Src s) (L s))
      (by rw [Lay.hlen]; exact (s.gpr .a7).isLt)
    rwa [Lay.hlen] at this
  simp only [callRes, hm, c3, c4, c5, c6, c7, c8, c9, c10, a0, a1]
  rw [hc', hh, hn, hd, ha, ht]

/-- What the call leaves of `dst` and `a0`: `vg_aes_gcm_open`'s result. -/
def Out (s : State) (e : BitVec 64) (m : Mem) : Prop :=
  match res s with
  | some pt => e.setWidth 32 = 1 ∧ bytesAt m (Dst s) (L s) = pt
  | none => e.setWidth 32 = 0

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.readW (fa s 16) 64 = s.gpr .ra
  a0 : z.mem.readW (sa s 0) 64 = Dst s
  a1 : z.mem.readW (sa s 1) 64 = stackArg s 1
  out : Out s (z.gpr .a0) z.mem
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FA s :: s.wr

theorem called_wp (hv : OpenOk) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call "vg_aes_gcm_open" openCode) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr (rdC s) (wrC s)
  refine WP.callAny (k := Proof.AesGcm.openRoundsContract RISCV64.abi 4640) hv (openSpec_pre hcp) hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [open_sdepth]; decide)
  have hpost := openSpec_post post' (by simp only [State.withRegions_gpr] at c4 ⊢; rw [c4]; exact h.pre.hR)
  rw [hc.xres h] at hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, c9, c10] at hpost
  -- What the call kept: our frame and our arguments.
  have hBn := h.hBn
  have kept {a : Addr} (hd : (⟨a, 8⟩ : Region).Disjoint (dR s))
      (hb : (⟨a, 8⟩ : Region).Disjoint (below c.sp (sdepth openCode))) :
      z.mem.readW a 64 = c.mem.readW a 64 := by
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hb
  have hbl {a : Nat} (ha : a + 8 ≤ 4704) (ha' : 4640 ≤ a) :
      (⟨Bs s + BitVec.ofNat 64 a, 8⟩ : Region).Disjoint (below c.sp (sdepth openCode)) := by
    simp only [below, hc.sp, open_sdepth, pf_sub]
    exact Offset.disjoint_base _ ha' (by omega_arith)
  have ra : z.mem.readW (fa s 16) 64 = s.gpr .ra := by
    rw [kept (h.pre.bd.sub_left (stk_sub s _ _ (by decide))) (hbl (by decide) (by decide)), hc.mem,
      h.slots_cMem.ra]
  have a0 : z.mem.readW (sa s 0) 64 = Dst s := by
    rw [kept (h.sa_dR (by decide)) (hbl (by decide) (by decide)), hc.mem, h.cArg (by decide)]
  have a1 : z.mem.readW (sa s 1) 64 = stackArg s 1 := by
    rw [kept (h.sa_dR (by decide)) (hbl (by decide) (by decide)), hc.mem, h.cArg (by decide)]
  have hpres : ∀ r ∈ preserved, r ∉ kregs := by decide
  refine ⟨ra, a0, a1, ?_, fun r hr => by rw [pres' r hr, hc.gpr r (hpres r hr)], sp'.trans hc.sp,
    rd'.trans hc.rd, wr'.trans hc.wr⟩
  unfold Out
  revert hpost
  cases res s with
  | some pt => intro hp; exact hp
  | none => intro hp; exact hp

/-! ## After the call -/

/-- `addiw d, n, 0`: the low word of `n`, sign-extended. -/
theorem wp_addiw0 {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg}
    (k : ∀ s', Upd s s' d (sext32 ((s.gpr n).setWidth 32 + BitVec.ofInt 32 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.addiw d n 0 :: is)) s Q :=
  WP.cons (exec_addiw (by unfold imm12; omega)) (k _ (Upd.write _ _ _))

/-- After `test`: what the call left, with the branch's condition on whether
it succeeded. -/
theorem tested_wp {s z : State} (hz : Called s z) :
    WP isa (.block test) z fun y => Called s y ∧ isa.eval (.zero .t0) y = some (res s).isNone := by
  unfold test
  refine wp_addiw0 fun y v => WP.block_nil ⟨?_, ?_⟩
  · have hpres : ∀ r ∈ preserved, r ≠ .t0 := by decide
    exact ⟨by rw [v.mem]; exact hz.ra, by rw [v.mem]; exact hz.a0, by rw [v.mem]; exact hz.a1,
      by rw [v.other _ (by decide), v.mem]; exact hz.out, fun r hr => by rw [v.other _ (hpres r hr), hz.pres r hr],
      by rw [v.sp, hz.sp], by rw [v.rd, hz.rd], by rw [v.wr, hz.wr]⟩
  · rw [eval_zero, v.gpr]
    have o := hz.out
    unfold Out at o
    revert o
    cases res s with
    | some pt => intro o; rw [o.1]; rfl
    | none => intro o; rw [o]; rfl

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `t2 = D`, `t3 = n` and
`t1 = 0`. -/
theorem wipeLoop_wp (u : State) {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (h₂ : u.gpr .t2 = D) (h₃ : u.gpr .t3 = BitVec.ofNat 64 n) (h₁ : u.gpr .t1 = 0)
    (hw : Covers [⟨D, n⟩] u.wr) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem D n ∧ Frame [⟨D, n⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp := by
  unfold wipeLoop
  refine WP.ite (decide (n = 0)) (eval_zero_ofNat u .t3 hn h₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl,
      rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .t2 = D + BitVec.ofNat 64 i ∧
        v.gpr .t3 = BitVec.ofNat 64 (n - i) ∧ (∀ r, r ≠ .t2 → r ≠ .t3 → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp ∧ Frame [⟨D, n⟩] u.mem v.mem ∧
        Proof.Zeroize.Prefix v.mem D i) ?_ (n - 0) _
      ⟨0, rfl, by omega, by rw [h₂]; exact (BitVec.add_zero _).symm, by rw [h₃, Nat.sub_zero],
        fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, r2, r3, gv, rdv, wrv, spv, fv, pv⟩
    have hcn : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    refine wp_sb (off := 0) (a := D + BitVec.ofNat 64 i) (by decide) (by rw [r2]; exact BitVec.add_zero _)
      (by rw [wrv]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩) fun t₁ u₁ => ?_
    refine wp_addi (imm := 1) (by decide) fun t₂ u₂ => wp_subi (imm := 1) (by decide) fun t₃ u₃ =>
      WP.block_nil ?_
    have z₁ : (v.gpr .t1).setWidth 8 = (0 : BitVec 8) := by rw [gv _ (by decide) (by decide), h₁]; rfl
    have m₃ : t₃.mem = v.mem.writeW (D + BitVec.ofNat 64 i) (0 : BitVec 8) := by
      rw [u₃.mem, u₂.mem, u₁.mem, z₁]
    have f' : Frame [⟨D, n⟩] u.mem t₃.mem := by
      rw [m₃]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    have p' : Proof.Zeroize.Prefix t₃.mem D (i + 1) := by
      rw [m₃]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega)
    have g' : ∀ r, r ≠ .t2 → r ≠ .t3 → t₃.gpr r = u.gpr r := fun r a b => by
      rw [u₃.other _ b, u₂.other _ a, u₁.gpr, gv r a b]
    have r2' : t₃.gpr .t2 = D + BitVec.ofNat 64 (i + 1) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, r2, Offset.add_add]
    have r3' : t₃.gpr .t3 = BitVec.ofNat 64 (n - (i + 1)) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, r3, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    have rd' : t₃.rd = u.rd := by rw [u₃.rd, u₂.rd, u₁.rd, rdv]
    have wr' : t₃.wr = u.wr := by rw [u₃.wr, u₂.wr, u₁.wr, wrv]
    have sp' : t₃.sp = u.sp := by rw [u₃.sp, u₂.sp, u₁.sp, spv]
    have ev := eval_nonzero_ofNat t₃ .t3 (k := n - (i + 1)) (by omega) r3'
    by_cases he : i + 1 = n
    · left
      exact ⟨by rw [ev]; simp [he], by rw [← he]; exact p', f', g', rd', wr', sp'⟩
    · right
      exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, r2', r3', g', rd', wr', sp',
        f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- After `wipeArgs`: `dst` in `t2`, `len` in `t3` and zero in `t1`. -/
structure WArgs (s z a : State) : Prop where
  t2 : a.gpr .t2 = Dst s
  t3 : a.gpr .t3 = BitVec.ofNat 64 (L s)
  t1 : a.gpr .t1 = 0
  gpr : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → a.gpr r = z.gpr r
  mem : a.mem = z.mem
  sp : a.sp = z.sp
  rd : a.rd = z.rd
  wr : a.wr = z.wr

theorem wipeArgs_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa (.block wipeArgs) z (WArgs s z) := by
  unfold wipeArgs
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .t0 = Pf s := by rw [v₁.gpr, hz.sp, BitVec.add_zero]
  refine wp_ld (a := sa s 0) (by decide) (by rw [p₁, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ (by rw [v₁.rd, hz.rd])) fun u₂ v₂ => ?_
  refine wp_ld (a := sa s 1) (by decide) (by rw [v₂.other _ (by decide), p₁, Offset.add_add])
    (h.al8 (by decide) (by decide)) (h.sa_in (by decide) _ (by rw [v₂.rd, v₁.rd, hz.rd])) fun u₃ v₃ => ?_
  refine wp_li (imm := 0) (by decide) fun u₄ v₄ => WP.block_nil ?_
  refine ⟨?_, ?_, v₄.gpr, fun r h0 h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, hz.a0]
  · rw [v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, hz.a1, h.dstLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [v₄.other _ h1, v₃.other _ h3, v₂.other _ h2, v₁.other _ h0]
  · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  · rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp]
  · rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]

/-- Where `after` leaves the state: what follows the call, with `dst` and
`a0` as `toPost` has them. -/
structure Done (s u : State) : Prop where
  post : toPost s u
  ra : u.mem.readW (fa s 16) 64 = s.gpr .ra
  pres : ∀ r ∈ preserved, u.gpr r = s.gpr r
  sp : u.sp = Pf s
  rd : u.rd = s.rd
  wr : u.wr = FA s :: s.wr

/-- When the call failed: `dst` zeroed. -/
theorem wipe_wp {s z : State} (h : Lay s) (hz : Called s z) (hres : res s = none) : WP isa wipe z (Done s) := by
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun a ha => ?_)
  have hw : Covers [⟨Dst s, L s⟩] a.wr := by
    rw [ha.wr, hz.wr, h.pre.wr]; exact covers_mem fun r hr => by simp at hr; subst hr; simp
  refine WP.mono (wipeLoop_wp a (s.gpr .a7).isLt h.pre.od ha.t2 ha.t3 ha.t1 hw)
    fun u ⟨pz, fu, gu, rdu, wru, spu⟩ => ?_
  have g' : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → u.gpr r = z.gpr r := fun r a b c d => by
    rw [gu r c d, ha.gpr r a b c d]
  have keep : u.mem.readW (fa s 16) 64 = z.mem.readW (fa s 16) 64 := by
    rw [← ha.mem]
    refine fu.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.sub_left (stk_sub s _ _ (by decide))
  have hpres : ∀ r ∈ preserved, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 := by decide
  have o := hz.out
  unfold Out at o
  rw [hres] at o
  refine ⟨?_, keep.trans hz.ra, fun r hr => ?_, spu.trans (ha.sp.trans hz.sp), by rw [rdu, ha.rd, hz.rd],
    by rw [wru, ha.wr, hz.wr]⟩
  · unfold toPost
    rw [hres]
    exact ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide)]; exact o, bytesAt_zeros pz⟩
  · obtain ⟨a₁, a₂, a₃, a₄⟩ := hpres r hr
    rw [g' r a₁ a₂ a₃ a₄]; exact hz.pres r hr

/-- After the call: `dst` zeroed if it failed. -/
theorem after_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa after z (Done s) := by
  unfold after
  refine WP.seq (WP.mono (tested_wp hz) fun y ⟨hy, ev⟩ => ?_)
  have o := hy.out
  unfold Out at o
  cases hr : res s with
  | none =>
    rw [hr] at ev
    exact WP.ite true ev (fun _ => wipe_wp h hy hr) (fun h' => absurd h' (by decide))
  | some pt =>
    rw [hr] at o ev
    refine WP.ite false ev (fun h' => absurd h' (by decide))
      (fun _ => WP.block_nil ⟨?_, hy.ra, hy.pres, hy.sp, hy.rd, hy.wr⟩)
    unfold toPost
    rw [hr]
    exact o

theorem toPost_congr {s u t : State} (hm : t.mem = u.mem) (hg : t.gpr .a0 = u.gpr .a0) (h : toPost s u) :
    toPost s t := by
  unfold toPost at h ⊢
  rw [hm, hg]
  exact h

/-- The return address back from the frame, and the frame freed. -/
theorem ret_wp {s u : State} (h : Lay s) (hu : Done s u) :
    WP isa (.block Impl.AesGcm.RISCV64.OpenTo.ret) u fun y => abiPreserved s (freed 32 y) ∧ toPost s (freed 32 y) := by
  unfold Impl.AesGcm.RISCV64.OpenTo.ret
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .t0 = Pf s := by rw [v₁.gpr, hu.sp, BitVec.add_zero]
  refine wp_ld (a := fa s 16) (by decide) (by rw [p₁, Offset.add_add]) (h.al8 (by decide) (by decide))
    ⟨FA s, List.mem_append_right _ (by rw [v₁.wr, hu.wr]; exact List.mem_cons_self ..), fa_in s (by decide)⟩
    fun u₂ v₂ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · -- The callee-saved registers.
    have hpres : ∀ r ∈ preserved, r ≠ .ra ∧ r ≠ .t0 := by decide
    show u₂.gpr r = s.gpr r
    rw [v₂.other _ (hpres r hr).1, v₁.other _ (hpres r hr).2, hu.pres r hr]
  · -- The stack pointer.
    show u₂.sp + BitVec.ofNat 64 32 = s.sp
    rw [v₂.sp, v₁.sp, hu.sp, Offset.add_add, h.hB]
  · -- The return address.
    show u₂.gpr .ra = s.gpr .ra
    rw [v₂.gpr, v₁.mem, hu.ra]
  · -- The result and the plaintext.
    refine toPost_congr (u := u) ?_ ?_ hu.post
    · show u₂.mem = u.mem
      rw [v₂.mem, v₁.mem]
    · show u₂.gpr .a0 = u.gpr .a0
      rw [v₂.other _ (by decide), v₁.other _ (by decide)]

theorem openTo_wp (hv : OpenOk) {s : State} (hs : ToPre s) :
    WP isa openTo s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  have w₁ := hs.w₁
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (copied_wp h he) fun c hc => ?_)
  refine WP.seq (WP.mono (ready_wp h hc) fun r hr => ?_)
  refine WP.seq (WP.mono (called_wp hv h hr) fun z hz => ?_)
  refine WP.seq (WP.mono (after_wp h hz) fun u hu => ?_)
  exact ret_wp h hu

end VG.Proof.AesGcm.RISCV64.OpenTo
