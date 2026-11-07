module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM decryption out of place, by a copy, PPC64LE: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against (`toK`), which the shared one implies
(`OpenTo/Verified.lean`), and its proof (`openTo_wp`). It calls
`vg_aes_gcm_open` in its frame of 2688 bytes (`openCode`) by its shared
contract (`Proof.AesGcm.openRoundsContract`, `OpenOk`).

With `Bs` the base of the 2848 bytes of stack below the stack pointer
(`sp = Bs + 2848`), the function allocates its frame of 160 bytes at
`Pf = Bs + 2688` (`WP.alloc`), keeps `ctx`, `rounds`, `nonce`, `nonce_len`
and our return address in it, and lays out the call's two stack arguments
(`entered_wp`). It copies the `len` bytes at `src` to `dst` (`copied_wp`, by
`Gather.PPC64LE.copySlice_wp`), reloads the arguments (`ready_wp`), calls
`vg_aes_gcm_open` on `dst` in place (`called_wp`), which writes only `dst`
and the stack below our frame, and zeroes `dst` if it returned 0
(`after_wp`, `wipe_wp`); then it reloads our return address (`ret_wp`).
Every write is to `dst` or to the stack below `sp`. As for
`vg_aes_gcm_seal_gather` (`Gather/Fn.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.PPC64LE.OpenTo

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.Gather.PPC64LE (SlicePre Keeps copySlice_wp copyRegs eval_zero eval_nonzero ofNat_sub_one)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd LrUpd wp_std wp_ld wp_mflr wp_mtlr wp_stb wp_addi wp_subi wp_li)

/-! ## The arguments and the contract -/

section
variable (s : State)

/-- The arguments `(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, src = r9, len = r10, dst, dst_len, tag, tag_len)`,
the last four in memory. -/
abbrev C : Addr := s.gpr .r3
abbrev Rn : Nat := (s.gpr .r4).toNat
abbrev Nn : Addr := s.gpr .r5
abbrev NL : Nat := (s.gpr .r6).toNat
abbrev Ad : Addr := s.gpr .r7
abbrev AL : Nat := (s.gpr .r8).toNat
abbrev Src : Addr := s.gpr .r9
abbrev L : Nat := (s.gpr .r10).toNat
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
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 2848, 2848⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (C s) (Rn s)) (ctxH s.mem (C s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-- What the proof of `vg_aes_gcm_open_to` needs: the layout of its shared
contract, with 2848 bytes of stack, `dst_len` its `len`. -/
structure ToPre (s : State) : Prop where
  w₁ : 2848 ≤ s.sp.toNat
  w₂ : s.sp.toNat + 32 + 96 ≤ 2 ^ 64
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

/-- `openToRoundsPost`, for the rounds of `ToPre`, with the result in `r3`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (Dst s) (L s) = pt
  | none => (s'.gpr .r3).setWidth 32 = 0 ∧ bytesAt s'.mem (Dst s) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak: whether it succeeds. -/
def toLeak (s : State) : List Nat :=
  if ¬(Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14) then [] else [if (res s).isSome = true then 1 else 0]

/-- What two runs agree on: the stack pointer, the arguments and the leak. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ toLeak s₁ = toLeak s₂ ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ ∀ i < 4, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_gcm_open_to`. -/
def toK : Contract isa where
  pre := ToPre
  post := toPost
  pub := toPub

/-! ## The function called -/

/-- The correctness of `vg_aes_gcm_open`, in its frame, by its shared contract. -/
abbrev OpenOk : Prop :=
  ∀ s, (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).pre s →
    ∃ t s', Exec isa openCode s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).post s s'

/-- The frame of `vg_aes_gcm_open` uses the 2688 bytes of stack its
contract reserves. -/
theorem open_sdepth : sdepth openCode = 2688 := by
  decide +kernel

/-- What a call of `vg_aes_gcm_open(ctx = r3, rounds = r4, nonce = r5,
nonce_len = r6, aad = r7, aad_len = r8, data = r9, len = r10, tag, tag_len)`
needs, `tag` and `tag_len` its stack arguments. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let arg : Region := ⟨stackArgAddr s 0, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 2688, 2688⟩
  s.rd = [ctx, nonce, aad, tag, arg] ∧ s.wr = [data] ∧
    ctx.Disjoint data ∧ nonce.Disjoint data ∧ aad.Disjoint data ∧ data.Disjoint tag ∧ data.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ 2688 ≤ s.sp.toNat ∧ s.sp.toNat + 112 ≤ 2 ^ 64 ∧
    ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

/-- The shared contract's precondition, from the layout the call gives. -/
theorem openSpec_pre {s : State} (h : callPre s) : (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁⟩ := h
  sig_pre [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, PPC64LE.abi, PPC64LE.argRegs,
    stackArgs_two, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, PPC64LE.abi, PPC64LE.argRegs,
    List.getD, stackArgs_two, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

/-- `vg_aes_gcm_open`'s result on the arguments of a call. -/
abbrev callRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxH s.mem (s.gpr .r3)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
    (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- Its postcondition, for rounds of 10, 12 or 14. -/
theorem openSpec_post {s s' : State} (h : (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).post s s')
    (hR : (s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14) :
    match callRes s with
    | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat = pt
    | none => (s'.gpr .r3).setWidth 32 = 0 := by
  sig_post [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Proof.AesGcm.openRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_two, List.range, List.range.loop] at h
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
  if ¬((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14) then []
  else [if (callRes s).isSome = true then 1 else 0]

/-- Its public data, from the arguments and the leak. -/
theorem openSpec_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ callLeak s₁ = callLeak s₂ ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧
    s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1) :
    (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).pub s₁ s₂ := by
  obtain ⟨q, l, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, b₀, b₁⟩ := h
  sig_pub [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, PPC64LE.abi, PPC64LE.argRegs,
    stackArgs_two, List.range, List.range.loop]
  exact ⟨q, l, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, b₀, b₁⟩

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 2848 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 2848

/-- Our frame: the stack pointer in it. -/
abbrev Pf : Addr := Bs s + BitVec.ofNat 64 2688

/-- The doubleword at offset `a` of the frame. -/
abbrev fa (a : Nat) : Addr := Pf s + BitVec.ofNat 64 a

/-- Our stack argument `i`. -/
abbrev sa (i : Nat) : Addr := Pf s + BitVec.ofNat 64 (256 + 8 * i)

/-- The frame past its header, which the frame makes writable, and the whole
frame. -/
abbrev FR : Region := ⟨Pf s + BitVec.ofNat 64 32, 128⟩
abbrev FA : Region := ⟨Pf s, 160⟩

/-- The memory after the entry: the back chain at `Pf`, `ctx`, `rounds`,
`nonce` and `nonce_len` at `Pf + 112` … `Pf + 136`, our return address at
`Pf + 152`, and `tag` and `tag_len` at `Pf + 96` and `Pf + 104`, for the
call. -/
abbrev eMem0 : Mem :=
  (((((s.mem.write (Pf s) 8 s.sp).writeW (fa s 112) (s.gpr .r3)).writeW (fa s 120) (s.gpr .r4)).writeW
    (fa s 128) (s.gpr .r5)).writeW (fa s 136) (s.gpr .r6)).writeW (fa s 152) s.lr

abbrev eMem1 : Mem := (eMem0 s).writeW (fa s 96) (Tg s)

abbrev eMem : Mem := (eMem1 s).writeW (fa s 104) (stackArg s 3)

/-- The memory once the ciphertext is copied to `dst`. -/
abbrev cMem : Mem := writeBytes (eMem s) (Dst s) (bytesAt s.mem (Src s) (L s))

/-- The regions the call of `vg_aes_gcm_open` reads and writes: its stack
arguments are at `Pf + 96`. -/
abbrev rdC : List Region := [kR s, nR s, aR s, tR s, ⟨fa s 96, 16⟩]
abbrev wrC : List Region := [dR s]

end

/-- What `ToPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : ToPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 2848
  hBn : (Bs s).toNat + 2976 ≤ 2 ^ 64
  hargR : argR s = ⟨Pf s + BitVec.ofNat 64 256, 32⟩

theorem lay {s : State} (hs : ToPre s) : Lay s := by
  have w₁ := hs.w₁
  have w₂ := hs.w₂
  have hB : s.sp = Bs s + BitVec.ofNat 64 2848 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 2976 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega_arith
  refine ⟨hs, hB, hBn, ?_⟩
  show (⟨s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)), 32⟩ : Region) =
    ⟨Bs s + BitVec.ofNat 64 2688 + BitVec.ofNat 64 256, 32⟩
  rw [hB, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2848) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2848⟩ :=
  Offset.sub_base _ h'

theorem pf_off (s : State) (a : Nat) : Pf s + BitVec.ofNat 64 a = Bs s + BitVec.ofNat 64 (2688 + a) :=
  Offset.add_ofNat_add_ofNat _ _ _

/-- Bytes of the frame, in the stack below the stack pointer. -/
theorem fr_sub (s : State) {a n : Nat} (ha : a + n ≤ 160) :
    (⟨Pf s + BitVec.ofNat 64 a, n⟩ : Region).Sub ⟨Bs s, 2848⟩ := by
  rw [pf_off]; exact stk_sub s _ _ (by omega_arith)

theorem fr_in (s : State) {a : Nat} (h₁ : 32 ≤ a) (h₂ : a + 8 ≤ 160) (wr : List Region) :
    InRegions (FR s :: wr) (Pf s + BitVec.ofNat 64 a) 8 :=
  ⟨_, List.mem_cons_self .., by
    show (⟨Pf s + BitVec.ofNat 64 32, 128⟩ : Region).Contains (Pf s + BitVec.ofNat 64 a) 8
    rw [show a = 32 + (a - 32) by omega_arith, ← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A doubleword of the frame, after a write to another. -/
theorem rd_sep (s : State) (m : Mem) (v : BitVec 64) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 160)
    (hb : b + 8 ≤ 160) :
    (m.writeW (Pf s + BitVec.ofNat 64 b) v).readW (Pf s + BitVec.ofNat 64 a) 64 =
      m.readW (Pf s + BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep (Pf s) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem fa_in (s : State) {a : Nat} (ha : a + 8 ≤ 160) : (FA s).Contains (Pf s + BitVec.ofNat 64 a) (64 / 8) :=
  Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem frame_eMem0 (s : State) : Frame [FA s] s.mem (eMem0 s) := by
  have m := List.mem_singleton_self (FA s)
  exact (((((Frame.refl _ _).write m _ (Region.contains_self' (by decide))).writeW m _
    (fa_in s (by decide))).writeW m _ (fa_in s (by decide))).writeW m _ (fa_in s (by decide))).writeW m _
    (fa_in s (by decide)) |>.writeW m _ (fa_in s (by decide))

theorem frame_eMem1 (s : State) : Frame [FA s] s.mem (eMem1 s) :=
  (frame_eMem0 s).writeW (List.mem_singleton_self _) _ (fa_in s (by decide))

theorem frame_eMem (s : State) : Frame [FA s] s.mem (eMem s) :=
  (frame_eMem1 s).writeW (List.mem_singleton_self _) _ (fa_in s (by decide))

/-- The words of the frame after the entry. -/
structure Slots (s : State) (m : Mem) : Prop where
  c : m.readW (fa s 112) 64 = s.gpr .r3
  r : m.readW (fa s 120) 64 = s.gpr .r4
  n : m.readW (fa s 128) 64 = s.gpr .r5
  nl : m.readW (fa s 136) 64 = s.gpr .r6
  ra : m.readW (fa s 152) 64 = s.lr
  tg : m.readW (fa s 96) 64 = Tg s
  tl : m.readW (fa s 104) 64 = stackArg s 3

theorem slots_eMem (s : State) : Slots s (eMem s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega_arith) only [eMem, eMem1, eMem0, fa, rd_sep, Mem.readW_writeW_self64]

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem pf_eq : s.sp - BitVec.ofNat 64 160 = Pf s := by
  rw [h.hB, Gather.add_ofNat_sub_ofNat _ (by decide)]

theorem pf_toNat : (Pf s).toNat = (Bs s).toNat + 2688 := by
  have := h.hBn
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem argIn : argR s ∈ s.rd := by rw [h.pre.rd]; simp

/-- Our stack argument `i`, from its address in our frame's terms. -/
theorem sa_eq {i : Nat} : stackArg s i = s.mem.readW (sa s i) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 = _
  show _ = s.mem.readW (Bs s + BitVec.ofNat 64 2688 + BitVec.ofNat 64 (256 + 8 * i)) 64
  rw [h.hB, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    show 2848 + (32 + 8 * (8 + i)) = 2688 + (256 + 8 * i) by omega_arith]

theorem sa_sub {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Sub (argR s) := by
  rw [h.hargR]
  show Region.Sub ⟨Pf s + BitVec.ofNat 64 (256 + 8 * i), 8⟩ ⟨Pf s + BitVec.ofNat 64 256, 32⟩
  exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem sa_in {i : Nat} (hi : i < 4) (u : State) (hrd : u.rd = s.rd) :
    InRegions (u.rd ++ u.wr) (sa s i) 8 :=
  ⟨_, List.mem_append_left _ (by rw [hrd]; exact h.argIn), by
    rw [h.hargR]
    show (⟨Pf s + BitVec.ofNat 64 256, 32⟩ : Region).Contains (Pf s + BitVec.ofNat 64 (256 + 8 * i)) 8
    rw [← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 2848⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 2688 160 (by decide) x hc)

/-- Our stack arguments are apart from the frame. -/
theorem sa_fa {i : Nat} (hi : i < 4) : ∀ r ∈ [FA s], (⟨sa s i, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega_arith) (by have := h.pf_toNat; have := h.hBn; omega_arith)

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
    exact h.pre.bs.symm.sub_right (stk_sub s 2688 160 (by decide))) (Nat.le_of_lt (s.gpr .r10).isLt)

omit h in
theorem hlen : (bytesAt s.mem (Src s) (L s)).length = L s := Proof.Cmac.bytesAt_length _ _ _

omit h in
theorem frame_cMem : Frame [dR s] (eMem s) (cMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Lay.hlen, Nat.le_refl]

/-- A doubleword of the frame, once the ciphertext is copied. -/
theorem cFr {a : Nat} (ha : a + 8 ≤ 160) :
    (cMem s).readW (Pf s + BitVec.ofNat 64 a) 64 = (eMem s).readW (Pf s + BitVec.ofNat 64 a) 64 :=
  Frame.readW Lay.frame_cMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.sub_left (fr_sub s ha)) (by decide)

theorem slots_cMem : Slots s (cMem s) := by
  have e := slots_eMem s
  exact ⟨(h.cFr (by decide)).trans e.c, (h.cFr (by decide)).trans e.r, (h.cFr (by decide)).trans e.n,
    (h.cFr (by decide)).trans e.nl, (h.cFr (by decide)).trans e.ra, (h.cFr (by decide)).trans e.tg,
    (h.cFr (by decide)).trans e.tl⟩

/-- Our stack arguments are apart from `dst`. -/
theorem sa_dR {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Disjoint (dR s) :=
  h.pre.da.symm.sub_left (h.sa_sub hi)

/-- Our stack arguments, once the ciphertext is copied. -/
theorem cArg {i : Nat} (hi : i < 4) : (cMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW Lay.frame_cMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.sa_dR hi) (by decide), h.eArg hi]

/-- `dst_len` is `len`. -/
theorem dstLen : stackArg s 1 = s.gpr .r10 := BitVec.eq_of_toNat_eq h.pre.dl

end Lay

/-! ## The phases -/

/-- The registers the entry and the copy write. -/
abbrev kregs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r9, .r12]

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  r3 : e.gpr .r3 = Src s
  r4 : e.gpr .r4 = s.gpr .r10
  r9 : e.gpr .r9 = Dst s
  r12 : e.gpr .r12 = Pf s
  gpr : ∀ r, r ∉ kregs → e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 160 s) (Entered s) := by
  have asp : (allocated 160 s).sp = Pf s := h.pf_eq
  have awr : (allocated 160 s).wr = FR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 160 + 32, 160 - 32⟩ :: s.wr : List Region) = _
    rw [h.pf_eq]; rfl
  have amem : (allocated 160 s).mem = s.mem.write (Pf s) 8 s.sp := by
    show s.mem.write (s.sp - BitVec.ofNat 64 160) 8 s.sp = _
    rw [h.pf_eq]
  have ag (r : Reg) : (allocated 160 s).gpr r = s.gpr r := rfl
  have fin : ∀ {a : Nat}, 32 ≤ a → a + 8 ≤ 160 → InRegions (FR s :: s.wr) (Pf s + BitVec.ofNat 64 a) 8 :=
    fun h₁ h₂ => fr_in s h₁ h₂ _
  unfold entry
  refine Gather.wp_addSp (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .r12 = Pf s := by rw [v₁.gpr, asp]; exact BitVec.add_zero _
  have w₁ : u₁.wr = FR s :: s.wr := by rw [v₁.wr, awr]
  refine wp_std (a := fa s 112) (by decide) (by decide) (by rw [p₁])
    (by rw [w₁]; exact fin (by decide) (by decide)) fun u₂ v₂ => ?_
  refine wp_std (a := fa s 120) (by decide) (by decide) (by rw [v₂.gpr, p₁])
    (by rw [v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₃ v₃ => ?_
  refine wp_std (a := fa s 128) (by decide) (by decide) (by rw [v₃.gpr, v₂.gpr, p₁])
    (by rw [v₃.wr, v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₄ v₄ => ?_
  refine wp_std (a := fa s 136) (by decide) (by decide) (by rw [v₄.gpr, v₃.gpr, v₂.gpr, p₁])
    (by rw [v₄.wr, v₃.wr, v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₅ v₅ => ?_
  have g₅ (r : Reg) (hr : r ≠ .r12) : u₅.gpr r = s.gpr r := by
    rw [v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, v₁.other _ hr, ag]
  have p₅ : u₅.gpr .r12 = Pf s := by rw [v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, p₁]
  have w₅ : u₅.wr = FR s :: s.wr := by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁]
  have rd₅ : u₅.rd = s.rd := by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]; rfl
  have sp₅ : u₅.sp = Pf s := by rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp]
  have lr₅ : u₅.lr = s.lr := by rw [v₅.lr, v₄.lr, v₃.lr, v₂.lr, v₁.lr]; rfl
  have m₅ : u₅.mem = ((((s.mem.write (Pf s) 8 s.sp).writeW (fa s 112) (s.gpr .r3)).writeW (fa s 120)
      (s.gpr .r4)).writeW (fa s 128) (s.gpr .r5)).writeW (fa s 136) (s.gpr .r6) := by
    rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, amem, v₄.gpr, v₃.gpr, v₂.gpr,
      v₁.other .r3 (by decide), v₁.other .r4 (by decide), v₁.other .r5 (by decide), v₁.other .r6 (by decide),
      ag, ag, ag, ag]
  refine wp_mflr fun u₆ v₆ => ?_
  refine wp_std (a := fa s 152) (by decide) (by decide) (by rw [v₆.other _ (by decide), p₅])
    (by rw [v₆.wr, w₅]; exact fin (by decide) (by decide)) fun u₇ v₇ => ?_
  have m₇ : u₇.mem = eMem0 s := by rw [v₇.mem, v₆.gpr, v₆.mem, m₅, lr₅]
  have p₇ : u₇.gpr .r12 = Pf s := by rw [v₇.gpr, v₆.other _ (by decide), p₅]
  have rd₇ : u₇.rd = s.rd := by rw [v₇.rd, v₆.rd, rd₅]
  have w₇ : u₇.wr = FR s :: s.wr := by rw [v₇.wr, v₆.wr, w₅]
  refine wp_ld (a := sa s 2) (by decide) (by decide) (by rw [p₇])
    (h.sa_in (by decide) _ rd₇) fun u₈ v₈ => ?_
  refine wp_std (a := fa s 96) (by decide) (by decide) (by rw [v₈.other _ (by decide), p₇])
    (by rw [v₈.wr, w₇]; exact fin (by decide) (by decide)) fun u₉ v₉ => ?_
  have m₉ : u₉.mem = eMem1 s := by rw [v₉.mem, v₈.gpr, v₈.mem, m₇, h.e0Arg (by decide)]
  have p₉ : u₉.gpr .r12 = Pf s := by rw [v₉.gpr, v₈.other _ (by decide), p₇]
  have rd₉ : u₉.rd = s.rd := by rw [v₉.rd, v₈.rd, rd₇]
  have w₉ : u₉.wr = FR s :: s.wr := by rw [v₉.wr, v₈.wr, w₇]
  refine wp_ld (a := sa s 3) (by decide) (by decide) (by rw [p₉])
    (h.sa_in (by decide) _ rd₉) fun u₁₀ v₁₀ => ?_
  refine wp_std (a := fa s 104) (by decide) (by decide) (by rw [v₁₀.other _ (by decide), p₉])
    (by rw [v₁₀.wr, w₉]; exact fin (by decide) (by decide)) fun u₁₁ v₁₁ => ?_
  have m₁₁ : u₁₁.mem = eMem s := by rw [v₁₁.mem, v₁₀.gpr, v₁₀.mem, m₉, h.e1Arg (by decide)]
  have g₁₁ (r : Reg) (h0 : r ≠ .r0) (hr : r ≠ .r12) : u₁₁.gpr r = s.gpr r := by
    rw [v₁₁.gpr, v₁₀.other _ h0, v₉.gpr, v₈.other _ h0, v₇.gpr, v₆.other _ h0, g₅ r hr]
  have p₁₁ : u₁₁.gpr .r12 = Pf s := by rw [v₁₁.gpr, v₁₀.other _ (by decide), p₉]
  have rd₁₁ : u₁₁.rd = s.rd := by rw [v₁₁.rd, v₁₀.rd, rd₉]
  have wr₁₁ : u₁₁.wr = FR s :: s.wr := by rw [v₁₁.wr, v₁₀.wr, w₉]
  have sp₁₁ : u₁₁.sp = Pf s := by
    rw [v₁₁.sp, v₁₀.sp, v₉.sp, v₈.sp, v₇.sp, v₆.sp, sp₅]
  refine Gather.wp_mov' fun u₁₂ v₁₂ => Gather.wp_mov' fun u₁₃ v₁₃ => ?_
  refine wp_ld (a := sa s 0) (by decide) (by decide)
    (by rw [v₁₃.other _ (by decide), v₁₂.other _ (by decide), p₁₁])
    (h.sa_in (by decide) _ (by rw [v₁₃.rd, v₁₂.rd, rd₁₁])) fun u₁₄ v₁₄ => WP.block_nil ?_
  refine ⟨by rw [v₁₄.mem, v₁₃.mem, v₁₂.mem, m₁₁], ?_, ?_, ?_, ?_, fun r hr => ?_,
    by rw [v₁₄.sp, v₁₃.sp, v₁₂.sp, sp₁₁], by rw [v₁₄.rd, v₁₃.rd, v₁₂.rd, rd₁₁],
    by rw [v₁₄.wr, v₁₃.wr, v₁₂.wr, wr₁₁]⟩
  · rw [v₁₄.other _ (by decide), v₁₃.other _ (by decide), v₁₂.gpr, g₁₁ _ (by decide) (by decide)]
  · rw [v₁₄.other _ (by decide), v₁₃.gpr, v₁₂.other _ (by decide), g₁₁ _ (by decide) (by decide)]
  · rw [v₁₄.gpr, v₁₃.mem, v₁₂.mem, m₁₁, h.eArg (by decide)]
  · rw [v₁₄.other _ (by decide), v₁₃.other _ (by decide), v₁₂.other _ (by decide), p₁₁]
  · simp only [kregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h3, h4, -, -, h9, h12⟩ := hr
    rw [v₁₄.other _ h9, v₁₃.other _ h4, v₁₂.other _ h3, g₁₁ r h0 h12]

/-- The copy's precondition after the entry. -/
theorem slicePre_of {s e : State} (h : Lay s) (he : Entered s e) : SlicePre e (Src s) (Dst s) (L s) :=
  { r3 := he.r3
    r9 := he.r9
    r4 := by rw [he.r4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    lt := (s.gpr .r10).isLt
    rd := Gather.covers_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_append_left _ (by rw [he.rd, h.pre.rd]; simp)
    wr := Gather.covers_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [he.wr, h.pre.wr]; simp
    disj := h.pre.sd }

/-- After the copy. -/
structure Copied (s c : State) : Prop where
  mem : c.mem = cMem s
  r12 : c.gpr .r12 = Pf s
  gpr : ∀ r, r ∉ kregs → c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem copied_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.Gather.PPC64LE.copySlice e (Copied s) := by
  refine WP.mono (copySlice_wp e (slicePre_of h he)) fun c ⟨mc, _, kc⟩ => ?_
  rw [he.mem, h.srcE] at mc
  have hk : ∀ r ∈ copyRegs, r ∈ kregs := by decide
  exact ⟨mc, (kc.gpr _ (by decide)).trans he.r12, fun r hr => (kc.gpr r fun hc => hr (hk r hc)).trans (he.gpr r hr),
    kc.sp.trans he.sp, kc.rd.trans he.rd, kc.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = cMem s
  r3 : c.gpr .r3 = C s
  r4 : c.gpr .r4 = s.gpr .r4
  r5 : c.gpr .r5 = Nn s
  r6 : c.gpr .r6 = s.gpr .r6
  r7 : c.gpr .r7 = Ad s
  r8 : c.gpr .r8 = s.gpr .r8
  r9 : c.gpr .r9 = Dst s
  r10 : c.gpr .r10 = s.gpr .r10
  pres : ∀ r ∈ preserved, c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Copied s g) : WP isa (.block callArgs) g (Ready s) := by
  have sl := h.slots_cMem
  have hin {a : Nat} (h₁ : 32 ≤ a) (h₂ : a + 8 ≤ 160) (u : State) (hwr : u.wr = FR s :: s.wr) :
      InRegions (u.rd ++ u.wr) (fa s a) 8 := by
    obtain ⟨r, hr, hc⟩ := fr_in s h₁ h₂ s.wr
    exact ⟨r, List.mem_append_right _ (by rw [hwr]; exact hr), hc⟩
  unfold callArgs
  refine wp_ld (a := fa s 112) (by decide) (by decide) (by rw [hg.r12]) (hin (by decide) (by decide) _ hg.wr)
    fun u₁ v₁ => ?_
  refine wp_ld (a := fa s 120) (by decide) (by decide) (by rw [v₁.other _ (by decide), hg.r12])
    (hin (by decide) (by decide) _ (by rw [v₁.wr, hg.wr])) fun u₂ v₂ => ?_
  refine wp_ld (a := fa s 128) (by decide) (by decide)
    (by rw [v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) (by decide) _ (by rw [v₂.wr, v₁.wr, hg.wr])) fun u₃ v₃ => ?_
  refine wp_ld (a := fa s 136) (by decide) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) (by decide) _ (by rw [v₃.wr, v₂.wr, v₁.wr, hg.wr])) fun u₄ v₄ => ?_
  have rd₄ : u₄.rd = s.rd := by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, hg.rd]
  refine wp_ld (a := sa s 0) (by decide) (by decide)
    (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
      hg.r12])
    (h.sa_in (by decide) _ rd₄) fun u₅ v₅ => WP.block_nil ?_
  have g₅ (r : Reg) (h3 : r ≠ .r3) (h4 : r ≠ .r4) (h5 : r ≠ .r5) (h6 : r ≠ .r6) (h9 : r ≠ .r9) :
      u₅.gpr r = g.gpr r := by
    rw [v₅.other _ h9, v₄.other _ h6, v₃.other _ h5, v₂.other _ h4, v₁.other _ h3]
  have m₅ : u₅.mem = cMem s := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, hg.mem]
  have hpres : ∀ r ∈ preserved, r ∉ kregs := by decide
  refine ⟨m₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      hg.mem, sl.c]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, hg.mem, sl.r]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, hg.mem, sl.n]
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, hg.mem, sl.nl]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.gpr _ (by decide)]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.gpr _ (by decide)]
  · rw [v₅.gpr, v₄.mem, v₃.mem, v₂.mem, v₁.mem, hg.mem, h.cArg (by decide)]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.gpr _ (by decide)]
  · have hk := hpres r hr
    simp only [kregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨-, h3, h4, h5, h6, h9, -⟩ := hk
    rw [g₅ r h3 h4 h5 h6 h9, hg.gpr r (hpres r hr)]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hg.sp]
  · rw [v₅.rd, rd₄]
  · rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hg.wr]

section
variable (s : State)

/-- The call's state, with its permissions. -/
abbrev xS (c : State) : State := c.callEntry.withRegions (rdC s) (wrC s)

end

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    c'.gpr .r3 = C s ∧ c'.gpr .r4 = s.gpr .r4 ∧ c'.gpr .r5 = Nn s ∧ c'.gpr .r6 = s.gpr .r6 ∧
      c'.gpr .r7 = Ad s ∧ c'.gpr .r8 = s.gpr .r8 ∧ c'.gpr .r9 = Dst s ∧ c'.gpr .r10 = s.gpr .r10 := by
  simp only [State.withRegions_gpr]
  exact ⟨by rw [c.callEntry_gpr (by decide), hc.r3], by rw [c.callEntry_gpr (by decide), hc.r4],
    by rw [c.callEntry_gpr (by decide), hc.r5], by rw [c.callEntry_gpr (by decide), hc.r6],
    by rw [c.callEntry_gpr (by decide), hc.r7], by rw [c.callEntry_gpr (by decide), hc.r8],
    by rw [c.callEntry_gpr (by decide), hc.r9], by rw [c.callEntry_gpr (by decide), hc.r10]⟩

theorem pf_sub (s : State) : Pf s - BitVec.ofNat 64 2688 = Bs s := BitVec.add_sub_cancel _ _

/-- The call's stack arguments, in its own terms. -/
theorem Ready.argAddr {s c : State} (hc : Ready s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 0 = fa s 96 := by
  show c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)) = Pf s + BitVec.ofNat 64 96
  rw [hc.sp]

theorem Ready.args {s c : State} (h : Lay s) (hc : Ready s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 0 = Tg s ∧
      stackArg ((c.callEntry).withRegions rd wr) 1 = stackArg s 3 := by
  constructor
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0))) 64 = _
    rw [hc.sp, hc.mem]; exact h.slots_cMem.tg
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 1))) 64 = _
    rw [hc.sp, hc.mem]; exact h.slots_cMem.tl

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre (xS s c) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have pre := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1⟩ := hc.args h (rdC s) (wrC s)
  have hPn := h.pf_toNat
  have hBn := h.hBn
  have aS : (⟨fa s 96, 16⟩ : Region).Sub ⟨Bs s, 2848⟩ := fr_sub s (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c3, c4, c5, c6, c7, c8, c9, c10, a0, a1, hc.sp, pf_sub, hc.argAddr]
    refine ⟨trivial, trivial, pre.kd, pre.nd, pre.ad, pre.dt, pre.bd.symm.sub_right aS,
      pre.bk.sub_left (Region.sub_prefix (by decide)), pre.bn.sub_left (Region.sub_prefix (by decide)),
      pre.ba.sub_left (Region.sub_prefix (by decide)), pre.bd.sub_left (Region.sub_prefix (by decide)),
      pre.bt.sub_left (Region.sub_prefix (by decide)), ?_, pre.ok, pre.on, pre.oa, pre.od, pre.ot,
      by omega_arith, by omega_arith, pre.hR⟩
    show (⟨Bs s, 2688⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 2688 + BitVec.ofNat 64 96, 16⟩
    rw [Offset.add_ofNat_add_ofNat]
    exact (Offset.disjoint_base _ (by decide) (by omega_arith)).symm
  · refine Covers.of_sub fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 64, ?_,
        by show 64 + 16 ≤ 128; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 64).symm
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
  · refine Gather.covers_mem fun r hr => ?_
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
  have apart {r : Region} (h₁ : (⟨Bs s, 2848⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FA s, dR s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h₁.symm.sub_right (stk_sub s 2688 160 (by decide))
    · exact h₂
  obtain ⟨hc', hh⟩ := Proof.AesGcm.ctx_frame hfc (apart pre.bk pre.kd) pre.hR
  have hn : bytesAt (cMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bn pre.nd) (Nat.le_of_lt (s.gpr .r6).isLt)
  have ha : bytesAt (cMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.ba pre.ad) (Nat.le_of_lt (s.gpr .r8).isLt)
  have ht : bytesAt (cMem s) (Tg s) (TL s) = bytesAt s.mem (Tg s) (TL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bt pre.dt.symm) (Nat.le_of_lt (stackArg s 3).isLt)
  have hd : bytesAt (cMem s) (Dst s) (L s) = bytesAt s.mem (Src s) (L s) := by
    have := Proof.AesGcm.bytesAt_writeBytes_self (eMem s) (Dst s) (bytesAt s.mem (Src s) (L s))
      (by rw [Lay.hlen]; exact (s.gpr .r10).isLt)
    rwa [Lay.hlen] at this
  simp only [callRes, hm, c3, c4, c5, c6, c7, c8, c9, c10, a0, a1]
  rw [hc', hh, hn, hd, ha, ht]

/-- What the call leaves of `dst` and `r3`: `vg_aes_gcm_open`'s result. -/
def Out (s : State) (e : BitVec 64) (m : Mem) : Prop :=
  match res s with
  | some pt => e.setWidth 32 = 1 ∧ bytesAt m (Dst s) (L s) = pt
  | none => e.setWidth 32 = 0

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.readW (fa s 152) 64 = s.lr
  a0 : z.mem.readW (sa s 0) 64 = Dst s
  a1 : z.mem.readW (sa s 1) 64 = stackArg s 1
  out : Out s (z.gpr .r3) z.mem
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem called_wp (hv : OpenOk) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call "vg_aes_gcm_open" openCode) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr (rdC s) (wrC s)
  refine WP.callAny (k := Proof.AesGcm.openRoundsContract PPC64LE.abi 2688) hv (openSpec_pre hcp) hcov hw
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
  have hbl {a : Nat} (ha : a + 8 ≤ 2848 - 2688 + 160) :
      (⟨Pf s + BitVec.ofNat 64 a, 8⟩ : Region).Disjoint (below c.sp (sdepth openCode)) := by
    simp only [below, hc.sp, open_sdepth, pf_sub, pf_off]
    exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  have ra : z.mem.readW (fa s 152) 64 = s.lr := by
    rw [kept (h.pre.bd.sub_left (fr_sub s (by decide))) (hbl (by decide)), hc.mem, h.slots_cMem.ra]
  have a0 : z.mem.readW (sa s 0) 64 = Dst s := by
    rw [kept (h.sa_dR (by decide)) (hbl (by decide)), hc.mem, h.cArg (by decide)]
  have a1 : z.mem.readW (sa s 1) 64 = stackArg s 1 := by
    rw [kept (h.sa_dR (by decide)) (hbl (by decide)), hc.mem, h.cArg (by decide)]
  refine ⟨ra, a0, a1, ?_, fun r hr => by rw [pres' r hr, hc.pres r hr], sp'.trans hc.sp, rd'.trans hc.rd,
    wr'.trans hc.wr⟩
  unfold Out
  revert hpost
  cases res s with
  | some pt => intro hp; exact hp
  | none => intro hp; exact hp

/-! ## After the call -/

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  simp only [eval, State.read, Size.bits]

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `r9 = D`, `r10 = n` and
`r11 = 0`. -/
theorem wipeLoop_wp (u : State) {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (h₉ : u.gpr .r9 = D) (h₁₀ : u.gpr .r10 = BitVec.ofNat 64 n) (h₁₁ : u.gpr .r11 = 0)
    (hw : Covers [⟨D, n⟩] u.wr) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem D n ∧ Frame [⟨D, n⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.lr = u.lr := by
  unfold wipeLoop
  refine WP.ite (decide (n = 0)) (eval_zero h₁₀ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl,
      rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .r9 = D + BitVec.ofNat 64 i ∧
        v.gpr .r10 = BitVec.ofNat 64 (n - i) ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp ∧ v.lr = u.lr ∧ Frame [⟨D, n⟩] u.mem v.mem ∧
        Proof.Zeroize.Prefix v.mem D i) ?_ (n - 0) _
      ⟨0, rfl, by omega, by rw [h₉]; exact (BitVec.add_zero _).symm, by rw [h₁₀, Nat.sub_zero],
        fun _ _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, r9, r10, gv, rdv, wrv, spv, lrv, fv, pv⟩
    have hcn : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    refine wp_stb (a := D + BitVec.ofNat 64 i) (by decide) (by decide) (by rw [r9]; exact BitVec.add_zero _)
      (by rw [wrv]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩) fun t₁ u₁ => ?_
    refine wp_addi (by decide) (by decide) fun t₂ u₂ => wp_subi (by decide) (by decide) fun t₃ u₃ =>
      WP.block_nil ?_
    have z₁ : (v.gpr .r11).setWidth 8 = (0 : BitVec 8) := by rw [gv _ (by decide) (by decide), h₁₁]; rfl
    have m₃ : t₃.mem = v.mem.writeW (D + BitVec.ofNat 64 i) (0 : BitVec 8) := by
      rw [u₃.mem, u₂.mem, u₁.mem, z₁]
    have f' : Frame [⟨D, n⟩] u.mem t₃.mem := by
      rw [m₃]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    have p' : Proof.Zeroize.Prefix t₃.mem D (i + 1) := by
      rw [m₃]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega)
    have g' : ∀ r, r ≠ .r9 → r ≠ .r10 → t₃.gpr r = u.gpr r := fun r a b => by
      rw [u₃.other _ b, u₂.other _ a, u₁.gpr, gv r a b]
    have r9' : t₃.gpr .r9 = D + BitVec.ofNat 64 (i + 1) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, r9, BitVec.add_assoc, ← BitVec.ofNat_add]
    have r10' : t₃.gpr .r10 = BitVec.ofNat 64 (n - (i + 1)) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, r10, ofNat_sub_one (by omega), Nat.sub_sub]
    have rd' : t₃.rd = u.rd := by rw [u₃.rd, u₂.rd, u₁.rd, rdv]
    have wr' : t₃.wr = u.wr := by rw [u₃.wr, u₂.wr, u₁.wr, wrv]
    have sp' : t₃.sp = u.sp := by rw [u₃.sp, u₂.sp, u₁.sp, spv]
    have lr' : t₃.lr = u.lr := by rw [u₃.lr, u₂.lr, u₁.lr, lrv]
    have ev := eval_nonzero (r := .r10) (a := n - (i + 1)) r10' (by omega)
    by_cases he : i + 1 = n
    · left
      exact ⟨by rw [ev]; simp [he], by rw [← he]; exact p', f', g', rd', wr', sp', lr'⟩
    · right
      exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, r9', r10', g', rd', wr', sp',
        lr', f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- After `wipeArgs`: `dst` in `r9`, `len` in `r10` and zero in `r11`. -/
structure WArgs (s z a : State) : Prop where
  r9 : a.gpr .r9 = Dst s
  r10 : a.gpr .r10 = BitVec.ofNat 64 (L s)
  r11 : a.gpr .r11 = 0
  gpr : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → a.gpr r = z.gpr r
  mem : a.mem = z.mem
  sp : a.sp = z.sp
  lr : a.lr = z.lr
  rd : a.rd = z.rd
  wr : a.wr = z.wr

theorem wipeArgs_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa (.block wipeArgs) z (WArgs s z) := by
  unfold wipeArgs
  refine Gather.wp_addSp (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .r12 = Pf s := by rw [v₁.gpr, hz.sp]; exact BitVec.add_zero _
  refine wp_ld (a := sa s 0) (by decide) (by decide) (by rw [p₁]) (h.sa_in (by decide) _ (by rw [v₁.rd, hz.rd]))
    fun u₂ v₂ => ?_
  refine wp_ld (a := sa s 1) (by decide) (by decide) (by rw [v₂.other _ (by decide), p₁])
    (h.sa_in (by decide) _ (by rw [v₂.rd, v₁.rd, hz.rd])) fun u₃ v₃ => ?_
  refine wp_li (by decide) fun u₄ v₄ => WP.block_nil ?_
  refine ⟨?_, ?_, v₄.gpr, fun r h9 h10 h11 h12 => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, hz.a0]
  · rw [v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, hz.a1, h.dstLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [v₄.other _ h11, v₃.other _ h10, v₂.other _ h9, v₁.other _ h12]
  · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  · rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp]
  · rw [v₄.lr, v₃.lr, v₂.lr, v₁.lr]
  · rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]

/-- Where `after` leaves the state: what follows the call, with `dst` and
`r3` as `toPost` has them. -/
structure Done (s u : State) : Prop where
  post : toPost s u
  ra : u.mem.readW (fa s 152) 64 = s.lr
  pres : ∀ r ∈ preserved, u.gpr r = s.gpr r
  sp : u.sp = Pf s
  rd : u.rd = s.rd
  wr : u.wr = FR s :: s.wr

/-- When the call failed: `dst` zeroed. -/
theorem wipe_wp {s z : State} (h : Lay s) (hz : Called s z) (hres : res s = none) : WP isa wipe z (Done s) := by
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun a ha => ?_)
  have hw : Covers [⟨Dst s, L s⟩] a.wr := by
    rw [ha.wr, hz.wr, h.pre.wr]; exact Gather.covers_mem fun r hr => by simp at hr; subst hr; simp
  refine WP.mono (wipeLoop_wp a (s.gpr .r10).isLt h.pre.od ha.r9 ha.r10 ha.r11 hw)
    fun u ⟨pz, fu, gu, rdu, wru, spu, _⟩ => ?_
  have g' : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → u.gpr r = z.gpr r := fun r a b c d => by
    rw [gu r a b, ha.gpr r a b c d]
  have keep : u.mem.readW (fa s 152) 64 = z.mem.readW (fa s 152) 64 := by
    rw [← ha.mem]
    refine fu.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bd.sub_left (fr_sub s (by decide))
  have hpres : ∀ r ∈ preserved, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide
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
  have o := hz.out
  unfold Out at o
  cases hr : res s with
  | none =>
    rw [hr] at o
    exact WP.ite true (by rw [eval_zero_w, o]; rfl) (fun _ => wipe_wp h hz hr) (fun h' => absurd h' (by decide))
  | some pt =>
    rw [hr] at o
    refine WP.ite false (by rw [eval_zero_w, o.1]; rfl) (fun h' => absurd h' (by decide))
      (fun _ => WP.block_nil ⟨?_, hz.ra, hz.pres, hz.sp, hz.rd, hz.wr⟩)
    unfold toPost
    rw [hr]
    exact o

theorem toPost_congr {s u t : State} (hm : t.mem = u.mem) (hg : t.gpr .r3 = u.gpr .r3) (h : toPost s u) :
    toPost s t := by
  unfold toPost at h ⊢
  rw [hm, hg]
  exact h

/-- The return address back in the link register, and the frame freed. -/
theorem ret_wp {s u : State} (h : Lay s) (hu : Done s u) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealGather.ret) u fun y =>
      abiPreserved s (freed 160 y) ∧ toPost s (freed 160 y) := by
  unfold Impl.AesGcm.PPC64LE.SealGather.ret
  refine Gather.wp_addSp (by decide) fun u₁ v₁ => ?_
  refine wp_ld (a := fa s 152) (by decide) (by decide) (by rw [v₁.gpr, hu.sp, BitVec.add_zero])
    (by
      obtain ⟨r, hr, hc⟩ := fr_in s (a := 152) (by decide) (by decide) s.wr
      exact ⟨r, List.mem_append_right _ (by rw [v₁.wr, hu.wr]; exact hr), hc⟩) fun u₂ v₂ => ?_
  refine wp_mtlr fun u₃ v₃ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · -- The callee-saved registers.
    have hpres : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r12 := by decide
    show u₃.gpr r = s.gpr r
    rw [v₃.gpr, v₂.other _ (hpres r hr).1, v₁.other _ (hpres r hr).2, hu.pres r hr]
  · -- The stack pointer.
    show u₃.sp + BitVec.ofNat 64 160 = s.sp
    rw [v₃.sp, v₂.sp, v₁.sp, hu.sp, Offset.add_ofNat_add_ofNat, h.hB]
  · -- The link register.
    show u₃.lr = s.lr
    rw [v₃.lr, v₂.gpr, v₁.mem, hu.ra]
  · -- The result and the plaintext.
    refine toPost_congr (u := u) ?_ ?_ hu.post
    · show u₃.mem = u.mem
      rw [v₃.mem, v₂.mem, v₁.mem]
    · show u₃.gpr .r3 = u.gpr .r3
      rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide)]

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

end VG.Proof.AesGcm.PPC64LE.OpenTo
