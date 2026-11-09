module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Split
public import VerifiedGarbage.Proof.AesGcm.Rounds
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
# AES-GCM decryption out of place, in one pass, PPC64LE: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against (`toK`), which the shared one implies
(`OpenTo/Verified.lean`), and its proof (`openTo_wp`). It calls
`vg_aes_gcm_open_split` by its contract (`splitPPC64LE`, `SplitOk`).

With `Pf` the base of the 2720 bytes of stack below the stack pointer
(`sp = Pf + 2720`), the function allocates its frame of 2720 bytes there
(`WP.alloc`), keeps our return address in it, and lays out the call's four
stack arguments, the working space being the rest of the frame
(`entered_wp`). It calls `vg_aes_gcm_open_split` (`called_wp`), which
writes only `dst` and the working space, and zeroes `dst` if it returned 0
(`after_wp`, `wipe_wp`); then it reloads our return address (`ret_wp`).
Every write is to `dst` or to the stack below `sp`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.PPC64LE.OpenTo

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Proof.Gather.PPC64LE (eval_zero eval_nonzero ofNat_sub_one)
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
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 2720, 2720⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (C s) (Rn s)) (ctxH s.mem (C s)) (TL s) (bytesAt s.mem (Nn s) (NL s))
    (bytesAt s.mem (Src s) (L s)) (bytesAt s.mem (Ad s) (AL s)) (bytesAt s.mem (Tg s) (TL s))

end

/-- What the proof of `vg_aes_gcm_open_to` needs: the layout of its shared
contract, with 2720 bytes of stack, `dst_len` its `len`. -/
structure ToPre (s : State) : Prop where
  w₁ : 2720 ≤ s.sp.toNat
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

/-- The correctness of `vg_aes_gcm_open_split`, by its contract. -/
abbrev SplitOk : Prop :=
  ∀ s, splitPPC64LE.pre s → ∃ t s', Exec isa openSplit s t s' ∧ abiPreserved s s' ∧ splitPPC64LE.post s s'

/-- `vg_aes_gcm_open_split` allocates no stack. -/
theorem split_sdepth : sdepth openSplit = 0 := by
  decide +kernel

/-! ## The layout -/

section
variable (s : State)

/-- Our frame, the 2720 bytes of stack below the stack pointer: the stack
pointer in it. -/
abbrev Pf : Addr := s.sp - BitVec.ofNat 64 2720

/-- The doubleword at offset `a` of the frame. -/
abbrev fa (a : Nat) : Addr := Pf s + BitVec.ofNat 64 a

/-- Our stack argument `i`. -/
abbrev sa (i : Nat) : Addr := Pf s + BitVec.ofNat 64 (2816 + 8 * i)

/-- The frame past its header, which the frame makes writable, the whole
frame, and the working space. -/
abbrev FR : Region := ⟨Pf s + BitVec.ofNat 64 32, 2688⟩
abbrev FA : Region := ⟨Pf s, 2720⟩
abbrev scR : Region := ⟨fa s 160, 2560⟩

/-- The memory after the entry: the back chain at `Pf`, our return address
at `Pf + 152`, and `tag`, `tag_len`, the working space's address and `dst`
at `Pf + 96` … `Pf + 120`, for the call. -/
abbrev eMem : Mem :=
  (((((s.mem.write (Pf s) 8 s.sp).writeW (fa s 152) s.lr).writeW (fa s 96) (Tg s)).writeW (fa s 104)
    (stackArg s 3)).writeW (fa s 112) (fa s 160)).writeW (fa s 120) (Dst s)

/-- The regions the call of `vg_aes_gcm_open_split` reads and writes: its
stack arguments are at `Pf + 96`. -/
abbrev rdC : List Region := [kR s, nR s, aR s, sR s, tR s, ⟨fa s 96, 32⟩]
abbrev wrC : List Region := [dR s, scR s]

end

/-- What `ToPre` gives. -/
structure Lay (s : State) : Prop where
  pre : ToPre s
  hB : s.sp = Pf s + BitVec.ofNat 64 2720
  hBn : (Pf s).toNat + 2848 ≤ 2 ^ 64
  hargR : argR s = ⟨Pf s + BitVec.ofNat 64 2816, 32⟩

theorem lay {s : State} (hs : ToPre s) : Lay s := by
  have w₁ := hs.w₁
  have w₂ := hs.w₂
  have hB : s.sp = Pf s + BitVec.ofNat 64 2720 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Pf s).toNat + 2848 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Pf s).isLt
    omega_arith
  refine ⟨hs, hB, hBn, ?_⟩
  show (⟨s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)), 32⟩ : Region) = ⟨Pf s + BitVec.ofNat 64 2816, 32⟩
  rw [hB, Offset.add_ofNat_add_ofNat]

/-- Bytes of the frame, in the stack below the stack pointer. -/
theorem fr_sub (s : State) {a n : Nat} (ha : a + n ≤ 2720) :
    (⟨Pf s + BitVec.ofNat 64 a, n⟩ : Region).Sub (FA s) :=
  Offset.sub_base _ ha

theorem fr_in (s : State) {a : Nat} (h₁ : 32 ≤ a) (h₂ : a + 8 ≤ 2720) (wr : List Region) :
    InRegions (FR s :: wr) (Pf s + BitVec.ofNat 64 a) 8 :=
  ⟨_, List.mem_cons_self .., by
    show (⟨Pf s + BitVec.ofNat 64 32, 2688⟩ : Region).Contains (Pf s + BitVec.ofNat 64 a) 8
    rw [show a = 32 + (a - 32) by omega_arith, ← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A doubleword of the frame, after a write to another. -/
theorem rd_sep (s : State) (m : Mem) (v : BitVec 64) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 2720)
    (hb : b + 8 ≤ 2720) :
    (m.writeW (Pf s + BitVec.ofNat 64 b) v).readW (Pf s + BitVec.ofNat 64 a) 64 =
      m.readW (Pf s + BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep (Pf s) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem fa_in (s : State) {a : Nat} (ha : a + 8 ≤ 2720) : (FA s).Contains (Pf s + BitVec.ofNat 64 a) (64 / 8) :=
  Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem frame_eMem (s : State) : Frame [FA s] s.mem (eMem s) := by
  have m := List.mem_singleton_self (FA s)
  exact (((((Frame.refl _ _).write m _ (Region.contains_self' (by decide))).writeW m _
    (fa_in s (by decide))).writeW m _ (fa_in s (by decide))).writeW m _ (fa_in s (by decide))).writeW m _
    (fa_in s (by decide)) |>.writeW m _ (fa_in s (by decide))

/-- The words of the frame after the entry. -/
structure Slots (s : State) (m : Mem) : Prop where
  ra : m.readW (fa s 152) 64 = s.lr
  tg : m.readW (fa s 96) 64 = Tg s
  tl : m.readW (fa s 104) 64 = stackArg s 3
  sc : m.readW (fa s 112) 64 = fa s 160
  dst : m.readW (fa s 120) 64 = Dst s

theorem slots_eMem (s : State) : Slots s (eMem s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega_arith) only [eMem, fa, rd_sep, Mem.readW_writeW_self64]

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem argIn : argR s ∈ s.rd := by rw [h.pre.rd]; simp

/-- Our stack argument `i`, from its address in our frame's terms. -/
theorem sa_eq {i : Nat} : stackArg s i = s.mem.readW (sa s i) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 = _
  show _ = s.mem.readW (Pf s + BitVec.ofNat 64 (2816 + 8 * i)) 64
  rw [h.hB, Offset.add_ofNat_add_ofNat, show 2720 + (32 + 8 * (8 + i)) = 2816 + 8 * i by omega_arith]

theorem sa_in {i : Nat} (hi : i < 4) (u : State) (hrd : u.rd = s.rd) :
    InRegions (u.rd ++ u.wr) (sa s i) 8 :=
  ⟨_, List.mem_append_left _ (by rw [hrd]; exact h.argIn), by
    rw [h.hargR]
    show (⟨Pf s + BitVec.ofNat 64 2816, 32⟩ : Region).Contains (Pf s + BitVec.ofNat 64 (2816 + 8 * i)) 8
    rw [← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem sa_sub {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Sub (argR s) := by
  rw [h.hargR]
  show Region.Sub ⟨Pf s + BitVec.ofNat 64 (2816 + 8 * i), 8⟩ ⟨Pf s + BitVec.ofNat 64 2816, 32⟩
  exact Offset.sub _ (by omega_arith) (by omega_arith)

/-- Our stack arguments are apart from the frame. -/
theorem sa_fa {i : Nat} (hi : i < 4) : ∀ r ∈ [FA s], (⟨sa s i, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega_arith) (by have := h.hBn; omega_arith)

theorem eArg {i : Nat} (hi : i < 4) : (eMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

/-- Our stack arguments are apart from `dst` and the working space. -/
theorem sa_dR {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Disjoint (dR s) :=
  h.pre.da.symm.sub_left (h.sa_sub hi)

theorem sa_sc {i : Nat} (hi : i < 4) : (⟨sa s i, 8⟩ : Region).Disjoint (scR s) := by
  show (⟨Pf s + BitVec.ofNat 64 (2816 + 8 * i), 8⟩ : Region).Disjoint ⟨Pf s + BitVec.ofNat 64 160, 2560⟩
  exact Offset.disjoint (Pf s) (.inr (by omega_arith)) (by omega_arith) (by have := h.hBn; omega_arith)

/-- `dst_len` is `len`. -/
theorem dstLen : stackArg s 1 = s.gpr .r10 := BitVec.eq_of_toNat_eq h.pre.dl

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  r12 : e.gpr .r12 = Pf s
  gpr : ∀ r, r ≠ .r0 → r ≠ .r12 → e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 2720 s) (Entered s) := by
  have asp : (allocated 2720 s).sp = Pf s := rfl
  have awr : (allocated 2720 s).wr = FR s :: s.wr := rfl
  have amem : (allocated 2720 s).mem = s.mem.write (Pf s) 8 s.sp := rfl
  have ag (r : Reg) : (allocated 2720 s).gpr r = s.gpr r := rfl
  have fin : ∀ {a : Nat}, 32 ≤ a → a + 8 ≤ 2720 → InRegions (FR s :: s.wr) (Pf s + BitVec.ofNat 64 a) 8 :=
    fun h₁ h₂ => fr_in s h₁ h₂ _
  unfold entry
  refine Gather.wp_addSp (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .r12 = Pf s := by rw [v₁.gpr, asp]; exact BitVec.add_zero _
  have w₁ : u₁.wr = FR s :: s.wr := by rw [v₁.wr, awr]
  refine wp_mflr fun u₂ v₂ => ?_
  refine wp_std (a := fa s 152) (by decide) (by decide) (by rw [v₂.other _ (by decide), p₁])
    (by rw [v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₃ v₃ => ?_
  have p₃ : u₃.gpr .r12 = Pf s := by rw [v₃.gpr, v₂.other _ (by decide), p₁]
  have rd₃ : u₃.rd = s.rd := by rw [v₃.rd, v₂.rd, v₁.rd]; rfl
  have w₃ : u₃.wr = FR s :: s.wr := by rw [v₃.wr, v₂.wr, w₁]
  have m₃ : u₃.mem = (s.mem.write (Pf s) 8 s.sp).writeW (fa s 152) s.lr := by
    rw [v₃.mem, v₂.gpr, v₂.mem, v₁.mem, v₁.lr, amem]; rfl
  refine wp_ld (a := sa s 2) (by decide) (by decide) (by rw [p₃]) (h.sa_in (by decide) _ rd₃) fun u₄ v₄ => ?_
  refine wp_std (a := fa s 96) (by decide) (by decide) (by rw [v₄.other _ (by decide), p₃])
    (by rw [v₄.wr, w₃]; exact fin (by decide) (by decide)) fun u₅ v₅ => ?_
  have p₅ : u₅.gpr .r12 = Pf s := by rw [v₅.gpr, v₄.other _ (by decide), p₃]
  have rd₅ : u₅.rd = s.rd := by rw [v₅.rd, v₄.rd, rd₃]
  have w₅ : u₅.wr = FR s :: s.wr := by rw [v₅.wr, v₄.wr, w₃]
  have sa' : ∀ {i : Nat}, i < 4 → ∀ m : Mem, Frame [FA s] s.mem m → m.readW (sa s i) 64 = stackArg s i :=
    fun hi m hm => by rw [Frame.readW hm (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]
  have fA : ∀ m a v, a + 8 ≤ 2720 → Frame [FA s] s.mem m → Frame [FA s] s.mem (m.writeW (fa s a) (v : BitVec 64)) :=
    fun m a v ha hm => hm.writeW (List.mem_singleton_self _) _ (fa_in s ha)
  have f₃ : Frame [FA s] s.mem u₃.mem := by
    rw [m₃]; exact fA _ _ _ (by decide) ((Frame.refl _ _).write (List.mem_singleton_self _) _
      (Region.contains_self' (by decide)))
  have m₅ : u₅.mem = u₃.mem.writeW (fa s 96) (Tg s) := by rw [v₅.mem, v₄.gpr, v₄.mem, sa' (by decide) _ f₃]
  have f₅ : Frame [FA s] s.mem u₅.mem := by rw [m₅]; exact fA _ _ _ (by decide) f₃
  refine wp_ld (a := sa s 3) (by decide) (by decide) (by rw [p₅]) (h.sa_in (by decide) _ rd₅) fun u₆ v₆ => ?_
  refine wp_std (a := fa s 104) (by decide) (by decide) (by rw [v₆.other _ (by decide), p₅])
    (by rw [v₆.wr, w₅]; exact fin (by decide) (by decide)) fun u₇ v₇ => ?_
  have p₇ : u₇.gpr .r12 = Pf s := by rw [v₇.gpr, v₆.other _ (by decide), p₅]
  have rd₇ : u₇.rd = s.rd := by rw [v₇.rd, v₆.rd, rd₅]
  have w₇ : u₇.wr = FR s :: s.wr := by rw [v₇.wr, v₆.wr, w₅]
  have m₇ : u₇.mem = u₅.mem.writeW (fa s 104) (stackArg s 3) := by
    rw [v₇.mem, v₆.gpr, v₆.mem, sa' (by decide) _ f₅]
  have f₇ : Frame [FA s] s.mem u₇.mem := by rw [m₇]; exact fA _ _ _ (by decide) f₅
  refine wp_addi (by decide) (by decide) fun u₈ v₈ => ?_
  refine wp_std (a := fa s 112) (by decide) (by decide) (by rw [v₈.other _ (by decide), p₇])
    (by rw [v₈.wr, w₇]; exact fin (by decide) (by decide)) fun u₉ v₉ => ?_
  have p₉ : u₉.gpr .r12 = Pf s := by rw [v₉.gpr, v₈.other _ (by decide), p₇]
  have rd₉ : u₉.rd = s.rd := by rw [v₉.rd, v₈.rd, rd₇]
  have w₉ : u₉.wr = FR s :: s.wr := by rw [v₉.wr, v₈.wr, w₇]
  have m₉ : u₉.mem = u₇.mem.writeW (fa s 112) (fa s 160) := by rw [v₉.mem, v₈.gpr, v₈.mem, p₇]
  have f₉ : Frame [FA s] s.mem u₉.mem := by rw [m₉]; exact fA _ _ _ (by decide) f₇
  refine wp_ld (a := sa s 0) (by decide) (by decide) (by rw [p₉]) (h.sa_in (by decide) _ rd₉) fun u₁₀ v₁₀ => ?_
  refine wp_std (a := fa s 120) (by decide) (by decide) (by rw [v₁₀.other _ (by decide), p₉])
    (by rw [v₁₀.wr, w₉]; exact fin (by decide) (by decide)) fun u₁₁ v₁₁ => WP.block_nil ?_
  refine ⟨?_, by rw [v₁₁.gpr, v₁₀.other _ (by decide), p₉], fun r h0 h12 => ?_, ?_, ?_, ?_⟩
  · rw [v₁₁.mem, v₁₀.gpr, v₁₀.mem, sa' (by decide) _ f₉, m₉, m₇, m₅, m₃]
  · rw [v₁₁.gpr, v₁₀.other _ h0, v₉.gpr, v₈.other _ h0, v₇.gpr, v₆.other _ h0, v₅.gpr, v₄.other _ h0, v₃.gpr,
      v₂.other _ h0, v₁.other _ h12, ag]
  · rw [v₁₁.sp, v₁₀.sp, v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp]
  · rw [v₁₁.rd, v₁₀.rd, rd₉]
  · rw [v₁₁.wr, v₁₀.wr, w₉]

section
variable (s : State)

/-- The call's state, with its permissions. -/
abbrev xS (c : State) : State := c.callEntry.withRegions (rdC s) (wrC s)

end

/-- The registers at the call: our arguments. -/
theorem Entered.callGpr {s c : State} (hc : Entered s c) (rd' wr' : List Region) {r : Reg}
    (hr : r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) :
    ((c.callEntry).withRegions rd' wr').gpr r = s.gpr r := by
  simp only [State.withRegions_gpr]
  rw [c.callEntry_gpr (by revert hr; revert r; decide), hc.gpr r (by revert hr; revert r; decide)
    (by revert hr; revert r; decide)]

/-- The call's stack arguments, in its own terms. -/
theorem Entered.argAddr {s c : State} (hc : Entered s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 0 = fa s 96 := by
  show c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)) = Pf s + BitVec.ofNat 64 96
  rw [hc.sp]

theorem Entered.args {s c : State} (hc : Entered s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 0 = Tg s ∧
      stackArg ((c.callEntry).withRegions rd wr) 1 = stackArg s 3 ∧
      stackArg ((c.callEntry).withRegions rd wr) 2 = fa s 160 ∧
      stackArg ((c.callEntry).withRegions rd wr) 3 = Dst s := by
  have sl := slots_eMem s
  refine ⟨?_, ?_, ?_, ?_⟩
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.tg
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 1))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.tl
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 2))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.sc
  · show c.mem.readW (c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 3))) 64 = _
    rw [hc.sp, hc.mem]; exact sl.dst

/-- What the call needs. -/
theorem Entered.call {s c : State} (h : Lay s) (hc : Entered s c) :
    splitPre (xS s c) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  have pre := h.pre
  have g := fun r hr => hc.callGpr (rdC s) (wrC s) (r := r) hr
  obtain ⟨a0, a1, a2, a3⟩ := hc.args (rdC s) (wrC s)
  have hBn := h.hBn
  have sc : (scR s).Sub (FA s) := fr_sub s (by decide)
  have hA : (⟨fa s 96, 32⟩ : Region).Disjoint (scR s) :=
    Offset.disjoint (Pf s) (.inl (by decide)) (by decide) (by omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · have f160 : (fa s 160).toNat + 2560 ≤ 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 160) (by decide),
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    simp only [splitPre, VG.Proof.AesGcm.PPC64LE.args, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
      g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), g .r10 (by decide), a0, a1, a2,
      a3, hc.sp, hc.argAddr]
    exact ⟨trivial, trivial, pre.bk.symm.sub_right sc, pre.bn.symm.sub_right sc, pre.ba.symm.sub_right sc,
      pre.bs.symm.sub_right sc, pre.bt.symm.sub_right sc, hA.symm, pre.kd, pre.sd, (pre.bd.sub_left sc).symm,
      pre.ok, pre.on, pre.oa, pre.os, pre.ot, f160, pre.od, by omega_arith, pre.hR⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, pre.rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 64, ?_,
        by show 64 + 32 ≤ 2688; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 64).symm
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 128, ?_,
        by show 128 + 2560 ≤ 2688; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 128).symm
  · refine Covers.of_sub fun r hr => ?_
    simp only [wrC, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by rw [hc.wr, pre.wr]; simp, 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, by rw [hc.wr]; exact List.mem_cons_self .., 128, ?_, by show 128 + 2560 ≤ 2688; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 128).symm

/-- The call's result, on the call's state. -/
theorem Entered.xres {s c : State} (h : Lay s) (hc : Entered s c) : openRes (xS s c) = res s := by
  have pre := h.pre
  have g := fun r hr => hc.callGpr (rdC s) (wrC s) (r := r) hr
  obtain ⟨a0, a1, -, -⟩ := hc.args (rdC s) (wrC s)
  have hm : (xS s c).mem = eMem s := by
    simp only [State.withRegions_mem, State.callEntry_mem, hc.mem]
  have apart {r : Region} (h₁ : (stkR s).Disjoint r) : ∀ r' ∈ [FA s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    exact h₁.symm
  obtain ⟨hc', hh⟩ := Proof.AesGcm.ctx_frame (frame_eMem s) (apart pre.bk) pre.hR
  have hn : bytesAt (eMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.bn) (Nat.le_of_lt (s.gpr .r6).isLt)
  have ha : bytesAt (eMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.ba) (Nat.le_of_lt (s.gpr .r8).isLt)
  have ht : bytesAt (eMem s) (Tg s) (TL s) = bytesAt s.mem (Tg s) (TL s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.bt) (Nat.le_of_lt (stackArg s 3).isLt)
  have hd : bytesAt (eMem s) (Src s) (L s) = bytesAt s.mem (Src s) (L s) :=
    Proof.Cmac.bytesAt_frame (frame_eMem s) (apart pre.bs) (Nat.le_of_lt (s.gpr .r10).isLt)
  simp only [openRes, hm, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide),
    g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), g .r10 (by decide), a0, a1]
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

theorem called_wp (hv : SplitOk) {s c : State} (h : Lay s) (hc : Entered s c) :
    WP isa (.call "vg_aes_gcm_open_split" openSplit) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  have g := fun r hr => hc.callGpr (rdC s) (wrC s) (r := r) hr
  obtain ⟨-, -, -, a3⟩ := hc.args (rdC s) (wrC s)
  refine WP.callAny (k := splitPPC64LE) hv hcp hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [split_sdepth]; decide)
  have hpost : match openRes (xS s c) with
      | some pt => ((z.withRegions (rdC s) (wrC s)).gpr .r3).setWidth 32 = 1 ∧
        bytesAt (z.withRegions (rdC s) (wrC s)).mem (stackArg (xS s c) 3) ((xS s c).gpr .r10).toNat = pt
      | none => ((z.withRegions (rdC s) (wrC s)).gpr .r3).setWidth 32 = 0 := post'
  rw [hc.xres h, a3, g .r10 (by decide)] at hpost
  simp only [State.withRegions_gpr, State.withRegions_mem] at hpost
  -- What the call kept: our frame's return address and our arguments.
  have kept {a : Addr} (hd : (⟨a, 8⟩ : Region).Disjoint (dR s)) (hs : (⟨a, 8⟩ : Region).Disjoint (scR s)) :
      z.mem.readW a 64 = c.mem.readW a 64 := by
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [wrC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact hd
    · exact hs
    · simp only [below, split_sdepth]
      intro x _ hc'
      simp only [Region.Contains] at hc'
      omega
  have ra : z.mem.readW (fa s 152) 64 = s.lr := by
    rw [kept (h.pre.bd.sub_left (fr_sub s (by decide)))
      (Offset.disjoint (Pf s) (.inl (by decide)) (by decide) (by have := h.hBn; omega_arith)), hc.mem,
      (slots_eMem s).ra]
  have a0 : z.mem.readW (sa s 0) 64 = Dst s := by
    rw [kept (h.sa_dR (by decide)) (h.sa_sc (by decide)), hc.mem, h.eArg (by decide)]
  have a1 : z.mem.readW (sa s 1) 64 = stackArg s 1 := by
    rw [kept (h.sa_dR (by decide)) (h.sa_sc (by decide)), hc.mem, h.eArg (by decide)]
  refine ⟨ra, a0, a1, ?_, fun r hr => by
    rw [pres' r hr, hc.gpr r (by revert hr; revert r; decide) (by revert hr; revert r; decide)],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr⟩
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
      abiPreserved s (freed 2720 y) ∧ toPost s (freed 2720 y) := by
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
    show u₃.sp + BitVec.ofNat 64 2720 = s.sp
    rw [v₃.sp, v₂.sp, v₁.sp, hu.sp]
    exact h.hB.symm
  · -- The link register.
    simp only [freed]
    rw [v₃.lr, v₂.gpr, v₁.mem, hu.ra]
  · -- The result and the plaintext.
    refine toPost_congr (u := u) ?_ ?_ hu.post
    · simp only [freed]
      rw [v₃.mem, v₂.mem, v₁.mem]
    · simp only [freed]
      rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide)]

theorem openTo_wp (hv : SplitOk) {s : State} (hs : ToPre s) :
    WP isa openTo s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  have w₁ := hs.w₁
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (called_wp hv h he) fun z hz => ?_)
  refine WP.seq (WP.mono (after_wp h hz) fun u hu => ?_)
  exact ret_wp h hu

end VG.Proof.AesGcm.PPC64LE.OpenTo
