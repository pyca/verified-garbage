module

public import VerifiedGarbage.Proof.Mont.X86.Words

public import VerifiedGarbage.Proof.Mont.Words32

public import VerifiedGarbage.Proof.Framework.X86.Wp

public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public prepared-square values cached in the sixteen-byte frame

The logical arguments retain the run-time square's numbering. Only the
working-space pointer and width, and the two absolute operand pointers,
need physical stack words. The inverse is at the prepared header's offset.
-/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.PreparedSquare
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep)

def cacheArg (i : Nat) : MemOp :=
  if i = 0 then at_ .esp 0 else if i = 2 then at_ .esp 12 else
    if i = 3 then at_ .esp 4 else at_ .esp 8

def cacheValue (A : Nat → BitVec 32) (i : Nat) : BitVec 32 :=
  if i = 3 ∨ i = 7 then A 0 + A i else A i

theorem cacheArg_base (i : Nat) : (cacheArg i).base = .esp := by
  unfold cacheArg
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

structure Args (s : State) (W : Addr) (L : Nat) (A : Nat → BitVec 32) : Prop where
  read : ∀ i ∈ [0, 2, 3, 7], readSrc s (.mem (cacheArg i)) = some (cacheValue A i)
  far : ∀ i ∈ [0, 2, 3, 7], ArgFar s W L (cacheArg i)
  inverse : A 4 = BitVec.ofNat 32 56
  modulus : A 3 = BitVec.ofNat 32 256

theorem Args.keep {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (h : Args s W L A)
    (O : Outs W [(0, L)] s.mem t.mem) (sp : t.gpr .esp = s.gpr .esp)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Args t W L A := by
  have hb (i : Nat) : t.gpr (cacheArg i).base = s.gpr (cacheArg i).base := by
    simpa only [cacheArg_base] using sp
  exact ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) (hb i) rd wr).trans (h.read i hi),
    fun i hi => (h.far i hi).keep (hb i), h.inverse, h.modulus⟩

theorem Args.of_keeps {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (h : Args s W L A)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) (O : Outs W [(0, L)] s.mem t.mem) :
    Args t W L A := h.keep O (K.1 _ sp) K.2.1 K.2.2

theorem Args.of_upd {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (h : Args s W L A)
    {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp) : Args t W L A :=
  h.of_keeps u.keeps (by simpa using hd.symm) (by rw [u.mem]; exact Outs.refl _ _ _)

def argA : Nat := 7
def argM : Nat := 3
def argInv : Nat := 4

def ptr (r : Reg) (i : Nat) (_t : Reg) : List Instr :=
  if i = 4 then [.mov r (.mem (cacheArg 3)), .alu .sub r (.imm 200)]
  else [.mov r (.mem (cacheArg i))]

theorem ptr_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (ha : Args s W L A)
    {r t : Reg} {i : Nat} (hi : i = 3 ∨ i = 4 ∨ i = 7) (_hr : r ≠ .esp) (_hrt : r ≠ t) :
    WP isa (.block (ptr r i t)) s fun u =>
      u.gpr r = A 0 + A i ∧ True ∧ u.mem = s.mem ∧ Keeps [r, t] s u := by
  rcases hi with rfl | rfl | rfl
  · simp only [ptr, show (3 : Nat) ≠ 4 by decide, ↓reduceIte]
    refine wp_movS (ha.read 3 (by decide)) fun u U _ => WP.block_nil ?_
    exact ⟨U.gpr, True.intro, U.mem, U.keeps.mono (by simp)⟩
  · simp only [ptr, ↓reduceIte]
    refine wp_movS (ha.read 3 (by decide)) fun u U _ => wp_subS rfl fun v V _ => WP.block_nil ?_
    refine ⟨?_, True.intro, V.mem.trans U.mem, (U.keeps.mono (by simp)).trans (V.keeps.mono (by simp))⟩
    rw [V.gpr, U.gpr]
    change (A 0 + A 3) - BitVec.ofNat 32 200 = A 0 + A 4
    rw [ha.inverse, ha.modulus]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := (A 0).isLt
    omega
  · simp only [ptr, show (7 : Nat) ≠ 4 by decide, ↓reduceIte]
    refine wp_movS (ha.read 7 (by decide)) fun u U _ => WP.block_nil ?_
    exact ⟨U.gpr, True.intro, U.mem, U.keeps.mono (by simp)⟩

theorem lenTimes_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (ha : Args s W L A)
    {r : Reg} (k : Nat) :
    WP isa (.block (lenTimes r k)) s fun u =>
      (u.gpr r).toNat = (A 2).toNat * 2 ^ (3 + k) % 2 ^ 32 ∧ u.mem = s.mem ∧ Keeps [r] s u := by
  simp only [VG.Impl.Mont.X86.PreparedSquare.lenTimes]
  refine wp_movS (ha.read 2 (by decide)) fun s₀ u₀ _ => ?_
  suffices ∀ c j (t : State), (t.gpr r).toNat = (A 2).toNat * 2 ^ j % 2 ^ 32 → t.mem = s.mem →
      Keeps [r] s t → WP isa (.block (List.replicate c (.alu .add r (.reg r)))) t fun u =>
        (u.gpr r).toNat = (A 2).toNat * 2 ^ (j + c) % 2 ^ 32 ∧ u.mem = s.mem ∧ Keeps [r] s u by
    have := this (3 + k) 0 s₀ (by rw [u₀.gpr]; simp [cacheValue, Nat.mod_eq_of_lt (A 2).isLt]) u₀.mem u₀.keeps
    rwa [Nat.zero_add] at this
  intro c
  induction c with
  | zero => intro j t h1 h2 h3; exact WP.block_nil ⟨by rw [h1, Nat.add_zero], h2, h3⟩
  | succ c ih =>
    intro j t h1 h2 h3
    rw [List.replicate_succ]
    refine wp_addS rfl fun t' u' _ => ?_
    refine (ih (j + 1) t' ?_ (by rw [u'.mem, h2]) (h3.trans (u'.keeps.mono (by simp)))).mono
      (fun u h => by rwa [show j + 1 + c = j + (c + 1) by omega] at h)
    rw [u'.gpr, BitVec.toNat_add, h1,
      show (A 2).toNat * 2 ^ (j + 1) = (A 2).toNat * 2 ^ j * 2 by rw [Nat.pow_succ, Nat.mul_assoc]]
    generalize (A 2).toNat * 2 ^ j = a
    omega


structure Lay (L N S mo inv a b : Nat) : Prop where
  scr : S + 8 * N + 32 ≤ L
  mo_le : mo + 4 * N ≤ L
  inv_le : inv + 4 ≤ L
  a_le : a + 4 * N ≤ L
  b_le : b + 4 * N ≤ L
  smo : mo + 4 * N ≤ S ∨ S + 8 * N + 32 ≤ mo
  sinv : inv + 4 ≤ S ∨ S + 8 * N + 32 ≤ inv
  sa : a + 4 * N ≤ S ∨ S + 8 * N + 32 ≤ a
  sb : b + 4 * N ≤ S ∨ S + 8 * N + 32 ≤ b

end VG.Proof.Mont.X86.PreparedSquare
