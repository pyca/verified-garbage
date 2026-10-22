module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryConstants
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Run the reused Montgomery setup inside the full generation workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def parentState (base : Addr) (s : State) : State :=
  s.withRegions s.rd [⟨base, montgomeryBytes⟩]

def ParentContext (base : Addr) (n m : Nat) (s : State) : Prop :=
  Context n m base montgomeryBytes (parentState base s)

theorem ParentContext.outside_keep {s t : State} {base : Addr} {n m d size : Nat}
    {regs : List Reg} (C : ParentContext base n m s) (K : Keeps regs s t)
    (edi : .edi ∉ regs) (esp : .esp ∉ regs) (F : Outside base d size s.mem t.mem)
    (modulus : slot n 0 + 8 * n ≤ d ∨ d + size ≤ slot n 0) (inverse : 4 ≤ d) :
    ParentContext base n m t :=
  VG.Proof.Mont.X86.Dynamic.Context.outside_keep (t := parentState base t) C
    ⟨K.1, K.2.1, rfl⟩ edi esp F modulus inverse

theorem ParentContext.frame_keep {s t : State} {base : Addr} {n m : Nat} {rs : List Region}
    {regs : List Reg} (C : ParentContext base n m s) (K : Keeps regs s t)
    (edi : .edi ∉ regs) (esp : .esp ∉ regs) (F : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨base, montgomeryBytes⟩ r) : ParentContext base n m t := by
  have virtualK : Keeps regs (parentState base s) (parentState base t) := ⟨K.1, K.2.1, rfl⟩
  refine ⟨C.scr.of_keeps virtualK edi esp, C.size_le,
    ⟨C.modulus.n0, C.modulus.mo, C.modulus.tmp, C.modulus.sep, ?_⟩, C.gt_one, ?_⟩
  · change wordsVal t.mem base (slot n 0) n = m
    rw [wordsVal_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
    rw [F.read (r := ⟨base, montgomeryBytes⟩)
      (Offset.contains_base _ (by have := C.modulus.mo; change slot n 0 + 8 * n ≤ montgomeryBytes at this; omega)
        (by simp [slot])) apart (by
          have := C.modulus.mo; change slot n 0 + 8 * n ≤ montgomeryBytes at this
          unfold montgomeryBytes at this; omega)]
    rw [VG.Proof.Bignum.read_eq_val32, ← wordsVal_eq_val32]
    exact C.modulus.val
  · have same : w32 t.mem base 0 = w32 s.mem base 0 := congrArg BitVec.toNat
      (F.readW (r := ⟨base, montgomeryBytes⟩) (Offset.contains_base _ (by decide) (by decide)) apart (by decide))
    change (m * w32 t.mem base 0 + 1) % 2 ^ 32 = 0
    rw [same]; exact C.inverse

theorem ParentContext.frame_slot {s t : State} {base : Addr} {n m j : Nat} {rs : List Region}
    (C : ParentContext base n m s) (F : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨base, montgomeryBytes⟩ r) (hj : j < 9) :
    wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
  have bound := VG.Proof.Mont.X86.Dynamic.slot_bound (n := n) hj
  have size := C.size_le
  unfold stride at bound
  have fit : slot n j + 4 * (2 * n) ≤ montgomeryBytes := by omega
  rw [wordsVal_eq_val32, wordsVal_eq_val32, ← VG.Proof.Bignum.read_eq_val32,
    ← VG.Proof.Bignum.read_eq_val32]
  rw [F.read (r := ⟨base, montgomeryBytes⟩)
    (Offset.contains_base _ fit (by unfold montgomeryBytes at fit; omega)) apart
    (by unfold montgomeryBytes at fit; omega)]

theorem ParentContext.frame_word {s t : State} {base : Addr} {n m d : Nat} {rs : List Region}
    (_C : ParentContext base n m s) (F : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨base, montgomeryBytes⟩ r) (fit : d + 8 ≤ montgomeryBytes) :
    word t.mem base d = word s.mem base d :=
  F.readW (r := ⟨base, montgomeryBytes⟩) (Offset.contains_base _ fit (by
    unfold montgomeryBytes at fit; omega)) apart (by decide)

theorem parent_constants {s : State} {base : Addr} {bytes n m bits : Nat}
    (scr : Scr s base bytes) (capacity : montgomeryBytes ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes)
    (hn : 0 < n) (hn' : n ≤ 48) (modulus : wordsVal s.mem base (slot n 0) n = m)
    (gt : 1 < m) (odd : m % 2 = 1)
    (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n) (top : 2 ^ (bits - 1) ≤ m) :
    WP isa (montgomeryConstants n bits) s fun t =>
      ParentContext base n m t ∧
      wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n) * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 6) n = 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 7) n = m - 2 ^ (64 * n) % m ∧
      MontgomerySetupFrame base (s.gpr .esp) n s t ∧ Keeps powerClob s t := by
  have narrow := workspace_prefix scr capacity
  have roomN : CallRoom ((parentState base s).gpr .esp) base montgomeryBytes :=
    ⟨room.low, room.apart.sub_right (Region.sub_prefix capacity)⟩
  have write := workspace_prefix_covers scr capacity
  have read : Covers (s.rd ++ [⟨base, montgomeryBytes⟩]) (s.rd ++ s.wr) :=
    Covers.append (Covers.refl _) write
  refine WP.mono (workspace_wp (montgomery_constants narrow roomN hn hn' modulus gt odd
    bitsLow bitsHigh top) read write) fun t ⟨u, ⟨C, ordinary, rr, one, minus, F, K⟩, eq⟩ => ?_
  subst eq
  have state : parentState base (u.withRegions s.rd s.wr) = u := by
    change u.withRegions s.rd [⟨base, montgomeryBytes⟩] = u
    have urd : u.rd = s.rd := K.2.1
    have uwr : u.wr = [⟨base, montgomeryBytes⟩] := K.2.2
    rw [← urd, ← uwr, State.withRegions_self]
  refine ⟨by change Context n m base montgomeryBytes (parentState base _); rw [state]; exact C,
    ordinary, rr, one, minus, F, ?_⟩
  exact ⟨K.1, rfl, rfl⟩

end VG.Proof.Dsa.X86.Generation
