import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Copy

/-!
# The function's environment

What the function may assume (`Env`), and the facts about it and about the
loop's counters that the loop's proof (`Loop.lean`) uses.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame toNat_ofNat_of_le ecb_blocks)

/-- What the function may assume of the state it starts in: the schedule
readable, the `n` blocks of data and the scratch buffer writable, apart from
each other. -/
structure Env (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 384⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 1024⟩]
  keyData : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega

theorem Env.len {s : State} (E : Env s) : 8 * (s.gpr .x2).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp)

theorem Env.keyIn {s : State} (E : Env s) :
    ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  rw [E.rd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩

theorem blockAt_eq_of_readW {m m' : Mem} {p p' : Addr} (h : m'.readW p' 64 = m.readW p 64) :
    blockAt m' p' = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m' p' (n := 8) hi, ← Mem.extractLsb'_read m p (n := 8) hi]
  have e : ∀ (m : Mem) (p : Addr), m.read p 8 = m.readW p 64 := fun m p => by
    simp only [Mem.readW]; rfl
  rw [e, e, h]

theorem lsr7 (m : Nat) (hm : 8 * m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> 7 = BitVec.ofNat 64 (m / 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ofNat_ne_zero {m : Nat} (h : m < 2 ^ 64) (h0 : m ≠ 0) : BitVec.ofNat 64 m ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  simp at this
  omega

theorem eval_nonzero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m != (0 : BitVec 64)) = (m != 0)
    simp only [bne, beq_eq_false_iff_ne.mpr (ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

theorem eval_zero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr (ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

end VG.Proof.TripleDes.AArch64.BitslicedNeon
