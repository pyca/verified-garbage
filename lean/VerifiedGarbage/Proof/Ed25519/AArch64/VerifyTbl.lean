module

public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.ConstMem
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 verification on AArch64: the cached `-[1]B … -[15]B` in a static

Untrusted: everything here is checked by Lean. The words of the static `bSym`
(`bWords`), as a contract states them (`BHeld`) and as the copy into the
working space reads them (`BTblAt`), and a memory holding them for contracts'
witnesses (`bSatMem`). Nothing here evaluates the table: each lemma holds for
its words by their definition (`bWord`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem bWords_length : bWords.length = 240 := by simp [bWords]

theorem bWords_getD {i : Nat} (hi : i < 240) : bWords.getD i 0 = bWord i := by
  simp [bWords, List.getD_eq_getElem?_getD, hi]

theorem bConsts_eq : bConsts = [(bSym, bWords)] := rfl

/-- Word `w` of coordinate `c` of entry `j`. -/
theorem bWord_eq (j c w : Nat) (hc : c < 4) (hw : w < 4) :
    bWord (16 * j + 4 * c + w) = BitVec.ofNat 64
      ((pointCoord (Impl.Ed25519.negBaseCached j) c).val / 2 ^ (64 * w)) := by
  unfold bWord
  rw [show (16 * j + 4 * c + w) / 16 = j by omega, show (16 * j + 4 * c + w) / 4 % 4 = c by omega,
    show (16 * j + 4 * c + w) % 4 = w by omega]

/-- The static, in `s`, as a contract states it: its words, not wrapping around, apart from the
regions `wr`. -/
def BHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0) ∧
  (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r

/-- The static's words at `T` in `m`. -/
def BWords (T : Addr) (m : Mem) : Prop :=
  ∀ i < 240, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0

/-- The static at `T`: readable, beyond the working space at `base`, word `i` its `bWord i`. -/
structure BTblAt (s : State) (base T : Addr) : Prop where
  rd : ∀ i < 240, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * i)) 8
  far : ∀ i < 1920, 8192 ≤ ofs base (T + BitVec.ofNat 64 i)
  val : ∀ i < 240, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = bWord i

/-- The static survives what keeps the regions and the memory beyond the working space. -/
theorem BTblAt.of_far {s t : State} {base T : Addr} (h : BTblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x) :
    BTblAt t base T :=
  ⟨fun i hi => hrw ▸ h.rd i hi, h.far, fun i hi => by
    rw [← h.val i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h.far _ (by omega)⟩

/-- The static, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem BHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : BHeld s wr)
    (hrd : (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : BTblAt s base (s.syms bSym) := by
  obtain ⟨held, fit, dj⟩ := h
  refine ⟨fun i hi => ⟨_, hrd, Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => ?_,
    fun i hi => by rw [held i hi, bWords_getD hi]⟩
  refine Nat.le_of_not_lt fun hlt => dj _ hsc _
    (Offset.contains_base _ (d := i) (n := 1) (k := 1920) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at hlt; omega

/-- The memory of the contracts' witnesses: the static at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the table). -/
@[irreducible] def bSatMem : Mem := constMem 0x100000 bWords

theorem bSatMem_held : ∀ i < 240,
    bSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0 := by
  unfold bSatMem
  intro i hi
  exact constMem_held _ _ (by rw [bWords_length]; omega) i (by rw [bWords_length]; exact hi)

end VG.Proof.Ed25519.AArch64
