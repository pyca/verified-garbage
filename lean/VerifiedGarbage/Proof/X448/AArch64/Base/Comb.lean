import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# X448 of the base point on AArch64: the comb's tables in a static

Untrusted: everything here is checked by Lean. The words of the static
`combSym`, as a contract states them (`CombHeld`), and a memory holding them for
contracts' witnesses (`satMem`). Kept apart from the selection's proof, so that
the callers' contracts need none of its algebra.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64.Base

theorem combWords_length : combWords.length = 57 * 128 := by simp [combWords]

theorem combWords_getD {i : Nat} (hi : i < 57 * 128) : combWords.getD i 0 = combWord i := by
  simp [combWords, List.getD_eq_getElem?_getD, hi]

/-- The comb's tables, the static `combSym`, in `s`, as a contract states them: its words, not
wrapping around, apart from the regions `wr`. -/
def CombHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < combWords.length,
    s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0) ∧
  (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The memory of the contract's witness: the tables at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 combWords

theorem satMem_held : ∀ i < combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [combWords_length]; omega)

end VG.Proof.X448.AArch64.Base
