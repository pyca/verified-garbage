import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P224.Comb7Shape

/-!
# ECDSA over P-224 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `p224.tsym`, not wrapping
around, and apart from the writable regions; their length
(`p224_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.AArch64.P224

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64 (p224)

/-- The comb's tables at the static `p224.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p224.combWords.length,
    s.mem.readW (s.syms p224.tsym + BitVec.ofNat 64 (8 * i)) 64 = p224.combWords.getD i 0) ∧
  (s.syms p224.tsym).toNat + 8 * p224.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms p224.tsym, 8 * p224.combWords.length⟩ r

theorem p224_combConsts : p224.combConsts = [(p224.tsym, p224.combWords)] := rfl

theorem p224_tsym : p224.tsym = "VG_P224_COMB" := rfl

theorem p224_tbl_len : Impl.P224.p224Comb7.length = 37 :=
  Proof.P224.p224Comb7_length

theorem p224_tbl_lenH : ∀ j < 37, (Impl.P224.p224Comb7.getD j []).length = 64 :=
  Proof.P224.p224Comb7_rows

/-- `p224.combWords` has `37 · 64 · 8` words. -/
theorem p224_combWords_length : p224.combWords.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := p224.n) (R := p224.R) (p := p224.C.p)
    (H := 64) (tbl := p224.tbl) p224_tbl_len p224_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p224.combWords

theorem satMem_held : ∀ i < p224.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p224_combWords_length]; omega)

end VG.Proof.Ecdsa.AArch64.P224
