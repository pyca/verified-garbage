import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P384.Comb7Shape

/-!
# ECDSA over P-384 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `p384.tsym`, not wrapping
around, and apart from the writable regions; their length
(`p384_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.AArch64.P384

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64 (p384)

/-- The comb's tables at the static `p384.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p384.combWords.length,
    s.mem.readW (s.syms p384.tsym + BitVec.ofNat 64 (8 * i)) 64 = p384.combWords.getD i 0) ∧
  (s.syms p384.tsym).toNat + 8 * p384.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms p384.tsym, 8 * p384.combWords.length⟩ r

theorem p384_combConsts : p384.combConsts = [(p384.tsym, p384.combWords)] := rfl

theorem p384_tsym : p384.tsym = "VG_P384_COMB" := rfl

theorem p384_tbl_len : Impl.P384.p384Comb7.length = 55 :=
  Proof.P384.p384Comb7_length

theorem p384_tbl_lenH : ∀ j < 55, (Impl.P384.p384Comb7.getD j []).length = 64 :=
  Proof.P384.p384Comb7_rows

/-- `p384.combWords` has `55 · 64 · 12` words. -/
theorem p384_combWords_length : p384.combWords.length = 42240 :=
  (Proof.Weierstrass.tcombWords_length (n := p384.n) (R := p384.R) (p := p384.C.p)
    (H := 64) (tbl := p384.tbl) p384_tbl_len p384_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p384.combWords

theorem satMem_held : ∀ i < p384.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p384_combWords_length]; omega)

end VG.Proof.Ecdsa.AArch64.P384
