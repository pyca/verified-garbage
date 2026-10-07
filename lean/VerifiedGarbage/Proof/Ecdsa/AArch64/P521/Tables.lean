import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P521.Comb7Shape

/-!
# ECDSA over P-521 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `p521.tsym`, not wrapping
around, and apart from the writable regions; their length
(`p521_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.AArch64.P521

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64 (p521)

/-- The comb's tables at the static `p521.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p521.combWords.length,
    s.mem.readW (s.syms p521.tsym + BitVec.ofNat 64 (8 * i)) 64 = p521.combWords.getD i 0) ∧
  (s.syms p521.tsym).toNat + 8 * p521.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms p521.tsym, 8 * p521.combWords.length⟩ r

theorem p521_combConsts : p521.combConsts = [(p521.tsym, p521.combWords)] := rfl

theorem p521_tsym : p521.tsym = "VG_P521_COMB" := rfl

theorem p521_tbl_len : Impl.P521.p521Comb7.length = 83 :=
  Proof.P521.p521Comb7_length

theorem p521_tbl_lenH : ∀ j < 83, (Impl.P521.p521Comb7.getD j []).length = 64 :=
  Proof.P521.p521Comb7_rows

/-- `p521.combWords` has `83 · 64 · 18` words. -/
theorem p521_combWords_length : p521.combWords.length = 95616 :=
  (Proof.Weierstrass.tcombWords_length (n := p521.n) (R := p521.R) (p := p521.C.p)
    (H := 64) (tbl := p521.tbl) p521_tbl_len p521_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p521.combWords

theorem satMem_held : ∀ i < p521.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p521.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p521_combWords_length]; omega)

end VG.Proof.Ecdsa.AArch64.P521
