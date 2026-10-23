module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64.Comb
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords

/-!
# ECDSA over brainpoolP256r1 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `combCfg.tsym`, not wrapping
around, and apart from the writable regions; their length
(`combCfg_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64.BrainpoolP256r1 (combCfg)

/-- The comb's tables at the static `combCfg.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < combCfg.combWords.length,
    s.mem.readW (s.syms combCfg.tsym + BitVec.ofNat 64 (8 * i)) 64 = combCfg.combWords.getD i 0) ∧
  (s.syms combCfg.tsym).toNat + 8 * combCfg.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms combCfg.tsym, 8 * combCfg.combWords.length⟩ r

theorem combCfg_combConsts : combCfg.combConsts = [(combCfg.tsym, combCfg.combWords)] := rfl

theorem combCfg_tsym : combCfg.tsym = "VG_BRAINPOOLP256R1_COMB7" := rfl

theorem combCfg_tbl_len : Impl.BrainpoolP256r1.comb7.length = 37 :=
  by decide +kernel

theorem combCfg_tbl_lenH : ∀ j < 37, (Impl.BrainpoolP256r1.comb7.getD j []).length = 64 :=
  by decide +kernel

/-- `combCfg.combWords` has `37 · 64 · 8` words. -/
theorem combCfg_combWords_length : combCfg.combWords.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := combCfg.n) (R := combCfg.R) (p := combCfg.C.p)
    (H := 64) (tbl := combCfg.tbl) combCfg_tbl_len combCfg_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 combCfg.combWords

theorem satMem_held : ∀ i < combCfg.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combCfg.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [combCfg_combWords_length]; omega)

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb
