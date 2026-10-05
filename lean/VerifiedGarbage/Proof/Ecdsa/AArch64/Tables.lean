import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombWords

/-!
# ECDSA over P-256 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `p256.tsym`, not wrapping
around, and apart from the writable regions; their length
(`p256_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64 (p256)

/-- The comb's tables at the static `p256.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p256.combWords.length,
    s.mem.readW (s.syms p256.tsym + BitVec.ofNat 64 (8 * i)) 64 = p256.combWords.getD i 0) ∧
  (s.syms p256.tsym).toNat + 8 * p256.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms p256.tsym, 8 * p256.combWords.length⟩ r

theorem p256_combConsts : p256.combConsts = [(p256.tsym, p256.combWords)] := rfl

theorem p256_tsym : p256.tsym = "VG_P256_COMB" := rfl

theorem p256_tbl_len : Impl.P256.p256Comb7.length = 37 := by decide

theorem p256_tbl_lenH : ∀ j < 37, (Impl.P256.p256Comb7.getD j []).length = 64 := by decide

/-- `p256.combWords` has `37 · 64 · 8` words. -/
theorem p256_combWords_length : p256.combWords.length = 18944 :=
  (Proof.Weierstrass.AArch64.tcombWords_length (n := p256.n) (R := p256.R) (p := p256.C.p)
    (H := 64) (tbl := p256.tbl) p256_tbl_len p256_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p256.combWords

theorem satMem_held : ∀ i < p256.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p256_combWords_length]; omega)

end VG.Proof.Ecdsa.AArch64
