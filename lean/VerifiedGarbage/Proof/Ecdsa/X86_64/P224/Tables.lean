import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords

/-!
# ECDSA over P-224 on x86-64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `VG_P224_COMB`, not wrapping
around, and apart from the writable regions and the return address; their
length (`p224W_length`, from the tables' shape alone); and a memory holding
them, for the contracts' witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.X86_64.P224

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (p224 CombData)

/-- P-224's comb. -/
abbrev p224d : CombData := ⟨7, Impl.P224.p224Comb7, Impl.P224.p224Comb7Start, "VG_P224_COMB", false⟩

theorem p224_comb : p224.comb = some p224d := rfl

/-- The words of P-224's tables. -/
abbrev p224W : List (BitVec 64) := p224.combWords p224d

theorem p224_combConsts : p224.combConsts = [("VG_P224_COMB", p224W)] := rfl

/-- The comb's tables at the static `VG_P224_COMB`, held, not wrapping around,
and apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p224W.length, s.mem.readW (s.syms "VG_P224_COMB" + BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0) ∧
  (s.syms "VG_P224_COMB").toNat + 8 * p224W.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P224_COMB", 8 * p224W.length⟩ r

theorem p224_tbl_len : Impl.P224.p224Comb7.length = 37 := by decide

theorem p224_tbl_lenH : ∀ j < 37, (Impl.P224.p224Comb7.getD j []).length = 64 := by decide

/-- `p224W` has `37 · 64 · 8` words. -/
theorem p224W_length : p224W.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := p224.n) (R := p224.R) (p := p224.C.p)
    (H := 64) (tbl := Impl.P224.p224Comb7) p224_tbl_len p224_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p224W

theorem satMem_held : ∀ i < p224W.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p224W_length]; omega)

end VG.Proof.Ecdsa.X86_64.P224
