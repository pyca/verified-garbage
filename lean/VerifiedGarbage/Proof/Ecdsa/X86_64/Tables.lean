import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords

/-!
# ECDSA over P-256 on x86-64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `VG_P256_COMB`, not wrapping
around, and apart from the writable regions and the return address; their
length (`p256W_length`, from the tables' shape alone); and a memory holding
them, for the contracts' witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (p256 CombData)

/-- P-256's comb. -/
abbrev p256d : CombData := ⟨7, Impl.P256.p256Comb7, Impl.P256.p256Comb7Start, "VG_P256_COMB"⟩

theorem p256_comb : p256.comb = some p256d := rfl

/-- The words of P-256's tables. -/
abbrev p256W : List (BitVec 64) := p256.combWords p256d

theorem p256_combConsts : p256.combConsts = [("VG_P256_COMB", p256W)] := rfl

/-- The comb's tables at the static `VG_P256_COMB`, held, not wrapping around,
and apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p256W.length, s.mem.readW (s.syms "VG_P256_COMB" + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0) ∧
  (s.syms "VG_P256_COMB").toNat + 8 * p256W.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P256_COMB", 8 * p256W.length⟩ r

theorem p256_tbl_len : Impl.P256.p256Comb7.length = 37 := by decide

theorem p256_tbl_lenH : ∀ j < 37, (Impl.P256.p256Comb7.getD j []).length = 64 := by decide

/-- `p256W` has `37 · 64 · 8` words. -/
theorem p256W_length : p256W.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := p256.n) (R := p256.R) (p := p256.C.p)
    (H := 64) (tbl := Impl.P256.p256Comb7) p256_tbl_len p256_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p256W

theorem satMem_held : ∀ i < p256W.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p256W_length]; omega)

end VG.Proof.Ecdsa.X86_64
