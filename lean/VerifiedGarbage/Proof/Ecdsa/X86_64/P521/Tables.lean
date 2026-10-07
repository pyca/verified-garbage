import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P521.Comb7Shape

/-!
# ECDSA over P-521 on x86-64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `VG_P521_COMB`, not wrapping
around, and apart from the writable regions and the return address; their
length (`p521W_length`, from the tables' shape alone) and region
(`p521_constRegions`); and a memory holding them, for the contracts'
witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.X86_64.P521

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (p521 CombData)

/-- P-521's comb. -/
abbrev p521d : CombData := ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false⟩

theorem p521_comb : p521.comb = some p521d := rfl

/-- The words of P-521's tables. -/
abbrev p521W : List (BitVec 64) := p521.combWords p521d

theorem p521_combConsts : p521.combConsts = [("VG_P521_COMB", p521W)] := rfl

/-- The comb's tables at the static `VG_P521_COMB`, held, not wrapping around,
and apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p521W.length, s.mem.readW (s.syms "VG_P521_COMB" + BitVec.ofNat 64 (8 * i)) 64 = p521W.getD i 0) ∧
  (s.syms "VG_P521_COMB").toNat + 764928 ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P521_COMB", 764928⟩ r

theorem p521_tbl_len : Impl.P521.p521Comb7.length = 83 :=
  Proof.P521.p521Comb7_length

theorem p521_tbl_lenH : ∀ j < 83, (Impl.P521.p521Comb7.getD j []).length = 64 :=
  Proof.P521.p521Comb7_rows

/-- `p521W` has `83 · 64 · 18` words. -/
theorem p521W_length : p521W.length = 95616 :=
  (Proof.Weierstrass.tcombWords_length (n := p521.n) (R := p521.R) (p := p521.C.p)
    (H := 64) (tbl := Impl.P521.p521Comb7) p521_tbl_len p521_tbl_lenH).trans rfl

theorem constRegions_single (f : String → BitVec 64) (n : String) (w : List (BitVec 64)) :
    Abi.constRegions f [(n, w)] = [⟨f n, 8 * w.length⟩] := rfl

/-- The tables' region, `8 · 95616` bytes at the static's address. The proofs
rewrite with this rather than unfold `Abi.constRegions`: the kernel evaluates
closed arithmetic such as `8 * p521W.length` when it compares two forms of
it, which would build the tables' 95616 words. -/
theorem p521_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_P521_COMB", p521W)] = [⟨f "VG_P521_COMB", 764928⟩] := by
  rw [constRegions_single, p521W_length]

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p521W

theorem satMem_held : ∀ i < p521W.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p521W.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p521W_length]; omega)

end VG.Proof.Ecdsa.X86_64.P521
