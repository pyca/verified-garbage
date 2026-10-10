import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P384.Comb7Shape

/-!
# ECDSA over P-384 on x86-64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `VG_P384_COMB`, not wrapping
around, and apart from the writable regions and the return address; their
length (`p384W_length`, from the tables' shape alone); and a memory holding
them, for the contracts' witnesses (`satMem`).
-/

namespace VG.Proof.Ecdsa.X86_64.P384

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (p384 CombData)

/-- P-384's comb. -/
abbrev p384d : CombData := ⟨7, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start, "VG_P384_COMB", false⟩

theorem p384_comb : p384.comb = some p384d := rfl

/-- The words of P-384's tables. -/
abbrev p384W : List (BitVec 64) := p384.combWords p384d

theorem p384_combConsts : p384.combConsts = [("VG_P384_COMB", p384W)] := rfl

/-- The comb's tables at the static `VG_P384_COMB`, held, not wrapping around,
and apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p384W.length, s.mem.readW (s.syms "VG_P384_COMB" + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0) ∧
  (s.syms "VG_P384_COMB").toNat + 8 * p384W.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P384_COMB", 8 * p384W.length⟩ r

theorem p384_tbl_len : Impl.P384.p384Comb7.length = 55 :=
  Proof.P384.p384Comb7_length

theorem p384_tbl_lenH : ∀ j < 55, (Impl.P384.p384Comb7.getD j []).length = 64 :=
  Proof.P384.p384Comb7_rows

/-- `p384W` has `55 · 64 · 12` words. -/
theorem p384W_length : p384W.length = 42240 :=
  (Proof.Weierstrass.tcombWords_length (n := p384.n) (R := p384.R) (p := p384.C.p)
    (H := 64) (tbl := Impl.P384.p384Comb7) p384_tbl_len p384_tbl_lenH).trans rfl

theorem constRegions_single (f : String → BitVec 64) (n : String) (w : List (BitVec 64)) :
    Abi.constRegions f [(n, w)] = [⟨f n, 8 * w.length⟩] := rfl

/-- The tables' region, `8 · 42240` bytes at the static's address. The proofs
rewrite with this rather than unfold `Abi.constRegions`: the kernel evaluates
closed arithmetic such as `8 * p384W.length` when it compares two forms of
it, which would build the tables' 42240 words. -/
theorem p384_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_P384_COMB", p384W)] = [⟨f "VG_P384_COMB", 337920⟩] := by
  rw [constRegions_single, p384W_length]

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p384W

theorem satMem_held : ∀ i < p384W.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p384W_length]; omega)

end VG.Proof.Ecdsa.X86_64.P384
