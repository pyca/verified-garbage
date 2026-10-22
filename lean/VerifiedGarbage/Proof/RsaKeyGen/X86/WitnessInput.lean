module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # Each remaining entropy block is a disjoint, readable native import source -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessInput
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

/-- The `count` native words at offset `used` of the entropy, into the witness array. -/
def geometryAt (g : Geometry) (rand : BitVec 32) (used count : Nat) : Import.Geometry :=
  ⟨rand + BitVec.ofNat 32 used, BitVec.ofNat 32 (g.W.toNat + g.array 6), count⟩

def geometry (g : Geometry) (rand : BitVec 32) (used : Nat) : Import.Geometry := geometryAt g rand used g.words

theorem source_address {rand : BitVec 32} {used : Nat} (fit : rand.toNat + used < 2 ^ 32) :
    (rand + BitVec.ofNat 32 used).setWidth 64 = off (rand.setWidth 64) used := by
  change addr rand used = _
  exact addr_eq fit

theorem destination_pointer {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used count : Nat} :
    (geometryAt g rand used count).dst = s.gpr .edi + BitVec.ofNat 32 (g.array 6) := by
  have arrBound : g.array 6 < 2 ^ 32 := by
    have := S.nowrap
    have a := v.arrayFit (j := 6) (by decide)
    have := v.minWidth
    unfold Geometry.words at a
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [geometryAt, BitVec.toNat_ofNat, BitVec.toNat_add, S.edi_toNat, Nat.mod_eq_of_lt arrBound]

theorem destination_address {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used count : Nat} :
    (geometryAt g rand used count).dst.setWidth 64 = off g.W (g.array 6) := by
  rw [destination_pointer v S]
  have fit : g.array 6 < g.L := by
    have a := v.arrayFit (j := 6) (by decide)
    have := v.minWidth
    unfold Geometry.words at a
    omega
  exact S.ea fit

theorem context_okAt {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used length count : Nat} (noWrap : rand.toNat + length ≤ 2 ^ 32)
    (positive : 0 < count) (wide : count ≤ g.words) (enough : used + 4 * count ≤ length)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) length)
    (separate : (⟨rand.setWidth 64, length⟩ : Region).Disjoint ⟨g.W, g.L⟩) :
    Import.Context (geometryAt g rand used count) s := by
  have sourceFit : rand.toNat + used < 2 ^ 32 := by omega
  have sourceAddr := source_address sourceFit
  have destAddr := destination_address v S (rand := rand) (used := used) (count := count)
  have destPtr := destination_pointer v S (rand := rand) (used := used) (count := count)
  have hw : g.words = 2 * g.w := rfl
  apply Import.context_of_regions
  · exact positive
  · change (rand + BitVec.ofNat 32 used).toNat + 4 * count ≤ 2 ^ 32
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := used) (by omega), Nat.mod_eq_of_lt sourceFit]
    omega
  · change (geometryAt g rand used count).dst.toNat + 4 * count ≤ 2 ^ 32
    rw [destPtr, BitVec.toNat_add, S.edi_toNat, BitVec.toNat_ofNat]
    have bound : g.W.toNat + g.array 6 < 2 ^ 32 := by
      have := S.nowrap; have := v.arrayFit (j := 6) (by decide); have := v.minWidth; omega
    rw [Nat.mod_eq_of_lt (a := g.array 6) (by omega), Nat.mod_eq_of_lt bound]
    have := S.nowrap
    have := v.arrayFit (j := 6) (by decide)
    omega
  · change InRegions (s.rd ++ s.wr) ((rand + BitVec.ofNat 32 used).setWidth 64) (4 * count)
    rw [sourceAddr]
    obtain ⟨r, member, access⟩ := readable
    exact ⟨r, member, Import.contains_offset access enough⟩
  · change InRegions s.wr ((geometryAt g rand used count).dst.setWidth 64) (4 * count)
    rw [destAddr]
    exact S.write (by have := v.arrayFit (j := 6) (by decide); omega)
  · change (⟨(rand + BitVec.ofNat 32 used).setWidth 64, 4 * count⟩ : Region).Disjoint
      ⟨(geometryAt g rand used count).dst.setWidth 64, 4 * count⟩
    rw [sourceAddr, destAddr]
    exact (separate.sub_left (Offset.sub_base _ enough)).sub_right
      (Offset.sub_base _ (by have := v.arrayFit (j := 6) (by decide); omega))

theorem context_ok {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used length : Nat} (noWrap : rand.toNat + length ≤ 2 ^ 32)
    (enough : used + 8 * g.w ≤ length)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) length)
    (separate : (⟨rand.setWidth 64, length⟩ : Region).Disjoint ⟨g.W, g.L⟩) :
    Import.Context (geometry g rand used) s :=
  context_okAt v S noWrap (by have := v.minWidth; unfold Geometry.words; omega) (Nat.le_refl _)
    (by unfold Geometry.words; omega) readable separate

end VG.Proof.RsaKeyGen.X86.WitnessInput
