module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # The precise write footprint of a fixed-window table scan -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86 VG.Proof.Mont

def scanWrites (g : Geometry) : List (Nat × Nat) := [(sEq1, 4), (g.array aX, 4 * g.words)]

theorem scanFrame_table {g : Geometry} (v : g.Valid) {m m' : Mem}
    (nowrap : g.W.toNat + g.L ≤ 2 ^ 32) (O : Outs g.W (scanWrites g) m m')
    {j : Nat} (index : j < 16) :
    val32 m' g.W (g.array (aTable + j)) g.words = val32 m g.W (g.array (aTable + j)) g.words := by
  have header := v.arrayHeader (aTable + j)
  have sep := g.arrayBefore (show aX < aTable + j by unfold aX aTable; omega)
  have fit := v.arrayFit (j := aTable + j) (by unfold aTable; omega)
  refine O.val32 ?_ (by omega)
  intro r hr
  simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right; unfold sEq1; omega
  · exact Or.inr sep

theorem scanFrame_value {g : Geometry} (v : g.Valid) {m m' : Mem}
    (O : Outs g.W (scanWrites g) m m') :
    m'.readW (off g.W sValue) 32 = m.readW (off g.W sValue) 32 := by
  have header := v.arrayHeader aX
  have V := O.val32 (d := sValue) (k := 1) (by
    intro r hr
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; decide
    · left; unfold sValue; omega) (by unfold sValue; decide)
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using V

end VG.Proof.MillerRabin.X86
