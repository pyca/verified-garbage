import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-- The inverse butterfly reduces only its difference branch. Its sum is
kept in signed form until the final compensated scaling. -/
def pair (a b z : Int) : Int × Int := (a+b, fastMul (a-b) z)

theorem pair_bounds {a b z bound : Int} (hq : 8380417 ≤ bound)
    (hsafe : 2*bound < 2147483648)
    (ha : -bound ≤ a ∧ a ≤ bound) (hb : -bound ≤ b ∧ b ≤ bound) :
    (-2*bound ≤ (pair a b z).1 ∧ (pair a b z).1 ≤ 2*bound) ∧
    (-2*bound ≤ (pair a b z).2 ∧ (pair a b z).2 ≤ 2*bound) := by
  have hm := fastMul_bounds (x := a-b) (z := z) (by omega) (by omega)
  dsimp only [pair]
  omega

theorem pair_word (a b : BitVec 32) (z : Int) {bound : Int}
    (hq : 8380417 ≤ bound) (hsafe : 2*bound < 2147483648)
    (ha : -bound ≤ a.toInt ∧ a.toInt ≤ bound)
    (hb : -bound ≤ b.toInt ∧ b.toInt ≤ bound) :
    (a+b).toInt = (pair a.toInt b.toInt z).1 ∧
    (fastMulWord (a-b) z).toInt = (pair a.toInt b.toInt z).2 := by
  dsimp only [pair]
  constructor
  · exact addWord_int a b (by omega) (by omega)
  · rw [fastMulWord_int,subWord_int a b (by omega) (by omega)]

theorem pair_field (a b z : Int) :
    ofInt (pair a b z).1 = ofInt a+ofInt b ∧
    ofInt (pair a b z).2 = (ofInt a-ofInt b)*ofInt z := by
  exact ⟨ofInt_add a b, (fastMul_field (a-b) z).trans (congrArg (· * ofInt z) (ofInt_sub a b))⟩

/-- The selected final multiplier always leaves its result in (-q,2q),
so sign correction followed by one subtraction is sufficient. -/
def canonical (x : Int) : Int :=
  let a := if x<0 then x+8380417 else x
  if a<8380417 then a else a-8380417

theorem canonical_bounds {x : Int} (hl : -8380417<x) (hh : x<2*8380417) :
    0≤canonical x ∧ canonical x<8380417 := by
  unfold canonical
  split <;> dsimp only <;> split <;> omega

theorem canonical_mod (x : Int) : canonical x % 8380417 = x % 8380417 := by
  unfold canonical
  split <;> dsimp only <;> split <;> omega

theorem canonical_field (x : Int) : ofInt (canonical x) = ofInt x := by
  unfold ofInt
  change Fin.ofNat q (canonical x % 8380417).toNat = Fin.ofNat q (x % 8380417).toNat
  rw [canonical_mod]

theorem scaled_canonical_bounds (x : BitVec 32) (z : Int) :
    0≤canonical (fastMul x.toInt z) ∧ canonical (fastMul x.toInt z)<8380417 :=
  canonical_bounds (fastMul_bounds (z := z) (BitVec.le_toInt x) (BitVec.toInt_lt (x := x))).1
    (fastMul_bounds (z := z) (BitVec.le_toInt x) (BitVec.toInt_lt (x := x))).2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
