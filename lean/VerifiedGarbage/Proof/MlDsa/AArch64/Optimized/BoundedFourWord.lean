import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMath

/-! Exact finite half-byte arithmetic used by the vector parser. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- The lane value after the eta-specific reduction and unsigned minimum. -/
def valueWord (η : Nat) (x : BitVec 32) : BitVec 32 :=
 let r := if η=2 then x-((x*13#32)>>>6)*5#32 else x
 let v := BitVec.ofNat 32 (q+η)-r
 if v.toNat ≤ (v-8380417#32).toNat then v else v-8380417#32

/-- The acceptance bit before multiplication by the lane's mask weight. -/
def acceptWord (η : Nat) (x : BitVec 32) : BitVec 32 :=
 (x-BitVec.ofNat 32 (rbB η))>>>31

theorem valueWord_two : ∀ b < 16,
    valueWord 2 (BitVec.ofNat 32 b) = BitVec.ofNat 32 (ofInt (rbC 2 b)).val := by decide

theorem valueWord_four : ∀ b < 16,
    valueWord 4 (BitVec.ofNat 32 b) = BitVec.ofNat 32 (ofInt (rbC 4 b)).val := by decide

theorem valueWord_eq {η : Nat} (hη : η=2 ∨ η=4) {b : Nat} (hb : b<16) :
    valueWord η (BitVec.ofNat 32 b) = BitVec.ofNat 32 (ofInt (rbC η b)).val := by
  rcases hη with rfl | rfl
  · exact valueWord_two b hb
  · exact valueWord_four b hb

theorem acceptWord_two : ∀ b < 16,
    acceptWord 2 (BitVec.ofNat 32 b) = BitVec.ofNat 32 (halfByteOk 2 b) := by decide

theorem acceptWord_four : ∀ b < 16,
    acceptWord 4 (BitVec.ofNat 32 b) = BitVec.ofNat 32 (halfByteOk 4 b) := by decide

theorem acceptWord_eq {η : Nat} (hη : η=2 ∨ η=4) {b : Nat} (hb : b<16) :
    acceptWord η (BitVec.ofNat 32 b) = BitVec.ofNat 32 (halfByteOk η b) := by
  rcases hη with rfl | rfl
  · exact acceptWord_two b hb
  · exact acceptWord_four b hb

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
