import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldSchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldPacked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedResult_field (a b : BitVec 128) (w : Poly) {len start : Nat}
    (hl : len=1 ∨ len=2) (hstart : start+8≤256) (second : Bool) (root : Nat → Nat)
    {e : Nat} (he : e<4) {bound : Int} (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound)
    (hf : ∀ i<8,ofInt (pairWord a b i).toInt=w[start+i]!) :
    ofInt (vword (packedResult len second a b (fun e => (negZetaNat (root e) : Int))) e).toInt=
      (InverseTraversal.run (InverseTraversal.packedSchedule start len root) w)[start+(if second then 4 else 0)+e]! := by
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega
  have hd := packed_indices hl hi
  rw [packedResult_int a b hl second _ he hb hs hv,Nat.add_assoc,
    InverseTraversal.packedSchedule_get w hl hstart hi]
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc,ofInt_add,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc]
  · rw [ite_eq_right hc,ite_eq_right hc,fastMul_field,ofInt_sub,
      InverseTraversal.ofInt_negZetaNat,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc,Fin.mul_comm]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
