import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldPackedField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedValues_field (v : Vector (BitVec 128) 8) (w : Poly) {g len u : Nat}
    (hg : g<4) (hl : len=1 ∨ len=2) (hu : u<8) (root : Nat → Nat) {bound : Int}
    (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ j<8, -bound≤(pairWord v[2*g] v[2*g+1] j).toInt ∧
      (pairWord v[2*g] v[2*g+1] j).toInt≤bound)
    (hf : InnerBankField u v w) :
    InnerBankField u (packedValues v ⟨2*g,by omega⟩ ⟨2*g+1,by omega⟩ len
      (fun e => (negZetaNat (root e) : Int)))
      (InverseTraversal.run (InverseTraversal.packedSchedule (32*u+8*g) len root) w) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega)
      true root he hb hs hv
      (fun i hi => pairWord_field v w hg hf hi)
    simpa only [ite_true,Traversal.innerLoc,← hj,show 32*u+4*(2*g+1)+e=32*u+8*g+4+e by omega] using h
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega)
        false root he hb hs hv
        (fun i hi => pairWord_field v w hg hf hi)
      simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Traversal.innerLoc,← hi,
        show 4*(2*g)=8*g by omega] using h
    · rw [ite_eq_right hi,InverseTraversal.packedSchedule_outside w hl (by omega)
        (by unfold Traversal.innerLoc; omega) (by unfold Traversal.innerLoc; omega),hf i e he]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
