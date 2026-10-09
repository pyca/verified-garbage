import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedBank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem pairWord_bound (v : Vector (BitVec 128) 8) {g : Nat} (hg : g<4) {bound : Int}
    (hv : BankBound v bound) {i : Nat} (hi : i<8) :
    -bound≤(pairWord v[2*g] v[2*g+1] i).toInt ∧
      (pairWord v[2*g] v[2*g+1] i).toInt≤bound := by
  unfold pairWord
  split
  · exact hv ⟨2*g,by omega⟩ i ‹_›
  · exact hv ⟨2*g+1,by omega⟩ (i-4) (by omega)

theorem pairWord_field (v : Vector (BitVec 128) 8) (w : Poly) {g u : Nat} (hg : g<4)
    (hf : InnerBankField u v w) {i : Nat} (hi : i<8) :
    ofInt (pairWord v[2*g] v[2*g+1] i).toInt = w[32*u+8*g+i]! := by
  unfold pairWord
  split
  · have h := hf ⟨2*g,by omega⟩ i ‹_›
    simpa only [Traversal.innerLoc,show 4*(2*g)=8*g by omega] using h
  · have h := hf ⟨2*g+1,by omega⟩ (i-4) (by omega)
    simpa only [Traversal.innerLoc,show 32*u+4*(2*g+1)+(i-4)=32*u+8*g+i by omega] using h

theorem packedValues_bound (v : Vector (BitVec 128) 8) {g len : Nat} (hg : g<4)
    (hl : len=1 ∨ len=2) (z : Nat → Int) {bound : Int} (hb : 0≤bound)
    (hs : bound+16760834<2147483648) (hv : BankBound v bound) :
    BankBound (packedValues v ⟨2*g,by omega⟩ ⟨2*g+1,by omega⟩ len z) (bound+16760834) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    exact packedResult_bound _ _ hl true z he hb hs (fun i hi => pairWord_bound v hg hv hi)
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      exact packedResult_bound _ _ hl false z he hb hs (fun i hi => pairWord_bound v hg hv hi)
    · rw [ite_eq_right hi]
      have h := hv i e he
      omega

theorem packedValues_field (v : Vector (BitVec 128) 8) (w : Poly) {g len u : Nat}
    (hg : g<4) (hl : len=1 ∨ len=2) (hu : u<8) (root : Nat → Nat) {bound : Int}
    (hb : 0≤bound) (hs : bound+16760834<2147483648) (hv : BankBound v bound)
    (hf : InnerBankField u v w) :
    InnerBankField u (packedValues v ⟨2*g,by omega⟩ ⟨2*g+1,by omega⟩ len
      (fun e => (zetaNat (root e) : Int)))
      (Traversal.run (Traversal.packedSchedule (32*u+8*g) len root) w) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega)
      true root he hb hs (fun i hi => pairWord_bound v hg hv hi)
      (fun i hi => pairWord_field v w hg hf hi)
    simpa only [ite_true,Traversal.innerLoc,← hj,show 32*u+4*(2*g+1)+e=32*u+8*g+4+e by omega] using h
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega)
        false root he hb hs (fun i hi => pairWord_bound v hg hv hi)
        (fun i hi => pairWord_field v w hg hf hi)
      simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Traversal.innerLoc,← hi,
        show 4*(2*g)=8*g by omega] using h
    · rw [ite_eq_right hi,Traversal.packedSchedule_outside w hl (by omega)
        (by unfold Traversal.innerLoc; omega) (by unfold Traversal.innerLoc; omega),hf i e he]

end VG.Proof.MlDsa.AArch64.Optimized
