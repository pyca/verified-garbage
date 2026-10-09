import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

def zBad (m : Mem) (p a : Addr) (B j e : Nat) : Bool :=
  decide (B≤normZq (ofInt (((coeffAt m p (4*j+e)).toNat:Int)+(coeffAt m a (4*j+e)).toInt)))

theorem addReduced_mask (a b : BitVec 32) (B : Nat) (ha : a.toNat<8380417)
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    normMask (reduceWord (a+b)) (BitVec.ofNat 32 B-1)
      (BitVec.ofNat 32 B+(BitVec.ofNat 32 B-1))=
      maskWord (decide (B≤normZq (ofInt ((a.toNat:Int)+b.toInt)))) := by
  have hlo : BitVec.ofNat 32 B-1=BitVec.ofNat 32 (B-1) := by bv_omega
  have hwidth : BitVec.ofNat 32 B+(BitVec.ofNat 32 B-1)=BitVec.ofNat 32 (2*B-1) := by bv_omega
  have hn := addReduced_norm a b B ha hb hB hB'
  unfold normMask maskWord
  rw [hwidth,hlo,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  by_cases h : B≤normZq (ofInt ((a.toNat:Int)+b.toInt))
  · rw [decide_eq_true h,ite_eq_left (by have := mt hn.mp (show ¬normZq (ofInt ((a.toNat:Int)+b.toInt))<B by omega); omega)]
    rfl
  · rw [decide_eq_false h,ite_eq_right (by have := hn.mpr (by omega); omega)]
    rfl

theorem zWords_current (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {j e : Nat} (hj : j<64) (he : e<4) :
    zWords (zRun m p a B j).mem p a j e=
      reduceWord (coeffAt m p (4*j+e)+coeffAt m a (4*j+e)) := by
  rw [zWords_coeff _ _ _ _ he,zRun_prefix m p a B hd (by omega) _ (by omega),ite_eq_right (by omega)]
  rw [coeffAt_frame (zRun_frame m p a B (by omega)) (by simpa using hd.symm) (by rw [n_eq]; omega)]

theorem zRun_flags (m : Mem) (p a : Addr) (B : Nat)
    (hd : (pR p).Disjoint (pR a)) (hB : 1≤B) (hB' : B≤524288)
    (ha : ∀k<256,(coeffAt m p k).toNat<8380417)
    (hb : ∀k<256,-8380417<(coeffAt m a k).toInt ∧ (coeffAt m a k).toInt<2*8380417)
    {j : Nat} (hj : j≤64) :
    ∀e<4,vword (zRun m p a (BitVec.ofNat 32 B) j).flags e=maskWord (flagBad (zBad m p a B) j e) := by
  induction j with
  | zero => intro e he; simp [zRun,flagBad,maskWord,vword]
  | succ j ih =>
    intro e he
    rw [zRun_next]
    simp only [zStep,laneVector_word _ he]
    rw [ih (by omega) e he,zWords_current m p a _ hd (by omega) he,
      addReduced_mask _ _ B (ha _ (by omega)) (hb _ (by omega)) hB hB',maskWord_or]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
