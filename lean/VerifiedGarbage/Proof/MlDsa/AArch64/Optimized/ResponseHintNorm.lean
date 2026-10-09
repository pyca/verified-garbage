import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFlags

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem hintCtAt_coeff (m : Mem) (a : Addr) (j : Nat) {e : Nat} (he : e<4) :
    hintCtAt m a j e=reduceWord (coeffAt m a (4*j+e)) := by
  unfold hintCtAt
  rw [show 16*j=4*(4*j) by omega]
  change reduceWord (vword (m.read (coeffAddr a (4*j)) 16) e)=_
  rw [VG.AArch64.vword_read16 _ _ he,coeffAddr_add]
  rfl

theorem hintCtAt_original (m : Mem) (B : BitVec 32) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) {j e : Nat} (hj : j<64) (he : e<4) :
    hintCtAt (hintRun m B p a h j).mem a j e=reduceWord (coeffAt m a (4*j+e)) := by
  rw [hintCtAt_coeff _ _ _ he]
  congr 1
  exact coeffAt_frame (hintRun_frame m p a h B (by omega)) (by simpa using hd.symm) (by change 4*j+e<256; omega)

def hintNormTest (m : Mem) (a : Addr) (B : BitVec 32) (k : Nat) : Prop :=
  (reduceWord (coeffAt m a k)+(B-1)).toNat<(B+(B-1)).toNat

theorem hintLaneFailure_false (m : Mem) (B : BitVec 32) (p a h : Addr)
    (hd : (pR p).Disjoint (pR a)) {j e : Nat} (hj : j≤64) (he : e<4) :
    hintLaneFailure m B p a h e j=false ↔ ∀i<j,hintNormTest m a B (4*i+e) := by
  induction j with
  | zero => simp [hintLaneFailure]
  | succ j ih =>
    rw [hintLaneFailure,Bool.or_eq_false_iff,ih (by omega),hintCtAt_original m B p a h hd (by omega) he]
    simp only [decide_eq_false_iff_not,Nat.not_le]
    change (_ ∧ hintNormTest m a B (4*j+e)) ↔ _
    constructor
    · rintro ⟨hp,hj⟩ i hi
      by_cases h : i<j
      · exact hp i h
      · have : i=j := by omega
        subst i; exact hj
    · intro hp; exact ⟨fun i hi => hp i (by omega),hp j (by omega)⟩

theorem hintNormTest_field {m : Mem} {a : Addr} {B k : Nat}
    (hB : 1≤B) (hB' : B≤524288)
    (hl : -8380417<(coeffAt m a k).toInt) (hh : (coeffAt m a k).toInt<2*8380417) :
    hintNormTest m a (BitVec.ofNat 32 B) k ↔ normZq (ofInt (coeffAt m a k).toInt)<B := by
  have hi := reduceWord_int (coeffAt m a k) (by omega) (by omega)
  have hb := reduce32_bounds (by omega : -2*8380417<(coeffAt m a k).toInt) (by omega : (coeffAt m a k).toInt<3*8380417)
  have hlo : BitVec.ofNat 32 B-1=BitVec.ofNat 32 (B-1) := by bv_omega
  have hw : BitVec.ofNat 32 B+(BitVec.ofNat 32 B-1)=BitVec.ofNat 32 (2*B-1) := by bv_omega
  unfold hintNormTest
  rw [hw,hlo,show (BitVec.ofNat 32 (2*B-1)).toNat=2*B-1 by rw [BitVec.toNat_ofNat]; omega]
  rw [norm_interval _ B hB hB' (by rw [hi]; omega) (by rw [hi]; omega),hi]
  exact (reduce32_norm_iff _ _ (by omega) (by omega) hB').symm

end VG.Proof.MlDsa.AArch64.Optimized.Response
