import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16 vector_contains)

theorem hintAt_coeff (B : BitVec 32) (m : Mem) (p a h : Addr) (j : Nat) {e : Nat} (he : e<4) :
    hintAt B m p a h j e=hintWord B (reduceWord (coeffAt m a (4*j+e))+coeffAt m p (4*j+e)) (coeffAt m h (4*j+e)) := by
  unfold hintAt hintCtAt
  rw [show 16*j=4*(4*j) by omega]
  change hintWord B (reduceWord (vword (m.read (coeffAddr a (4*j)) 16) e)+
    vword (m.read (coeffAddr p (4*j)) 16) e) (vword (m.read (coeffAddr h (4*j)) 16) e)=_
  rw [VG.AArch64.vword_read16 _ _ he,VG.AArch64.vword_read16 _ _ he,VG.AArch64.vword_read16 _ _ he,coeffAddr_add,coeffAddr_add,coeffAddr_add]
  rfl

theorem hintStep_coeff (d : HintData) (p a h : Addr) (B : BitVec 32) {j k : Nat}
    (hj : j<64) (hk : k<256) :
    coeffAt (hintStep B p a h j d).mem p k =
      if 4*j≤k ∧ k<4*j+4 then hintWord B (reduceWord (coeffAt d.mem a k)+coeffAt d.mem p k) (coeffAt d.mem h k)
      else coeffAt d.mem p k := by
  simp only [hintStep]
  rw [show 16*j=4*(4*j) by omega]
  change coeffAt (d.mem.write (coeffAddr p (4*j)) 16 _) p k=_
  rw [coeffAt_write16 _ _ (by omega) _ hk]
  split
  · rename_i h
    rw [laneVector_word _ (by omega),hintAt_coeff _ _ _ _ _ _ (by omega),show 4*j+(k-4*j)=k by omega]
  · rfl

theorem hintRun_frame (m : Mem) (p a h : Addr) (B : BitVec 32) {j : Nat} (hj : j≤64) :
    Frame [pR p] m (hintRun m B p a h j).mem := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih =>
    rw [hintRun]
    simp only [hintStep]
    rw [show 16*j=4*(4*j) by omega]
    change Frame [pR p] m ((hintRun m B p a h j).mem.write (coeffAddr p (4*j)) 16 _)
    exact (ih (by omega)).write (by simp) _ (vector_contains p (by omega))

def HintPrefix (initial current : Mem) (p a h : Addr) (B : BitVec 32) (done : Nat) : Prop :=
  ∀k<256,coeffAt current p k=if k<done then
    hintWord B (reduceWord (coeffAt initial a k)+coeffAt initial p k) (coeffAt initial h k) else coeffAt initial p k

theorem hintRun_prefix (m : Mem) (p a h : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (he : (pR p).Disjoint (pR h)) {j : Nat} (hj : j≤64) :
    HintPrefix m (hintRun m B p a h j).mem p a h B (4*j) := by
  induction j with
  | zero => intro k hk; simp [hintRun]
  | succ j ih =>
    have hp := ih (by omega)
    have ha : ∀k<256,coeffAt (hintRun m B p a h j).mem a k=coeffAt m a k := by
      intro k hk
      exact coeffAt_frame (hintRun_frame m p a h B (by omega)) (by simpa using hd.symm) hk
    have hh : ∀k<256,coeffAt (hintRun m B p a h j).mem h k=coeffAt m h k := by
      intro k hk
      exact coeffAt_frame (hintRun_frame m p a h B (by omega)) (by simpa using he.symm) hk
    intro k hk
    rw [hintRun,hintStep_coeff _ _ _ _ _ (by omega) hk]
    by_cases before : k<4*j
    · rw [ite_eq_right (by omega),hp k hk,ite_eq_left before,ite_eq_left (by omega)]
    · by_cases inside : k<4*j+4
      · rw [ite_eq_left (by omega),hp k hk,ite_eq_right before,ha k hk,hh k hk,ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega),hp k hk,ite_eq_right before,ite_eq_right (by omega)]

theorem hintRun_coeff (m : Mem) (p a h : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (he : (pR p).Disjoint (pR h)) {k : Nat} (hk : k<256) :
    coeffAt (hintRun m B p a h 64).mem p k=hintWord B (reduceWord (coeffAt m a k)+coeffAt m p k) (coeffAt m h k) := by
  rw [hintRun_prefix m p a h B hd he (by decide) k hk,ite_eq_left hk]

end VG.Proof.MlDsa.AArch64.Optimized.Response
