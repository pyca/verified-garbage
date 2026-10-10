import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ

/-! ## From `ResponseZSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16 vector_contains)

theorem zWords_coeff (m : Mem) (p a : Addr) (j : Nat) {e : Nat} (he : e<4) :
    zWords m p a j e=reduceWord (coeffAt m p (4*j+e)+coeffAt m a (4*j+e)) := by
  unfold zWords
  rw [show 16*j=4*(4*j) by omega]
  change reduceWord (vword (m.read (coeffAddr p (4*j)) 16) e+
    vword (m.read (coeffAddr a (4*j)) 16) e)=_
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,coeffAddr_add]
  rfl

theorem zStep_coeff (d : ZData) (p a : Addr) (B : BitVec 32) {j k : Nat}
    (hj : j<64) (hk : k<256) :
    coeffAt (zStep p a B j d).mem p k =
      if 4*j≤k ∧ k<4*j+4 then reduceWord (coeffAt d.mem p k+coeffAt d.mem a k)
      else coeffAt d.mem p k := by
  simp only [zStep]
  rw [show 16*j=4*(4*j) by omega]
  change coeffAt (d.mem.write (coeffAddr p (4*j)) 16 _) p k=_
  rw [coeffAt_write16 _ _ (by omega) _ hk]
  split
  · rename_i h
    rw [laneVector_word _ (by omega),zWords_coeff _ _ _ _ (by omega),show 4*j+(k-4*j)=k by omega]
  · rfl

theorem zRun_frame (m : Mem) (p a : Addr) (B : BitVec 32) {j : Nat} (hj : j≤64) :
    Frame [pR p] m (zRun m p a B j).mem := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih =>
    rw [zRun_next]
    simp only [zStep]
    rw [show 16*j=4*(4*j) by omega]
    change Frame [pR p] m ((zRun m p a B j).mem.write (coeffAddr p (4*j)) 16 _)
    exact (ih (by omega)).write (by simp) _ (vector_contains p (by omega))

def ZPrefix (initial current : Mem) (p a : Addr) (done : Nat) : Prop :=
  ∀k<256,coeffAt current p k=if k<done then
    reduceWord (coeffAt initial p k+coeffAt initial a k) else coeffAt initial p k

theorem zRun_prefix (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {j : Nat} (hj : j≤64) :
    ZPrefix m (zRun m p a B j).mem p a (4*j) := by
  induction j with
  | zero => intro k hk; simp [zRun]
  | succ j ih =>
    have hp := ih (by omega)
    have ha : ∀k<256,coeffAt (zRun m p a B j).mem a k=coeffAt m a k := by
      intro k hk
      exact coeffAt_frame (zRun_frame m p a B (by omega)) (by simpa using hd.symm) hk
    intro k hk
    rw [zRun_next,zStep_coeff _ _ _ _ (by omega) hk]
    by_cases before : k<4*j
    · rw [ite_eq_right (by omega),hp k hk,ite_eq_left before,ite_eq_left (by omega)]
    · by_cases inside : k<4*j+4
      · rw [ite_eq_left (by omega),hp k hk,ite_eq_right before,ha k hk,ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega),hp k hk,ite_eq_right before,ite_eq_right (by omega)]

theorem zRun_coeff (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) {k : Nat} (hk : k<256) :
    coeffAt (zRun m p a B 64).mem p k=reduceWord (coeffAt m p k+coeffAt m a k) := by
  rw [zRun_prefix m p a B hd (by decide) k hk,ite_eq_left hk]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZFlags.lean` -/

section

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

end
