import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFinish

/-! ## From `ResponseHintSemantic.lean` -/

section

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

end

/-! ## From `ResponseHintCount.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

theorem shift31_bound (x : BitVec 32) : (x >>> 31).toNat≤1 := by
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have h := x.isLt
  change _<4294967296 at h
  change _/2147483648≤1
  omega

/-- The final logical shift makes every hint a bit, even on rejected inputs. -/
theorem hintWord_bit (B t h : BitVec 32) : (hintWord B t h).toNat≤1 :=
  shift31_bound _

theorem hintAt_bit (B : BitVec 32) (m : Mem) (p a h : Addr) (j e : Nat) :
    (hintAt B m p a h j e).toNat≤1 := hintWord_bit _ _ _

theorem add_bit_bound (x y : BitVec 32) {j : Nat}
    (hx : x.toNat≤j) (hj : j<64) (hy : y.toNat≤1) : (x+y).toNat≤j+1 := by
  rw [BitVec.toNat_add]
  omega

theorem add_bit_value (x y : BitVec 32) {j : Nat}
    (hx : x.toNat≤j) (hj : j<64) (hy : y.toNat≤1) :
    (x+y).toNat=x.toNat+y.toNat := by
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by change _<4294967296; omega)]

theorem hintRun_count_bound (m : Mem) (B : BitVec 32) (p a h : Addr) {j : Nat}
    (hj : j≤64) {e : Nat} (he : e<4) :
    (vword (hintRun m B p a h j).counts e).toNat≤j := by
  induction j with
  | zero => simp [hintRun,vword]
  | succ j ih =>
    have hi := ih (by omega)
    change (vword (laneVector fun e =>
      vword (hintRun m B p a h j).counts e+hintAt B (hintRun m B p a h j).mem p a h j e) e).toNat≤j+1
    rw [laneVector_word _ he]
    exact add_bit_bound _ _ hi (by omega) (hintAt_bit _ _ _ _ _ _ _)

def hintLaneCount (m : Mem) (B : BitVec 32) (p a h : Addr) (e : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => hintLaneCount m B p a h e j+
      (hintAt B (hintRun m B p a h j).mem p a h j e).toNat

theorem hintRun_count_value (m : Mem) (B : BitVec 32) (p a h : Addr) {j : Nat}
    (hj : j≤64) {e : Nat} (he : e<4) :
    (vword (hintRun m B p a h j).counts e).toNat=hintLaneCount m B p a h e j := by
  induction j with
  | zero => simp [hintRun,hintLaneCount,vword]
  | succ j ih =>
    have bound := hintRun_count_bound m B p a h (j:=j) (by omega) he
    change (vword (laneVector fun e =>
      vword (hintRun m B p a h j).counts e+hintAt B (hintRun m B p a h j).mem p a h j e) e).toNat=_
    rw [laneVector_word _ he,add_bit_value _ _ bound (by omega) (hintAt_bit _ _ _ _ _ _ _),ih (by omega)]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
