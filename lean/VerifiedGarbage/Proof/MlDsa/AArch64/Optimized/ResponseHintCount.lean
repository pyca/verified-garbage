import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFinish

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
