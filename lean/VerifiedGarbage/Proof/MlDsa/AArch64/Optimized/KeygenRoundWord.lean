import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64 VG.Spec.MlDsa

def highWord (x : BitVec 32) : BitVec 32 := (x+4095#32)>>>13
def rawWord (x : BitVec 32) : BitVec 32 := x-(highWord x<<<13)
def lowWord (x : BitVec 32) : BitVec 32 := Inverse.signCorrected (rawWord x)

theorem highWord_nat {x : BitVec 32} (hx : x.toNat<q) :
    (highWord x).toNat=(x.toNat+4095)/8192 := by
  change x.toNat<8380417 at hx
  simp only [highWord,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_add]
  change ((x.toNat+4095)%4294967296)/8192=(x.toNat+4095)/8192
  rw [Nat.mod_eq_of_lt (by omega)]

theorem rawWord_int {x : BitVec 32} (hx : x.toNat<q) :
    (rawWord x).toInt=((x.toNat+4095)%8192:Int)-4095 := by
  have hh := highWord_nat hx
  have hx' : x.toNat<8380417 := hx
  have he := BitVec.toInt_eq_toNat_cond (rawWord x)
  have hv : (rawWord x).toNat=(2^32-(((x.toNat+4095)/8192*8192)%2^32)+x.toNat)%2^32 := by
    simp only [rawWord,BitVec.toNat_sub,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,hh]
  rw [hv] at he
  omega

theorem highWord_eq {x : BitVec 32} (hx : x.toNat<q) :
    highWord x=VG.Proof.MlDsa.AArch64.Round.t1V x := by
  apply BitVec.eq_of_toNat_eq
  rw [highWord_nat hx,VG.Proof.MlDsa.AArch64.Round.t1V_toNat hx]

theorem lowWord_eq {x : BitVec 32} (hx : x.toNat<q) :
    lowWord x=VG.Proof.MlDsa.AArch64.Round.t0V x := by
  have hr := rawWord_int hx
  have hb : (x.toNat+4095)%8192<8192 := Nat.mod_lt _ (by decide)
  have he := Inverse.signCorrected_int (rawWord x) (by omega) (by omega)
  have hv := BitVec.toInt_eq_toNat_cond (lowWord x)
  change (lowWord x).toInt=_ at he
  rw [hr] at he
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.MlDsa.AArch64.Round.t0V_toNat hx]
  change (lowWord x).toNat=if (x.toNat+4095)%8192<4095 then (x.toNat+4095)%8192+8380417-4095 else (x.toNat+4095)%8192-4095
  split <;> split at he <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
