import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa

def encoded (b : Nat) (x : BitVec 32) : BitVec 32 :=
  Inverse.signCorrected (BitVec.ofNat 32 b-x)

theorem encoded_int {b : Nat} {x : BitVec 32} (hb : b<q) (hx : x.toNat<q) :
    (BitVec.ofNat 32 b-x).toInt=(b:Int)-x.toNat := by
  have hq : q=8380417 := rfl
  have ht := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 b-x)
  rw [BitVec.toNat_sub,BitVec.toNat_ofNat] at ht
  omega

theorem encoded_nat {b : Nat} {x : BitVec 32} (hb : b<q) (hx : x.toNat<q) :
    (encoded b x).toNat=(b+q-x.toNat)%q := by
  have hq : q=8380417 := rfl
  have hv := encoded_int hb hx
  have hi := Inverse.signCorrected_int (BitVec.ofNat 32 b-x) (by rw [hv]; omega) (by rw [hv]; omega)
  rw [hv] at hi
  have ht := BitVec.toInt_eq_toNat_cond (encoded b x)
  change (encoded b x).toInt=_ at hi
  rw [hq]
  by_cases h : x.toNat≤b
  · rw [ite_eq_right (by omega)] at hi
    omega
  · rw [ite_eq_left (by omega)] at hi
    omega

theorem encoded_bpVal {b : Nat} {x : BitVec 32} (hb : b<q) (hx : x.toNat<q) :
    (encoded b x).toNat=Pack.bpVal b x := by
  rw [encoded_nat hb hx]
  unfold Pack.bpVal
  rw [show x.setWidth 64=BitVec.ofNat 64 x.toNat by simp,Pack.subModQ_toNat hb hx]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
