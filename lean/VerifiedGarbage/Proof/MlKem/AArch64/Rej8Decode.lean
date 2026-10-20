module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Parse
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Spec.MlKem


/-! # Agreement between packed candidates and the specified byte decoder -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

private theorem three_toNat (m : Mem) (p : Addr) :
    (m.read p 3).toNat = (m p).toNat+256*(m (p+1)).toNat+65536*(m (p+2)).toNat := by
  simp only [Mem.read,BitVec.toNat_append]
  have he : p+1+1=p+2 := by bv_omega
  rw [he]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (m (p+1)).isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (m (p+2)).isLt]
  simp only [Nat.shiftLeft_eq,show (0#0).toNat=0 from rfl]
  omega

theorem candidate_even (m : Mem) (p : Addr) (j : Nat) :
    (candidate m p (2*j)).toNat =
      (m (p+BitVec.ofNat 64 (3*j))).toNat +
        256*((m (p+BitVec.ofNat 64 (3*j)+1)).toNat%16) := by
  simp only [candidate, Nat.mul_div_cancel_left _ (by decide : 0<2),
    Nat.mul_mod_right, Nat.mul_zero,BitVec.toNat_setWidth_of_le (by decide : 12≤16),
    BitVec.extractLsb'_toNat,Nat.shiftRight_zero,three_toNat]
  have h0 := (m (p+BitVec.ofNat 64 (3*j))).isLt
  omega

theorem candidate_odd (m : Mem) (p : Addr) (j : Nat) :
    (candidate m p (2*j+1)).toNat =
      (m (p+BitVec.ofNat 64 (3*j)+1)).toNat/16 +
        16*(m (p+BitVec.ofNat 64 (3*j)+2)).toNat := by
  have hd : (2*j+1)/2=j := by omega
  have hm : (2*j+1)%2=1 := by omega
  simp only [candidate,hd,hm,Nat.mul_one,BitVec.toNat_setWidth_of_le (by decide : 12≤16),
    BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,three_toNat]
  have h0 := (m (p+BitVec.ofNat 64 (3*j))).isLt
  have h1 := (m (p+BitVec.ofNat 64 (3*j)+1)).isLt
  have h2 := (m (p+BitVec.ofNat 64 (3*j)+2)).isLt
  omega

end VG.Proof.MlKem.AArch64.Rej8
