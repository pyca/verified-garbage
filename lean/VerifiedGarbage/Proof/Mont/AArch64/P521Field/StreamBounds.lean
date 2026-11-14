module

public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Omega

/-! Bounds justifying the shortened top row of the ordinary P-521 product. -/

-- separate module: pure integer bounds used by the final streaming step
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi)

/-- Dividing a processed prefix's product by its radix leaves at most B. -/
theorem tail_acc_bound {P S T B : Nat} (hP : P<2^512)
    (he : S+2^512*T=P*B) : T≤B := by
  have hmul := Nat.mul_le_mul_right B (Nat.le_of_lt hP)
  have h : 2^512*T≤2^512*B := by omega_using [he,hmul]
  have hn := Nat.two_pow_pos 512
  have hcancel := Nat.le_of_mul_le_mul_left (a:=T) (b:=B) (c:=2^512)
  exact hcancel h hn

/-- A nine-word value below 2^521 has a nine-bit final word. -/
theorem top_limb_bound {L A top : Nat} (he : A=L+2^512*top) (ha : A<2^521) : top<512 := by
  have hp := Nat.pow_add (2 : Nat) 512 9
  simp only [Nat.reduceAdd,show (2 : Nat)^9=512 from by decide] at hp
  rw [hp] at ha
  by_contra h
  have hm := Nat.mul_le_mul_left (2^512) (Nat.le_of_not_gt h)
  omega_using [he,ha,hm]

theorem final_row_bound {T B : Nat} (a : Word)
    (ht : T≤B) (hb : B<2^521) (ha : a.toNat<512) : T+a.toNat*B<2^576 := by
  have hs : T+a.toNat*B≤(a.toNat+1)*B := by
    rw [Nat.add_mul,Nat.one_mul]
    omega_arith
  have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt ha)
  have hb' := Nat.mul_lt_mul_of_pos_left hb (by decide : 0<512)
  have hp := Nat.pow_add (2 : Nat) 9 521
  simp only [Nat.reduceAdd,show (2 : Nat)^9=512 from by decide] at hp
  rw [←hp] at hb'
  have hsmall : (2 : Nat)^530<2^576 := Nat.pow_lt_pow_right (a:=2) (m:=530) (n:=576) (by decide) (by decide)
  exact Nat.lt_of_le_of_lt (Nat.le_trans hs hm) (Nat.lt_trans hb' hsmall)

theorem mulHi_small (a b : Word) (ha : a.toNat<512) (hb : b.toNat<512) : mulHi a b=0 := by
  have h := Nat.mul_lt_mul'' ha hb
  have hh : a.toNat*b.toNat<2^64 := Nat.lt_trans h (by decide)
  simp only [mulHi,Nat.div_eq_of_lt hh]
  rfl

end VG.Proof.Mont.AArch64.P521Field
