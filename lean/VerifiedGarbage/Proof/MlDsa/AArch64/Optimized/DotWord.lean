import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductWord

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

def dotNat (a b : Nat → BitVec 32) : Nat → Nat
  | 0 => 0
  | n+1 => dotNat a b n + (a n).toNat*(b n).toNat

def dotWord (a b : Nat → BitVec 32) (n : Nat) : BitVec 64 := BitVec.ofNat 64 (dotNat a b n)
def centeredDot (a b : Nat → BitVec 32) (n : Nat) : BitVec 32 := redc (dotWord a b n)-BitVec.ofNat 32 q

theorem dotWord_zero (a b : Nat → BitVec 32) : dotWord a b 0=0 := rfl

theorem dotWord_succ (a b : Nat → BitVec 32) (n : Nat) :
    dotWord a b (n+1)=dotWord a b n+product (a n) (b n) := by
  have hp := congrArg (BitVec.ofNat 64) (product_nat (a n) (b n))
  rw [BitVec.ofNat_toNat] at hp
  rw [dotWord,dotNat,BitVec.ofNat_add,← hp]
  rfl

theorem dotNat_congr (a b a' b' : Nat → BitVec 32) (n : Nat)
    (ha : ∀j<n,a j=a' j) (hb : ∀j<n,b j=b' j) : dotNat a b n=dotNat a' b' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dotNat,dotNat,ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega)),
      ha n (by omega),hb n (by omega)]

theorem centeredDot_congr (a b a' b' : Nat → BitVec 32) (n : Nat)
    (ha : ∀j<n,a j=a' j) (hb : ∀j<n,b j=b' j) : centeredDot a b n=centeredDot a' b' n := by
  unfold centeredDot dotWord
  rw [dotNat_congr a b a' b' n ha hb]

theorem dotNat_le (a b : Nat → BitVec 32) (n : Nat)
    (ha : ∀j<n,(a j).toNat<3*q) (hb : ∀j<n,(b j).toNat<3*q) :
    dotNat a b n≤n*(9*q^2-1) := by
  induction n with
  | zero => simp only [dotNat,Nat.zero_mul,Nat.le_refl]
  | succ n ih =>
    have hi := ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    have hp := product_lt_nine_q2 (ha n (by omega)) (hb n (by omega))
    simp only [dotNat,Nat.succ_mul]
    exact Nat.add_le_add hi (by omega)

theorem dotNat_lt_qR (a b : Nat → BitVec 32) {n : Nat} (hn : n≤7)
    (ha : ∀j<n,(a j).toNat<3*q) (hb : ∀j<n,(b j).toNat<3*q) :
    dotNat a b n<q*2^32 := by
  have h := dotNat_le a b n ha hb
  have hc : 7*(9*q^2-1)<q*2^32 := by decide
  exact Nat.lt_of_le_of_lt (Nat.le_trans h (Nat.mul_le_mul_right _ hn)) hc

theorem dotWord_nat (a b : Nat → BitVec 32) {n : Nat} (hn : n≤7)
    (ha : ∀j<n,(a j).toNat<3*q) (hb : ∀j<n,(b j).toNat<3*q) :
    (dotWord a b n).toNat=dotNat a b n := by
  have h := dotNat_lt_qR a b hn ha hb
  rw [dotWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))]

theorem centeredDot_int (a b : Nat → BitVec 32) {n : Nat} (hn : n≤7)
    (ha : ∀j<n,(a j).toNat<3*q) (hb : ∀j<n,(b j).toNat<3*q) :
    (centeredDot a b n).toInt=(mont (dotNat a b n) : Int)-q := by
  have hw := dotWord_nat a b hn ha hb
  have hr := redc_nat (dotWord a b n) (by rw [hw]; exact dotNat_lt_qR a b hn ha hb)
  rw [hw] at hr
  have hbnd := mont_lt (dotNat_lt_qR a b hn ha hb)
  unfold centeredDot
  rw [centeredWord_int _ (by rw [hr]; exact hbnd),hr]
  rfl

theorem centeredDot_bound (a b : Nat → BitVec 32) {n : Nat} (hn : n≤7)
    (ha : ∀j<n,(a j).toNat<3*q) (hb : ∀j<n,(b j).toNat<3*q) :
    -(q : Int)≤(centeredDot a b n).toInt ∧ (centeredDot a b n).toInt<(q : Int) := by
  rw [centeredDot_int a b hn ha hb]
  have h := mont_lt (dotNat_lt_qR a b hn ha hb)
  omega

theorem centeredDot_scaled (a b : Nat → BitVec 32) {n : Nat} (hn : n≤7)
    (ha : ∀j<n,(a j).toNat<3*q) (hb : ∀j<n,(b j).toNat<3*q) :
    ofInt (centeredDot a b n).toInt*ofInt 4294967296=ofInt (dotNat a b n : Int) := by
  rw [centeredDot_int a b hn ha hb,centeredMont_scaled]

end VG.Proof.MlDsa.AArch64.Optimized
