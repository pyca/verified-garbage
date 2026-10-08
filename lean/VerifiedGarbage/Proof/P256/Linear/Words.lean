import VerifiedGarbage.Proof.P256.Linear.Arithmetic

namespace VG.Proof.P256.Linear
open VG VG.Proof.Ed25519
open VG.Proof.P256.VerifySparse (four)

def five (a b c d e : BitVec 64) : Nat := four a b c d+2^256*e.toNat

theorem five_eq (a b c d e : BitVec 64) : five a b c d e=
    a.toNat+2^64*(b.toNat+2^64*(c.toNat+2^64*(d.toNat+2^64*e.toNat))) := by
  unfold five four
  omega

theorem four_lt (a b c d : BitVec 64) : four a b c d<2^256 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  unfold four; omega

theorem five_lt (a b c d e : BitVec 64) : five a b c d e<2^320 := by
  have := four_lt a b c d; have := e.isLt
  unfold five; omega

/-- The small shifts used here keep a full fifth carry word. -/
theorem leftShift_value (k : Nat) (hk : k=1 ∨ k=2 ∨ k=3)
    (a b c d : BitVec 64) :
    five (a<<<k) ((b++a).extractLsb' (64-k) 64)
      ((c++b).extractLsb' (64-k) 64) ((d++c).extractLsb' (64-k) 64)
      (d>>>(64-k)) = 2^k*four a b c d := by
  have extr (hi lo : BitVec 64) :
      ((hi++lo).extractLsb' (64-k) 64).toNat =
        lo.toNat/2^(64-k)+(2^k*hi.toNat)%2^64 := by
    rw [BitVec.extractLsb'_toNat,BitVec.toNat_append,
      ←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    have := hi.isLt; have := lo.isLt
    rcases hk with rfl | rfl | rfl <;> omega
  simp only [five,four,extr,BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  rcases hk with rfl | rfl | rfl <;>
    have := a.isLt <;> have := b.isLt <;> have := c.isLt <;> have := d.isLt <;> omega

theorem leftShiftFive2_value (a b c d e : BitVec 64) (he : e.toNat<2^62) :
    five (a<<<2) ((b++a).extractLsb' 62 64) ((c++b).extractLsb' 62 64)
      ((d++c).extractLsb' 62 64) ((e++d).extractLsb' 62 64)=4*five a b c d e := by
  have h := leftShift_value 2 (Or.inr (Or.inl rfl)) a b c d
  have hex : ((e++d).extractLsb' 62 64).toNat=d.toNat/2^62+4*e.toNat := by
    rw [BitVec.extractLsb'_toNat,BitVec.toNat_append,
      ←Nat.shiftLeft_add_eq_or_of_lt d.isLt,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    have := d.isLt; omega
  simp only [five,show 64-2=62 from rfl,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at h
  simp only [five,hex]
  omega

/-- Five-word addition, with a modular top word. -/
theorem addFive_value (a b c d e x y z w v : BitVec 64) :
    let u := Word64.addCarry a x false
    let c0 := Word64.carryOut a x false
    let r := Word64.addCarry b y c0
    let c1 := Word64.carryOut b y c0
    let s := Word64.addCarry c z c1
    let c2 := Word64.carryOut c z c1
    let t := Word64.addCarry d w c2
    let c3 := Word64.carryOut d w c2
    let f := Word64.addCarry e v c3
    five u r s t f = (five a b c d e+five x y z w v)%2^320 := by
  dsimp only
  have h0 := Word64.addCarry_value a x false
  have h1 := Word64.addCarry_value b y (Word64.carryOut a x false)
  have h2 := Word64.addCarry_value c z (Word64.carryOut b y (Word64.carryOut a x false))
  have h3 := Word64.addCarry_value d w (Word64.carryOut c z (Word64.carryOut b y (Word64.carryOut a x false)))
  have h4 := Word64.addCarry_value e v (Word64.carryOut d w (Word64.carryOut c z (Word64.carryOut b y (Word64.carryOut a x false))))
  have l0 := (Word64.addCarry a x false).isLt
  have l1 := (Word64.addCarry b y (Word64.carryOut a x false)).isLt
  have l2 := (Word64.addCarry c z (Word64.carryOut b y (Word64.carryOut a x false))).isLt
  have l3 := (Word64.addCarry d w (Word64.carryOut c z (Word64.carryOut b y (Word64.carryOut a x false)))).isLt
  have l4 := (Word64.addCarry e v (Word64.carryOut d w (Word64.carryOut c z (Word64.carryOut b y (Word64.carryOut a x false))))).isLt
  simp only [Bool.toNat_false,Nat.add_zero] at h0
  unfold five four
  omega

/-- Full-width subtraction retains the last borrow. -/
theorem subFive_value (a b c d e x y z w v : BitVec 64) :
    five (Word64.addCarry a (~~~x) true) (Word64.addCarry b (~~~y) (Word64.carryOut a (~~~x) true)) (Word64.addCarry c (~~~z) (Word64.carryOut b (~~~y) (Word64.carryOut a (~~~x) true))) (Word64.addCarry d (~~~w) (Word64.carryOut c (~~~z) (Word64.carryOut b (~~~y) (Word64.carryOut a (~~~x) true)))) (Word64.addCarry e (~~~v) (Word64.carryOut d (~~~w) (Word64.carryOut c (~~~z) (Word64.carryOut b (~~~y) (Word64.carryOut a (~~~x) true))))) + five x y z w v =
      five a b c d e+2^320*(!(Word64.carryOut e (~~~v) (Word64.carryOut d (~~~w) (Word64.carryOut c (~~~z) (Word64.carryOut b (~~~y) (Word64.carryOut a (~~~x) true)))))).toNat := by
  have h0 := VG.Proof.Mont.AArch64.sub_borrow a x true
  have h1 := VG.Proof.Mont.AArch64.sub_borrow b y (Word64.carryOut a (~~~x) true)
  have h2 := VG.Proof.Mont.AArch64.sub_borrow c z (Word64.carryOut b (~~~y) (Word64.carryOut a (~~~x) true))
  have h3 := VG.Proof.Mont.AArch64.sub_borrow d w (Word64.carryOut c (~~~z) (Word64.carryOut b (~~~y) (Word64.carryOut a (~~~x) true)))
  have h4 := VG.Proof.Mont.AArch64.sub_borrow e v (Word64.carryOut d (~~~w) (Word64.carryOut c (~~~z) (Word64.carryOut b (~~~y) (Word64.carryOut a (~~~x) true))))
  simp only [Bool.not_true,Bool.toNat_false,Nat.add_zero] at h0
  unfold five four
  omega

end VG.Proof.P256.Linear
