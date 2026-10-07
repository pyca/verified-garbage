import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519 VG.Proof.Ed25519.AArch64

abbrev nafVal5 (a b c d e : BitVec 64) : Nat :=
  a.toNat+2^64*b.toNat+2^128*c.toNat+2^192*d.toNat+2^256*e.toNat

theorem nafVal5_lt (a b c d e : BitVec 64) : nafVal5 a b c d e<2^320 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; have := e.isLt
  dsimp only [nafVal5]
  omega

theorem nafVal5_inj {a b c d e f g h i j : BitVec 64}
    (hv : nafVal5 a b c d e=nafVal5 f g h i j) :
    a=f ∧ b=g ∧ c=h ∧ d=i ∧ e=j := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; have := e.isLt
  have := f.isLt; have := g.isLt; have := h.isLt; have := i.isLt; have := j.isLt
  dsimp only [nafVal5] at hv
  refine ⟨?_,?_,?_,?_,?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> omega

def nafSub5 (a b c d e x mask : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let c0 := Word64.carryOut a (~~~x) true
  let c1 := Word64.carryOut b (~~~mask) c0
  let c2 := Word64.carryOut c (~~~mask) c1
  let c3 := Word64.carryOut d (~~~mask) c2
  (Word64.addCarry a (~~~x) true,Word64.addCarry b (~~~mask) c0,
   Word64.addCarry c (~~~mask) c1,Word64.addCarry d (~~~mask) c2,
   Word64.addCarry e (~~~mask) c3)

theorem nafSub5_value (a b c d e x mask : BitVec 64) :
    let out := nafSub5 a b c d e x mask
    (nafVal5 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 +
      nafVal5 x mask mask mask mask)%2^320 = nafVal5 a b c d e := by
  have h0 := sub_borrow a x true
  have h1 := sub_borrow b mask (Word64.carryOut a (~~~x) true)
  have h2 := sub_borrow c mask (Word64.carryOut b (~~~mask) (Word64.carryOut a (~~~x) true))
  have h3 := sub_borrow d mask (Word64.carryOut c (~~~mask)
    (Word64.carryOut b (~~~mask) (Word64.carryOut a (~~~x) true)))
  have h4 := sub_borrow e mask (Word64.carryOut d (~~~mask) (Word64.carryOut c (~~~mask)
    (Word64.carryOut b (~~~mask) (Word64.carryOut a (~~~x) true))))
  have hb := nafVal5_lt a b c d e
  simp only [Bool.not_true,Bool.toNat_false,Nat.add_zero] at h0
  dsimp only [nafSub5,nafVal5] at hb ⊢
  omega

theorem nafWord_toNat (k j : Nat) :
    (BitVec.ofInt 64 (Naf5.digit k j)).toNat =
      if Naf5.negative k j then 2^64-Naf5.magnitude k j else Naf5.magnitude k j := by
  have hb := Naf5.magnitude_le k j
  simp only [Naf5.digit,BitVec.toNat_ofInt]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((Naf5.magnitude k j:Int)%18446744073709551616).toNat=_
    omega
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]
    change ((-(Naf5.magnitude k j:Int))%18446744073709551616).toNat=_
    omega

theorem nafSign_toNat (k j : Nat) :
    (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63)).toNat =
      if Naf5.negative k j then 2^64-1 else 0 := by
  have hb := Naf5.magnitude_le k j
  have hp := Naf5.negative_magnitude_pos k j
  simp only [BitVec.toNat_sub,BitVec.toNat_zero,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,nafWord_toNat]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := hp hn
    simp only [ite_true]; omega

theorem nafSub5_next (a b c d e : BitVec 64) (k j : Nat)
    (hv : nafVal5 a b c d e=Naf5.residual k j) (hb : Naf5.residual k j≤2^256) :
    let x := BitVec.ofInt 64 (Naf5.digit k j)
    let out := nafSub5 a b c d e x (0#64-(x>>>63))
    nafVal5 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 = 2*Naf5.residual k (j+1) := by
  have hs := nafSub5_value a b c d e (BitVec.ofInt 64 (Naf5.digit k j))
    (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))
  have hlt := nafVal5_lt (nafSub5 a b c d e (BitVec.ofInt 64 (Naf5.digit k j))
    (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))).1
    (nafSub5 a b c d e (BitVec.ofInt 64 (Naf5.digit k j)) (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))).2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (Naf5.digit k j)) (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))).2.2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (Naf5.digit k j)) (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))).2.2.2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (Naf5.digit k j)) (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))).2.2.2.2
  dsimp only at hs ⊢
  rw [hv] at hs
  have he : nafVal5 (BitVec.ofInt 64 (Naf5.digit k j))
      (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))
      (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))
      (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63))
      (0#64-(BitVec.ofInt 64 (Naf5.digit k j)>>>63)) =
      if Naf5.negative k j then 2^320-Naf5.magnitude k j else Naf5.magnitude k j := by
    simp only [nafVal5,nafWord_toNat,nafSign_toNat]
    cases hn : Naf5.negative k j <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · omega
    · have := Naf5.magnitude_le k j; omega
  rw [he] at hs
  have hr := Naf5.recurrence k j
  have hm := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at hs hr <;> omega

/-- Five adjacent extract-right instructions implement a whole-number shift. -/
theorem nafShift5_value (a b c d e : BitVec 64) :
    nafVal5 ((b++a).extractLsb' 1 64) ((c++b).extractLsb' 1 64)
      ((d++c).extractLsb' 1 64) ((e++d).extractLsb' 1 64) (e>>>1) = nafVal5 a b c d e/2 := by
  have extr (hi lo : BitVec 64) : ((hi++lo).extractLsb' 1 64).toNat = lo.toNat/2+2^63*(hi.toNat%2) := by
    rw [BitVec.extractLsb'_toNat,BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
      Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    have := hi.isLt; have := lo.isLt
    omega
  simp only [nafVal5,extr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega

theorem nafSubtract_ok (s : State) (k j : Nat) (h12 : s.gpr .x12=0)
    (h2 : s.gpr .x2=BitVec.ofInt 64 (Naf5.digit k j))
    (hv : nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=Naf5.residual k j)
    (hb : Naf5.residual k j≤2^256) :
    WP isa (.block Naf.subtractShift) s fun t =>
      nafVal5 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x8) (t.gpr .x9)=Naf5.residual k (j+1) ∧
      Keeps [.x3,.x5,.x6,.x7,.x8,.x9] s t := by
  have hs := nafSub5_next (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) k j hv hb
  apply WP.of_runBlock
  simp only [Naf.subtractShift,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,h12,h2,
    show 63<Size.x.bits from by decide,show 1<Size.x.bits from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · dsimp only [nafSub5] at hs
    rw [nafShift5_value]
    dsimp only [Word64.addCarry,Word64.carryOut,Size.bits] at hs ⊢
    simpa using congrArg (fun n : Nat => n/2) hs
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hr.1,hr.2.1,hr.2.2.1,
      hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2,ite_false]

end VG.Proof.Weierstrass.AArch64
