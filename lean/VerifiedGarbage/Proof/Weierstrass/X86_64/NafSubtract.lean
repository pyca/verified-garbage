import VerifiedGarbage.Impl.Weierstrass.X86_64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.X25519.X86_64.Step

/-! The five-word subtraction used by signed scalar recoding. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

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
  let c0 := decide (a.toNat < x.toNat)
  let c1 := decide (b.toNat < mask.toNat + c0.toNat)
  let c2 := decide (c.toNat < mask.toNat + c1.toNat)
  let c3 := decide (d.toNat < mask.toNat + c2.toNat)
  (a-x,b-mask-(BitVec.ofBool c0).setWidth 64,c-mask-(BitVec.ofBool c1).setWidth 64,
   d-mask-(BitVec.ofBool c2).setWidth 64,e-mask-(BitVec.ofBool c3).setWidth 64)

theorem nafSub5_value (a b c d e x mask : BitVec 64) :
    let out := nafSub5 a b c d e x mask
    (nafVal5 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 +
      nafVal5 x mask mask mask mask)%2^320 = nafVal5 a b c d e := by
  have h0 := sub_borrow a x
  have h1 := sbb_borrow b mask (decide (a.toNat < x.toNat))
  have h2 := sbb_borrow c mask (decide (b.toNat < mask.toNat + (decide (a.toNat < x.toNat)).toNat))
  have h3 := sbb_borrow d mask (decide (c.toNat < mask.toNat +
    (decide (b.toNat < mask.toNat + (decide (a.toNat < x.toNat)).toNat)).toNat))
  have h4 := sbb_borrow e mask (decide (d.toNat < mask.toNat +
    (decide (c.toNat < mask.toNat + (decide (b.toNat < mask.toNat +
      (decide (a.toNat < x.toNat)).toNat)).toNat)).toNat))
  have hb := nafVal5_lt a b c d e
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


/-- The adjacent-word shifts preserve all bits of the five-word scalar. -/
theorem nafShift5_value (a b c d e : BitVec 64) :
    nafVal5 ((a>>>1)|||(b<<<63)) ((b>>>1)|||(c<<<63))
      ((c>>>1)|||(d<<<63)) ((d>>>1)|||(e<<<63)) (e>>>1) = nafVal5 a b c d e/2 := by
  have join (lo hi : BitVec 64) :
      ((lo>>>1)|||(hi<<<63)).toNat=lo.toNat/2+2^63*(hi.toNat%2) := by
    have hlo : (lo>>>1).toNat<2^63 := BitVec.toNat_ushiftRight_lt lo 1 (by decide)
    have hhi : (hi<<<63).toNat=(hi.toNat%2)<<<63 := by
      simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
      omega
    rw [BitVec.toNat_or,hhi,Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt hlo]
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
    omega
  simp only [nafVal5,join,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega

theorem subtractDigit_ok (s : State) (k j : Nat)
    (hx : s.gpr .rcx=BitVec.ofInt 64 (Naf5.digit k j))
    (hv : nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)=Naf5.residual k j)
    (hb : Naf5.residual k j≤2^256) :
    WP isa (.block Naf.subtractDigit) s fun t =>
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=2*Naf5.residual k (j+1) ∧
      Keeps [.rax,.rdx,.r8,.r9,.r10,.r11,.r12] s t := by
  have hs := nafSub5_next (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) k j hv hb
  apply WP.of_runBlock
  simp only [Naf.subtractDigit,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags,RegUpd.cf_setReg,ite_true,ite_false,and_self,reduceCtorEq,hx,
    show 1≤63 ∧ 63≤63 from by decide,show ¬(63=1) from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · exact hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2,ite_false]

theorem nafShift_ok (s : State) :
    WP isa (.block Naf.shift) s fun t =>
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=
        nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)/2 ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12] s t := by
  apply WP.of_runBlock
  simp only [Naf.shift,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    ite_true,ite_false,and_self,reduceCtorEq,
    show 1≤63 ∧ 63≤63 from by decide,show 1≤1 ∧ 1≤63 from by decide,
    show ¬(63=1) from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨nafShift5_value _ _ _ _ _,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2,ite_false]

end VG.Proof.Weierstrass.X86_64
