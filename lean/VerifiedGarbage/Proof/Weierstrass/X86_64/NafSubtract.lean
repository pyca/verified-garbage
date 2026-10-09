import VerifiedGarbage.Impl.Weierstrass.X86_64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Mont.X86_64.Words

/-! The five-, seven- and ten-word subtractions used by signed scalar recoding, and the value of the
scalar's registers (`nafValN`). -/
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

/-- One more word below a bound: `a + 2⁶⁴ y < 2⁶⁴ B` for `y < B`. -/
theorem horner_lt {a y B : Nat} (ha : a<2^64) (hy : y<B) : a+2^64*y<2^64*B := by omega

/-- One word of a borrow chain below the words above it: `o = i - s - c`
with borrow `c'`, and the words above with borrow-in `c'`. -/
theorem sbb_chain {o s c i c' vo vs vi top : Nat} (h : o+s+c=i+2^64*c') (ih : vo+vs+c'=vi+top) :
    (o+2^64*vo)+(s+2^64*vs)+c=(i+2^64*vi)+2^64*top := by omega

theorem mod_of_chain {A S I T M c : Nat} (h : A+S+0=I+T) (hI : I<M) (hT : T=M*c) :
    (A+S)%M=I := by
  rw [show A+S=I+M*c by omega,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hI]

/-- Seven words: a scalar of six words and its top word (with no numeral
exponent above 256, which Lean would not evaluate). -/
abbrev nafVal7 (a b c d e f g : BitVec 64) : Nat :=
  a.toNat+2^64*(b.toNat+2^64*(c.toNat+2^64*(d.toNat+2^64*(e.toNat+2^64*(f.toNat+2^64*g.toNat)))))

theorem nafVal7_lt (a b c d e f g : BitVec 64) : nafVal7 a b c d e f g<2^256*2^192 :=
  Nat.lt_of_lt_of_eq (horner_lt a.isLt <| horner_lt b.isLt <| horner_lt c.isLt <| horner_lt d.isLt <|
    horner_lt e.isLt <| horner_lt f.isLt g.isLt) (by decide)

/-- `nafSub5` for seven words. -/
def nafSub7 (a b c d e f g x mask : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let c0 := decide (a.toNat < x.toNat)
  let c1 := decide (b.toNat < mask.toNat + c0.toNat)
  let c2 := decide (c.toNat < mask.toNat + c1.toNat)
  let c3 := decide (d.toNat < mask.toNat + c2.toNat)
  let c4 := decide (e.toNat < mask.toNat + c3.toNat)
  let c5 := decide (f.toNat < mask.toNat + c4.toNat)
  (a-x,b-mask-(BitVec.ofBool c0).setWidth 64,c-mask-(BitVec.ofBool c1).setWidth 64,
   d-mask-(BitVec.ofBool c2).setWidth 64,e-mask-(BitVec.ofBool c3).setWidth 64,
   f-mask-(BitVec.ofBool c4).setWidth 64,g-mask-(BitVec.ofBool c5).setWidth 64)

theorem nafSub7_value (a b c d e f g x mask : BitVec 64) :
    let out := nafSub7 a b c d e f g x mask
    (nafVal7 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 out.2.2.2.2.2.1 out.2.2.2.2.2.2 +
      nafVal7 x mask mask mask mask mask mask)%(2^256*2^192) = nafVal7 a b c d e f g := by
  have hb := nafVal7_lt a b c d e f g
  dsimp only [nafSub7,nafVal7] at hb ⊢
  have h0 := sub_borrow a x
  generalize decide (a.toNat < x.toNat) = c0 at h0 ⊢
  have h1 := sbb_borrow b mask c0
  generalize decide (b.toNat < mask.toNat + c0.toNat) = c1 at h1 ⊢
  have h2 := sbb_borrow c mask c1
  generalize decide (c.toNat < mask.toNat + c1.toNat) = c2 at h2 ⊢
  have h3 := sbb_borrow d mask c2
  generalize decide (d.toNat < mask.toNat + c2.toNat) = c3 at h3 ⊢
  have h4 := sbb_borrow e mask c3
  generalize decide (e.toNat < mask.toNat + c3.toNat) = c4 at h4 ⊢
  have h5 := sbb_borrow f mask c4
  generalize decide (f.toNat < mask.toNat + c4.toNat) = c5 at h5 ⊢
  have h6 := sbb_borrow g mask c5
  generalize decide (g.toNat < mask.toNat + c5.toNat) = c6 at h6 ⊢
  have h0' : (a-x).toNat+x.toNat+0=a.toNat+2^64*c0.toNat := by rw [Nat.add_zero]; exact h0
  refine mod_of_chain (c:=c6.toNat) (sbb_chain h0' <| sbb_chain h1 <| sbb_chain h2 <| sbb_chain h3 <|
    sbb_chain h4 <| sbb_chain h5 h6) hb ?_
  cases c6 <;> decide

/-- Ten words: a scalar of nine words and its top word (as `nafVal7`, in
Horner form; a definition, so that `omega` takes it as one atom rather than
ten words, which it would eliminate in exponential time). -/
def nafVal10 (a b c d e f g h i l : BitVec 64) : Nat :=
  a.toNat+2^64*(b.toNat+2^64*(c.toNat+2^64*(d.toNat+2^64*(e.toNat+2^64*(f.toNat+2^64*(g.toNat+2^64*
    (h.toNat+2^64*(i.toNat+2^64*l.toNat))))))))

/-- `nafVal10` unfolded. Rewrite with this, not `simp [nafVal10]`: generating
`nafVal10`'s equation lemma takes seconds. -/
theorem nafVal10_unfold (a b c d e f g h i l : BitVec 64) : nafVal10 a b c d e f g h i l =
    a.toNat+2^64*(b.toNat+2^64*(c.toNat+2^64*(d.toNat+2^64*(e.toNat+2^64*(f.toNat+2^64*(g.toNat+2^64*
      (h.toNat+2^64*(i.toNat+2^64*l.toNat)))))))) := (rfl)

/-- A word at a time (`omega` on all ten at once is exponential). -/
theorem nafVal10_lt (a b c d e f g h i l : BitVec 64) :
    nafVal10 a b c d e f g h i l<2^256*2^256*2^128 :=
  Nat.lt_of_lt_of_eq (horner_lt a.isLt <| horner_lt b.isLt <| horner_lt c.isLt <| horner_lt d.isLt <|
    horner_lt e.isLt <| horner_lt f.isLt <| horner_lt g.isLt <| horner_lt h.isLt <|
    horner_lt i.isLt l.isLt) (by decide)

/-- `nafSub5` for ten words. -/
def nafSub10 (a b c d e f g h i l x mask : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
      BitVec 64 × BitVec 64 × BitVec 64 :=
  let c0 := decide (a.toNat < x.toNat)
  let c1 := decide (b.toNat < mask.toNat + c0.toNat)
  let c2 := decide (c.toNat < mask.toNat + c1.toNat)
  let c3 := decide (d.toNat < mask.toNat + c2.toNat)
  let c4 := decide (e.toNat < mask.toNat + c3.toNat)
  let c5 := decide (f.toNat < mask.toNat + c4.toNat)
  let c6 := decide (g.toNat < mask.toNat + c5.toNat)
  let c7 := decide (h.toNat < mask.toNat + c6.toNat)
  let c8 := decide (i.toNat < mask.toNat + c7.toNat)
  (a-x,
   b-mask-(BitVec.ofBool c0).setWidth 64,
   c-mask-(BitVec.ofBool c1).setWidth 64,
   d-mask-(BitVec.ofBool c2).setWidth 64,
   e-mask-(BitVec.ofBool c3).setWidth 64,
   f-mask-(BitVec.ofBool c4).setWidth 64,
   g-mask-(BitVec.ofBool c5).setWidth 64,
   h-mask-(BitVec.ofBool c6).setWidth 64,
   i-mask-(BitVec.ofBool c7).setWidth 64,
   l-mask-(BitVec.ofBool c8).setWidth 64)

theorem nafSub10_value (a b c d e f g h i l x mask : BitVec 64) :
    let out := nafSub10 a b c d e f g h i l x mask
    (nafVal10 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 out.2.2.2.2.2.1 out.2.2.2.2.2.2.1 out.2.2.2.2.2.2.2.1 out.2.2.2.2.2.2.2.2.1 out.2.2.2.2.2.2.2.2.2 +
      nafVal10 x mask mask mask mask mask mask mask mask mask)%(2^256*2^256*2^128) =
      nafVal10 a b c d e f g h i l := by
  have hb := nafVal10_lt a b c d e f g h i l
  dsimp only [nafSub10,nafVal10] at hb ⊢
  have h0 := sub_borrow a x
  generalize decide (a.toNat < x.toNat) = c0 at h0 ⊢
  have h1 := sbb_borrow b mask c0
  generalize decide (b.toNat < mask.toNat + c0.toNat) = c1 at h1 ⊢
  have h2 := sbb_borrow c mask c1
  generalize decide (c.toNat < mask.toNat + c1.toNat) = c2 at h2 ⊢
  have h3 := sbb_borrow d mask c2
  generalize decide (d.toNat < mask.toNat + c2.toNat) = c3 at h3 ⊢
  have h4 := sbb_borrow e mask c3
  generalize decide (e.toNat < mask.toNat + c3.toNat) = c4 at h4 ⊢
  have h5 := sbb_borrow f mask c4
  generalize decide (f.toNat < mask.toNat + c4.toNat) = c5 at h5 ⊢
  have h6 := sbb_borrow g mask c5
  generalize decide (g.toNat < mask.toNat + c5.toNat) = c6 at h6 ⊢
  have h7 := sbb_borrow h mask c6
  generalize decide (h.toNat < mask.toNat + c6.toNat) = c7 at h7 ⊢
  have h8 := sbb_borrow i mask c7
  generalize decide (i.toNat < mask.toNat + c7.toNat) = c8 at h8 ⊢
  have h9 := sbb_borrow l mask c8
  generalize decide (l.toNat < mask.toNat + c8.toNat) = c9 at h9 ⊢
  have h0' : (a-x).toNat+x.toNat+0=a.toNat+2^64*c0.toNat := by rw [Nat.add_zero]; exact h0
  refine mod_of_chain (c:=c9.toNat) (sbb_chain h0' <| sbb_chain h1 <| sbb_chain h2 <| sbb_chain h3 <|
    sbb_chain h4 <| sbb_chain h5 <| sbb_chain h6 <| sbb_chain h7 <| sbb_chain h8 h9) hb ?_
  cases c9 <;> decide

/-- The scalar's registers (`Naf.sregs n`: `n` words and a top word) as a number. -/
abbrev nafValN (n : Nat) (s : State) : Nat := VG.Proof.Mont.X86_64.regsVal s (Naf.sregs n)

theorem nafValN_four (s : State) :
    nafValN 4 s=nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) := by
  simp only [nafValN,Naf.sregs,List.take,VG.Proof.Mont.X86_64.regsVal,nafVal5]
  omega

theorem nafValN_six (s : State) :
    nafValN 6 s=nafVal7 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)
      (s.gpr .r13) (s.gpr .r14) := by
  simp only [nafValN,Naf.sregs,List.take,VG.Proof.Mont.X86_64.regsVal,nafVal7]
  omega

theorem nafValN_nine (s : State) :
    nafValN 9 s=nafVal10 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)
      (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rbp) (s.gpr .rsi) := by
  -- Not `simp [nafVal10]`: generating `nafVal10`'s equation lemma takes seconds.
  simp only [nafValN,Naf.sregs,List.take,VG.Proof.Mont.X86_64.regsVal,Nat.mul_zero,Nat.add_zero]
  rfl

/-- The low word of the scalar's registers. -/
theorem nafValN_r8 (n : Nat) (s : State) :
    nafValN n s=(s.gpr .r8).toNat+2^64*VG.Proof.Mont.X86_64.regsVal s
      ([Reg.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi].take n) := rfl

/-- Equal values of the scalar's registers are equal registers. -/
theorem regsVal_inj {s t : State} : ∀ {rs : List Reg},
    VG.Proof.Mont.X86_64.regsVal s rs=VG.Proof.Mont.X86_64.regsVal t rs →
      ∀ r∈rs,s.gpr r=t.gpr r
  | [],_,r,hr => absurd hr List.not_mem_nil
  | q::qs,h,r,hr => by
    simp only [VG.Proof.Mont.X86_64.regsVal] at h
    have := (s.gpr q).isLt; have := (t.gpr q).isLt
    have hq : s.gpr q=t.gpr q := BitVec.eq_of_toNat_eq (by omega)
    rcases List.mem_cons.mp hr with rfl|hr
    · exact hq
    · exact regsVal_inj (by omega) r hr

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
