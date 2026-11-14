module

-- separate module: The consolidated sixteen-step doubling/context induction costs about one second versus 0.39s of imports; DoubleOutput changes reuse this checked body.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleBlocks
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointResult
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointRebase
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- The two point buffers and seven-field temporary area use separate labels. -/
def doubleSlot (a o : Nat) (i : Nat) : Nat :=
  if i<3 then a+72*i else if i<6 then o+72*(i-3) else 4080+72*(i-6)

structure DoubleContext (base : Addr) (a o : Nat) (s : State) : Prop where
  input : Ptr s .x27 (off base a) 216
  temp : Ptr s .x28 (off base 4080) 504
  tempW : PtrW s .x28 (off base 4080) 504
  output : PtrW s .x26 (off base o) 216

theorem DoubleContext.of_keepRegs {base : Addr} {a o : Nat} {s t : State}
    (h : DoubleContext base a o s) (k : KeepRegs pointFullProductClob s t) : DoubleContext base a o t := by
  have ptr {r : Reg} {p : Addr} {n : Nat} (hp : Ptr s r p n) (hr : r∉pointFullProductClob) : Ptr t r p n :=
    ⟨(k.gpr r hr).trans hp.reg,by rw [k.rd,k.wr]; exact hp.ld,hp.enc⟩
  exact ⟨ptr h.input (by decide),ptr h.temp (by decide),h.tempW.of_keepRegs k (by decide),
    h.output.of_keepRegs k (by decide)⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.Proof.Mont

/-- Only the output point and the temporary field slots may change. -/
def DoubleFrame (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<o ∨ o+216≤ofs base x) →
    (ofs base x<4080 ∨ 4584≤ofs base x) → m' x=m x

theorem DoubleFrame.trans {base : Addr} {o : Nat} {m m' m'' : Mem}
    (h : DoubleFrame base o m m') (k : DoubleFrame base o m' m'') : DoubleFrame base o m m'' :=
  fun x ho ht => (k x ho ht).trans (h x ho ht)

theorem double_slot_frame {base : Addr} {a o out : Nat} {m m' : Mem}
    (lo : 3≤out) (hi : out<13) (h : Outside base (doubleSlot a o out) 72 m m') :
    DoubleFrame base o m m' := by
  intro x ho ht
  apply h x
  by_cases h6 : out<6
  · have hb : out-3≤2 := by omega_arith
    simp only [doubleSlot,show ¬out<3 by omega_arith,ite_false,h6,ite_true] at *
    omega_arith
  · simp only [doubleSlot,show ¬out<3 by omega_arith,ite_false,h6] at *
    omega_arith

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step3 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 0∈V) (readB : 6∈V) (capA : caps 0=1) (capB : caps 6=1) (zeroIn : s.gpr .x1=0)
    (apart : ∀x∈V,x≠10 → doubleSlot a o x+72≤doubleSlot a o 10 ∨ doubleSlot a o 10+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSub0Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (10::V) (Function.update E 10 (E 0-E 6))
        (Function.update caps 10 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 0=a+0 := rfl
  have locB : doubleSlot a o 6=4080+0 := rfl
  have locO : doubleSlot a o 10=4080+288 := rfl
  have hA := inv.bound 0 readA
  have hB := inv.bound 6 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base a) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := DoubleSub0_ok ctx.input ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.sub 10 0 6) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+288+72<2^64)
  have ni := inv.point_update (.sub 10 0 6)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,(k.gpr .x1 (by decide)).trans zeroIn,kc,double_slot_frame (out:=10) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step5 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 1∈V) (readB : 2∈V) (capA : caps 1=1) (capB : caps 2=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠11 → doubleSlot a o x+72≤doubleSlot a o 11 ∨ doubleSlot a o 11+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleAdd1Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (11::V) (Function.update E 11 (E 1+E 2))
        (Function.update caps 11 1) t ∧ DoubleContext base a o t ∧ t.gpr .x2=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 1=a+72 := rfl
  have locB : doubleSlot a o 2=a+144 := rfl
  have locO : doubleSlot a o 11=4080+360 := rfl
  have hA := inv.bound 1 readA
  have hB := inv.bound 2 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base a) 72 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base a) 144 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := DoubleAdd1_ok ctx.input ctx.input ctx.tempW (by decide) (by decide) (by decide) zeroIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.add 11 1 2) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+360+72<2^64)
  have ni := inv.point_update (.add 11 1 2)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,kc,double_slot_frame (out:=11) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)

theorem double_step6 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readZ : 8∈V) (capZ : caps 8=1)
    (apart : ∀x∈V,x≠12 → doubleSlot a o x+72≤doubleSlot a o 12 ∨ doubleSlot a o 12+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSquare2Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (12::V) (Function.update E 12 (E 8*E 8))
        (Function.update caps 12 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have hz := inv.bound 8 readZ
  rw [capZ,Nat.one_mul] at hz
  have locA : doubleSlot a o 8=4080+144 := rfl
  have locO : doubleSlot a o 12=4080+432 := rfl
  have zBound : wordsVal s.mem (off base 4080) 144 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hz
  refine WP.mono (DoubleSquare2_ok ctx.temp ctx.tempW (by decide) (by decide) zBound)
    fun t ⟨bound,value,zero,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 12 8 8 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locA,locO,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+432+72<2^64)
  have ni := inv.point_update (.mul 12 8 8 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readZ)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capZ]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,k,double_slot_frame (out:=12) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step4 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 11∈V) (readB : 10∈V) (capA : caps 11=1) (capB : caps 10=1)
    (apart : ∀x∈V,x≠8 → doubleSlot a o x+72≤doubleSlot a o 8 ∨ doubleSlot a o 8+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleMul0FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (8::V) (Function.update E 8 (E 11*E 10))
        (Function.update caps 8 1) t ∧ DoubleContext base a o t ∧ t.gpr .x2=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 11=4080+360 := rfl
  have locB : doubleSlot a o 10=4080+288 := rfl
  have locO : doubleSlot a o 8=4080+144 := rfl
  have hA := inv.bound 11 readA
  have hB := inv.bound 10 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base 4080) 360) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 288) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base 4080) 360) (off (off base 4080) 144) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=4440) (o:=4224)
      (by decide) (by decide) (by decide)
  refine WP.mono (DoubleMul0Field_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) stable aBound bBound)
    fun t ⟨bound,value,zero,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 8 11 10 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4224) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4224+0+72<2^64)
  have ni := inv.point_update (.mul 8 11 10 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,k,double_slot_frame (out:=8) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step9 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 9∈V) (readB : 12∈V) (capA : caps 9=2) (capB : caps 12=1) 
    (apart : ∀x∈V,x≠12 → doubleSlot a o x+72≤doubleSlot a o 12 ∨ doubleSlot a o 12+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block doubleCms12Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (12::V)
        (Function.update E 12 (VG.Proof.Weierstrass.Cms.smulN 12 (E 9)-VG.Proof.Weierstrass.Cms.smulN 9 (E 12)))
        (Function.update caps 12 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 9=4080+216 := rfl
  have locB : doubleSlot a o 12=4080+432 := rfl
  have locO : doubleSlot a o 12=4080+432 := rfl
  have hA := inv.bound 9 readA
  have hB := inv.bound 12 readB
  rw [capA] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 216 9<2*fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 432 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := double_cms12_ok ctx.tempW (by decide) (by decide)
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound) fun t ⟨value,bound,zero,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.cms 12 12 9 9 12) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+432+72<2^64)
  have ni := inv.point_update (.cms 12 12 9 9 12)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inr ⟨12,9,9,12,rfl,rfl,by rw [capA]⟩
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o' C' a' D' b' he; cases he; rw [capB])
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,zero,kc,double_slot_frame (out:=12) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step7 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (inputLow : a+216≤4080)
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 0∈V) (readB : 7∈V) (capA : caps 0=1) (capB : caps 7=1)
    (apart : ∀x∈V,x≠9 → doubleSlot a o x+72≤doubleSlot a o 9 ∨ doubleSlot a o 9+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleMul1FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (9::V) (Function.update E 9 (E 0*E 7))
        (Function.update caps 9 2) t ∧ DoubleContext base a o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 0=a+0 := rfl
  have locB : doubleSlot a o 7=4080+72 := rfl
  have locO : doubleSlot a o 9=4080+216 := rfl
  have hA := inv.bound 0 readA
  have hB := inv.bound 7 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base a) 0) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 72) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base a) 0) (off (off base 4080) 216) := by
    simpa only [off_off,Nat.add_zero] using stable_input_apart (s:=s) (base:=base) (a:=a) (o:=4296)
      (Or.inl (by omega_arith)) (by omega_arith) (by decide)
  refine WP.mono (DoubleMul1Field_ok ctx.input ctx.temp ctx.tempW (by decide) (by decide) (by decide) stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 9 0 7 true) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.add_zero] using bound
    · simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.add_zero] using value
    · have om : Outside (off base 4296) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4296+0+72<2^64)
  have ni := inv.point_update (.mul 9 0 7 true)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,mask,k,double_slot_frame (out:=9) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)

theorem double_step1 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readZ : 1∈V) (capZ : caps 1=1) (zeroIn : s.gpr .x1=0)
    (apart : ∀x∈V,x≠7 → doubleSlot a o x+72≤doubleSlot a o 7 ∨ doubleSlot a o 7+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSquare1Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (7::V) (Function.update E 7 (E 1*E 1))
        (Function.update caps 7 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have hz := inv.bound 1 readZ
  rw [capZ,Nat.one_mul] at hz
  have zBound : wordsVal s.mem (off base a) 72 9<fieldPrime := by
    simpa only [doubleSlot,wordsVal_off,show (1 : Nat)<3 from by decide,ite_true,Nat.reduceMul] using hz
  refine WP.mono (DoubleSquare1_ok ctx.input ctx.tempW (by decide) (by decide) zeroIn zBound)
    fun t ⟨bound,value,zero,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 7 1 1 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,doubleSlot,show ¬(7 : Nat)<3 from by decide,
        show ¬(7 : Nat)<6 from by decide,ite_false,Nat.reduceSub,Nat.reduceMul,Nat.add_zero,
        Nat.one_mul,wordsVal_off] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,doubleSlot,show ¬(7 : Nat)<3 from by decide,
        show ¬(7 : Nat)<6 from by decide,show (1 : Nat)<3 from by decide,ite_false,ite_true,
        Nat.reduceSub,Nat.reduceMul,Nat.add_zero,Nat.reduceMul,wordsVal_off,Nat.mod_mod] using he
    · have he := outside_rebase outside (by decide : 4080+72+72<2^64)
      simpa only [PointOp.out,doubleSlot,show ¬(7 : Nat)<3 from by decide,
        show ¬(7 : Nat)<6 from by decide,ite_false,Nat.reduceSub,Nat.reduceMul,Nat.add_zero] using he
  have ni := inv.point_update (.mul 7 1 1 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readZ)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capZ]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,k,double_slot_frame (out:=7) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step2 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 0∈V) (readB : 6∈V) (capA : caps 0=1) (capB : caps 6=1) (zeroIn : s.gpr .x1=0)
    (apart : ∀x∈V,x≠11 → doubleSlot a o x+72≤doubleSlot a o 11 ∨ doubleSlot a o 11+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleAdd0Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (11::V) (Function.update E 11 (E 0+E 6))
        (Function.update caps 11 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 0=a+0 := rfl
  have locB : doubleSlot a o 6=4080+0 := rfl
  have locO : doubleSlot a o 11=4080+360 := rfl
  have hA := inv.bound 0 readA
  have hB := inv.bound 6 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base a) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := DoubleAdd0_ok ctx.input ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.add 11 0 6) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+360+72<2^64)
  have ni := inv.point_update (.add 11 0 6)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,(k.gpr .x1 (by decide)).trans zeroIn,kc,double_slot_frame (out:=11) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)

theorem double_step0 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readZ : 2∈V) (capZ : caps 2=1)
    (apart : ∀x∈V,x≠6 → doubleSlot a o x+72≤doubleSlot a o 6 ∨ doubleSlot a o 6+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSquare0Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (6::V) (Function.update E 6 (E 2*E 2))
        (Function.update caps 6 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have hz := inv.bound 2 readZ
  rw [capZ,Nat.one_mul] at hz
  have zBound : wordsVal s.mem (off base a) 144 9<fieldPrime := by
    simpa only [doubleSlot,wordsVal_off,show (2 : Nat)<3 from by decide,ite_true,Nat.reduceMul] using hz
  refine WP.mono (DoubleSquare0_ok ctx.input ctx.tempW (by decide) (by decide) zBound)
    fun t ⟨bound,value,zero,_,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 6 2 2 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,doubleSlot,show ¬(6 : Nat)<3 from by decide,
        show ¬(6 : Nat)<6 from by decide,ite_false,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
        Nat.one_mul,wordsVal_off] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,doubleSlot,show ¬(6 : Nat)<3 from by decide,
        show ¬(6 : Nat)<6 from by decide,show (2 : Nat)<3 from by decide,ite_false,ite_true,
        Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.reduceMul,wordsVal_off,Nat.mod_mod] using he
    · have he := outside_rebase outside (by decide : 4080+0+72<2^64)
      simpa only [PointOp.out,doubleSlot,show ¬(6 : Nat)<3 from by decide,
        show ¬(6 : Nat)<6 from by decide,ite_false,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using he
  have ni := inv.point_update (.mul 6 2 2 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readZ)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capZ]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,k,double_slot_frame (out:=6) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step15 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (outputLow : o+216≤4080)
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 11∈V) (readB : 10∈V) (capA : caps 11=2) (capB : caps 10=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x1=511)
    (apart : ∀x∈V,x≠4 → doubleSlot a o x+72≤doubleSlot a o 4 ∨ doubleSlot a o 4+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block doubleCms38Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (4::V)
        (Function.update E 4 (VG.Proof.Weierstrass.Cms.smulN 3 (E 11)-VG.Proof.Weierstrass.Cms.smulN 8 (E 10)))
        (Function.update caps 4 1) t ∧ DoubleContext base a o t ∧ t.gpr .x2=0 ∧ t.gpr .x1=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 11=4080+360 := rfl
  have locB : doubleSlot a o 10=4080+288 := rfl
  have locO : doubleSlot a o 4=o+72 := rfl
  have hA := inv.bound 11 readA
  have hB := inv.bound 10 readB
  rw [capA] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 360 9<2*fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 288 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := double_cms38_ok ctx.temp ctx.output (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound) fun t ⟨value,bound,mask,zero,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.cms 4 3 11 8 10) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by omega_arith : o+72+72<2^64)
  have ni := inv.point_update (.cms 4 3 11 8 10)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inr ⟨3,11,8,10,rfl,rfl,by rw [capA]⟩
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o' C' a' D' b' he; cases he; rw [capB])
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,double_slot_frame (out:=4) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

structure DoubleLayout (a o : Nat) : Prop where
  inputLow : a+216≤4080
  outputLow : o+216≤4080
  apart : ∀i<13,∀j<13,i≠j → doubleSlot a o i+72≤doubleSlot a o j ∨ doubleSlot a o j+72≤doubleSlot a o i
  fits : ∀i<13,doubleSlot a o i+72≤2^64

theorem double_layout_forward : DoubleLayout 1072 1288 := by constructor <;> decide

theorem double_layout_backward : DoubleLayout 1288 1072 := by constructor <;> decide

theorem DoubleLayout.live_apart {a o : Nat} (h : DoubleLayout a o) {V : List Nat}
    (live : ∀x∈V,x<13) {out : Nat} (hout : out<13) :
    ∀x∈V,x≠out → doubleSlot a o x+72≤doubleSlot a o out ∨ doubleSlot a o out+72≤doubleSlot a o x :=
  fun x hx hne => h.apart x (live x hx) out hout hne

theorem DoubleLayout.live_fits {a o : Nat} (h : DoubleLayout a o) {V : List Nat}
    (live : ∀x∈V,x<13) : ∀x∈V,doubleSlot a o x+72≤2^64 := fun x hx => h.fits x (live x hx)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step14 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (outputLow : o+216≤4080)
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 9∈V) (readB : 12∈V) (capA : caps 9=2) (capB : caps 12=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠3 → doubleSlot a o x+72≤doubleSlot a o 3 ∨ doubleSlot a o 3+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block doubleCms41Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (3::V)
        (Function.update E 3 (VG.Proof.Weierstrass.Cms.smulN 4 (E 9)-VG.Proof.Weierstrass.Cms.smulN 1 (E 12)))
        (Function.update caps 3 1) t ∧ DoubleContext base a o t ∧ t.gpr .x2=0 ∧ t.gpr .x1=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 9=4080+216 := rfl
  have locB : doubleSlot a o 12=4080+432 := rfl
  have locO : doubleSlot a o 3=o+0 := rfl
  have hA := inv.bound 9 readA
  have hB := inv.bound 12 readB
  rw [capA] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 216 9<2*fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 432 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := double_cms41_ok ctx.temp ctx.output (by decide) (by decide) (by decide) zeroIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound) fun t ⟨value,bound,mask,zero,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.cms 3 4 9 1 12) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.one_mul] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by omega_arith : o+0+72<2^64)
  have ni := inv.point_update (.cms 3 4 9 1 12)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inr ⟨4,9,1,12,rfl,rfl,by rw [capA]⟩
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o' C' a' D' b' he; cases he; rw [capB])
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,double_slot_frame (out:=3) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step12 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (outputLow : o+216≤4080)
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 11∈V) (readB : 7∈V) (capA : caps 11=1) (capB : caps 7=1) (zeroIn : s.gpr .x1=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠5 → doubleSlot a o x+72≤doubleSlot a o 5 ∨ doubleSlot a o 5+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSub2Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (5::V) (Function.update E 5 (E 11-E 7))
        (Function.update caps 5 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 11=4080+360 := rfl
  have locB : doubleSlot a o 7=4080+72 := rfl
  have locO : doubleSlot a o 5=o+144 := rfl
  have hA := inv.bound 11 readA
  have hB := inv.bound 7 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 360 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 72 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := DoubleSub2_ok ctx.temp ctx.temp ctx.output (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.sub 5 11 7) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by omega_arith : o+144+72<2^64)
  have ni := inv.point_update (.sub 5 11 7)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,(k.gpr .x1 (by decide)).trans zeroIn,mask,kc,double_slot_frame (out:=5) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step10 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 10∈V) (readB : 6∈V) (capA : caps 10=1) (capB : caps 6=1) (zeroIn : s.gpr .x1=0)
    (apart : ∀x∈V,x≠11 → doubleSlot a o x+72≤doubleSlot a o 11 ∨ doubleSlot a o 11+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSub1Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (11::V) (Function.update E 11 (E 10-E 6))
        (Function.update caps 11 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 10=4080+288 := rfl
  have locB : doubleSlot a o 6=4080+0 := rfl
  have locO : doubleSlot a o 11=4080+360 := rfl
  have hA := inv.bound 10 readA
  have hB := inv.bound 6 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 288 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := DoubleSub1_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.sub 11 10 6) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+360+72<2^64)
  have ni := inv.point_update (.sub 11 10 6)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  exact ⟨ni,ctx.of_keepRegs kc,(k.gpr .x1 (by decide)).trans zeroIn,mask,kc,double_slot_frame (out:=11) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)

theorem double_step8 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readZ : 11∈V) (capZ : caps 11=1)
    (apart : ∀x∈V,x≠10 → doubleSlot a o x+72≤doubleSlot a o 10 ∨ doubleSlot a o 10+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSquare3Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (10::V) (Function.update E 10 (E 11*E 11))
        (Function.update caps 10 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have hz := inv.bound 11 readZ
  rw [capZ,Nat.one_mul] at hz
  have locA : doubleSlot a o 11=4080+360 := rfl
  have locO : doubleSlot a o 10=4080+288 := rfl
  have zBound : wordsVal s.mem (off base 4080) 360 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hz
  refine WP.mono (DoubleSquare3_ok ctx.temp ctx.tempW (by decide) (by decide) zBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 10 11 11 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locA,locO,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+288+72<2^64)
  have ni := inv.point_update (.mul 10 11 11 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readZ)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capZ]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,mask,k,double_slot_frame (out:=10) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem double_step13 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readA : 12∈V) (readB : 8∈V) (capA : caps 12=1) (capB : caps 8=1)
    (apart : ∀x∈V,x≠11 → doubleSlot a o x+72≤doubleSlot a o 11 ∨ doubleSlot a o 11+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleMul2FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (11::V) (Function.update E 11 (E 12*E 8))
        (Function.update caps 11 2) t ∧ DoubleContext base a o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have locA : doubleSlot a o 12=4080+432 := rfl
  have locB : doubleSlot a o 8=4080+144 := rfl
  have locO : doubleSlot a o 11=4080+360 := rfl
  have hA := inv.bound 12 readA
  have hB := inv.bound 8 readB
  rw [capA,Nat.one_mul] at hA
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base 4080) 432) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 144) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base 4080) 432) (off (off base 4080) 360) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=4512) (o:=4440)
      (by decide) (by decide) (by decide)
  refine WP.mono (DoubleMul2Field_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 11 12 8 true) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.add_zero] using bound
    · simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.add_zero] using value
    · have om : Outside (off base 4440) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4440+0+72<2^64)
  have ni := inv.point_update (.mul 11 12 8 true)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> with_reducible assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,mask,k,double_slot_frame (out:=11) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)

theorem double_step11 [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : DoubleContext base a o s) (inv : OrdinaryInv base fieldPrime (doubleSlot a o) V E caps s)
    (readZ : 7∈V) (capZ : caps 7=1) (zeroIn : s.gpr .x1=0)
    (apart : ∀x∈V,x≠10 → doubleSlot a o x+72≤doubleSlot a o 10 ∨ doubleSlot a o 10+72≤doubleSlot a o x)
    (fits : ∀x∈V,doubleSlot a o x+72≤2^64) :
    WP isa (.block DoubleSquare4Code) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (10::V) (Function.update E 10 (E 7*E 7))
        (Function.update caps 10 1) t ∧ DoubleContext base a o t ∧ t.gpr .x1=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  have hz := inv.bound 7 readZ
  rw [capZ,Nat.one_mul] at hz
  have locA : doubleSlot a o 7=4080+72 := rfl
  have locO : doubleSlot a o 10=4080+288 := rfl
  have zBound : wordsVal s.mem (off base 4080) 72 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hz
  refine WP.mono (DoubleSquare4_ok ctx.temp ctx.tempW (by decide) (by decide) zeroIn zBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (doubleSlot a o) (.mul 10 7 7 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locA,locO,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+288+72<2^64)
  have ni := inv.point_update (.mul 10 7 7 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readZ)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capZ]))
    result apart fits (by intro o C a D b he; cases he)
  exact ⟨ni,ctx.of_keepRegs k,zero,mask,k,double_slot_frame (out:=10) (by decide) (by decide) result.outside⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def doubleLive (i : Nat) : List Nat := (doubleOps.take i).foldl (fun V op => op.out::V) [0,1,2]
def doubleCaps (i : Nat) : Nat → Nat := (doubleOps.take i).foldl (fun C op => Function.update C op.out op.cap) (fun _ => 1)

theorem double_body_ok [NeZero fieldPrime] {base : Addr} {a o : Nat} {s : State} {E : Nat → Fin fieldPrime}
    (layout : DoubleLayout a o) (ctx : DoubleContext base a o s)
    (inv : OrdinaryInv base fieldPrime (doubleSlot a o) [0,1,2] E (fun _ => 1) s) :
    WP isa (.block doubleArithmeticCode) s fun t =>
      OrdinaryInv base fieldPrime (doubleSlot a o) (doubleLive 16) (pointRun doubleOps E) (doubleCaps 16) t ∧
      DoubleContext base a o t ∧ KeepRegs pointFullProductClob s t ∧ DoubleFrame base o s.mem t.mem := by
  simp only [doubleArithmeticCode,doubleArithmeticBlocks,List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (double_step0 ctx inv (by decide) (by rfl) (layout.live_apart (by decide) (by decide : 6<13)) (layout.live_fits (by decide))) fun s1 ⟨I1,C1,Z1,K1,F1⟩ => ?_
  let Env1 : Nat → Fin fieldPrime := (doubleOps.getD 0 (.mul 0 0 0 false)).run E
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env1 _ _ at I1
  rw [WP.block_append_iff]
  refine WP.mono (double_step1 (E:=Env1) C1 I1 (by decide) (by rfl) Z1 (layout.live_apart (by decide) (by decide : 7<13)) (layout.live_fits (by decide))) fun s2 ⟨I2,C2,Z2,K2,F2⟩ => ?_
  let Env2 : Nat → Fin fieldPrime := (doubleOps.getD 1 (.mul 0 0 0 false)).run Env1
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env2 _ _ at I2
  rw [WP.block_append_iff]
  refine WP.mono (double_step2 (E:=Env2) C2 I2 (by decide) (by decide) (by rfl) (by rfl) Z2 (layout.live_apart (by decide) (by decide : 11<13)) (layout.live_fits (by decide))) fun s3 ⟨I3,C3,Z3,K3,F3⟩ => ?_
  let Env3 : Nat → Fin fieldPrime := (doubleOps.getD 2 (.mul 0 0 0 false)).run Env2
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env3 _ _ at I3
  rw [WP.block_append_iff]
  refine WP.mono (double_step3 (E:=Env3) C3 I3 (by decide) (by decide) (by rfl) (by rfl) Z3 (layout.live_apart (by decide) (by decide : 10<13)) (layout.live_fits (by decide))) fun s4 ⟨I4,C4,Z4,K4,F4⟩ => ?_
  let Env4 : Nat → Fin fieldPrime := (doubleOps.getD 3 (.mul 0 0 0 false)).run Env3
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env4 _ _ at I4
  rw [WP.block_append_iff]
  refine WP.mono (double_step4 (E:=Env4) C4 I4 (by decide) (by decide) (by rfl) (by rfl) (layout.live_apart (by decide) (by decide : 8<13)) (layout.live_fits (by decide))) fun s5 ⟨I5,C5,Z5,K5,F5⟩ => ?_
  let Env5 : Nat → Fin fieldPrime := (doubleOps.getD 4 (.mul 0 0 0 false)).run Env4
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env5 _ _ at I5
  rw [WP.block_append_iff]
  refine WP.mono (double_step5 (E:=Env5) C5 I5 (by decide) (by decide) (by rfl) (by rfl) Z5 (layout.live_apart (by decide) (by decide : 11<13)) (layout.live_fits (by decide))) fun s6 ⟨I6,C6,Z6,K6,F6⟩ => ?_
  let Env6 : Nat → Fin fieldPrime := (doubleOps.getD 5 (.mul 0 0 0 false)).run Env5
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env6 _ _ at I6
  rw [WP.block_append_iff]
  refine WP.mono (double_step6 (E:=Env6) C6 I6 (by decide) (by rfl) (layout.live_apart (by decide) (by decide : 12<13)) (layout.live_fits (by decide))) fun s7 ⟨I7,C7,Z7,K7,F7⟩ => ?_
  let Env7 : Nat → Fin fieldPrime := (doubleOps.getD 6 (.mul 0 0 0 false)).run Env6
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env7 _ _ at I7
  rw [WP.block_append_iff]
  refine WP.mono (double_step7 (E:=Env7) layout.inputLow C7 I7 (by decide) (by decide) (by rfl) (by rfl) (layout.live_apart (by decide) (by decide : 9<13)) (layout.live_fits (by decide))) fun s8 ⟨I8,C8,Z8,M8,K8,F8⟩ => ?_
  let Env8 : Nat → Fin fieldPrime := (doubleOps.getD 7 (.mul 0 0 0 false)).run Env7
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env8 _ _ at I8
  rw [WP.block_append_iff]
  refine WP.mono (double_step8 (E:=Env8) C8 I8 (by decide) (by rfl) (layout.live_apart (by decide) (by decide : 10<13)) (layout.live_fits (by decide))) fun s9 ⟨I9,C9,Z9,M9,K9,F9⟩ => ?_
  let Env9 : Nat → Fin fieldPrime := (doubleOps.getD 8 (.mul 0 0 0 false)).run Env8
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env9 _ _ at I9
  rw [WP.block_append_iff]
  refine WP.mono (double_step9 (E:=Env9) C9 I9 (by decide) (by decide) (by rfl) (by rfl) (layout.live_apart (by decide) (by decide : 12<13)) (layout.live_fits (by decide))) fun s10 ⟨I10,C10,Z10,K10,F10⟩ => ?_
  let Env10 : Nat → Fin fieldPrime := (doubleOps.getD 9 (.mul 0 0 0 false)).run Env9
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env10 _ _ at I10
  rw [WP.block_append_iff]
  refine WP.mono (double_step10 (E:=Env10) C10 I10 (by decide) (by decide) (by rfl) (by rfl) Z10 (layout.live_apart (by decide) (by decide : 11<13)) (layout.live_fits (by decide))) fun s11 ⟨I11,C11,Z11,M11,K11,F11⟩ => ?_
  let Env11 : Nat → Fin fieldPrime := (doubleOps.getD 10 (.mul 0 0 0 false)).run Env10
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env11 _ _ at I11
  rw [WP.block_append_iff]
  refine WP.mono (double_step11 (E:=Env11) C11 I11 (by decide) (by rfl) Z11 (layout.live_apart (by decide) (by decide : 10<13)) (layout.live_fits (by decide))) fun s12 ⟨I12,C12,Z12,M12,K12,F12⟩ => ?_
  let Env12 : Nat → Fin fieldPrime := (doubleOps.getD 11 (.mul 0 0 0 false)).run Env11
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env12 _ _ at I12
  rw [WP.block_append_iff]
  refine WP.mono (double_step12 (E:=Env12) layout.outputLow C12 I12 (by decide) (by decide) (by rfl) (by rfl) Z12 M12 (layout.live_apart (by decide) (by decide : 5<13)) (layout.live_fits (by decide))) fun s13 ⟨I13,C13,Z13,M13,K13,F13⟩ => ?_
  let Env13 : Nat → Fin fieldPrime := (doubleOps.getD 12 (.mul 0 0 0 false)).run Env12
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env13 _ _ at I13
  rw [WP.block_append_iff]
  refine WP.mono (double_step13 (E:=Env13) C13 I13 (by decide) (by decide) (by rfl) (by rfl) (layout.live_apart (by decide) (by decide : 11<13)) (layout.live_fits (by decide))) fun s14 ⟨I14,C14,Z14,M14,K14,F14⟩ => ?_
  let Env14 : Nat → Fin fieldPrime := (doubleOps.getD 13 (.mul 0 0 0 false)).run Env13
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env14 _ _ at I14
  rw [WP.block_append_iff]
  refine WP.mono (double_step14 (E:=Env14) layout.outputLow C14 I14 (by decide) (by decide) (by rfl) (by rfl) Z14 (layout.live_apart (by decide) (by decide : 3<13)) (layout.live_fits (by decide))) fun s15 ⟨I15,C15,Z15,M15,K15,F15⟩ => ?_
  let Env15 : Nat → Fin fieldPrime := (doubleOps.getD 14 (.mul 0 0 0 false)).run Env14
  change OrdinaryInv base fieldPrime (doubleSlot a o) _ Env15 _ _ at I15
  refine WP.mono (double_step15 (E:=Env15) layout.outputLow C15 I15 (by decide) (by decide) (by rfl) (by rfl) Z15 M15 (layout.live_apart (by decide) (by decide : 4<13)) (layout.live_fits (by decide))) fun s16 ⟨I16,C16,Z16,M16,K16,F16⟩ => ?_
  exact ⟨I16,C16,(((((((((((((((K1.trans K2).trans K3).trans K4).trans K5).trans K6).trans K7).trans K8).trans K9).trans K10).trans K11).trans K12).trans K13).trans K14).trans K15).trans K16),(((((((((((((((F1.trans F2).trans F3).trans F4).trans F5).trans F6).trans F7).trans F8).trans F9).trans F10).trans F11).trans F12).trans F13).trans F14).trans F15).trans F16)⟩

end VG.Proof.Mont.AArch64.P521Field
