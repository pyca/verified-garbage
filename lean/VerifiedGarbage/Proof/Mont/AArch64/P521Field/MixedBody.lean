module

-- separate module: The mixed-add arithmetic/context induction over the checked instruction groups (mixed_body_arith) costs 2.32s of proof versus 0.42s of imports; MixedFunction composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedBlocks
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointResult
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointRebase
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointOps
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def mixedSlot (a b : Nat) (i : Nat) : Nat :=
  if i<3 then a+72*i else if i<5 then b+72*(i-3) else 4080+72*(i-5)

structure MixedContext (base : Addr) (a b o : Nat) (s : State) : Prop where
  input : Ptr s .x27 (off base a) 216
  affine : Ptr s .x28 (off base b) 144
  temp : Ptr s .x30 (off base 4080) 432
  tempW : PtrW s .x30 (off base 4080) 432
  output : PtrW s .x26 (off base o) 216
  inputLow : a+216≤4080
  affineLow : b+144≤4080

theorem MixedContext.of_keepRegs {base : Addr} {a b o : Nat} {s t : State}
    (h : MixedContext base a b o s) (k : KeepRegs pointFullProductClob s t) : MixedContext base a b o t := by
  have ptr {r : Reg} {p : Addr} {n : Nat} (hp : Ptr s r p n) (hr : r∉pointFullProductClob) : Ptr t r p n :=
    ⟨(k.gpr r hr).trans hp.reg,by rw [k.rd,k.wr]; exact hp.ld,hp.enc⟩
  exact ⟨ptr h.input (by decide),ptr h.affine (by decide),ptr h.temp (by decide),
    h.tempW.of_keepRegs k (by decide),h.output.of_keepRegs k (by decide),h.inputLow,h.affineLow⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Weierstrass

/-- Inputs X,Y,Z use 0..2 and affine x,y use 3..4. Labels 5..10 are
scratch offsets 0,72,144,216,288,360. Before the zero-Z mux, the resulting
Jacobian coordinates occupy labels 5,9,10. -/
def mixedOps : List PointOp := [
  .mul 5 2 2 false,.mul 6 2 4 false,.mul 7 5 3 false,.mul 6 5 6 false,
  .sub 10 7 0,.sub 6 6 1,.mul 8 10 10 false,.mul 5 6 6 false,
  .mul 9 8 0 false,.mul 7 8 7 false,.sub 5 5 9,.sub 8 7 9,
  .mul 10 2 10 false,.sub 5 5 7,.sub 9 9 5,.mul 8 1 8 false,
  .mul 9 6 9 false,.sub 9 9 8]

theorem mixedOps_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    (pointRun mixedOps E 5,pointRun mixedOps E 9,pointRun mixedOps E 10)=
      maddJF (E 0) (E 1) (E 2) (E 3) (E 4) := by
  rw [←nativeMixed_eq]
  simp only [pointRun,mixedOps,List.foldl,PointOp.run,Function.update_apply,nativeMixed,ite_true]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> grind

theorem mixedOps_reads : pointReadsOk mixedOps [0,1,2,3,4] (fun _ => 1)=true := by decide

/-- Every mixed-addition intermediate remains canonical. -/
theorem mixedOps_canonical : ∀op∈mixedOps,op.cap=1 := by
  simp only [mixedOps,List.mem_cons,List.not_mem_nil,or_false]
  intro op h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

structure MixedLayoutState (a b : Nat) : Prop where
  inputLow : a+216≤4080
  affineLow : b+144≤4080
  apart : a+216≤b ∨ b+144≤a

theorem MixedLayoutState.slots_apart {a b i j : Nat} (h : MixedLayoutState a b)
    (hi : i<11) (hj : j<11) (hne : i≠j) :
    mixedSlot a b i+72≤mixedSlot a b j ∨ mixedSlot a b j+72≤mixedSlot a b i := by
  have ha := h.inputLow
  have hb := h.affineLow
  have hab := h.apart
  unfold mixedSlot
  split_ifs <;> omega_arith

theorem MixedLayoutState.slot_bound {a b i : Nat} (h : MixedLayoutState a b) (hi : i<11) :
    mixedSlot a b i+72≤4512 := by
  have ha := h.inputLow
  have hb := h.affineLow
  unfold mixedSlot
  split_ifs <;> omega_arith

theorem mixed_caps_update (o : Nat) : Function.update (fun _ : Nat => 1) o 1=(fun _ => 1) := by
  funext x
  simp only [Function.update_apply]
  split <;> rfl

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step9 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 8∈V) (readB : 7∈V) (capA : caps 8=1) (capB : caps 7=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠7 → mixedSlot a b x+72≤mixedSlot a b 7 ∨ mixedSlot a b 7+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul7FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (7::V) (Function.update E 7 (E 8*E 7))
        (Function.update caps 7 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 8=4080+216 := rfl
  have locB : mixedSlot a b 7=4080+144 := rfl
  have locO : mixedSlot a b 7=4080+144 := rfl
  have hA := inv.bound 8 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 7 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base 4080) 216) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 144) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base 4080) 216) (off (off base 4080) 144) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=4296) (o:=4224)
      (by decide) (by decide) (by decide)
  refine WP.mono (MixedMul7Field_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 7 8 7 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4224) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4224+0+72<2^64)
  have ni := inv.point_update (.mul 7 8 7 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step17 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 9∈V) (readB : 8∈V) (capA : caps 9=1) (capB : caps 8=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠9 → mixedSlot a b x+72≤mixedSlot a b 9 ∨ mixedSlot a b 9+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSub6Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (9::V) (Function.update E 9 (E 9-E 8))
        (Function.update caps 9 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 9=4080+288 := rfl
  have locB : mixedSlot a b 8=4080+216 := rfl
  have locO : mixedSlot a b 9=4080+288 := rfl
  have hA := inv.bound 9 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 8 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 288 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 216 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := MixedSub6_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.sub 9 9 8) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+288+72<2^64)
  have ni := inv.point_update (.sub 9 9 8)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step13 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 5∈V) (readB : 7∈V) (capA : caps 5=1) (capB : caps 7=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠5 → mixedSlot a b x+72≤mixedSlot a b 5 ∨ mixedSlot a b 5+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSub4Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (5::V) (Function.update E 5 (E 5-E 7))
        (Function.update caps 5 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 5=4080+0 := rfl
  have locB : mixedSlot a b 7=4080+144 := rfl
  have locO : mixedSlot a b 5=4080+0 := rfl
  have hA := inv.bound 5 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 7 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 144 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := MixedSub4_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.sub 5 5 7) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+0+72<2^64)
  have ni := inv.point_update (.sub 5 5 7)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step3 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 5∈V) (readB : 6∈V) (capA : caps 5=1) (capB : caps 6=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠6 → mixedSlot a b x+72≤mixedSlot a b 6 ∨ mixedSlot a b 6+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul5FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (6::V) (Function.update E 6 (E 5*E 6))
        (Function.update caps 6 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 5=4080+0 := rfl
  have locB : mixedSlot a b 6=4080+72 := rfl
  have locO : mixedSlot a b 6=4080+72 := rfl
  have hA := inv.bound 5 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 6 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base 4080) 0) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 72) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base 4080) 0) (off (off base 4080) 72) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=4080) (o:=4152)
      (by decide) (by decide) (by decide)
  refine WP.mono (MixedMul5Field_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 6 5 6 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4152) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4152+0+72<2^64)
  have ni := inv.point_update (.mul 6 5 6 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step2 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 5∈V) (readB : 3∈V) (capA : caps 5=1) (capB : caps 3=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠7 → mixedSlot a b x+72≤mixedSlot a b 7 ∨ mixedSlot a b 7+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul4FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (7::V) (Function.update E 7 (E 5*E 3))
        (Function.update caps 7 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 5=4080+0 := rfl
  have locB : mixedSlot a b 3=b+0 := rfl
  have locO : mixedSlot a b 7=4080+144 := rfl
  have hA := inv.bound 5 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 3 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base 4080) 0) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base b) 0) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base 4080) 0) (off (off base 4080) 144) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=4080) (o:=4224)
      (by decide) (by decide) (by decide)
  refine WP.mono (MixedMul4Field_ok ctx.temp ctx.affine ctx.tempW (by decide) (by decide) (by decide) zeroIn stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 7 5 3 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4224) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4224+0+72<2^64)
  have ni := inv.point_update (.mul 7 5 3 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step12 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 2∈V) (readB : 10∈V) (capA : caps 2=1) (capB : caps 10=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠10 → mixedSlot a b x+72≤mixedSlot a b 10 ∨ mixedSlot a b 10+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul8FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (10::V) (Function.update E 10 (E 2*E 10))
        (Function.update caps 10 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 2=a+144 := rfl
  have locB : mixedSlot a b 10=4080+360 := rfl
  have locO : mixedSlot a b 10=4080+360 := rfl
  have hA := inv.bound 2 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 10 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base a) 144) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 360) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base a) 144) (off (off base 4080) 360) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=a+144) (o:=4440)
      (Or.inl (by have h:=ctx.inputLow; omega_arith)) (by have h:=ctx.inputLow; omega_arith) (by decide)
  refine WP.mono (MixedMul8Field_ok ctx.input ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 10 2 10 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4440) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4440+0+72<2^64)
  have ni := inv.point_update (.mul 10 2 10 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step6 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 10∈V) (capA : caps 10=1)
    (apart : ∀x∈V,x≠8 → mixedSlot a b x+72≤mixedSlot a b 8 ∨ mixedSlot a b 8+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSquare6Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (8::V) (Function.update E 8 (E 10*E 10))
        (Function.update caps 8 1) t ∧ MixedContext base a b o t ∧ t.gpr .x1=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 10=4080+360 := rfl
  have locO : mixedSlot a b 8=4080+216 := rfl
  have hA := inv.bound 10 readA
  rw [capA,Nat.one_mul] at hA
  have aBound : wordsVal s.mem (off base 4080) 360 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  refine WP.mono (MixedSquare6_ok ctx.temp ctx.tempW (by decide) (by decide) aBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 8 10 10 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+216+72<2^64)
  have ni := inv.point_update (.mul 8 10 10 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readA)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capA]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step1 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 2∈V) (readB : 4∈V) (capA : caps 2=1) (capB : caps 4=1)
    (apart : ∀x∈V,x≠6 → mixedSlot a b x+72≤mixedSlot a b 6 ∨ mixedSlot a b 6+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul3FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (6::V) (Function.update E 6 (E 2*E 4))
        (Function.update caps 6 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 2=a+144 := rfl
  have locB : mixedSlot a b 4=b+72 := rfl
  have locO : mixedSlot a b 6=4080+72 := rfl
  have hA := inv.bound 2 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 4 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base a) 144) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base b) 72) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base a) 144) (off (off base 4080) 72) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=a+144) (o:=4152)
      (Or.inl (by have h:=ctx.inputLow; omega_arith)) (by have h:=ctx.inputLow; omega_arith) (by decide)
  refine WP.mono (MixedMul3Field_ok ctx.input ctx.affine ctx.tempW (by decide) (by decide) (by decide) stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 6 2 4 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4152) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4152+0+72<2^64)
  have ni := inv.point_update (.mul 6 2 4 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step15 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 1∈V) (readB : 8∈V) (capA : caps 1=1) (capB : caps 8=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠8 → mixedSlot a b x+72≤mixedSlot a b 8 ∨ mixedSlot a b 8+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul9FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (8::V) (Function.update E 8 (E 1*E 8))
        (Function.update caps 8 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 1=a+72 := rfl
  have locB : mixedSlot a b 8=4080+216 := rfl
  have locO : mixedSlot a b 8=4080+216 := rfl
  have hA := inv.bound 1 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 8 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base a) 72) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 216) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base a) 72) (off (off base 4080) 216) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=a+72) (o:=4296)
      (Or.inl (by have h:=ctx.inputLow; omega_arith)) (by have h:=ctx.inputLow; omega_arith) (by decide)
  refine WP.mono (MixedMul9Field_ok ctx.input ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 8 1 8 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4296) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4296+0+72<2^64)
  have ni := inv.point_update (.mul 8 1 8 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step8 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 8∈V) (readB : 0∈V) (capA : caps 8=1) (capB : caps 0=1)
    (apart : ∀x∈V,x≠9 → mixedSlot a b x+72≤mixedSlot a b 9 ∨ mixedSlot a b 9+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul6FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (9::V) (Function.update E 9 (E 8*E 0))
        (Function.update caps 9 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 8=4080+216 := rfl
  have locB : mixedSlot a b 0=a+0 := rfl
  have locO : mixedSlot a b 9=4080+288 := rfl
  have hA := inv.bound 8 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 0 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base 4080) 216) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base a) 0) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base 4080) 216) (off (off base 4080) 288) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=4296) (o:=4368)
      (by decide) (by decide) (by decide)
  refine WP.mono (MixedMul6Field_ok ctx.temp ctx.input ctx.tempW (by decide) (by decide) (by decide) stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 9 8 0 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4368) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4368+0+72<2^64)
  have ni := inv.point_update (.mul 9 8 0 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step5 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 6∈V) (readB : 1∈V) (capA : caps 6=1) (capB : caps 1=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠6 → mixedSlot a b x+72≤mixedSlot a b 6 ∨ mixedSlot a b 6+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSub1Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (6::V) (Function.update E 6 (E 6-E 1))
        (Function.update caps 6 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 6=4080+72 := rfl
  have locB : mixedSlot a b 1=a+72 := rfl
  have locO : mixedSlot a b 6=4080+72 := rfl
  have hA := inv.bound 6 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 1 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 72 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base a) 72 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := MixedSub1_ok ctx.temp ctx.input ctx.tempW (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.sub 6 6 1) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+72+72<2^64)
  have ni := inv.point_update (.sub 6 6 1)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step16 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 6∈V) (readB : 9∈V) (capA : caps 6=1) (capB : caps 9=1) (zeroIn : s.gpr .x2=0)
    (apart : ∀x∈V,x≠9 → mixedSlot a b x+72≤mixedSlot a b 9 ∨ mixedSlot a b 9+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedMul10FieldCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (9::V) (Function.update E 9 (E 6*E 9))
        (Function.update caps 9 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 6=4080+72 := rfl
  have locB : mixedSlot a b 9=4080+288 := rfl
  have locO : mixedSlot a b 9=4080+288 := rfl
  have hA := inv.bound 6 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 9 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off (off base 4080) 72) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA,Nat.add_zero] using hA
  have bBound : wordsVal s.mem (off (off base 4080) 288) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB,Nat.add_zero] using hB
  have stable : StableInput s (off (off base 4080) 72) (off (off base 4080) 288) := by
    simpa only [off_off] using stable_input_apart (s:=s) (base:=base) (a:=4152) (o:=4368)
      (by decide) (by decide) (by decide)
  refine WP.mono (MixedMul10Field_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn stable aBound bBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 9 6 9 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul,Nat.add_zero] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod,Nat.add_zero] using he
    · have om : Outside (off base 4368) 0 72 s.mem t.mem := by simpa only [off_off] using outside
      simpa only [PointOp.out,locO,Nat.add_zero] using outside_rebase om (by decide : 4368+0+72<2^64)
  have ni := inv.point_update (.mul 9 6 9 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step14 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 9∈V) (readB : 5∈V) (capA : caps 9=1) (capB : caps 5=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠9 → mixedSlot a b x+72≤mixedSlot a b 9 ∨ mixedSlot a b 9+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSub5Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (9::V) (Function.update E 9 (E 9-E 5))
        (Function.update caps 9 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 9=4080+288 := rfl
  have locB : mixedSlot a b 5=4080+0 := rfl
  have locO : mixedSlot a b 9=4080+288 := rfl
  have hA := inv.bound 9 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 5 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 288 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := MixedSub5_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.sub 9 9 5) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+288+72<2^64)
  have ni := inv.point_update (.sub 9 9 5)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step7 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 6∈V) (capA : caps 6=1) (zeroIn : s.gpr .x1=0)
    (apart : ∀x∈V,x≠5 → mixedSlot a b x+72≤mixedSlot a b 5 ∨ mixedSlot a b 5+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSquare7Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (5::V) (Function.update E 5 (E 6*E 6))
        (Function.update caps 5 1) t ∧ MixedContext base a b o t ∧ t.gpr .x1=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 6=4080+72 := rfl
  have locO : mixedSlot a b 5=4080+0 := rfl
  have hA := inv.bound 6 readA
  rw [capA,Nat.one_mul] at hA
  have aBound : wordsVal s.mem (off base 4080) 72 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  refine WP.mono (MixedSquare7_ok ctx.temp ctx.tempW (by decide) (by decide) zeroIn aBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 5 6 6 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+0+72<2^64)
  have ni := inv.point_update (.mul 5 6 6 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readA)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capA]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step4 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 7∈V) (readB : 0∈V) (capA : caps 7=1) (capB : caps 0=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠10 → mixedSlot a b x+72≤mixedSlot a b 10 ∨ mixedSlot a b 10+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSub0Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (10::V) (Function.update E 10 (E 7-E 0))
        (Function.update caps 10 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 7=4080+144 := rfl
  have locB : mixedSlot a b 0=a+0 := rfl
  have locO : mixedSlot a b 10=4080+360 := rfl
  have hA := inv.bound 7 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 0 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 144 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base a) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := MixedSub0_ok ctx.temp ctx.input ctx.tempW (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.sub 10 7 0) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+360+72<2^64)
  have ni := inv.point_update (.sub 10 7 0)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step0 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 2∈V) (capA : caps 2=1)
    (apart : ∀x∈V,x≠5 → mixedSlot a b x+72≤mixedSlot a b 5 ∨ mixedSlot a b 5+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSquare5Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (5::V) (Function.update E 5 (E 2*E 2))
        (Function.update caps 5 1) t ∧ MixedContext base a b o t ∧ t.gpr .x1=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 2=a+144 := rfl
  have locO : mixedSlot a b 5=4080+0 := rfl
  have hA := inv.bound 2 readA
  rw [capA,Nat.one_mul] at hA
  have aBound : wordsVal s.mem (off base a) 144 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  refine WP.mono (MixedSquare5_ok ctx.input ctx.tempW (by decide) (by decide) aBound)
    fun t ⟨bound,value,zero,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.mul 5 2 2 false) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+0+72<2^64)
  have ni := inv.point_update (.mul 5 2 2 false)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact readA)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] at hx
        subst x; exact Or.inl (by rw [capA]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,zero,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step10 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 5∈V) (readB : 9∈V) (capA : caps 5=1) (capB : caps 9=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠5 → mixedSlot a b x+72≤mixedSlot a b 5 ∨ mixedSlot a b 5+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSub2Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (5::V) (Function.update E 5 (E 5-E 9))
        (Function.update caps 5 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 5=4080+0 := rfl
  have locB : mixedSlot a b 9=4080+288 := rfl
  have locO : mixedSlot a b 5=4080+0 := rfl
  have hA := inv.bound 5 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 9 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 0 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 288 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := MixedSub2_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.sub 5 5 9) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+0+72<2^64)
  have ni := inv.point_update (.sub 5 5 9)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off off_off)

theorem mixed_step11 [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (ctx : MixedContext base a b o s) (inv : OrdinaryInv base fieldPrime (mixedSlot a b) V E caps s)
    (readA : 7∈V) (readB : 9∈V) (capA : caps 7=1) (capB : caps 9=1) (zeroIn : s.gpr .x2=0) (maskIn : s.gpr .x0=511)
    (apart : ∀x∈V,x≠8 → mixedSlot a b x+72≤mixedSlot a b 8 ∨ mixedSlot a b 8+72≤mixedSlot a b x)
    (fits : ∀x∈V,mixedSlot a b x+72≤2^64) :
    WP isa (.block MixedSub3Code) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) (8::V) (Function.update E 8 (E 7-E 9))
        (Function.update caps 8 1) t ∧ MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
        KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  have locA : mixedSlot a b 7=4080+144 := rfl
  have locB : mixedSlot a b 9=4080+288 := rfl
  have locO : mixedSlot a b 8=4080+216 := rfl
  have hA := inv.bound 7 readA
  rw [capA,Nat.one_mul] at hA
  have hB := inv.bound 9 readB
  rw [capB,Nat.one_mul] at hB
  have aBound : wordsVal s.mem (off base 4080) 144 9<fieldPrime := by
    simpa only [wordsVal_off,locA] using hA
  have bBound : wordsVal s.mem (off base 4080) 288 9<fieldPrime := by
    simpa only [wordsVal_off,locB] using hB
  have kernel := MixedSub3_ok ctx.temp ctx.temp ctx.tempW (by decide) (by decide) (by decide) zeroIn maskIn
  rw [←fieldPrime] at kernel
  refine WP.mono (kernel aBound bBound)
    fun t ⟨value,bound,mask,k,outside⟩ => ?_
  have result : PointResult base fieldPrime (mixedSlot a b) (.sub 8 7 9) s t := by
    constructor
    · simpa only [PointOp.out,PointOp.cap,locO,wordsVal_off,Nat.one_mul] using bound
    · have he := congrArg (fun n => n%fieldPrime) value
      simpa only [PointOp.out,PointOp.natural,locO,locA,locB,wordsVal_off,Nat.mod_mod] using he
    · simpa only [PointOp.out,locO] using outside_rebase outside (by decide : 4080+216+72<2^64)
  have ni := inv.point_update (.sub 8 7 9)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl <;> assumption)
    (by intro x hx; simp only [PointOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl
        · exact Or.inl (by rw [capA])
        · exact Or.inl (by rw [capB]))
    result apart fits (by intro o C a D b he; cases he)
  have kc : KeepRegs pointFullProductClob s t := k.mono (by decide)
  refine ⟨ni,ctx.of_keepRegs kc,(k.gpr .x2 (by decide)).trans zeroIn,mask,kc,?_⟩
  have frame := result.outside
  rw [PointOp.out,locO] at frame
  exact frame.mono (by decide) (by decide)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

theorem mixed_body_arith
    [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {E : Nat → Fin fieldPrime}
    (ctx : MixedContext base a b o s) (layout : MixedLayoutState a b)
    (inv : OrdinaryInv base fieldPrime (mixedSlot a b) [0,1,2,3,4] E (fun _ => 1) s) :
    WP isa (.block mixedArithmeticCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) [0,1,2,3,4,5,9,10] (pointRun mixedOps E) (fun _ => 1) t ∧
      MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
      KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem := by
  let env1 : Nat → Fin fieldPrime := Function.update E 5 (E 2*E 2)
  let env2 : Nat → Fin fieldPrime := Function.update env1 6 (env1 2*env1 4)
  let env3 : Nat → Fin fieldPrime := Function.update env2 7 (env2 5*env2 3)
  let env4 : Nat → Fin fieldPrime := Function.update env3 6 (env3 5*env3 6)
  let env5 : Nat → Fin fieldPrime := Function.update env4 10 (env4 7-env4 0)
  let env6 : Nat → Fin fieldPrime := Function.update env5 6 (env5 6-env5 1)
  let env7 : Nat → Fin fieldPrime := Function.update env6 8 (env6 10*env6 10)
  let env8 : Nat → Fin fieldPrime := Function.update env7 5 (env7 6*env7 6)
  let env9 : Nat → Fin fieldPrime := Function.update env8 9 (env8 8*env8 0)
  let env10 : Nat → Fin fieldPrime := Function.update env9 7 (env9 8*env9 7)
  let env11 : Nat → Fin fieldPrime := Function.update env10 5 (env10 5-env10 9)
  let env12 : Nat → Fin fieldPrime := Function.update env11 8 (env11 7-env11 9)
  let env13 : Nat → Fin fieldPrime := Function.update env12 10 (env12 2*env12 10)
  let env14 : Nat → Fin fieldPrime := Function.update env13 5 (env13 5-env13 7)
  let env15 : Nat → Fin fieldPrime := Function.update env14 9 (env14 9-env14 5)
  let env16 : Nat → Fin fieldPrime := Function.update env15 8 (env15 1*env15 8)
  let env17 : Nat → Fin fieldPrime := Function.update env16 9 (env16 6*env16 9)
  let env18 : Nat → Fin fieldPrime := Function.update env17 9 (env17 9-env17 8)
  rw [mixedArithmeticCode,mixedArithmeticBlocks]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step0 (E:=E) ctx inv (by decide) rfl
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s1 ⟨inv1,ctx1,zero1,mask1,k1,f1⟩ => ?_
  simp only [mixed_caps_update] at inv1
  change OrdinaryInv base fieldPrime (mixedSlot a b) [5,0,1,2,3,4] env1 (fun _ => 1) s1 at inv1
  have keep1 := k1
  have frame1 := f1
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step1 (E:=env1) ctx1 inv1 (by decide) (by decide) rfl rfl
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s2 ⟨inv2,ctx2,zero2,mask2,k2,f2⟩ => ?_
  simp only [mixed_caps_update] at inv2
  change OrdinaryInv base fieldPrime (mixedSlot a b) [6,5,0,1,2,3,4] env2 (fun _ => 1) s2 at inv2
  have keep2 := keep1.trans k2
  have frame2 := frame1.trans f2
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step2 (E:=env2) ctx2 inv2 (by decide) (by decide) rfl rfl zero2
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s3 ⟨inv3,ctx3,zero3,mask3,k3,f3⟩ => ?_
  simp only [mixed_caps_update] at inv3
  change OrdinaryInv base fieldPrime (mixedSlot a b) [7,6,5,0,1,2,3,4] env3 (fun _ => 1) s3 at inv3
  have keep3 := keep2.trans k3
  have frame3 := frame2.trans f3
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step3 (E:=env3) ctx3 inv3 (by decide) (by decide) rfl rfl zero3
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s4 ⟨inv4,ctx4,zero4,mask4,k4,f4⟩ => ?_
  simp only [mixed_caps_update] at inv4
  change OrdinaryInv base fieldPrime (mixedSlot a b) [6,7,6,5,0,1,2,3,4] env4 (fun _ => 1) s4 at inv4
  have keep4 := keep3.trans k4
  have frame4 := frame3.trans f4
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step4 (E:=env4) ctx4 inv4 (by decide) (by decide) rfl rfl zero4 mask4
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s5 ⟨inv5,ctx5,zero5,mask5,k5,f5⟩ => ?_
  simp only [mixed_caps_update] at inv5
  change OrdinaryInv base fieldPrime (mixedSlot a b) [10,6,7,6,5,0,1,2,3,4] env5 (fun _ => 1) s5 at inv5
  have keep5 := keep4.trans k5
  have frame5 := frame4.trans f5
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step5 (E:=env5) ctx5 inv5 (by decide) (by decide) rfl rfl zero5 mask5
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s6 ⟨inv6,ctx6,zero6,mask6,k6,f6⟩ => ?_
  simp only [mixed_caps_update] at inv6
  change OrdinaryInv base fieldPrime (mixedSlot a b) [6,10,6,7,6,5,0,1,2,3,4] env6 (fun _ => 1) s6 at inv6
  have keep6 := keep5.trans k6
  have frame6 := frame5.trans f6
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step6 (E:=env6) ctx6 inv6 (by decide) rfl
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s7 ⟨inv7,ctx7,zero7,mask7,k7,f7⟩ => ?_
  simp only [mixed_caps_update] at inv7
  change OrdinaryInv base fieldPrime (mixedSlot a b) [8,6,10,6,7,6,5,0,1,2,3,4] env7 (fun _ => 1) s7 at inv7
  have keep7 := keep6.trans k7
  have frame7 := frame6.trans f7
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step7 (E:=env7) ctx7 inv7 (by decide) rfl zero7
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s8 ⟨inv8,ctx8,zero8,mask8,k8,f8⟩ => ?_
  simp only [mixed_caps_update] at inv8
  change OrdinaryInv base fieldPrime (mixedSlot a b) [5,8,6,10,6,7,6,5,0,1,2,3,4] env8 (fun _ => 1) s8 at inv8
  have keep8 := keep7.trans k8
  have frame8 := frame7.trans f8
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step8 (E:=env8) ctx8 inv8 (by decide) (by decide) rfl rfl
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s9 ⟨inv9,ctx9,zero9,mask9,k9,f9⟩ => ?_
  simp only [mixed_caps_update] at inv9
  change OrdinaryInv base fieldPrime (mixedSlot a b) [9,5,8,6,10,6,7,6,5,0,1,2,3,4] env9 (fun _ => 1) s9 at inv9
  have keep9 := keep8.trans k9
  have frame9 := frame8.trans f9
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step9 (E:=env9) ctx9 inv9 (by decide) (by decide) rfl rfl zero9
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s10 ⟨inv10,ctx10,zero10,mask10,k10,f10⟩ => ?_
  simp only [mixed_caps_update] at inv10
  change OrdinaryInv base fieldPrime (mixedSlot a b) [7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env10 (fun _ => 1) s10 at inv10
  have keep10 := keep9.trans k10
  have frame10 := frame9.trans f10
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step10 (E:=env10) ctx10 inv10 (by decide) (by decide) rfl rfl zero10 mask10
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s11 ⟨inv11,ctx11,zero11,mask11,k11,f11⟩ => ?_
  simp only [mixed_caps_update] at inv11
  change OrdinaryInv base fieldPrime (mixedSlot a b) [5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env11 (fun _ => 1) s11 at inv11
  have keep11 := keep10.trans k11
  have frame11 := frame10.trans f11
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step11 (E:=env11) ctx11 inv11 (by decide) (by decide) rfl rfl zero11 mask11
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s12 ⟨inv12,ctx12,zero12,mask12,k12,f12⟩ => ?_
  simp only [mixed_caps_update] at inv12
  change OrdinaryInv base fieldPrime (mixedSlot a b) [8,5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env12 (fun _ => 1) s12 at inv12
  have keep12 := keep11.trans k12
  have frame12 := frame11.trans f12
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step12 (E:=env12) ctx12 inv12 (by decide) (by decide) rfl rfl zero12
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s13 ⟨inv13,ctx13,zero13,mask13,k13,f13⟩ => ?_
  simp only [mixed_caps_update] at inv13
  change OrdinaryInv base fieldPrime (mixedSlot a b) [10,8,5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env13 (fun _ => 1) s13 at inv13
  have keep13 := keep12.trans k13
  have frame13 := frame12.trans f13
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step13 (E:=env13) ctx13 inv13 (by decide) (by decide) rfl rfl zero13 mask13
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s14 ⟨inv14,ctx14,zero14,mask14,k14,f14⟩ => ?_
  simp only [mixed_caps_update] at inv14
  change OrdinaryInv base fieldPrime (mixedSlot a b) [5,10,8,5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env14 (fun _ => 1) s14 at inv14
  have keep14 := keep13.trans k14
  have frame14 := frame13.trans f14
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step14 (E:=env14) ctx14 inv14 (by decide) (by decide) rfl rfl zero14 mask14
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s15 ⟨inv15,ctx15,zero15,mask15,k15,f15⟩ => ?_
  simp only [mixed_caps_update] at inv15
  change OrdinaryInv base fieldPrime (mixedSlot a b) [9,5,10,8,5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env15 (fun _ => 1) s15 at inv15
  have keep15 := keep14.trans k15
  have frame15 := frame14.trans f15
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step15 (E:=env15) ctx15 inv15 (by decide) (by decide) rfl rfl zero15
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s16 ⟨inv16,ctx16,zero16,mask16,k16,f16⟩ => ?_
  simp only [mixed_caps_update] at inv16
  change OrdinaryInv base fieldPrime (mixedSlot a b) [8,9,5,10,8,5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env16 (fun _ => 1) s16 at inv16
  have keep16 := keep15.trans k16
  have frame16 := frame15.trans f16
  rw [WP.block_append_iff]
  refine WP.mono (mixed_step16 (E:=env16) ctx16 inv16 (by decide) (by decide) rfl rfl zero16
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s17 ⟨inv17,ctx17,zero17,mask17,k17,f17⟩ => ?_
  simp only [mixed_caps_update] at inv17
  change OrdinaryInv base fieldPrime (mixedSlot a b) [9,8,9,5,10,8,5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env17 (fun _ => 1) s17 at inv17
  have keep17 := keep16.trans k17
  have frame17 := frame16.trans f17
  refine WP.mono (mixed_step17 (E:=env17) ctx17 inv17 (by decide) (by decide) rfl rfl zero17 mask17
    (by intro x hx hne; exact layout.slots_apart (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith) (by decide) hne)
    (by intro x hx; exact Nat.le_trans (layout.slot_bound (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith)) (by decide : 4512≤2^64)))
    fun s18 ⟨inv18,ctx18,zero18,mask18,k18,f18⟩ => ?_
  simp only [mixed_caps_update] at inv18
  change OrdinaryInv base fieldPrime (mixedSlot a b) [9,9,8,9,5,10,8,5,7,9,5,8,6,10,6,7,6,5,0,1,2,3,4] env18 (fun _ => 1) s18 at inv18
  have keep18 := keep17.trans k18
  have frame18 := frame17.trans f18
  have result := inv18.sub (V':=[0,1,2,3,4,5,9,10]) (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  change OrdinaryInv base fieldPrime (mixedSlot a b) [0,1,2,3,4,5,9,10] (pointRun mixedOps E) (fun _ => 1) s18 at result
  exact ⟨result,ctx18,zero18,mask18,keep18,frame18⟩

theorem mixed_body_ok
    [NeZero fieldPrime] {base : Addr} {a b o : Nat} {s : State} {E : Nat → Fin fieldPrime}
    (ctx : MixedContext base a b o s) (layout : MixedLayoutState a b)
    (inv : OrdinaryInv base fieldPrime (mixedSlot a b) [0,1,2,3,4] E (fun _ => 1) s) :
    WP isa (.block mixedArithmeticCode) s fun t =>
      OrdinaryInv base fieldPrime (mixedSlot a b) [0,1,2,3,4,5,9,10] (pointRun mixedOps E) (fun _ => 1) t ∧
      MixedContext base a b o t ∧ t.gpr .x2=0 ∧ t.gpr .x0=511 ∧
      KeepRegs pointFullProductClob s t ∧ Outside base 4080 432 s.mem t.mem ∧ t.v=s.v := by
  exact WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec mixed_arithmetic_novec
    (mixed_body_arith ctx layout inv))
    (fun t ⟨⟨i,c,z,m,k,f⟩,v⟩ => ⟨i,c,z,m,k,f,v⟩)

end VG.Proof.Mont.AArch64.P521Field
