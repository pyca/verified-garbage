module

public import VerifiedGarbage.Proof.Divstep.Batch
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Data.Finset.Attr
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.P256.EcdhInverse.Shift
import Mathlib.Data.BitVec
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Group.Nat
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Divstep.WordBasic
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.NormNum.Inv
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Tactic.SetLike

/-! ### `P256.EcdhInverse.Encode`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem encode_row (x : BitVec 64) {k : Nat} (hk : k=41 ∨ k=62) :
    (x &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^k)) =
      BitVec.ofInt 64 ((x.toNat%2^20 : Nat)- (2^k : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or,BitVec.toNat_and]
  have ha : x.toNat%1048576<1048576 := Nat.mod_lt _ (by decide)
  have hp : x.toNat &&& (0xfffff : BitVec 64).toNat=x.toNat%1048576 := by
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 20
  rw [hp]
  rcases hk with rfl|rfl
  all_goals
    norm_num only [BitVec.toNat_ofInt]
    rw [Nat.or_comm]
  · have ho := Nat.shiftLeft_add_eq_or_of_lt (by exact ha : x.toNat%1048576<2^20) 17592183947264
    norm_num only [Nat.shiftLeft_eq] at ho
    rw [show Int.toNat 18446741874686296064=18446741874686296064 by decide,←ho]
    omega_using []
  · have ho := Nat.shiftLeft_add_eq_or_of_lt (by exact ha : x.toNat%1048576<2^20) 13194139533312
    norm_num only [Nat.shiftLeft_eq] at ho
    rw [show Int.toNat 13835058055282163712=13835058055282163712 by decide,←ho]
    omega_using []


def encodeCode : List Instr :=
  [.movz .x .x28 65535 0,
   .movk .x .x28 15 1,
   .logic .and .x .x4 .x2 .x28,
   .movz .x .x28 0 0,
   .movk .x .x28 65024 2,
   .movk .x .x28 65535 3,
   .logic .orr .x .x4 .x4 .x28,
   .movz .x .x28 65535 0,
   .movk .x .x28 15 1,
   .logic .and .x .x5 .x3 .x28,
   .movz .x .x28 0 0,
   .movk .x .x28 49152 3,
   .logic .orr .x .x5 .x5 .x28]

theorem encodeCode_ok (s : State) :
    WP isa (.block encodeCode) s fun t =>
      t.gpr .x4=BitVec.ofInt 64 (((s.gpr .x2).toNat%2^20 : Nat)-(2^41 : Int)) ∧
      t.gpr .x5=BitVec.ofInt 64 (((s.gpr .x3).toNat%2^20 : Nat)-(2^62 : Int)) ∧
      Keeps [.x4,.x5,.x28] s t := by
  apply WP.of_runBlock
  simp only [encodeCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (16*2:Nat)<Size.x.bits by decide,
    show (16*3:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change ((s.gpr .x2 &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^41)))=_
    exact encode_row _ (Or.inl rfl)
  · change ((s.gpr .x3 &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^62)))=_
    exact encode_row _ (Or.inr rfl)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h4,h5,h28⟩ := hr
    simp only [RegUpd.gpr_write,h4,h5,h28,↓reduceIte]

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.Rounds`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Round`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Step`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- Update before halving the second packed row. The incoming zero flag is its parity. -/
def updateStep : List Instr :=
  [.cselc .x .x6 .x4 .x27 .ne,.ccmp .x .x1 0 8 .ne,
   .csneg .x .x1 .x1 .x1 .lt,.csneg .x .x6 .x6 .x6 .lt,
   .cselc .x .x4 .x5 .x4 .ge,.add .x .x5 .x5 .x6,.addImm .x .x1 .x1 2]

def halfStep : List Instr :=
  [.lsr .x .x26 .x5 63,.sub .x .x26 .x27 .x26,.extr .x .x5 .x26 .x5 1]

def roundStep : List Instr := updateStep ++ [.movz .x .x28 2 0,.tst .x .x5 .x28] ++ halfStep

theorem updateStep_run (s : State) (h27 : s.gpr .x27=0) {odd neg : Bool}
    (hz : s.zf = !odd) (hn : (s.gpr .x1).msb=neg) :
    WP isa (.block updateStep) s fun t =>
      t.gpr .x1=(if odd && !neg then -s.gpr .x1+2 else s.gpr .x1+2) ∧
      t.gpr .x4=(if odd && !neg then s.gpr .x5 else s.gpr .x4) ∧
      t.gpr .x5=s.gpr .x5+(if odd then (if neg then s.gpr .x4 else -s.gpr .x4) else 0) ∧
      Keeps [.x1,.x4,.x5,.x6] s t := by
  apply WP.of_runBlock
  have hadd (x : BitVec 64) : x + 18446744073709551615#64 + 1#64 = x := by
    rw [BitVec.add_assoc,show 18446744073709551615#64 + 1#64 = 0 by decide]
    exact BitVec.add_zero x
  have hflag : (s.gpr .x1 + BitVec.allOnes Size.x.bits + 1#Size.x.bits).msb = neg := by
    change (s.gpr .x1 + 18446744073709551615#64 + 1#64).msb=neg
    rw [hadd]
    exact hn
  cases odd <;> cases neg <;>
  · simp only [updateStep,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
      RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,exists_eq_left',and_self,
      h27,hz,CondCode.holds,State.flagsAdd,toInt_not0,int_m1p1,
      RegUpd.nf_write,RegUpd.zf_write,RegUpd.vf_write,Bool.not_true,Bool.not_false,
      Bool.bne_false,Bool.and_true,Bool.and_false,
      Bool.toNat_true,Int.natCast_one,show (2:Nat)<4096 by decide,
      show (0:Nat)<32 ∧ (8:Nat)<16 by decide,
      show Nat.testBit 8 3=true by decide,show Nat.testBit 8 0=false by decide,
      Bool.false_eq_true]
    refine ⟨?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
    · simp [hflag]
    · simp [hflag]
    · simp [hflag]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      obtain ⟨h1,h4,h5,h6⟩ := hr
      simp only [RegUpd.gpr_write,h1,h4,h5,h6,↓reduceIte]


theorem halfStep_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block halfStep) s fun t =>
      t.gpr .x5=(s.gpr .x5).sshiftRight 1 ∧ t.zf=s.zf ∧
      Keeps [.x5,.x26] s t := by
  apply WP.of_runBlock
  simp only [halfStep,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,show 63<Size.x.bits by decide,show 1<Size.x.bits by decide]
  refine ⟨?_,rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [show (0 : BitVec 64)-(s.gpr .x5 >>> 63)= -(s.gpr .x5 >>> 63) by ring]
    exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h5,h26⟩ := hr
    simp only [RegUpd.gpr_write,h5,h26,↓reduceIte]


def testHalf : List Instr := [.movz .x .x28 2 0,.tst .x .x5 .x28] ++ halfStep

theorem testHalf_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block testHalf) s fun t =>
      t.gpr .x5=(s.gpr .x5).sshiftRight 1 ∧
      t.zf=decide (t.gpr .x5 &&& 1 = 0) ∧ Keeps [.x5,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [testHalf,halfStep,List.cons_append,List.nil_append,
    runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,show (16*0:Nat)<Size.x.bits by decide,
    Nat.mul_zero,BitVec.shiftLeft_zero,
    RegUpd.zf_write,show 63<Size.x.bits by decide,show 1<Size.x.bits by decide]
  have he : ((s.gpr .x27-(s.gpr .x5 >>> 63)) ++ s.gpr .x5).extractLsb' 1 64 =
      (s.gpr .x5).sshiftRight 1 := by
    rw [h27,show (0 : BitVec 64)-(s.gpr .x5 >>> 63)= -(s.gpr .x5 >>> 63) by ring]
    exact signed_extract _ (by decide)
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simpa only [h27] using he
  · rw [show (((0 : BitVec 64)-(s.gpr .x5 >>> 63)) ++ s.gpr .x5).extractLsb' 1 64 =
      (s.gpr .x5).sshiftRight 1 by simpa only [h27] using he]
    simp only [half_parity]
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h5,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h5,h26,h28,↓reduceIte]

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.Bounds`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG.Proof.Divstep

/-- Packed initial rows and all their successors fit signed63 bits. -/
def rowBounds (t : MSt) : Prop :=
  -(2^62)≤t.f ∧ t.f<2^62 ∧ -(2^62)≤t.g ∧ t.g<2^62

theorem rowBounds_step {t : MSt} (h : rowBounds t) : rowBounds (mstep t) := by
  rcases h with ⟨hf,hf',hg,hg'⟩
  unfold rowBounds mstep
  split
  · simp only
    omega_using [hf, hf', hg, hg']
  · rcases Int.emod_two_eq_zero_or_one t.g with hz|ho
    · simp only [hz,Int.zero_mul,Int.add_zero]
      omega_using [hf, hf', hg, hg']
    · simp only [ho,one_mul]
      omega_using [hf, hf', hg, hg']

theorem rowBounds_steps {t : MSt} (h : rowBounds t) (n : Nat) : rowBounds (msteps n t) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [msteps_succ]; exact rowBounds_step ih

theorem packed_initial_bounds (d : Int) {a b : Nat} (ha : a<2^20) (hb : b<2^20) :
    rowBounds (MSt.init d ((a:Int)-2^41) ((b:Int)-2^62)) := by
  unfold rowBounds MSt.init
  simp only at *
  omega_using [ha, hb]

/-- The unhalved second row is still a representable signed64-bit integer. -/
theorem row_numerator_bound {t : MSt} (h : rowBounds t) :
    let z := if 0≤t.d ∧ t.g%2=1 then t.g - t.f else t.g + t.g%2*t.f;
    -(2^63)≤z ∧ z<2^63 := by
  rcases h with ⟨hf,hf',hg,hg'⟩
  dsimp only
  split
  · omega_using [hf, hf', hg, hg']
  · rcases Int.emod_two_eq_zero_or_one t.g with hz|ho
    · simp only [hz,Int.zero_mul,Int.add_zero]
      omega_using [hg, hg']
    · simp only [ho,one_mul]
      omega_using [hf, hf', hg, hg']

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

structure RowState (t : MSt) (s : State) : Prop where
  d : s.gpr .x1=BitVec.ofInt 64 t.d
  f : s.gpr .x4=BitVec.ofInt 64 t.f
  g : s.gpr .x5=BitVec.ofInt 64 t.g
  zero : s.gpr .x27=0
  parity : s.zf=decide (t.g%2=0)

def numerator (t : MSt) : Int :=
  if 0≤t.d ∧ t.g%2=1 then t.g-t.f else t.g+t.g%2*t.f

theorem updateStep_int {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) :
    WP isa (.block updateStep) s fun a =>
      a.gpr .x1=BitVec.ofInt 64 (mstep t).d ∧
      a.gpr .x4=BitVec.ofInt 64 (mstep t).f ∧
      a.gpr .x5=BitVec.ofInt 64 (numerator t) ∧ Keeps [.x1,.x4,.x5,.x6] s a := by
  have hz : s.zf = !decide (t.g%2=1) := by
    rw [hs.parity]
    rcases Int.emod_two_eq_zero_or_one t.g with h|h <;> simp [h]
  have hn : (s.gpr .x1).msb=decide (t.d<0) := by rw [hs.d]; exact msb_ofInt hd
  refine WP.mono (updateStep_run s hs.zero hz hn) fun a ⟨ad,af,ag,hk⟩ => ?_
  rw [hs.d] at ad
  rw [hs.f,hs.g] at af
  rw [hs.f,hs.g] at ag
  have e2 : BitVec.ofInt 64 2=(2 : BitVec 64) := by decide
  by_cases hg : t.g%2=1
  · by_cases hd0 : 0≤t.d
    · have hn0 : ¬t.d<0 := by omega_using [hd0]
      simp only [hg,hn0,decide_true,decide_false,Bool.not_false,
        Bool.and_true,Bool.false_eq_true,↓reduceIte] at ad af ag
      simp only [mstep,numerator,hg,hd0,and_self,↓reduceIte]
      refine ⟨?_,af,?_,hk⟩
      · rw [show (2-t.d:Int)= -t.d+2 by omega_using [],BitVec.ofInt_add,BitVec.ofInt_neg,e2]
        exact ad
      · rw [ofInt_sub']
        simpa only [BitVec.sub_eq_add_neg] using ag
    · have hdn : t.d<0 := by omega_using [hd0]
      simp only [hg,hdn,decide_true,Bool.not_true,Bool.and_false,↓reduceIte] at ad af ag
      simp only [mstep,numerator,hg,hd0,false_and,↓reduceIte,one_mul]
      refine ⟨?_,af,?_,hk⟩
      · rw [BitVec.ofInt_add,e2,BitVec.add_comm]; exact ad
      · rw [BitVec.ofInt_add]; exact ag
  · have hg0 : t.g%2=0 := by omega_using [hg]
    simp only [hg,decide_false,Bool.false_and,Bool.false_eq_true,↓reduceIte,add_zero] at ad af ag
    simp only [mstep,numerator,hg0,show ¬(0:Int)=1 by decide,and_false,↓reduceIte,zero_mul,add_zero]
    refine ⟨?_,af,ag,hk⟩
    rw [BitVec.ofInt_add,e2,BitVec.add_comm]; exact ad


theorem numerator_half (t : MSt) : numerator t / 2 = (mstep t).g := by
  unfold numerator mstep
  split <;> rfl

theorem roundStep_ok {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) (hb : rowBounds t) :
    WP isa (.block roundStep) s fun a => RowState (mstep t) a ∧
      Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  have he : roundStep=updateStep++testHalf := by
    simp only [roundStep,testHalf,List.append_assoc]
  rw [he,WP.block_append_iff]
  refine WP.mono (updateStep_int hs hd) fun a ⟨ad,af,ag,ka⟩ => ?_
  have a27 : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hs.zero
  refine WP.mono (testHalf_run a a27) fun b ⟨bg,bz,kb⟩ => ?_
  have bg' : b.gpr .x5=BitVec.ofInt 64 (mstep t).g := by
    have hnum : -(2^63)≤numerator t ∧ numerator t<2^63 := row_numerator_bound hb
    rw [bg,ag,signed_shift_ofInt hnum]
    change BitVec.ofInt 64 (numerator t / 2)=_
    rw [numerator_half]
  refine ⟨⟨?_,?_,bg',?_,?_⟩,(ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide)]; exact ad
  · rw [kb.gpr _ (by decide)]; exact af
  · rw [kb.gpr _ (by decide)]; exact a27
  · rw [bz,bg']
    simp only [ofInt_parity]

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def rounds : Nat → List Instr
  | 0 => []
  | n+1 => roundStep++rounds n

theorem rounds_ok {t : MSt} {s : State} (hs : RowState t s) (hb : rowBounds t)
    (n : Nat) (hd : |t.d|+2*n<2^62) :
    WP isa (.block (rounds n)) s fun a => RowState (msteps n t) a ∧
      Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  induction n generalizing t s with
  | zero =>
    exact WP.block_nil ⟨hs,⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩⟩
  | succ n ih =>
    rw [rounds,WP.block_append_iff]
    have hdr : -(2^63)≤t.d ∧ t.d<2^63 := by
      have := le_abs_self t.d
      have := neg_abs_le t.d
      omega_arith
    refine WP.mono (roundStep_ok hs hdr hb) fun a ⟨ha,ka⟩ => ?_
    have hdn : |(mstep t).d|+2*n<2^62 := by
      have h := mstep_d t
      norm_num only [Nat.cast_add,Nat.cast_one] at hd
      omega_using [h, hd]
    refine WP.mono (ih ha (rowBounds_step hb) hdn) fun b ⟨hb,kb⟩ => ?_
    exact ⟨hb,ka.trans kb⟩

/-- The last half does not need to prepare parity for another step. -/
theorem lastStep_ok {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) (hb : rowBounds t) :
    WP isa (.block (updateStep++halfStep)) s fun a =>
      a.gpr .x1=BitVec.ofInt 64 (mstep t).d ∧
      a.gpr .x4=BitVec.ofInt 64 (mstep t).f ∧
      a.gpr .x5=BitVec.ofInt 64 (mstep t).g ∧
      a.gpr .x27=0 ∧ Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  rw [WP.block_append_iff]
  refine WP.mono (updateStep_int hs hd) fun a ⟨ad,af,ag,ka⟩ => ?_
  have a27 : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hs.zero
  refine WP.mono (halfStep_run a a27) fun b ⟨bg,_,kb⟩ => ?_
  refine ⟨?_,?_,?_,?_,(ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide)]; exact ad
  · rw [kb.gpr _ (by decide)]; exact af
  · have hnum : -(2^63)≤numerator t ∧ numerator t<2^63 := row_numerator_bound hb
    rw [bg,ag,signed_shift_ofInt hnum]
    change BitVec.ofInt 64 (numerator t/2)=_
    rw [numerator_half]
  · rw [kb.gpr _ (by decide)]; exact a27

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x Keeps.trans Keeps.mono)

def parityCode : List Instr := [.movz .x .x28 1 0,.tst .x .x5 .x28]

theorem parityCode_ok (s : State) :
    WP isa (.block parityCode) s fun t =>
      t.zf=decide (s.gpr .x5 &&& 1=0) ∧ Keeps [.x28] s t := by
  apply WP.of_runBlock
  simp only [parityCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',show (16*0:Nat)<Size.x.bits by decide]
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [RegUpd.gpr_write,hr,↓reduceIte]

def encoded (s : State) (d : Int) : MSt :=
  MSt.init d (((s.gpr .x2).toNat%2^20:Nat)-(2^41:Int))
    (((s.gpr .x3).toNat%2^20:Nat)-(2^62:Int))

theorem encode_parity_ok (s : State) (d : Int) (hd : s.gpr .x1=BitVec.ofInt 64 d)
    (hz : s.gpr .x27=0) :
    WP isa (.block (encodeCode++parityCode)) s fun t =>
      RowState (encoded s d) t ∧ Keeps [.x4,.x5,.x28] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (encodeCode_ok s) fun a ⟨af,ag,ka⟩ => ?_
  refine WP.mono (parityCode_ok a) fun b ⟨bz,kb⟩ => ?_
  refine ⟨⟨?_,?_,?_,?_,?_⟩,ka.trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide)]; exact hd
  · rw [kb.gpr _ (by decide)]; exact af
  · rw [kb.gpr _ (by decide)]; exact ag
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide)]; exact hz
  · rw [bz,ag]; simp only [ofInt_parity]; rfl

theorem encoded_bounds (s : State) (d : Int) : rowBounds (encoded s d) :=
  packed_initial_bounds d (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

def chunkCode (n : Nat) : List Instr :=
  encodeCode++parityCode++rounds n++updateStep++halfStep

theorem chunkCode_ok (s : State) (d : Int) (n : Nat)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hbound : |d|+2*(n+1)<2^62) :
    WP isa (.block (chunkCode n)) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).d ∧
      t.gpr .x4=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).f ∧
      t.gpr .x5=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).g ∧
      t.gpr .x27=0 ∧ Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s t := by
  rw [chunkCode,show encodeCode++parityCode++rounds n++updateStep++halfStep=
    (encodeCode++parityCode)++rounds n++(updateStep++halfStep) by simp only [List.append_assoc],
    WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (encode_parity_ok s d hd hz) fun a ⟨ha,ka⟩ => ?_
  have hn : |(encoded s d).d|+2*n<2^62 := by
    change |d|+2*n<2^62
    norm_num only [Nat.cast_add,Nat.cast_one] at hbound
    omega_using [hbound]
  refine WP.mono (rounds_ok ha (encoded_bounds s d) n hn) fun b ⟨hb,kb⟩ => ?_
  have hd' : -(2^63)≤(msteps n (encoded s d)).d ∧
      (msteps n (encoded s d)).d<2^63 := by
    have hm := msteps_d (encoded s d) n
    have hl := neg_abs_le (msteps n (encoded s d)).d
    have hh := le_abs_self (msteps n (encoded s d)).d
    omega_using [hn, hm, hl, hh]
  refine WP.mono (lastStep_ok hb hd' (rowBounds_steps (encoded_bounds s d) n))
    fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  rw [msteps_succ]
  exact ⟨td,tf,tg,tz,((ka.mono (by decide)).trans kb).trans kt⟩

theorem encoded_cong (s : State) (d : Int) :
    (encoded s d).cong (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) 20 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  all_goals
    dsimp only [encoded,MSt.init]
    norm_num
    omega_using []

theorem encoded_odd (s : State) (d : Int) (hf : (s.gpr .x2).toNat%2=1) :
    (encoded s d).f%2=1 := by
  dsimp only [encoded,MSt.init]
  norm_num
  omega_using [hf]

end VG.Proof.P256.EcdhInverse
