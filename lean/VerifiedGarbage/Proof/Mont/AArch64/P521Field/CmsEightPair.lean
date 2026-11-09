module

-- separate module: The paired eightfold-word arithmetic equations (cms_eight_pair_words) costs 0.94s of proof versus 0.43s of imports; CmsEightEight composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsShiftMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPair
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsComplement
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsOnePair

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsEightShift (x prev : Word) : Word := addCarry (8*x) (mulHi 8 prev) false

theorem cms_eight_shift_zero (x : Word) : cmsEightShift x 0=8*x := by
  change (8*x)+0#64+0#64=8*x
  rw [BitVec.add_zero,BitVec.add_zero]

theorem cms_eight_shift_value (x prev : Word) :
    (cmsEightShift x prev).toNat=(8*x).toNat+(mulHi 8 prev).toNat := by
  have he := addCarry_value (8*x) (mulHi 8 prev) false
  have hc : carryOut (8*x) (mulHi 8 prev) false=false := cms_shift_carry x prev 3 (by decide)
  rw [hc] at he
  simpa only [cmsEightShift,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using he

theorem cms_eight_pair_math (a0 a1 x0 x1 prev : Word) (c : Bool) :
    let s0 := cmsEightShift x0 prev
    let s1 := cmsEightShift x1 x0
    let c0 := carryOut a0 s0 c
    let c1 := carryOut a1 s1 c0
    (addCarry a0 s0 c).toNat+2^64*(addCarry a1 s1 c0).toNat+
      2^128*((mulHi 8 x1).toNat+c1.toNat)=
      a0.toNat+2^64*a1.toNat+8*(x0.toNat+2^64*x1.toNat)+(mulHi 8 prev).toNat+c.toNat := by
  intro s0 s1 c0 c1
  have e0 := addCarry_value a0 s0 c
  have e1 := addCarry_value a1 s1 c0
  have sh0 := cms_eight_shift_value x0 prev
  have sh1 := cms_eight_shift_value x1 x0
  have m0 := mul_lo_hi 8 x0
  have m1 := mul_lo_hi 8 x1
  simp only [show (8 : Word).toNat=8 from rfl] at m0 m1
  change s0.toNat=(8*x0).toNat+(mulHi 8 prev).toNat at sh0
  change s1.toNat=(8*x1).toNat+(mulHi 8 x0).toNat at sh1
  change (addCarry a0 s0 c).toNat+2^64*c0.toNat=_ at e0
  change (addCarry a1 s1 c0).toNat+2^64*c1.toNat=_ at e1
  simp only [Nat.mul_add]
  omega_using [e0,e1,sh0,sh1,m0,m1]

theorem cms_eight_complement_pair (a0 a1 b0 b1 prev : Word) (c : Bool) :
    let s0 := cmsEightShift (~~~b0) prev
    let s1 := cmsEightShift (~~~b1) (~~~b0)
    let c0 := carryOut a0 s0 c
    let c1 := carryOut a1 s1 c0
    (addCarry a0 s0 c).toNat+2^64*(addCarry a1 s1 c0).toNat+
      2^128*((mulHi 8 (~~~b1)).toNat+c1.toNat)+8*(b0.toNat+2^64*b1.toNat)=
      a0.toNat+2^64*a1.toNat+8*(2^128-1)+(mulHi 8 prev).toNat+c.toNat := by
  have he := cms_eight_pair_math a0 a1 (~~~b0) (~~~b1) prev c
  have hb0 := b0.isLt
  have hb1 := b1.isLt
  simp only [BitVec.toNat_not] at he
  dsimp only
  omega_using [he,hb0,hb1]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsEightFirstArith : List Instr := [
  .sub .x .x20 .x2 .x20,
  .subImm .x .x20 .x20 1,
  .lsl .x .x0 .x20 3,
  .adds .x .x3 .x3 .x0,
  .sub .x .x21 .x2 .x21,
  .subImm .x .x21 .x21 1,
  .extr .x .x0 .x21 .x20 61,
  .adcs .x .x4 .x4 .x0]

def cmsEightFirstClob : List Reg := [.x0,.x20,.x21,.x3,.x4]

theorem cms_eight_first_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block cmsEightFirstArith) s fun t =>
      t.gpr .x3=addCarry (s.gpr .x3) (8*(~~~s.gpr .x20)) false ∧
      t.gpr .x4=addCarry (s.gpr .x4) (cmsEightShift (~~~s.gpr .x21) (~~~s.gpr .x20))
        (carryOut (s.gpr .x3) (8*(~~~s.gpr .x20)) false) ∧
      t.c=carryOut (s.gpr .x4) (cmsEightShift (~~~s.gpr .x21) (~~~s.gpr .x20))
        (carryOut (s.gpr .x3) (8*(~~~s.gpr .x20)) false) ∧
      t.gpr .x21= ~~~s.gpr .x21 ∧ Keeps cmsEightFirstClob s t := by
  have extr (n m : Word) : (n++m).extractLsb' 61 64=cmsEightShift n m := cms_shift_extract n m 3 (by decide)
  have low (x : Word) : x<<<3=8*x := cms_shift_low x 3
  apply WP.of_runBlock
  simp only [cmsEightFirstArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hz,cms_complement,low,extr,
    Option.some.injEq,exists_eq_left']
  refine ⟨by rfl,by rfl,by rfl,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · dsimp only [cmsEightFirstClob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_eight_first_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block cmsEightFirstArith) s fun t =>
      regsVal t [.x3,.x4]+2^128*((mulHi 8 (t.gpr .x21)).toNat+t.c.toNat)+8*regsVal s [.x20,.x21]=
        regsVal s [.x3,.x4]+8*(2^128-1) ∧ t.gpr .x21= ~~~s.gpr .x21 ∧ Keeps cmsEightFirstClob s t := by
  refine WP.mono (cms_eight_first_words s hz) fun t ⟨a0,a1,cc,cache,k⟩ => ?_
  have h := cms_eight_complement_pair (s.gpr .x3) (s.gpr .x4) (s.gpr .x20) (s.gpr .x21) 0 false
  simp only [cms_eight_shift_zero,show (mulHi 8 (0 : Word)).toNat=0 from rfl,Bool.toNat_false,Nat.add_zero] at h
  rw [←a0,←a1,←cc,←cache] at h
  exact ⟨by simpa only [regsVal,Nat.mul_zero,Nat.add_zero] using h,cache,k⟩

def cmsEightFirst (b : Nat) : List Instr := twoLoads .x28 .x20 .x21 b++cmsEightFirstArith

theorem cms_eight_first_loaded {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+16≤size) (hb8 : b%8=0) (hz : s.gpr .x2=0) :
    WP isa (.block (cmsEightFirst b)) s fun t =>
      regsVal t [.x3,.x4]+2^128*((mulHi 8 (t.gpr .x21)).toNat+t.c.toNat)+8*wordsVal s.mem p b 2=
        regsVal s [.x3,.x4]+8*(2^128-1) ∧ t.gpr .x21= ~~~word s.mem p (b+8) ∧ Keeps cmsEightFirstClob s t := by
  rw [cmsEightFirst,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 (by decide) (by decide)) fun u ⟨b0,b1,_,ku⟩ => ?_
  refine WP.mono (cms_eight_first_value u ((ku.gpr .x2 (by decide)).trans hz)) fun t ⟨e,cache,kt⟩ => ?_
  have out : regsVal u [.x3,.x4]=regsVal s [.x3,.x4] := regsVal_congr fun r h =>
    ku.gpr r ((by decide : ∀r∈[Reg.x3,.x4],r∉[Reg.x20,.x21]) r h)
  rw [out] at e
  rw [b1] at cache
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,b0,b1] at e
  exact ⟨by simpa only [regsVal,wordsVal,Nat.mul_zero,Nat.add_zero] using e,cache,(ku.mono (by decide)).trans kt⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsEightIn0 : Nat → Reg | 0 => .x22 | 1 => .x20 | _ => .x22
def cmsEightIn1 : Nat → Reg | 0 => .x23 | 1 => .x21 | _ => .x23
def cmsEightPrev : Nat → Reg | 0 => .x21 | 1 => .x23 | _ => .x21

def cmsEightPairClob (i : Nat) : List Reg := [.x0,cmsEightIn0 i,cmsEightIn1 i,cmsOneR0 i,cmsOneR1 i,.x15]

def cmsEightPairArith (i : Nat) : List Instr := [
  .sub .x (cmsEightIn0 i) .x2 (cmsEightIn0 i),
  .subImm .x (cmsEightIn0 i) (cmsEightIn0 i) 1,
  .extr .x .x0 (cmsEightIn0 i) (cmsEightPrev i) 61,
  .adcs .x (cmsOneR0 i) (cmsOneR0 i) .x0,
  .logic .and .x .x15 (cmsOnePrev i) (cmsOneR0 i),
  .sub .x (cmsEightIn1 i) .x2 (cmsEightIn1 i),
  .subImm .x (cmsEightIn1 i) (cmsEightIn1 i) 1,
  .extr .x .x0 (cmsEightIn1 i) (cmsEightIn0 i) 61,
  .adcs .x (cmsOneR1 i) (cmsOneR1 i) .x0,
  .logic .and .x .x15 .x15 (cmsOneR1 i)]

theorem cms_eight_pair_words (s : State) (i : Nat) (hi : i<3) (hz : s.gpr .x2=0) :
    WP isa (.block (cmsEightPairArith i)) s fun t =>
      t.gpr (cmsOneR0 i)=addCarry (s.gpr (cmsOneR0 i)) (cmsEightShift (~~~s.gpr (cmsEightIn0 i)) (s.gpr (cmsEightPrev i))) s.c ∧
      t.gpr (cmsOneR1 i)=addCarry (s.gpr (cmsOneR1 i)) (cmsEightShift (~~~s.gpr (cmsEightIn1 i)) (~~~s.gpr (cmsEightIn0 i)))
        (carryOut (s.gpr (cmsOneR0 i)) (cmsEightShift (~~~s.gpr (cmsEightIn0 i)) (s.gpr (cmsEightPrev i))) s.c) ∧
      t.c=carryOut (s.gpr (cmsOneR1 i)) (cmsEightShift (~~~s.gpr (cmsEightIn1 i)) (~~~s.gpr (cmsEightIn0 i)))
        (carryOut (s.gpr (cmsOneR0 i)) (cmsEightShift (~~~s.gpr (cmsEightIn0 i)) (s.gpr (cmsEightPrev i))) s.c) ∧
      t.gpr (cmsEightIn1 i)= ~~~s.gpr (cmsEightIn1 i) ∧
      t.gpr .x15=(s.gpr (cmsOnePrev i)&&&t.gpr (cmsOneR0 i))&&&t.gpr (cmsOneR1 i) ∧ Keeps (cmsEightPairClob i) s t := by
  have extr (n m : Word) : (n++m).extractLsb' 61 64=cmsEightShift n m := cms_shift_extract n m 3 (by decide)
  have hc : i=0 ∨ i=1 ∨ i=2 := by omega_arith
  rcases hc with rfl|rfl|rfl <;> apply WP.of_runBlock <;>
    simp only [cmsEightPairArith,cmsEightIn0,cmsEightIn1,cmsEightPrev,cmsOneR0,cmsOneR1,cmsOnePrev,
      runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hz,cms_complement,extr,
      Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨by rfl,by rfl,by rfl,True.intro,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
    · dsimp only [cmsEightPairClob,cmsEightIn0,cmsEightIn1,cmsOneR0,cmsOneR1]
      reg_keeps
    · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
    · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
    · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
    · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_eight_pair_value (s : State) (i : Nat) (hi : i<3) (hz : s.gpr .x2=0) :
    WP isa (.block (cmsEightPairArith i)) s fun t =>
      regsVal t [cmsOneR0 i,cmsOneR1 i]+2^128*((mulHi 8 (t.gpr (cmsEightIn1 i))).toNat+t.c.toNat)+
        8*regsVal s [cmsEightIn0 i,cmsEightIn1 i]=regsVal s [cmsOneR0 i,cmsOneR1 i]+8*(2^128-1)+
        (mulHi 8 (s.gpr (cmsEightPrev i))).toNat+s.c.toNat ∧
      t.gpr (cmsEightIn1 i)= ~~~s.gpr (cmsEightIn1 i) ∧
      t.gpr .x15=(s.gpr (cmsOnePrev i)&&&t.gpr (cmsOneR0 i))&&&t.gpr (cmsOneR1 i) ∧ Keeps (cmsEightPairClob i) s t := by
  refine WP.mono (cms_eight_pair_words s i hi hz) fun t ⟨a0,a1,cc,cache,m,k⟩ => ?_
  have h := cms_eight_complement_pair (s.gpr (cmsOneR0 i)) (s.gpr (cmsOneR1 i))
    (s.gpr (cmsEightIn0 i)) (s.gpr (cmsEightIn1 i)) (s.gpr (cmsEightPrev i)) s.c
  dsimp only at h
  rw [←a0,←a1,←cc,←cache] at h
  exact ⟨by simpa only [regsVal,Nat.mul_zero,Nat.add_zero] using h,cache,m,k⟩

def cmsEightPair (i b : Nat) : List Instr := twoLoads .x28 (cmsEightIn0 i) (cmsEightIn1 i) b++cmsEightPairArith i

theorem cms_eight_pair_loaded {s : State} {p : Addr} {size b : Nat} (i : Nat) (hi : i<3)
    (hp : Ptr s .x28 p size) (hb : b+16≤size) (hb8 : b%8=0) (hz : s.gpr .x2=0) :
    WP isa (.block (cmsEightPair i b)) s fun t =>
      regsVal t [cmsOneR0 i,cmsOneR1 i]+2^128*((mulHi 8 (t.gpr (cmsEightIn1 i))).toNat+t.c.toNat)+8*wordsVal s.mem p b 2=
        regsVal s [cmsOneR0 i,cmsOneR1 i]+8*(2^128-1)+(mulHi 8 (s.gpr (cmsEightPrev i))).toNat+s.c.toNat ∧
      t.gpr (cmsEightIn1 i)= ~~~word s.mem p (b+8) ∧
      t.gpr .x15=(s.gpr (cmsOnePrev i)&&&t.gpr (cmsOneR0 i))&&&t.gpr (cmsOneR1 i) ∧ Keeps (cmsEightPairClob i) s t := by
  have hc : i=0 ∨ i=1 ∨ i=2 := by omega_arith
  have hf : .x28≠cmsEightIn0 i ∧ cmsEightIn0 i≠cmsEightIn1 i ∧
      Reg.x2∉[cmsEightIn0 i,cmsEightIn1 i] ∧ (∀r∈[cmsOneR0 i,cmsOneR1 i],r∉[cmsEightIn0 i,cmsEightIn1 i]) ∧
      cmsEightPrev i∉[cmsEightIn0 i,cmsEightIn1 i] ∧ cmsOnePrev i∉[cmsEightIn0 i,cmsEightIn1 i] ∧
      (∀r∈[cmsEightIn0 i,cmsEightIn1 i],r∈cmsEightPairClob i) := by
    rcases hc with rfl|rfl|rfl <;> decide
  rw [cmsEightPair,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 hf.1 hf.2.1) fun u ⟨b0,b1,cu,ku⟩ => ?_
  have uz : u.gpr .x2=0 := (ku.gpr .x2 hf.2.2.1).trans hz
  refine WP.mono (cms_eight_pair_value u i hi uz) fun t ⟨e,cache,m,kt⟩ => ?_
  have out : regsVal u [cmsOneR0 i,cmsOneR1 i]=regsVal s [cmsOneR0 i,cmsOneR1 i] := regsVal_congr fun r h => ku.gpr r (hf.2.2.2.1 r h)
  rw [out,cu,ku.gpr (cmsEightPrev i) hf.2.2.2.2.1] at e
  rw [ku.gpr (cmsOnePrev i) hf.2.2.2.2.2.1] at m
  rw [b1] at cache
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,b0,b1] at e
  exact ⟨by simpa only [regsVal,wordsVal,Nat.mul_zero,Nat.add_zero] using e,cache,m,
    (ku.mono hf.2.2.2.2.2.2).trans kt⟩

end VG.Proof.Mont.AArch64.P521Field
