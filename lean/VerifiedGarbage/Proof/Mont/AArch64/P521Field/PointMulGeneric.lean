module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow8
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulProduct
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionFold
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeReduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeFold
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMemory
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeArithmetic

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (folded)

def pointMulFoldLowRegs : List Reg := [.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]
def pointMulFoldInputs : List Reg := pointMulFoldLowRegs++pointMulRow8In
abbrev pointMulFoldWordAt (s : State) (i : Nat) : Word := s.gpr (pointMulFoldInputs.getD i .x5)
abbrev pointMulFoldOutAt (s : State) (i : Nat) : Word := s.gpr (bRegs.getD i .x5)
def pointMulFoldClob : List Reg := [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14]

def pointMulFoldArith : List Instr := [
  .extr .x .x14 .x1 .x24 9,
  .adcs .x .x5 .x5 .x14,
  .extr .x .x14 .x0 .x1 9,
  .adcs .x .x6 .x6 .x14,
  .extr .x .x14 .x15 .x0 9,
  .adcs .x .x7 .x7 .x14,
  .extr .x .x14 .x16 .x15 9,
  .adcs .x .x8 .x8 .x14,
  .extr .x .x14 .x17 .x16 9,
  .adcs .x .x9 .x9 .x14,
  .extr .x .x14 .x19 .x17 9,
  .adcs .x .x10 .x10 .x14,
  .extr .x .x14 .x20 .x19 9,
  .adcs .x .x11 .x11 .x14,
  .extr .x .x14 .x21 .x20 9,
  .adcs .x .x12 .x12 .x14,
  .subImm .x .x0 .x2 512,
  .logic .orr .x .x13 .x24 .x0,
  .lsr .x .x14 .x21 9,
  .adcs .x .x13 .x13 .x14]

theorem point_mul_fold_arith_ok (s : State) (hz : s.gpr .x2=0) (hc : s.c=true) :
    WP isa (.block pointMulFoldArith) s fun t =>
      (∀i,i<9 → pointMulFoldOutAt t i=(folded (pointMulFoldWordAt s)).1.getD i 0) ∧
      t.c=(folded (pointMulFoldWordAt s)).2 ∧ Keeps pointMulFoldClob s t := by
  apply WP.of_runBlock
  simp only [pointMulFoldArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,show (9 : Nat)<64 from by decide,show (512 : Nat)<4096 from by decide,
    ite_true,ite_false,reduceCtorEq,hz,hc,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl
  · dsimp only [pointMulFoldClob]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square

def weakLow (w : Nat → Word) : List Word :=
  (List.range 8).map w++[w 8 &&& BitVec.ofNat 64 511]

def weakFold (w : Nat → Word) : List Word × Bool := addWords (weakLow w) (foldHigh w) false

theorem weakLow_value (w : Nat → Word) : value (weakLow w)=inputValue w%fieldBase := by
  dsimp only [fieldBase]
  have h := foldLow_value w
  have he : value (weakLow w)+(2^576-2^521)=value (foldLow w) := by
    simp only [weakLow,foldLow,value_append,List.length_map,List.length_range,value,
      Nat.mul_zero,Nat.add_zero,mask9_value,orHigh9_value]
    omega_arith
  omega_using [h,he]

theorem weakFold_value (w : Nat → Word) :
    value (weakFold w).1+2^576*(weakFold w).2.toNat=inputValue w%fieldBase+inputValue w/fieldBase := by
  have h := addWords_value (weakLow w) (foldHigh w) false (by rfl)
  rw [weakLow_value,foldHigh_value] at h
  have hl : (weakLow w).length=9 := rfl
  rw [hl,show (64*9 : Nat)=576 from rfl] at h
  simpa only [weakFold,Bool.toNat_false,Nat.add_zero,fieldBase] using h

theorem weakFold_bounded {w : Nat → Word} (hu : inputValue w<fieldPrime*fieldPrime) :
    value (weakFold w).1<2*fieldPrime ∧ value (weakFold w).1%fieldPrime=inputValue w%fieldPrime := by
  have hs := fold_sum_bound hu
  have hv := weakFold_value w
  have cap : 2*fieldPrime<2^576 := by
    dsimp only [fieldPrime]
    rw [prime_value]
    decide +kernel
  have hc : (weakFold w).2.toNat=0 := by
    cases he : (weakFold w).2 with
    | false => rfl
    | true =>
      rw [he] at hv
      simp only [Bool.toNat_true,Nat.mul_one] at hv
      omega_using [hv,hs,cap]
  simp only [hc,Nat.mul_zero,Nat.add_zero] at hv
  refine ⟨by rw [hv]; exact hs,?_⟩
  rw [hv]
  exact (fold_value_mod (inputValue w)).symm

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def pointMulWeakArith : List Instr := [
  .extr .x .x14 .x1 .x24 9,
  .adds .x .x5 .x5 .x14,
  .extr .x .x14 .x0 .x1 9,
  .adcs .x .x6 .x6 .x14,
  .extr .x .x14 .x15 .x0 9,
  .adcs .x .x7 .x7 .x14,
  .extr .x .x14 .x16 .x15 9,
  .adcs .x .x8 .x8 .x14,
  .extr .x .x14 .x17 .x16 9,
  .adcs .x .x9 .x9 .x14,
  .extr .x .x14 .x19 .x17 9,
  .adcs .x .x10 .x10 .x14,
  .extr .x .x14 .x20 .x19 9,
  .adcs .x .x11 .x11 .x14,
  .extr .x .x14 .x21 .x20 9,
  .adcs .x .x12 .x12 .x14,
  .movz .x .x0 511 0,
  .logic .and .x .x13 .x24 .x0,
  .lsr .x .x14 .x21 9,
  .adc .x .x13 .x13 .x14]

theorem point_mul_weak_arith_ok (s : State) :
    WP isa (.block pointMulWeakArith) s fun t =>
      (∀i,i<9 → pointMulFoldOutAt t i=(weakFold (pointMulFoldWordAt s)).1.getD i 0) ∧
      t.gpr .x0=511 ∧ Keeps pointMulFoldClob s t := by
  apply WP.of_runBlock
  simp only [pointMulWeakArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,show (9 : Nat)<64 from by decide,show (16*0 : Nat)<64 from by decide,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,by rfl,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · dsimp only [pointMulFoldClob]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 VG.Proof.Mont.AArch64.P521Square

def pointMulCorrect : List Instr := [
  .sbcs .x .x5 .x5 .x2,
  .sbcs .x .x6 .x6 .x2,
  .sbcs .x .x7 .x7 .x2,
  .sbcs .x .x8 .x8 .x2,
  .sbcs .x .x9 .x9 .x2,
  .sbcs .x .x10 .x10 .x2,
  .sbcs .x .x11 .x11 .x2,
  .sbcs .x .x12 .x12 .x2,
  .sbc .x .x13 .x13 .x2,
  .movz .x .x0 511 0,
  .logic .and .x .x13 .x13 .x0]

theorem point_mul_correct_ok (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulCorrect) s fun t =>
      (∀i,i<9 → pointMulFoldOutAt t i=(corrected ((List.range 9).map (pointMulFoldOutAt s)) s.c).getD i 0) ∧
      t.gpr .x0=511 ∧ Keeps pointMulFoldClob s t := by
  apply WP.of_runBlock
  simp only [pointMulCorrect,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show (16*0 : Nat)<64 from by decide,
    ite_true,ite_false,reduceCtorEq,hz,Option.some.injEq,exists_eq_left']
  refine ⟨?_,by rfl,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · dsimp only [pointMulFoldClob]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.AArch64
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)
open VG.Proof.Mont.AArch64.P521Square
  (value inputValue folded fieldPrime addWords_length corrected_length corrected_value prime_value)

def pointMulStreamedValue (s : State) (pt : Addr) : Nat :=
  wordsVal s.mem pt 0 8+2^512*regsVal s pointMulRow8In

def pointMulReset : List Instr := [.subs .x .x2 .x2 .x2]

theorem point_mul_reset_ok (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulReset) s fun t => t.gpr .x2=0 ∧ t.c=true ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [pointMulReset,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,ite_true,
    hz,self_sub_carry,Option.some.injEq,exists_eq_left']
  refine ⟨by decide,by decide,⟨?_,by simp only [RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_addWithCarry],by simp only [RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_addWithCarry]⟩⟩
  reg_keeps

def pointMulReduceNormalized (ro : Reg) (o : Nat) : List Instr :=
  pointMulReset++(loadsR ro pointMulFoldLowRegs o++(pointMulFoldArith++pointMulCorrect))

theorem point_mul_fold_output_value (s : State) :
    value ((List.range 9).map (pointMulFoldOutAt s))=regsVal s bRegs := rfl

theorem point_mul_loaded_input_value {s₀ s : State} {pt : Addr}
    (low : regsVal s pointMulFoldLowRegs=wordsVal s₀.mem pt 0 8)
    (high : regsVal s pointMulRow8In=regsVal s₀ pointMulRow8In) :
    inputValue (pointMulFoldWordAt s)=pointMulStreamedValue s₀ pt := by
  have hm : (List.range 17).map (pointMulFoldWordAt s)=pointMulFoldInputs.map s.gpr := rfl
  rw [inputValue,hm,value_map_gpr,pointMulFoldInputs,regsVal_append,low,high]
  simp only [pointMulStreamedValue,show pointMulFoldLowRegs.length=8 from rfl,Nat.reduceMul]

theorem point_mul_reduce_normalized_ok {s : State} {ro : Reg} {po : Addr} {cap o : Nat}
    (hp : Ptr s ro po cap) (hO : o+64≤cap) (ho8 : o%8=0)
    (hro : ro∉pointMulStreamClob) (hz : s.gpr .x2=0)
    (hu : pointMulStreamedValue s (off po o)<fieldPrime*fieldPrime) :
    WP isa (.block (pointMulReduceNormalized ro o)) s fun t =>
      regsVal t bRegs<fieldPrime ∧
      regsVal t bRegs=pointMulStreamedValue s (off po o)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ Keeps pointMulStreamClob s t := by
  rw [pointMulReduceNormalized,WP.block_append_iff]
  refine WP.mono (point_mul_reset_ok s hz) fun u ⟨zu,cu,kr⟩ => ?_
  have hp' := hp.of_keeps kr (fun h => hro
    ((show ∀r∈[Reg.x2],r∈pointMulStreamClob from by decide) ro h))
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok pointMulFoldLowRegs hp' (a:=o)
    (by simpa only [show pointMulFoldLowRegs.length=8 from rfl] using hO) ho8 (by decide)
    (fun h => hro ((show ∀r∈pointMulFoldLowRegs,r∈pointMulStreamClob from by decide) ro h)))
    fun v ⟨loaded,kl,cl⟩ => ?_
  have zv : v.gpr .x2=0 := (kl.gpr _ (by decide)).trans zu
  have cv : v.c=true := cl.trans cu
  have hinput : inputValue (pointMulFoldWordAt v)=pointMulStreamedValue s (off po o) := by
    have hm : (List.range 17).map (pointMulFoldWordAt v)=pointMulFoldInputs.map v.gpr := rfl
    have high : regsVal v pointMulRow8In=regsVal s pointMulRow8In := regsVal_congr fun r hr =>
      (kl.gpr r ((show ∀r∈pointMulRow8In,r∉pointMulFoldLowRegs from by decide) r hr)).trans
        (kr.gpr r ((show ∀r∈pointMulRow8In,r∉[Reg.x2] from by decide) r hr))
    change regsVal v pointMulFoldLowRegs=wordsVal u.mem po o 8 at loaded
    rw [kr.mem] at loaded
    rw [inputValue,hm,value_map_gpr,pointMulFoldInputs,regsVal_append,loaded,high,
      pointMulStreamedValue,wordsVal_off,Nat.add_zero]
    simp only [show pointMulFoldLowRegs.length=8 from rfl,Nat.reduceMul]
  rw [WP.block_append_iff]
  refine WP.mono (point_mul_fold_arith_ok v zv cv) fun w ⟨fold,carry,kf⟩ => ?_
  have hlen : (folded (pointMulFoldWordAt v)).1.length=9 := addWords_length _ _ _ rfl
  have efold := range9_eq hlen fold
  have zw : w.gpr .x2=0 := (kf.gpr _ (by decide)).trans zv
  refine WP.mono (point_mul_correct_ok w zw) fun t ⟨correct,mask,kc⟩ => ?_
  have ecorrect := range9_eq (corrected_length ((List.range 9).map (pointMulFoldOutAt w)) w.c rfl) correct
  rw [efold,carry] at ecorrect
  have hv := congrArg value ecorrect
  rw [point_mul_fold_output_value,corrected_value (pointMulFoldWordAt v)
    (by rw [hinput]; exact hu),hinput] at hv
  have hpos : 0<fieldPrime := by dsimp only [fieldPrime]; rw [prime_value]; decide
  exact ⟨by rw [hv]; exact Nat.mod_lt _ hpos,hv,(kc.gpr _ (by decide)).trans zw,mask,
    (kr.mono (by decide)).trans ((kl.mono (by decide)).trans
      ((kf.mono (by decide)).trans (kc.mono (by decide))))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime inputValue value addWords_length)

def pointMulWeakNormalized (ro : Reg) (o : Nat) : List Instr :=
  loadsR ro pointMulFoldLowRegs o++pointMulWeakArith

theorem point_mul_weak_normalized_ok {s : State} {ro : Reg} {po : Addr} {cap o : Nat}
    (hp : Ptr s ro po cap) (hO : o+64≤cap) (ho8 : o%8=0)
    (hro : ro∉pointMulStreamClob) (hz : s.gpr .x2=0)
    (hu : pointMulStreamedValue s (off po o)<fieldPrime*fieldPrime) :
    WP isa (.block (pointMulWeakNormalized ro o)) s fun t =>
      regsVal t bRegs<2*fieldPrime ∧
      regsVal t bRegs%fieldPrime=pointMulStreamedValue s (off po o)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ Keeps pointMulStreamClob s t := by
  rw [pointMulWeakNormalized,WP.block_append_iff]
  refine WP.mono (loadsR_ok pointMulFoldLowRegs hp (a:=o)
    (by simpa only [show pointMulFoldLowRegs.length=8 from rfl] using hO) ho8 (by decide)
    (fun h => hro ((show ∀r∈pointMulFoldLowRegs,r∈pointMulStreamClob from by decide) ro h)))
    fun u ⟨loaded,kl,_⟩ => ?_
  have zu : u.gpr .x2=0 := (kl.gpr _ (by decide)).trans hz
  have high : regsVal u pointMulRow8In=regsVal s pointMulRow8In := regsVal_congr fun r hr =>
    kl.gpr r ((show ∀r∈pointMulRow8In,r∉pointMulFoldLowRegs from by decide) r hr)
  have low : regsVal u pointMulFoldLowRegs=wordsVal s.mem (off po o) 0 8 := by
    change regsVal u pointMulFoldLowRegs=wordsVal s.mem po o 8 at loaded
    rw [wordsVal_off,Nat.add_zero]
    exact loaded
  have hinput := point_mul_loaded_input_value low high
  refine WP.mono (point_mul_weak_arith_ok u) fun t ⟨words,mask,kf⟩ => ?_
  have hl : (weakFold (pointMulFoldWordAt u)).1.length=9 := addWords_length _ _ _ rfl
  have e := range9_eq hl words
  have hv := congrArg value e
  rw [point_mul_fold_output_value] at hv
  have hw := weakFold_bounded (w:=pointMulFoldWordAt u) (by rw [hinput]; exact hu)
  exact ⟨by rw [hv]; exact hw.1,by rw [hv,hw.2,hinput],
    (kf.gpr _ (by decide)).trans zu,mask,(kl.mono (by decide)).trans (kf.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def pointMulCanonicalCode (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointMulProductCode ra a rb b ro o++(pointMulReduceNormalized ro o++storesR ro bRegs o)

theorem point_mul_canonical_ok {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+72≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o))
    (ha' : wordsVal s.mem (off pa a) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb b) 0 9<fieldPrime) :
    WP isa (.block (pointMulCanonicalCode ra a rb b ro o)) s fun t =>
      wordsVal t.mem (off po o) 0 9<fieldPrime ∧
      wordsVal t.mem (off po o) 0 9=
        (wordsVal s.mem (off pa a) 0 9*wordsVal s.mem (off pb b) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po o) 0 72 s.mem t.mem := by
  have fieldBound : fieldPrime≤2^521 := by
    dsimp only [fieldPrime]
    have h := Nat.sub_le ((2:Nat)^521) 1
    exact h
  have aa : wordsVal s.mem (off pa a) 0 9<2^521 := Nat.lt_of_lt_of_le ha' fieldBound
  have bb : wordsVal s.mem (off pb b) 0 9<2^521 := Nat.lt_of_lt_of_le hb' fieldBound
  rw [pointMulCanonicalCode,WP.block_append_iff]
  refine WP.mono (point_mul_product_ok ha hb ht hA hB (by omega_arith)
    ha8 hb8 ho8 hra hrb hro stable aa bb) fun u inv => ?_
  have ht' := ht.of_keepRegs inv.kept hro
  have hu : pointMulStreamedValue u (off po o)<fieldPrime*fieldPrime := by
    dsimp only [pointMulStreamedValue]
    rw [inv.product]
    exact Nat.mul_lt_mul'' ha' hb'
  rw [WP.block_append_iff]
  refine WP.mono (point_mul_reduce_normalized_ok ht'.readable (by omega_arith)
    ho8 hro inv.zero hu) fun v ⟨bound,val,z2,mask,kr⟩ => ?_
  dsimp only [pointMulStreamedValue] at val
  rw [inv.product] at val
  have ht'' := ht'.of_keepRegs (Keeps.regs kr) hro
  refine WP.mono (point_store_field ht'' hO ho8) fun t ⟨stored,ks,frame⟩ => ?_
  have prior : Outside (off po o) 0 72 s.mem v.mem := by
    rw [kr.mem]
    exact inv.memory.mono (by decide) (by decide)
  exact ⟨by rw [stored]; exact bound,by rw [stored,val],
    (ks.gpr .x2 (by decide)).trans z2,(ks.gpr .x0 (by decide)).trans mask,
    inv.kept.trans (((Keeps.regs kr).mono (by decide)).trans (ks.mono (by decide))),prior.trans frame⟩

def pointMulCanonicalZ2Code (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointMulProductZ2Code ra a rb b ro o++(pointMulReduceNormalized ro o++storesR ro bRegs o)

theorem point_mul_canonicalz2_ok {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+72≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hz : s.gpr .x2=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o))
    (ha' : wordsVal s.mem (off pa a) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb b) 0 9<fieldPrime) :
    WP isa (.block (pointMulCanonicalZ2Code ra a rb b ro o)) s fun t =>
      wordsVal t.mem (off po o) 0 9<fieldPrime ∧
      wordsVal t.mem (off po o) 0 9=
        (wordsVal s.mem (off pa a) 0 9*wordsVal s.mem (off pb b) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po o) 0 72 s.mem t.mem := by
  have fieldBound : fieldPrime≤2^521 := by
    dsimp only [fieldPrime]
    have h := Nat.sub_le ((2:Nat)^521) 1
    exact h
  have aa : wordsVal s.mem (off pa a) 0 9<2^521 := Nat.lt_of_lt_of_le ha' fieldBound
  have bb : wordsVal s.mem (off pb b) 0 9<2^521 := Nat.lt_of_lt_of_le hb' fieldBound
  rw [pointMulCanonicalZ2Code,WP.block_append_iff]
  refine WP.mono (point_mul_product_z2_ok ha hb ht hA hB (by omega_arith)
    ha8 hb8 ho8 hz hra hrb hro stable aa bb) fun u inv => ?_
  have ht' := ht.of_keepRegs inv.kept hro
  have hu : pointMulStreamedValue u (off po o)<fieldPrime*fieldPrime := by
    dsimp only [pointMulStreamedValue]
    rw [inv.product]
    exact Nat.mul_lt_mul'' ha' hb'
  rw [WP.block_append_iff]
  refine WP.mono (point_mul_reduce_normalized_ok ht'.readable (by omega_arith)
    ho8 hro inv.zero hu) fun v ⟨bound,val,z2,mask,kr⟩ => ?_
  dsimp only [pointMulStreamedValue] at val
  rw [inv.product] at val
  have ht'' := ht'.of_keepRegs (Keeps.regs kr) hro
  refine WP.mono (point_store_field ht'' hO ho8) fun t ⟨stored,ks,frame⟩ => ?_
  have prior : Outside (off po o) 0 72 s.mem v.mem := by
    rw [kr.mem]
    exact inv.memory.mono (by decide) (by decide)
  exact ⟨by rw [stored]; exact bound,by rw [stored,val],
    (ks.gpr .x2 (by decide)).trans z2,(ks.gpr .x0 (by decide)).trans mask,
    inv.kept.trans (((Keeps.regs kr).mono (by decide)).trans (ks.mono (by decide))),prior.trans frame⟩

def pointMulWeakCode (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointMulProductCode ra a rb b ro o++(pointMulWeakNormalized ro o++storesR ro bRegs o)

theorem point_mul_weak_ok {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+72≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o))
    (ha' : wordsVal s.mem (off pa a) 0 9<fieldPrime)
    (hb' : wordsVal s.mem (off pb b) 0 9<fieldPrime) :
    WP isa (.block (pointMulWeakCode ra a rb b ro o)) s fun t =>
      wordsVal t.mem (off po o) 0 9<2*fieldPrime ∧
      wordsVal t.mem (off po o) 0 9%fieldPrime=
        (wordsVal s.mem (off pa a) 0 9*wordsVal s.mem (off pb b) 0 9)%fieldPrime ∧
      t.gpr .x2=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointMulStreamClob s t ∧ Outside (off po o) 0 72 s.mem t.mem := by
  have fieldBound : fieldPrime≤2^521 := by
    dsimp only [fieldPrime]
    have h := Nat.sub_le ((2:Nat)^521) 1
    exact h
  have aa : wordsVal s.mem (off pa a) 0 9<2^521 := Nat.lt_of_lt_of_le ha' fieldBound
  have bb : wordsVal s.mem (off pb b) 0 9<2^521 := Nat.lt_of_lt_of_le hb' fieldBound
  rw [pointMulWeakCode,WP.block_append_iff]
  refine WP.mono (point_mul_product_ok ha hb ht hA hB (by omega_arith)
    ha8 hb8 ho8 hra hrb hro stable aa bb) fun u inv => ?_
  have ht' := ht.of_keepRegs inv.kept hro
  have hu : pointMulStreamedValue u (off po o)<fieldPrime*fieldPrime := by
    dsimp only [pointMulStreamedValue]
    rw [inv.product]
    exact Nat.mul_lt_mul'' ha' hb'
  rw [WP.block_append_iff]
  refine WP.mono (point_mul_weak_normalized_ok ht'.readable (by omega_arith)
    ho8 hro inv.zero hu) fun v ⟨bound,val,z2,mask,kr⟩ => ?_
  dsimp only [pointMulStreamedValue] at val
  rw [inv.product] at val
  have ht'' := ht'.of_keepRegs (Keeps.regs kr) hro
  refine WP.mono (point_store_field ht'' hO ho8) fun t ⟨stored,ks,frame⟩ => ?_
  have prior : Outside (off po o) 0 72 s.mem v.mem := by
    rw [kr.mem]
    exact inv.memory.mono (by decide) (by decide)
  exact ⟨by rw [stored]; exact bound,by rw [stored,val],
    (ks.gpr .x2 (by decide)).trans z2,(ks.gpr .x0 (by decide)).trans mask,
    inv.kept.trans (((Keeps.regs kr).mono (by decide)).trans (ks.mono (by decide))),prior.trans frame⟩

end VG.Proof.Mont.AArch64.P521Field
