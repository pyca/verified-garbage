module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsShiftMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsChainMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionFold
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsScalar
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value value_lt value_append)

theorem cms_value_take (xs : List Word) (n : Nat) : value (xs.take n)=value xs%2^(64*n) := by
  by_cases hn : n≤xs.length
  · have hl : (xs.take n).length=n := List.length_take_of_le hn
    have he := value_append (xs.take n) (xs.drop n)
    rw [List.take_append_drop,hl] at he
    have hb := value_lt (xs.take n)
    rw [hl] at hb
    rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb]
  · have hp : 2^(64*xs.length)≤2^(64*n) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    rw [List.take_of_length_le (by omega_arith),Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (value_lt xs) hp)]

def cmsShiftChain (k : Nat) (prev : Word) : List Word → List Word
  | [] => []
  | x::xs => addCarry (BitVec.ofNat 64 (2^k)*x) (mulHi (BitVec.ofNat 64 (2^k)) prev) false::cmsShiftChain k x xs

def cmsShiftWords (k : Nat) : List Word → List Word
  | [] => []
  | x::xs => BitVec.ofNat 64 (2^k)*x::cmsShiftChain k x xs

theorem cms_shift_chain_take (k : Nat) (hk : k=1 ∨ k=2 ∨ k=3) (prev : Word) (xs : List Word) :
    (firstChain (BitVec.ofNat 64 (2^k)) (mulHi (BitVec.ofNat 64 (2^k)) prev) false xs).take xs.length=cmsShiftChain k prev xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    simp only [firstChain,cmsShiftChain,List.length_cons,List.take_succ_cons]
    rw [cms_addCarry_comm (mulHi (BitVec.ofNat 64 (2^k)) prev),
      cms_carryOut_comm (mulHi (BitVec.ofNat 64 (2^k)) prev),cms_shift_carry x prev k hk,ih]

theorem cms_shift_words_take (k : Nat) (hk : k=1 ∨ k=2 ∨ k=3) (xs : List Word) :
    (firstRow (BitVec.ofNat 64 (2^k)) xs).take xs.length=cmsShiftWords k xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [firstRow,cmsShiftWords,List.length_cons,List.take_succ_cons,cms_shift_chain_take k hk]

theorem cms_shift_words_length (k : Nat) (xs : List Word) : (cmsShiftWords k xs).length=xs.length := by
  have chain (p : Word) (ys : List Word) : (cmsShiftChain k p ys).length=ys.length := by
    induction ys generalizing p with
    | nil => rfl
    | cons y ys ih => simp only [cmsShiftChain,List.length_cons,ih]
  cases xs with
  | nil => rfl
  | cons x xs => simp only [cmsShiftWords,List.length_cons,chain]

theorem cms_shift_words_value (k : Nat) (hk : k=1 ∨ k=2 ∨ k=3) (xs : List Word)
    (hb : 2^k*value xs<2^(64*xs.length)) : value (cmsShiftWords k xs)=2^k*value xs := by
  have hp : 2^k<2^64 := by rcases hk with rfl|rfl|rfl <;> decide
  rw [←cms_shift_words_take k hk,cms_value_take,firstRow_value,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hb]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def cmsSmallInputs : List Reg := [.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14]

def cmsFourCode : List Instr := [
  .lsl .x .x3 .x6 2,
  .extr .x .x4 .x7 .x6 62,
  .extr .x .x5 .x8 .x7 62,
  .extr .x .x6 .x9 .x8 62,
  .extr .x .x7 .x10 .x9 62,
  .extr .x .x8 .x11 .x10 62,
  .extr .x .x9 .x12 .x11 62,
  .extr .x .x10 .x13 .x12 62,
  .extr .x .x11 .x14 .x13 62]

theorem cms_four_words (s : State) :
    WP isa (.block cmsFourCode) s fun t =>
      cmsScalarRegs.map t.gpr=cmsShiftWords 2 (cmsSmallInputs.map s.gpr) ∧ Keeps cmsScalarRegs s t := by
  apply WP.of_runBlock
  simp only [cmsFourCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  · have extr (n m : Word) : addCarry (BitVec.ofNat 64 (2^2)*n) (mulHi (BitVec.ofNat 64 (2^2)) m) false=
        (n++m).extractLsb' 62 64 := (cms_shift_extract n m 2 (by decide)).symm
    simp only [cmsScalarRegs,cmsSmallInputs,List.map_cons,List.map_nil,cmsShiftWords,cmsShiftChain,
      RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    simp only [extr]
    rw [←cms_shift_low (s.gpr .x6) 2]
  · dsimp only [cmsScalarRegs]
    reg_keeps
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

theorem cms_four_value (s : State) (ha : regsVal s cmsSmallInputs<2*(2^521-1)) :
    WP isa (.block cmsFourCode) s fun t =>
      regsVal t cmsScalarRegs=4*regsVal s cmsSmallInputs ∧ Keeps cmsScalarRegs s t := by
  refine WP.mono (cms_four_words s) fun t ⟨w,k⟩ => ?_
  have fits : 2^2*value (cmsSmallInputs.map s.gpr)<2^(64*(cmsSmallInputs.map s.gpr).length) := by
    rw [value_map_gpr]
    simp only [List.length_map,show cmsSmallInputs.length=9 from by decide,Nat.reduceMul,show (2:Nat)^2=4 from rfl]
    omega_using [ha]
  have h := cms_shift_words_value 2 (by decide) (cmsSmallInputs.map s.gpr) fits
  have e := congrArg value w
  rw [value_map_gpr,h,value_map_gpr] at e
  exact ⟨e,k⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords addWords_value)

def cmsThreeCode : List Instr := [
  .lsl .x .x3 .x6 1,
  .adds .x .x3 .x3 .x6,
  .extr .x .x4 .x7 .x6 63,
  .adcs .x .x4 .x4 .x7,
  .extr .x .x5 .x8 .x7 63,
  .adcs .x .x5 .x5 .x8,
  .extr .x .x6 .x9 .x8 63,
  .adcs .x .x6 .x6 .x9,
  .extr .x .x7 .x10 .x9 63,
  .adcs .x .x7 .x7 .x10,
  .extr .x .x8 .x11 .x10 63,
  .adcs .x .x8 .x8 .x11,
  .extr .x .x9 .x12 .x11 63,
  .adcs .x .x9 .x9 .x12,
  .extr .x .x10 .x13 .x12 63,
  .adcs .x .x10 .x10 .x13,
  .extr .x .x11 .x14 .x13 63,
  .adc .x .x11 .x11 .x14]

theorem cms_three_words (s : State) :
    WP isa (.block cmsThreeCode) s fun t =>
      cmsScalarRegs.map t.gpr=(addWords (cmsShiftWords 1 (cmsSmallInputs.map s.gpr)) (cmsSmallInputs.map s.gpr) false).1 ∧
      Keeps cmsScalarRegs s t := by
  apply WP.of_runBlock
  simp only [cmsThreeCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  · have extr (n m : Word) : addCarry (BitVec.ofNat 64 (2^1)*n) (mulHi (BitVec.ofNat 64 (2^1)) m) false=
        (n++m).extractLsb' 63 64 := (cms_shift_extract n m 1 (by decide)).symm
    simp only [cmsScalarRegs,cmsSmallInputs,List.map_cons,List.map_nil,cmsShiftWords,cmsShiftChain,addWords,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    simp only [extr]
    rw [←cms_shift_low (s.gpr .x6) 1]
    rfl
  · dsimp only [cmsScalarRegs]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_three_value (s : State) (ha : regsVal s cmsSmallInputs<2*(2^521-1)) :
    WP isa (.block cmsThreeCode) s fun t =>
      regsVal t cmsScalarRegs=3*regsVal s cmsSmallInputs ∧ Keeps cmsScalarRegs s t := by
  refine WP.mono (cms_three_words s) fun t ⟨w,k⟩ => ?_
  have fits : 2^1*value (cmsSmallInputs.map s.gpr)<2^(64*(cmsSmallInputs.map s.gpr).length) := by
    rw [value_map_gpr]
    simp only [List.length_map,show cmsSmallInputs.length=9 from by decide,Nat.reduceMul,show (2:Nat)^1=2 from rfl]
    omega_using [ha]
  have h := cms_shift_words_value 1 (by decide) (cmsSmallInputs.map s.gpr) fits
  have e := addWords_value (cmsShiftWords 1 (cmsSmallInputs.map s.gpr)) (cmsSmallInputs.map s.gpr) false
    (cms_shift_words_length _ _)
  rw [←w,value_map_gpr,h,value_map_gpr] at e
  simp only [cms_shift_words_length,List.length_map,show cmsSmallInputs.length=9 from by decide,Nat.reduceMul,
    Bool.toNat_false,Nat.add_zero,show (2:Nat)^1=2 from rfl] at e
  have fit3 : 3*regsVal s cmsSmallInputs<2^576 := by omega_using [ha]
  exact ⟨by omega_using [e,fit3],k⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.AArch64

def cmsSmallClob : List Reg := [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14]
def cmsSmallBody (triple : Bool) : List Instr := if triple then cmsThreeCode else cmsFourCode

def cmsSmallLoaded (triple : Bool) (b : Nat) : List Instr := loadsR .x28 cmsSmallInputs b++cmsSmallBody triple

theorem cms_small_body_value (s : State) (triple : Bool) (ha : regsVal s cmsSmallInputs<2*(2^521-1)) :
    WP isa (.block (cmsSmallBody triple)) s fun t =>
      regsVal t cmsScalarRegs=(if triple then 3 else 4)*regsVal s cmsSmallInputs ∧ Keeps cmsScalarRegs s t := by
  cases triple
  · exact cms_four_value s ha
  · exact cms_three_value s ha

theorem cms_small_loaded_value {s : State} {p : Addr} {size b : Nat} (triple : Bool)
    (hp : Ptr s .x28 p size) (hb : b+72≤size) (hb8 : b%8=0)
    (ha : wordsVal s.mem p b 9<2*(2^521-1)) :
    WP isa (.block (cmsSmallLoaded triple b)) s fun t =>
      regsVal t cmsScalarRegs=(if triple then 3 else 4)*wordsVal s.mem p b 9 ∧ Keeps cmsSmallClob s t := by
  rw [cmsSmallLoaded,WP.block_append_iff]
  refine WP.mono (loadsR_ok cmsSmallInputs hp (by simpa only [show cmsSmallInputs.length=9 from by decide] using hb)
    hb8 (by decide) (by decide)) fun u ⟨eu,ku,_⟩ => ?_
  simp only [show cmsSmallInputs.length=9 from by decide] at eu
  refine WP.mono (cms_small_body_value u triple (by rw [eu]; exact ha)) fun t ⟨et,kt⟩ => ?_
  rw [eu] at et
  exact ⟨et,(ku.mono (by decide)).trans (kt.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field
