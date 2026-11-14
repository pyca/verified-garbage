module

-- separate module: The checked left/right rotation replay is the expensive computational boundary; memory permission and alias proofs reuse it without rechecking word arithmetic.

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Representation
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationFin
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationMath
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionFold

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64.P521Square
open VG.Proof.Ed25519.AArch64

def representationReg (i : Nat) : Reg := [.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x21].getD i .x8

abbrev representationFromCode := VG.Impl.Weierstrass.AArch64.P521Native.representationFromCode

def representationClob : List Reg := [.x1,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x21]

theorem representation_from_words (s : State) :
    WP isa (.block representationFromCode) s fun t =>
      (∀i<9,t.gpr (representationReg i)=(rotated (fun j => s.gpr (representationReg j))).getD i 0) ∧
      Keeps representationClob s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [representationFromCode,VG.Impl.Weierstrass.AArch64.P521Native.representationFromCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,Nat.reduceLT,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · intro i hi
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · dsimp only [representationClob]
    reg_keeps
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]
  · simp only [RegUpd.v_write]

theorem representation_from_value (s : State)
    (bound : value ((List.range 9).map (fun j => s.gpr (representationReg j)))<fieldPrime) :
    WP isa (.block representationFromCode) s fun t =>
      value ((List.range 9).map (fun j => t.gpr (representationReg j)))=
        fromMontValue (value ((List.range 9).map (fun j => s.gpr (representationReg j)))) ∧
      value ((List.range 9).map (fun j => t.gpr (representationReg j)))<fieldPrime ∧
      Keeps representationClob s t ∧ t.v=s.v := by
  refine WP.mono (representation_from_words s) fun t ⟨words,k,v⟩ => ?_
  have he : (List.range 9).map (fun j => t.gpr (representationReg j))=
      rotated (fun j => s.gpr (representationReg j)) := by
    apply List.ext_getElem
    · rfl
    · intro i h1 h2
      have hi : i<9 := by simpa only [List.length_map,List.length_range] using h1
      simpa only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2,Option.getD_some] using words i hi
  rw [he]
  have hv := rotated_value (fun j => s.gpr (representationReg j)) (Nat.lt_trans bound (by
    dsimp only [fieldPrime]; omega_arith))
  change _=fromMontValue _ at hv
  exact ⟨hv,by rw [hv]; exact fromMontValue_bound bound,k,v⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square

theorem orLow55 (x y : Word) (hy : y.toNat < 2^55) :
    y ||| (x <<< 55) = (x.setWidth 9 ++ y.setWidth 55) := by
  have he : y = (y.setWidth 55).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega_using [hy]
  rw [he]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : i < 55
  · simp only [hi, h, decide_true, Bool.not_true, Bool.true_and, Bool.and_false,
      Bool.false_and, Bool.or_false, ite_true]
  · have hi9 : i - 55 < 9 := by omega_using [hi]
    simp only [hi, h, hi9, decide_true, decide_false, Bool.not_false,
      Bool.true_and, Bool.false_and, Bool.false_or, ite_false]

theorem orLow55_value (x y : Word) (hy : y.toNat < 2^55) :
    (y ||| (x <<< 55)).toNat = y.toNat + 2^55*(x.toNat % 2^9) := by
  rw [orLow55 x y hy, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (y.setWidth 55).isLt]
  simp only [BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega_using [hy]


theorem orLow46 (x y : Word) (hy : y.toNat < 2^46) :
    y ||| (x <<< 46) = (x.setWidth 18 ++ y.setWidth 46) := by
  have he : y = (y.setWidth 46).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega_using [hy]
  rw [he]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : i < 46
  · simp only [hi, h, decide_true, Bool.not_true, Bool.true_and, Bool.and_false,
      Bool.false_and, Bool.or_false, ite_true]
  · have hi18 : i - 46 < 18 := by omega_using [hi]
    simp only [hi, h, hi18, decide_true, decide_false, Bool.not_false,
      Bool.true_and, Bool.false_and, Bool.false_or, ite_false]

theorem orLow46_value (x y : Word) (hy : y.toNat < 2^46) :
    (y ||| (x <<< 46)).toNat = y.toNat + 2^46*(x.toNat % 2^18) := by
  rw [orLow46 x y hy, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (y.setWidth 46).isLt]
  simp only [BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega_using [hy]


end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square

def representationHigh (w : Nat → Word) : Word := (w 7 >>> 18)|||(w 8 <<< 46)
def representationFirst (w : Nat → Word) : Word := representationHigh w ||| (w 0 <<< 55)
def representationForwardRaw (w : Nat → Word) : List Word :=
  representationFirst w :: shifted9 ((List.range 8).map w)
def representationForwardWords (w : Nat → Word) : List Word :=
  (representationForwardRaw w).take 8++[(representationForwardRaw w).getD 8 0 &&& 511]

theorem representation_forward_value (w : Nat → Word)
    (bound : value ((List.range 9).map w)<fieldPrime) :
    value (representationForwardWords w)=toMontValue (value ((List.range 9).map w)) := by
  have split9 := value_append ((List.range 8).map w) [w 8]
  have eq9 : (List.range 9).map w=(List.range 8).map w++[w 8] := rfl
  rw [←eq9] at split9
  simp only [List.length_map,List.length_range,value,Nat.mul_zero,Nat.add_zero] at split9
  have lo8 := value_lt ((List.range 8).map w)
  simp only [List.length_map,List.length_range] at lo8
  have topBound : (w 8).toNat<512 := by
    dsimp only [fieldPrime] at bound
    omega_using [split9,bound,lo8]
  have lowTopBound : (w 7 >>> 18).toNat<2^46 := by
    have hb := (w 7).isLt
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    omega_arith
  have highValue : (representationHigh w).toNat=(w 7).toNat/2^18+2^46*(w 8).toNat := by
    rw [representationHigh,orLow46_value _ _ lowTopBound]
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega_arith : (w 8).toNat<2^18)]
  have highBound : (representationHigh w).toNat<2^55 := by
    rw [highValue]
    have hb := (w 7).isLt
    omega_arith
  have firstValue := orLow55_value (w 0) (representationHigh w) highBound
  change (representationFirst w).toNat=_ at firstValue
  have shiftValue := shifted9_value ((List.range 8).map w)
  have low7 := value_lt ((List.range 7).map w)
  have split8 := value_append ((List.range 7).map w) [w 7]
  have eq8 : (List.range 8).map w=(List.range 7).map w++[w 7] := rfl
  rw [←eq8] at split8
  simp only [List.length_map,List.length_range,value,Nat.mul_zero,Nat.add_zero] at split8 low7
  have highDivision : value ((List.range 9).map w)/upperBase=(representationHigh w).toNat := by
    rw [highValue]
    dsimp only [upperBase]
    omega_using [split9,split8,low7]
  have rawValue : value (representationForwardRaw w)=
      (representationHigh w).toNat+rotateBase*value ((List.range 8).map w) := by
    simp only [representationForwardRaw,value]
    rw [firstValue]
    change value ((List.range 8).map w)=512*value (shifted9 ((List.range 8).map w))+(w 0).toNat%512 at shiftValue
    dsimp only [rotateBase]
    omega_using [shiftValue]
  have mask := maskLast_value (representationForwardRaw w) (by rfl)
  change value (representationForwardWords w)=_ at mask
  rw [mask,rawValue]
  have divLo := Nat.mod_add_div (value ((List.range 8).map w)) upperBase
  have remLo : value ((List.range 8).map w)%upperBase<upperBase := Nat.mod_lt _ (by apply Nat.pow_pos; decide)
  have divFull := Nat.mod_add_div (value ((List.range 9).map w)) upperBase
  have remFull : value ((List.range 9).map w)%upperBase<upperBase := Nat.mod_lt _ (by apply Nat.pow_pos; decide)
  rw [highDivision] at divFull
  dsimp only [toMontValue,rotateBase,upperBase] at divLo remLo divFull remFull ⊢
  omega_using [split9,highValue,split8,low7,topBound,divLo,remLo,divFull,remFull,highBound]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64.P521Square
open VG.Proof.Ed25519.AArch64

abbrev representationToCode := VG.Impl.Weierstrass.AArch64.P521Native.representationToCode

def representationToClob : List Reg := [.x1,.x2,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x21]

theorem representation_to_words (s : State) :
    WP isa (.block representationToCode) s fun t =>
      (∀i<9,t.gpr (representationReg i)=
        (representationForwardWords (fun j => s.gpr (representationReg j))).getD i 0) ∧
      Keeps representationToClob s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [representationToCode,VG.Impl.Weierstrass.AArch64.P521Native.representationToCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,Nat.reduceLT,Nat.mul_zero,BitVec.shiftLeft_zero,BitVec.add_zero,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · intro i hi
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · dsimp only [representationToClob]
    reg_keeps
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]
  · simp only [RegUpd.v_write]

theorem representation_to_value (s : State)
    (bound : value ((List.range 9).map (fun j => s.gpr (representationReg j)))<fieldPrime) :
    WP isa (.block representationToCode) s fun t =>
      value ((List.range 9).map (fun j => t.gpr (representationReg j)))=
        toMontValue (value ((List.range 9).map (fun j => s.gpr (representationReg j)))) ∧
      value ((List.range 9).map (fun j => t.gpr (representationReg j)))<fieldPrime ∧
      Keeps representationToClob s t ∧ t.v=s.v := by
  refine WP.mono (representation_to_words s) fun t ⟨words,k,v⟩ => ?_
  have he : (List.range 9).map (fun j => t.gpr (representationReg j))=
      representationForwardWords (fun j => s.gpr (representationReg j)) := by
    apply List.ext_getElem
    · rfl
    · intro i h1 h2
      have hi : i<9 := by simpa only [List.length_map,List.length_range] using h1
      simpa only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h2,Option.getD_some] using words i hi
  rw [he]
  have hv := representation_forward_value (fun j => s.gpr (representationReg j)) bound
  exact ⟨hv,by rw [hv]; exact toMontValue_bound bound,k,v⟩

end VG.Proof.Mont.AArch64.P521Field
