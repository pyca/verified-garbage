module

public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Structural stack safety without expanding the fixed schedules -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Impl.Mont.X86.Rt.StaticSquare

 def noSp (i : Instr) : Bool := !VG.X86.Taint.clobbers i .esp

 theorem inputProducts_noSp (N k count : Nat) : (inputProducts N k count).all noSp=true := by
  unfold inputProducts
  rw [List.all_flatMap,List.all_eq_true]
  intro i hi
  unfold inputTerm
  split <;> rfl

 theorem reductionProducts_noSp (N k count : Nat) : (reductionProducts N k count).all noSp=true := by
  unfold reductionProducts
  rw [List.all_flatMap,List.all_eq_true]
  intro i hi
  unfold reductionTerm
  split <;> rfl

 theorem input_noSp (N k : Nat) : (input N k).all noSp=true := by
  unfold input
  split
  · simp only [List.all_append,inputProducts_noSp]
    split <;> rfl
  · rfl

 theorem column_noSp (N k : Nat) : (column N k).allInstrs noSp=true := by
  rw [Code.allInstrs_eq]
  simp only [column,seqs,VG.Impl.Mont.X86.Rt.Square.seqs,instrs,List.all_append,
    input_noSp,reductionProducts_noSp]
  unfold digit
  split <;> rfl

 theorem columns_noSp (N k count : Nat) : (columns N k count).allInstrs noSp=true := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
    change (column N k).allInstrs noSp && (columns N (k+1) count).allInstrs noSp=true
    rw [column_noSp,ih]
    rfl

 theorem square_noSp (N : Nat) : (square N).allInstrs noSp=true := by
  change (((.block init : Prog isa).allInstrs noSp &&
    ((columns N 0 (2*N)).allInstrs noSp && (.block (finish N) : Prog isa).allInstrs noSp)) &&
    (VG.Impl.Mont.X86.Rt.subM.allInstrs noSp &&
      ((.block VG.Impl.Mont.X86.Rt.mask : Prog isa).allInstrs noSp &&
        (VG.Impl.Mont.X86.Rt.select.allInstrs noSp && (.block VG.Impl.Mont.X86.Rt.restoreRegs : Prog isa).allInstrs noSp))))=true
  rw [columns_noSp]
  rfl

 theorem selectSize_noSp (N : Nat) {fallback : Prog isa} (h : fallback.allInstrs noSp=true) :
    (selectSize N fallback).allInstrs noSp=true := by
  change true && ((square N).allInstrs noSp && fallback.allInstrs noSp)=true
  rw [square_noSp,h]
  rfl

 theorem seq_noSp {a b : Prog isa} (ha : a.allInstrs noSp=true) (hb : b.allInstrs noSp=true) :
    (Code.seq a b).allInstrs noSp=true := by change a.allInstrs noSp && b.allInstrs noSp=true; rw [ha,hb]; rfl
 theorem ite_noSp {a b : Prog isa} (cond : Cond) (ha : a.allInstrs noSp=true) (hb : b.allInstrs noSp=true) :
    (Code.ite cond a b).allInstrs noSp=true := by change a.allInstrs noSp && b.allInstrs noSp=true; rw [ha,hb]; rfl

 theorem body_noSp : VG.Impl.Mont.X86.Rt.body.allInstrs noSp=true := by
  unfold VG.Impl.Mont.X86.Rt.body dispatch
  apply seq_noSp (by rfl)
  apply ite_noSp
  · exact selectSize_noSp 64 (selectSize_noSp 96 (selectSize_noSp 128 (by decide)))
  · decide

 theorem body_NoSp : NoSp VG.Impl.Mont.X86.Rt.body := NoSp.of_all body_noSp

 theorem column_stack (N k : Nat) : stackUse (column N k)=0 := rfl
 theorem columns_stack (N k count : Nat) : stackUse (columns N k count)=0 := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih => change max (stackUse (column N k)) (stackUse (columns N (k+1) count))=0; rw [column_stack,ih]; rfl
 theorem square_stack (N : Nat) : stackUse (square N)=0 := by
  change max (max 0 (max (stackUse (columns N 0 (2*N))) 0)) 0=0
  rw [columns_stack]
  rfl
 theorem selectSize_stack (N : Nat) {fallback : Prog isa} (h : stackUse fallback=0) : stackUse (selectSize N fallback)=0 := by
  change max 0 (max (stackUse (square N)) (stackUse fallback))=0
  rw [square_stack,h]
  rfl
 theorem body_stack : stackUse VG.Impl.Mont.X86.Rt.body=0 := by
  unfold VG.Impl.Mont.X86.Rt.body dispatch
  change max 0 (max
    (stackUse (selectSize 64 (selectSize 96 (selectSize 128 VG.Impl.Mont.X86.Rt.Square.square))))
    (stackUse VG.Impl.Mont.X86.Rt.scalarBody))=0
  rw [selectSize_stack 64 (selectSize_stack 96 (selectSize_stack 128 rfl))]
  rfl

 theorem body_spSafe : VG.Impl.Mont.X86.Rt.body.all (fun i => !isa.writesSp i)=true := by
  have e : (fun i : Instr => !isa.writesSp i)=noSp := by funext i; cases i <;> rfl
  rw [e]
  exact Code.all_of_allInstrs body_noSp

end VG.Proof.Mont.X86.StaticSquare
