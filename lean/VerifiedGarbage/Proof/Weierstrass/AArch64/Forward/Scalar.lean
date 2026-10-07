import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Pure scalar effects used by the checked doubling schedule. The semantics
below run the existing ISA; no arithmetic operation is redefined. -/
namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

inductive Op where
  | add | sub | adds | adcs | subs | sbcs | adc | sbc | csel
  | logic (o : LogicOp)
  | mul | umulh | madd
  | lsl (n : Nat) | lsr (n : Nat)
  | movz (v : BitVec 16) (n : Nat) | movk (v : BitVec 16) (n : Nat)
  deriving DecidableEq, Repr

def Op.instr : Op → Reg → Reg → Reg → Reg → Instr
  | .add,d,a,b,_ => .add .x d a b
  | .sub,d,a,b,_ => .sub .x d a b
  | .adds,d,a,b,_ => .adds .x d a b
  | .adcs,d,a,b,_ => .adcs .x d a b
  | .subs,d,a,b,_ => .subs .x d a b
  | .sbcs,d,a,b,_ => .sbcs .x d a b
  | .adc,d,a,b,_ => .adc .x d a b
  | .sbc,d,a,b,_ => .sbc .x d a b
  | .csel,d,a,b,_ => .csel .x d a b
  | .logic o,d,a,b,_ => .logic o .x d a b
  | .mul,d,a,b,_ => .mul .x d a b
  | .umulh,d,a,b,_ => .umulh d a b
  | .madd,d,a,b,c => .madd .x d a b c
  | .lsl n,d,a,_,_ => .lsl .x d a n
  | .lsr n,d,a,_,_ => .lsr .x d a n
  | .movz v n,d,_,_,_ => .movz .x d v n
  | .movk v n,d,_,_,_ => .movk .x d v n

def Op.valid : Op → Bool
  | .lsl n | .lsr n => n<64
  | .movz _ n | .movk _ n => 16*n<64
  | _ => true

def Op.flags : Op → Bool
  | .adds | .adcs | .subs | .sbcs => true
  | _ => false

/-- Canonical registers hold the operands, including the old destination for MOVK. -/
def scalarState (a b c d : BitVec 64) (carry : Bool) : State :=
  { gpr := fun r => if r=.x1 then a else if r=.x2 then b else if r=.x3 then c
      else if r=.x8 then d else 0
    sp:=0,c:=carry,mem:=fun _ => 0,rd:=[],wr:=[] }

def Op.useA : Op → Bool
  | .movz .. | .movk .. => false
  | _ => true

def Op.useB : Op → Bool
  | .lsl .. | .lsr .. | .movz .. | .movk .. => false
  | _ => true

def Op.useC : Op → Bool
  | .madd => true
  | _ => false

def Op.useD : Op → Bool
  | .movk .. => true
  | _ => false

def Op.useCarry : Op → Bool
  | .adcs | .sbcs | .adc | .sbc | .csel => true
  | _ => false

def Op.eval (op : Op) (a b c d : BitVec 64) (carry : Bool) : BitVec 64 × Bool :=
  let s := scalarState (if op.useA then a else 0) (if op.useB then b else 0)
    (if op.useC then c else 0) (if op.useD then d else 0) (op.useCarry && carry)
  let t := (exec (op.instr .x8 .x1 .x2 .x3) s).getD s
  (t.gpr .x8,t.c)

/-- The original ISA computes the same scalar value regardless of operand register names. -/
theorem scalar_run (op : Op) (hv : op.valid=true) (s : State) (d a b c : Reg) :
    ∃ t, exec (op.instr d a b c) s=some t ∧
      t.gpr d=(op.eval (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) s.c).1 ∧
      t.c=(if op.flags then (op.eval (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) s.c).2 else s.c) ∧
      (∀ r,r≠d → t.gpr r=s.gpr r) ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      t.sp=s.sp ∧ t.v=s.v ∧ t.syms=s.syms ∧ t.unknowns=s.unknowns := by
  cases op <;>
    simp only [Op.valid,decide_eq_true_eq] at hv <;>
    simp [Op.instr,Op.eval,Op.flags,Op.useA,Op.useB,Op.useC,Op.useD,Op.useCarry,exec,scalarState,State.read,State.write,State.addWithCarry,
      hv,Size.bits,BitVec.setWidth_eq ]
  all_goals intro r hne he; exact (hne he).elim

theorem Op.eval_congr (op : Op) {a b c d a' b' c' d' : BitVec 64} {cf cf' : Bool}
    (ha : op.useA=true → a=a') (hb : op.useB=true → b=b')
    (hc : op.useC=true → c=c') (hd : op.useD=true → d=d')
    (hf : op.useCarry=true → cf=cf') : op.eval a b c d cf=op.eval a' b' c' d' cf' := by
  have va : (if op.useA then a else 0)=(if op.useA then a' else 0) := by
    split <;> simp_all
  have vb : (if op.useB then b else 0)=(if op.useB then b' else 0) := by
    split <;> simp_all
  have vc : (if op.useC then c else 0)=(if op.useC then c' else 0) := by
    split <;> simp_all
  have vd : (if op.useD then d else 0)=(if op.useD then d' else 0) := by
    split <;> simp_all
  have vf : (op.useCarry && cf)=(op.useCarry && cf') := by
    cases he : op.useCarry <;> simp [he,hf]
  simp only [Op.eval,va,vb,vc,vd,vf]

end VG.Proof.Weierstrass.AArch64.Forward
