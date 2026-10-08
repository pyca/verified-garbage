import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Data
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Pure scalar effects used by the checked doubling schedule. The semantics
below run the existing ISA; no arithmetic operation is redefined. -/
namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

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
