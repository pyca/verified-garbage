import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Scalar
import VerifiedGarbage.Proof.Mont.AArch64.Words

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

inductive Decoded where
  | scalar (op : Op) (d a b c : Reg)
  | load (d : Reg) (off : Nat)
  | store (r : Reg) (off : Nat)

def Decoded.instr : Decoded → Instr
  | .scalar op d a b c => op.instr d a b c
  | .load d off => .ldr .x d .x0 off
  | .store r off => .str .x r .x0 off

/-- Only the scalar instruction forms actually used by field arithmetic are accepted. -/
def decode : (i : Instr) → Option {v : Decoded // v.instr=i}
  | .add .x d a b => some ⟨.scalar .add d a b .x0,rfl⟩
  | .sub .x d a b => some ⟨.scalar .sub d a b .x0,rfl⟩
  | .adds .x d a b => some ⟨.scalar .adds d a b .x0,rfl⟩
  | .adcs .x d a b => some ⟨.scalar .adcs d a b .x0,rfl⟩
  | .subs .x d a b => some ⟨.scalar .subs d a b .x0,rfl⟩
  | .sbcs .x d a b => some ⟨.scalar .sbcs d a b .x0,rfl⟩
  | .adc .x d a b => some ⟨.scalar .adc d a b .x0,rfl⟩
  | .sbc .x d a b => some ⟨.scalar .sbc d a b .x0,rfl⟩
  | .csel .x d a b => some ⟨.scalar .csel d a b .x0,rfl⟩
  | .logic o .x d a b => some ⟨.scalar (.logic o) d a b .x0,rfl⟩
  | .mul .x d a b => some ⟨.scalar .mul d a b .x0,rfl⟩
  | .umulh d a b => some ⟨.scalar .umulh d a b .x0,rfl⟩
  | .madd .x d a b c => some ⟨.scalar .madd d a b c,rfl⟩
  | .lsl .x d a n => some ⟨.scalar (.lsl n) d a .x0 .x0,rfl⟩
  | .lsr .x d a n => some ⟨.scalar (.lsr n) d a .x0 .x0,rfl⟩
  | .extr .x d a b n => some ⟨.scalar (.extr n) d a b .x0,rfl⟩
  | .movz .x d v n => some ⟨.scalar (.movz v n) d .x0 .x0 .x0,rfl⟩
  | .movk .x d v n => some ⟨.scalar (.movk v n) d .x0 .x0 .x0,rfl⟩
  | .ldr .x d .x0 off => some ⟨.load d off,rfl⟩
  | .str .x r .x0 off => some ⟨.store r off,rfl⟩
  | _ => none

structure Dom (α : Type) where
  zero : α
  applyOp : Op → α → α → α → α → α → Option α

structure Dom.Sound {α : Type} (D : Dom α) (v : α → BitVec 64 × Bool) : Prop where
  zero : (v D.zero).1=0 ∧ (v D.zero).2=false
  applyOp : ∀ op a b c d f r,D.applyOp op a b c d f=some r →
    (v r).1=(op.eval (v a).1 (v b).1 (v c).1 (v d).1 (v f).2).1 ∧
    (op.flags=true → (v r).2=(op.eval (v a).1 (v b).1 (v c).1 (v d).1 (v f).2).2)

structure Env (α : Type) where
  reg : Reg → Option α
  slot : Nat → α
  carry : Option α

variable {α : Type}

def Env.setReg (e : Env α) (d : Reg) (v : α) : Env α :=
  { e with reg:=fun r => if r=d then some v else e.reg r }

def Env.setSlot (e : Env α) (off : Nat) (v : α) : Env α :=
  { e with slot:=fun j => if j=off then v else e.slot j }

def arg (D : Dom α) (e : Env α) (use : Bool) (r : Reg) : Option α :=
  if use then e.reg r else some D.zero

def carryArg (D : Dom α) (e : Env α) (op : Op) : Option α :=
  if op.useCarry then e.carry else some D.zero

def decodedStep (D : Dom α) (size : Nat) (e : Env α) : Decoded → Option (Env α)
  | .scalar op d a b c => do
    if d=.x0 || !op.valid then none else do
      let va ← arg D e op.useA a
      let vb ← arg D e op.useB b
      let vc ← arg D e op.useC c
      let vd ← arg D e op.useD d
      let cf ← carryArg D e op
      let vr ← D.applyOp op va vb vc vd cf
      return {e.setReg d vr with carry:=if op.flags then some vr else e.carry}
  | .load d off => if d=.x0 || !(off%8=0 && off+8≤size && off<32768) then none
      else some (e.setReg d (e.slot off))
  | .store r off => if !(off%8=0 && off+8≤size && off<32768) then none
      else (e.reg r).map (e.setSlot off)

def step (D : Dom α) (size : Nat) (e : Env α) (i : Instr) : Option (Env α) := do
  let view ← decode i
  decodedStep D size e view.val

def eval (D : Dom α) (size : Nat) : List Instr → Env α → Option (Env α)
  | [],e => some e
  | i::is,e => (step D size e i).bind (eval D size is)

/-- The abstract state records only initialized field words and carry. -/
structure Rel (v : α → BitVec 64 × Bool) (base : Addr) (size : Nat) (e : Env α) (s : State) : Prop where
  reg : ∀ r a,e.reg r=some a → (v a).1=s.gpr r
  slot : ∀ off,off%8=0 → off+8≤size → (v (e.slot off)).1=s.mem.readW (base+BitVec.ofNat 64 off) 64
  carry : ∀ a,e.carry=some a → (v a).2=s.c

end VG.Proof.Weierstrass.AArch64.Forward
