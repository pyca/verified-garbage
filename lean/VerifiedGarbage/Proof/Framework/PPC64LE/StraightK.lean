module

import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Bitslice.Dom
public import VerifiedGarbage.Proof.Framework.Bitslice.Machine
import VerifiedGarbage.Proof.Framework.InlineMatch
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# PPC64LE: straight-line bitwise code with constants, by evaluation

As `Framework/X86_64/Straight.lean` and `Framework/Arm/Straight.lean`, for
PPC64LE: a block of 64-bit `and`, `or`, `xor`, `rotrdi` and `srdi`
instructions, of `ld` and `std` on two memory areas (read-write *slots*
`8k(base)`, `k < slots`, and read-only *external words* `8k(ext)`,
`k < exts`), and of the instructions that build constants (`li`, `lis`,
`ori`, `oris`, `sldi`, `addi`, `subi` of known values) is evaluated over an
abstract domain (`VG.Bitslice.Dom`) by `eval`. `run` says that the machine
then runs the block without faulting, and that its registers and memory
words are related to the abstract result as they were to the abstract
initial values.

Constants are built from immediates, so the evaluator also tracks the
registers whose concrete value it knows (`Env.cst`); such a register's
abstract value is the domain's constant, if the domain has one. `or d n n`
(`mr`) copies a register, whatever its abstract value. (`Straight.lean` is
the same evaluator without constants.)

The evaluator rejects (`none`) any other instruction, any other memory
operand, any write of the two base registers and any use of an unknown
value.
-/

@[expose] public section

namespace VG.PPC64LE.StraightK

open VG.Bitslice

/-- The two memory areas: slots `8k(base)` for `k < slots` (read and
written), and external words `8k(ext)` for `k < exts` (only read). -/
structure Cfg where
  base : Reg
  slots : Nat
  ext : Reg
  exts : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the registers and slots (`none` if unknown), and
the registers whose concrete value is known. -/
structure Env (α : Type) where
  reg : Reg → Option α
  slot : Nat → Option α
  cst : Reg → Option (BitVec 64) := fun _ => none

variable {α : Type}

/-- Set register `d` to the abstract value `a` and the known value `c`. -/
def Env.set (e : Env α) (d : Reg) (a : Option α) (c : Option (BitVec 64)) : Env α :=
  { e with reg := fun r => if r = d then a else e.reg r,
           cst := fun r => if r = d then c else e.cst r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

/-- Where a memory operand points. -/
inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

/-- The slot or external word that `off(n)` addresses, if any. -/
def Cfg.loc (c : Cfg) (n : Reg) (off : Nat) : Option Where :=
  if off % 8 = 0 ∧ off < 2 ^ 15 ∧ n ≠ .r0 then
    if n = c.base ∧ off / 8 < c.slots then some (.slot (off / 8))
    else if n = c.ext ∧ off / 8 < c.exts then some (.ext (off / 8))
    else none
  else none

/-- The concrete logical operation. -/
def logicOp : LogicOp → BitVec 64 → BitVec 64 → BitVec 64
  | .and => (· &&& ·)
  | .or => (· ||| ·)
  | .xor => (· ^^^ ·)

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

def binop : LogicOp → α → α → Option α
  | .xor => D.xor
  | .and => D.and
  | .or => D.or

/-- A known constant. -/
def constant (e : Env α) (d : Reg) (v : BitVec 64) : Env α := e.set d (D.const v) (some v)

/-- The written register is neither base. -/
def okDst (d : Reg) : Bool := d != c.base && d != c.ext

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .logic op d n m =>
    if !okDst c d then none else
    match e.cst n, e.cst m with
    | some x, some y => some (constant D e d (logicOp op x y))
    | _, _ =>
      if op = .or ∧ n = m then (e.reg n).map fun a => e.set d (some a) none else
      match e.reg n, e.reg m with
      | some a, some b => (binop D op a b).map fun r => e.set d (some r) none
      | _, _ => none
  | .rotr .d d n sh =>
    if !okDst c d ∨ ¬ sh < 64 then none else
    match e.cst n with
    | some x => some (constant D e d (x.rotateRight sh))
    | none => ((e.reg n).bind (D.ror sh)).map fun r => e.set d (some r) none
  | .lsr .d d n sh =>
    if !okDst c d ∨ ¬ sh < 64 then none else
    match e.cst n with
    | some x => some (constant D e d (x >>> sh))
    | none => ((e.reg n).bind (D.shr sh)).map fun r => e.set d (some r) none
  | .lsl d n sh =>
    if !okDst c d ∨ ¬ sh < 64 then none else
    (e.cst n).map fun (x : BitVec 64) => constant D e d (x <<< sh)
  | .li d imm =>
    if !okDst c d ∨ ¬ imm < 2 ^ 15 then none else some (constant D e d (BitVec.ofNat 64 imm))
  | .lis d imm =>
    if !okDst c d then none else some (constant D e d ((imm ++ (0 : BitVec 16)).signExtend 64))
  | .ori d n imm =>
    if !okDst c d then none else (e.cst n).map fun x => constant D e d (x ||| imm.setWidth 64)
  | .oris d n imm =>
    if !okDst c d then none else
    (e.cst n).map fun x => constant D e d (x ||| imm.setWidth 64 <<< 16)
  | .addi d n imm =>
    if !okDst c d ∨ n = .r0 ∨ ¬ imm < 2 ^ 15 then none else
    (e.cst n).map fun x => constant D e d (x + BitVec.ofNat 64 imm)
  | .subi d n imm =>
    if !okDst c d ∨ n = .r0 ∨ ¬ imm ≤ 2 ^ 15 then none else
    (e.cst n).map fun x => constant D e d (x - BitVec.ofNat 64 imm)
  | .load .d t n off =>
    if !okDst c t then none else
    match c.loc n off with
    | some (.slot k) => (e.slot k).map fun a => e.set t (some a) none
    | some (.ext k) => (ext k).map fun a => e.set t (some a) none
    | none => none
  | .store .d t n off =>
    match c.loc n off with
    | some (.slot k) => (e.reg t).map (e.setSlot k)
    | _ => none
  | _ => none

/-- The block's effect on the abstract values. -/
def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c ext e i).bind (eval is)

end

/-! ## The evaluator the kernel runs (`Framework/Bitslice/Machine.lean`) -/

namespace Kernel

open VG.Bitslice.Machine (Op Idx bool_rec_idx Ent valK cstK val1 val2 cst1 cstK_eq)

instance : Idx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

/-- An instruction that `step` evaluates. -/
inductive Shape where
  | bad
  | logic (op : LogicOp) (d n m : Reg)
  | rotr (d n : Reg) (sh : Nat)
  | lsr (d n : Reg) (sh : Nat)
  | lsl (d n : Reg) (sh : Nat)
  | li (d : Reg) (imm : Nat)
  | lis (d : Reg) (imm : BitVec 16)
  | ori (d n : Reg) (imm : BitVec 16)
  | oris (d n : Reg) (imm : BitVec 16)
  | addi (d n : Reg) (imm : Nat)
  | subi (d n : Reg) (imm : Nat)
  | load (t n : Reg) (off : Nat)
  | store (t n : Reg) (off : Nat)

def shapeFn : Instr → Shape
  | .logic op d n m => .logic op d n m
  | .rotr .d d n sh => .rotr d n sh
  | .lsr .d d n sh => .lsr d n sh
  | .lsl d n sh => .lsl d n sh
  | .li d imm => .li d imm
  | .lis d imm => .lis d imm
  | .ori d n imm => .ori d n imm
  | .oris d n imm => .oris d n imm
  | .addi d n imm => .addi d n imm
  | .subi d n imm => .subi d n imm
  | .load .d t n off => .load t n off
  | .store .d t n off => .store t n off
  | _ => .bad

/-- `shapeFn`, with its cases closed (`inline_match%`). -/
def shape : Instr → Shape := inline_match% shapeFn

theorem shape_eq (i : Instr) : shape i = shapeFn i := by
  cases i <;> first | rfl | (rename Size => sz; cases sz <;> rfl)

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

/-- `Cfg.loc`. -/
noncomputable def locK (n : Reg) (off : Nat) (slot ext : Nat → Op Reg (Ent α) α) : Op Reg (Ent α) α :=
  .eq (Nat.mod off 8) 0 (.lt off 32768 (.ne n .r0
    (.area n c.base c.slots c.ext c.exts (Nat.div off 8) slot ext)))

noncomputable def binopK (op : LogicOp) : α → α → Option α := LogicOp.rec D.and D.or D.xor op

noncomputable def logicK (op : LogicOp) : Nat → Nat → Nat := LogicOp.rec Nat.land Nat.lor Nat.xor op

/-- `or d, n, n`: a move. -/
noncomputable def orSame (x : Ent α) : Option (Ent α) :=
  Option.rec (valK x.val) (fun u => cstK D (Nat.lor u u)) x.cst

noncomputable def logic2 (op : LogicOp) (x y : Ent α) : Option (Ent α) :=
  Option.rec (val2 (binopK D op) x y)
    (fun u => Option.rec (val2 (binopK D op) x y) (fun v => cstK D (logicK op u v)) y.cst) x.cst

/-- `fk` of a known constant, or else `fv` of the abstract value. -/
noncomputable def cstOr (fk : Nat → Nat) (fv : α → Option α) (x : Ent α) : Option (Ent α) :=
  Option.rec (val1 fv x) (fun u => cstK D (fk u)) x.cst

/-- `2 ^ 64`. -/
abbrev two64 : Nat := 18446744073709551616

noncomputable def op (i : Instr) : Op Reg (Ent α) α :=
  Shape.rec (motive := fun _ => Op Reg (Ent α) α) .bad
    (fun op d n m => .dst c.base c.ext d (LogicOp.rec
      (.r2 (logic2 D .and) d n m)
      (Bool.rec (.r2 (logic2 D .or) d n m) (.r1 (orSame D) d n) (Nat.beq (Idx.ix n) (Idx.ix m)))
      (.r2 (logic2 D .xor) d n m) op))
    (fun d n sh => .dst c.base c.ext d (.lt sh 64
      (.r1 (cstOr D (fun v => ((BitVec.ofNat 64 v).rotateRight sh).toNat) (D.ror sh)) d n)))
    (fun d n sh => .dst c.base c.ext d (.lt sh 64
      (.r1 (cstOr D (fun v => Nat.shiftRight v sh) (D.shr sh)) d n)))
    (fun d n sh => .dst c.base c.ext d (.lt sh 64
      (.r1 (cst1 D fun v => Nat.mod (Nat.shiftLeft v sh) two64) d n)))
    (fun d imm => .dst c.base c.ext d (.lt imm 32768 (.r0 (cstK D imm) d)))
    (fun d imm => .dst c.base c.ext d (.r0 (cstK D ((imm ++ (0 : BitVec 16)).signExtend 64).toNat) d))
    (fun d n imm => .dst c.base c.ext d (.r1 (cst1 D fun v => Nat.lor v imm.toNat) d n))
    (fun d n imm => .dst c.base c.ext d
      (.r1 (cst1 D fun v => Nat.lor v (Nat.mod (Nat.shiftLeft imm.toNat 16) two64)) d n))
    (fun d n imm => .dst c.base c.ext d (.ne n .r0 (.lt imm 32768
      (.r1 (cst1 D fun v => Nat.mod (Nat.add v imm) two64) d n))))
    (fun d n imm => .dst c.base c.ext d (.ne n .r0 (.lt imm 32769
      (.r1 (cst1 D fun v => Nat.mod (Nat.add (Nat.sub two64 imm) v) two64) d n))))
    (fun t n off => .dst c.base c.ext t
      (locK c n off (.ld (fun a => valK (some a)) t) fun k => .r0 (valK (ext k)) t))
    (fun t n off => locK c n off (fun k => .st (fun x => x.val) k t) fun _ => .bad)
    (shape i)

/-- The abstract state, as the kernel's evaluator has it. -/
def toM (e : Env α) : Machine.Env Reg (Ent α) α :=
  ⟨fun r => some ⟨e.reg r, (e.cst r).map BitVec.toNat⟩, e.slot⟩

def ofM (e : Machine.Env Reg (Ent α) α) : Env α :=
  ⟨fun r => (e.reg r).bind Ent.val, e.slot, fun r => (e.reg r).bind fun x => x.cst.map (BitVec.ofNat 64)⟩

theorem ofM_toM (e : Env α) : ofM (toM e) = e := by
  cases e with
  | mk r s k =>
    refine congrArg (Env.mk r s) (funext fun q => ?_)
    show (k q |>.map BitVec.toNat).map (BitVec.ofNat 64) = k q
    cases k q with
    | none => rfl
    | some v => exact congrArg some (BitVec.ofNat_toNat ..|>.trans (BitVec.setWidth_eq v))

theorem toM_set (e : Env α) (d : Reg) (a : Option α) (k : Option (BitVec 64)) :
    (toM e).setReg d ⟨a, k.map BitVec.toNat⟩ = toM (e.set d a k) := by
  refine congrArg (fun f => (⟨f, _⟩ : Machine.Env Reg (Ent α) α)) (funext fun r => ?_)
  show (if Idx.ix r = Idx.ix d then _ else _) = _
  by_cases h : r = d
  · subst h; simp only [Env.set, ite_true]
  · rw [ite_eq_right fun e => h (Idx.ix_inj e)]; simp only [toM, Env.set, ite_eq_right h]

theorem toM_val (e : Env α) (d : Reg) (a : Option α) :
    (valK a).map ((toM e).setReg d) = (a.map fun a => e.set d (some a) none).map toM := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (toM_set e d (some a) none)

theorem toM_cst {D : Dom α 64} (e : Env α) (d : Reg) (v : BitVec 64) :
    (cstK D v.toNat).map ((toM e).setReg d) = some (toM (constant D e d v)) := by
  rw [cstK_eq]; exact congrArg some (toM_set e d (D.const v) (some v))

theorem toM_cst' {D : Dom α 64} (e : Env α) (d : Reg) {n : Nat} {v : BitVec 64} (h : n = v.toNat) :
    (cstK D n).map ((toM e).setReg d) = some (toM (constant D e d v)) := by
  rw [h, toM_cst]

theorem locK_eq (n : Reg) (off : Nat) (slot ext : Nat → Op Reg (Ent α) α) :
    locK c n off slot ext = match c.loc n off with
      | some (.slot k) => slot k
      | some (.ext k) => ext k
      | none => .bad := by
  rw [locK, Op.eq_eq, Op.lt_eq, Op.ne_eq, Op.area_eq, Cfg.loc]
  show (if off % 8 = 0 then if off < 32768 then if n = .r0 then .bad else
    (if n = c.base ∧ off / 8 < c.slots then slot (off / 8)
    else if n = c.ext ∧ off / 8 < c.exts then ext (off / 8) else .bad) else .bad else .bad) = _
  by_cases h1 : off % 8 = 0
  · rw [ite_eq_left h1]
    by_cases h2 : off < 32768
    · rw [ite_eq_left h2]
      by_cases h0 : n = .r0
      · rw [ite_eq_left h0, ite_eq_right fun h => h.2.2 h0]
      · rw [ite_eq_right h0, ite_eq_left (show _ ∧ _ ∧ _ from ⟨h1, h2, h0⟩)]
        by_cases hb : n = c.base ∧ off / 8 < c.slots
        · rw [ite_eq_left hb, ite_eq_left hb]
        · rw [ite_eq_right hb, ite_eq_right hb]
          by_cases he : n = c.ext ∧ off / 8 < c.exts
          · rw [ite_eq_left he, ite_eq_left he]
          · rw [ite_eq_right he, ite_eq_right he]
    · rw [ite_eq_right h2, ite_eq_right fun h => h2 h.2.1]
  · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.1]

variable {D c ext}

theorem okDst_of {d : Reg} (h : ¬ (d = c.base ∨ d = c.ext)) : okDst c d = true := by
  rw [okDst, Bool.and_eq_true, bne_iff_ne, bne_iff_ne]
  exact ⟨fun e => h (.inl e), fun e => h (.inr e)⟩

theorem not_okDst {d : Reg} {p : Prop} (h : ¬ (d = c.base ∨ d = c.ext)) (hp : p) :
    ¬ ((!okDst c d) = true ∨ ¬ p) := by
  rw [okDst_of h]; exact fun h => h.elim (fun h => Bool.false_ne_true h) fun h => h hp

theorem not_okDst1 {d : Reg} (h : ¬ (d = c.base ∨ d = c.ext)) : ¬ (!okDst c d) = true := by
  rw [okDst_of h]; exact Bool.false_ne_true

theorem val1_eq (f : α → Option α) (x : Ent α) : val1 f x = valK (x.val.bind f) := by
  obtain ⟨_ | a, _⟩ := x <;> rfl

theorem val2_eq (f : α → α → Option α) (x y : Ent α) :
    val2 f x y = valK (x.val.bind fun a => y.val.bind (f a)) := by
  obtain ⟨_ | a, _⟩ := x <;> obtain ⟨_ | b, _⟩ := y <;> rfl

theorem logicK_eq (op : LogicOp) (u v : BitVec 64) : logicK op u.toNat v.toNat = (logicOp op u v).toNat := by
  cases op
  · exact (BitVec.toNat_and ..).symm
  · exact (BitVec.toNat_or ..).symm
  · exact (BitVec.toNat_xor ..).symm

theorem cstOr_step {e : Env α} {fk : Nat → Nat} {gk : BitVec 64 → BitVec 64} {fv : α → Option α} {d n : Reg}
    {m : Machine.Env Reg (Ent α) α} (hf : ∀ v : BitVec 64, fk v.toNat = (gk v).toNat)
    (h : Machine.step (toM e) (.r1 (cstOr D fk fv) d n) = some m) :
    (match e.cst n with
      | some x => some (constant D e d (gk x))
      | none => ((e.reg n).bind fv).map fun r => e.set d (some r) none).map toM = some m := by
  change (cstOr D _ _ ⟨e.reg n, (e.cst n).map _⟩).map _ = _ at h
  cases hn : e.cst n with
  | some v => rw [hn] at h; rw [← h]; exact (toM_cst' e d (hf v)).symm
  | none =>
    rw [hn] at h; change (val1 _ _).map _ = _ at h
    rw [val1_eq] at h; rw [← h]; exact (toM_val e d _).symm

theorem cst1_step {e : Env α} {fk : Nat → Nat} {gk : BitVec 64 → BitVec 64} {d n : Reg}
    {m : Machine.Env Reg (Ent α) α} (hf : ∀ v : BitVec 64, fk v.toNat = (gk v).toNat)
    (h : Machine.step (toM e) (.r1 (cst1 D fk) d n) = some m) :
    ((e.cst n).map fun x => constant D e d (gk x)).map toM = some m := by
  change (cst1 D _ ⟨e.reg n, (e.cst n).map _⟩).map _ = _ at h
  cases hn : e.cst n with
  | some v => rw [hn] at h; rw [← h]; exact (toM_cst' e d (hf v)).symm
  | none => rw [hn] at h; cases h

theorem logic2_step {e : Env α} {op : LogicOp} {d n k : Reg} {m : Machine.Env Reg (Ent α) α}
    (ho : ¬ (op = LogicOp.or ∧ n = k)) (h : Machine.step (toM e) (.r2 (logic2 D op) d n k) = some m) :
    (match e.cst n, e.cst k with
      | some x, some y => some (constant D e d (logicOp op x y))
      | _, _ =>
        if op = LogicOp.or ∧ n = k then (e.reg n).map fun a => e.set d (some a) none else
        match e.reg n, e.reg k with
        | some a, some b => (binop D op a b).map fun r => e.set d (some r) none
        | _, _ => none).map toM = some m := by
  rw [ite_eq_right ho]
  change (logic2 D op ⟨e.reg n, (e.cst n).map _⟩ ⟨e.reg k, (e.cst k).map _⟩).map _ = _ at h
  have hv (x y : Option Nat) (h : (val2 (binopK D op) ⟨e.reg n, x⟩ ⟨e.reg k, y⟩).map ((toM e).setReg d) = some m) :
      (match e.reg n, e.reg k with
        | some a, some b => (binop D op a b).map fun r => e.set d (some r) none
        | _, _ => none).map toM = some m := by
    rw [val2_eq, toM_val] at h
    rw [← h]
    have e1 : binopK D op = binop D op := by cases op <;> rfl
    rw [e1]
    cases e.reg n <;> cases e.reg k <;> rfl
  cases hn : e.cst n with
  | none => rw [hn] at h; exact hv _ _ h
  | some u =>
    cases hk : e.cst k with
    | none => rw [hn, hk] at h; exact hv _ _ h
    | some v => rw [hn, hk] at h; rw [← h]; exact (toM_cst' e d (logicK_eq op u v)).symm

/-- What the kernel's evaluator computes, `step` does. -/
theorem step_of_op {e : Env α} {i : Instr} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.step (toM e) (op D c ext i) = some m) : (step D c ext e i).map toM = some m := by
  rw [op, shape_eq] at h
  cases i with
  | logic op d n k =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right (not_okDst1 hd)]
    cases op with
    | and => exact logic2_step (fun h => by cases h.1) h
    | xor => exact logic2_step (fun h => by cases h.1) h
    | or =>
      rw [bool_rec_idx] at h
      by_cases hk : n = k
      · subst hk
        rw [ite_eq_left rfl] at h
        rw [ite_eq_left (show LogicOp.or = LogicOp.or ∧ n = n from ⟨rfl, rfl⟩)]
        change (orSame D ⟨e.reg n, (e.cst n).map _⟩).map _ = _ at h
        cases hn : e.cst n with
        | none => rw [hn] at h; rw [← h]; exact (toM_val e d _).symm
        | some u => rw [hn] at h; rw [← h]; exact (toM_cst' e d (logicK_eq LogicOp.or u u)).symm
      · rw [ite_eq_right hk] at h
        exact logic2_step (fun h => hk h.2) h
  | rotr sz d n sh =>
    cases sz
    · cases h
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]; rw [ite_eq_right (not_okDst hd hs)]
    exact cstOr_step (gk := fun v => v.rotateRight sh) (fun v => by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) h
  | lsr sz d n sh =>
    cases sz
    · cases h
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]; rw [ite_eq_right (not_okDst hd hs)]
    exact cstOr_step (gk := fun v => v >>> sh) (fun v => (BitVec.toNat_ushiftRight ..).symm) h
  | lsl d n sh =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]; rw [ite_eq_right (not_okDst hd hs)]
    exact cst1_step (gk := fun v => v <<< sh) (fun v => BitVec.toNat_shiftLeft.symm) h
  | li d imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]; rw [ite_eq_right (not_okDst hd hs), ← h]
    refine (toM_cst' e d ?_).symm
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hs (by decide))]
  | lis d imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right (not_okDst1 hd), ← h]
    exact (toM_cst e d _).symm
  | ori d n imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right (not_okDst1 hd)]
    refine cst1_step (gk := fun v => v ||| imm.setWidth 64) (fun v => ?_) h
    rw [BitVec.toNat_or, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans imm.isLt (by decide))]; rfl
  | oris d n imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right (not_okDst1 hd)]
    refine cst1_step (gk := fun v => v ||| imm.setWidth 64 <<< 16) (fun v => ?_) h
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans imm.isLt (by decide))]; rfl
  | addi d n imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨h0, h⟩ := Machine.step_ne h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]
    rw [ite_eq_right fun x => x.elim (not_okDst1 hd) fun x => x.elim h0 fun x => x hs]
    refine cst1_step (gk := fun v => v + BitVec.ofNat 64 imm) (fun v => ?_) h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (b := 2 ^ 64) (a := imm) (Nat.lt_trans hs (by decide))]; rfl
  | subi d n imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨h0, h⟩ := Machine.step_ne h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]
    rw [ite_eq_right fun x => x.elim (not_okDst1 hd) fun x => x.elim h0 fun x => x (Nat.le_of_lt_succ hs)]
    refine cst1_step (gk := fun v => v - BitVec.ofNat 64 imm) (fun v => ?_) h
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (b := 2 ^ 64) (a := imm) (Nat.lt_trans hs (by decide))]; rfl
  | load sz t n off =>
    cases sz
    · cases h
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right (not_okDst1 hd)]
    rw [locK_eq] at h
    cases hl : c.loc n off with
    | none => rw [hl] at h; cases h
    | some w =>
      rw [hl] at h
      cases w with
      | slot k =>
        change ((e.slot k).bind _).map _ = _ at h
        show ((e.slot k).map _).map toM = _
        cases hk : e.slot k with
        | none => rw [hk] at h; cases h
        | some a => rw [hk] at h; rw [← h]; exact (toM_val e t _).symm
      | ext k => rw [← h]; exact (toM_val e t _).symm
  | store sz t n off =>
    cases sz
    · cases h
    simp only [step]
    change Machine.step (toM e) (locK c n off _ _) = _ at h
    rw [locK_eq] at h
    cases hl : c.loc n off with
    | none => rw [hl] at h; cases h
    | some w =>
      rw [hl] at h
      cases w with
      | slot k =>
        change (e.reg t).map _ = _ at h
        show ((e.reg t).map _).map toM = _
        rw [← h]; cases e.reg t <;> rfl
      | ext k => cases h
  | _ => cases h

/-- What the kernel's evaluator computes, `eval` does. -/
theorem eval_of_op {is : List Instr} {e : Env α} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.eval (op D c ext) is (toM e) = some m) : ∃ e', eval D c ext is e = some e' ∧ toM e' = m := by
  induction is generalizing e with
  | nil => exact ⟨e, rfl, Option.some.inj h⟩
  | cons i is ih =>
    simp only [Machine.eval, Option.bind_eq_some_iff] at h
    obtain ⟨m₁, h₁, h₂⟩ := h
    obtain ⟨e₁, he₁, rfl⟩ := Option.map_eq_some_iff.mp (step_of_op h₁)
    obtain ⟨e', he', hm⟩ := ih h₂
    exact ⟨e', by rw [eval, he₁]; exact he', hm⟩

end

end Kernel

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

/-- Evaluates the block and checks `post` of the result, for the kernel. -/
noncomputable def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  Machine.run (Kernel.toM e) 5 (Nat.log2 c.slots + 1) (Kernel.op D c ext) (fun e => post (Kernel.ofM e)) is

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c ext is e post = true) : ∃ e', eval D c ext is e = some e' ∧ post e' = true := by
  obtain ⟨m, hm, hp⟩ := Machine.run_sound h
  obtain ⟨e', he, rfl⟩ := Kernel.eval_of_op hm
  rw [Kernel.ofM_toM] at hp
  exact ⟨e', he, hp⟩

theorem check_mono {is : List Instr} {e : Env α} {p q : Env α → Bool}
    (hpq : ∀ e, p e = true → q e = true) (h : check D c ext is e p = true) :
    check D c ext is e q = true := Machine.run_mono (fun _ => hpq _) h

end

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` (or external word `k`) of the base address `b`. -/
abbrev wordAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (8 * k)

/-- The machine state's registers, slots and external words are related by
`R` to the abstract ones that are known, and the known constants are the
registers' values. -/
structure Rel (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e : Env α)
    (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.gpr r)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    R a (s.mem.readW (wordAddr (s.gpr c.base) k) 64)
  ext : ∀ k a, k < c.exts → ext k = some a → R a (s.mem.readW (wordAddr (s.gpr c.ext) k) 64)
  cst : ∀ r v, e.cst r = some v → s.gpr r = v

/-- What the machine needs for the memory areas: they are accessible, the
slots do not wrap around, and the external words do not overlap the slots. -/
structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (wordAddr (s.gpr c.base) k) 8
  extIn : ∀ k < c.exts, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.ext) k) 8
  slots : 8 * c.slots < 2 ^ 64
  sep : ∀ k < c.slots, ∀ j < c.exts,
    Mem.Sep (wordAddr (s.gpr c.base) k) 8 (wordAddr (s.gpr c.ext) j) 8

/-- The slot area. -/
def slotRegion (c : Cfg) (s : State) : Region := ⟨s.gpr c.base, 8 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (he : s'.gpr c.ext = s.gpr c.ext) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  extIn k hk := by rw [he, hrd, hwr]; exact h.extIn k hk
  slots := h.slots
  sep k hk j hj := by rw [hb, he]; exact h.sep k hk j hj

theorem slot_sep (b : Addr) {j k : Nat} (hj : 8 * j < 2 ^ 64) (hk : 8 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (wordAddr b j) 8 (wordAddr b k) 8 := by
  intro x h₁ h₂
  simp only [wordAddr, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - b).isLt
  omega_using [hj, hk, h, h₁, h₂]

theorem slot_contains (b : Addr) {n k : Nat} (hk : k < n) (hn : 8 * n < 2 ^ 64) :
    (⟨b, 8 * n⟩ : Region).Contains (wordAddr b k) (64 / 8) := by
  simp only [Region.Contains, wordAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk, hn])]
  omega_using [hk]

theorem loc_some_slot {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some (.slot k)) :
    n = c.base ∧ off = 8 * k ∧ k < c.slots ∧ off < 2 ^ 15 ∧ n ≠ .r0 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      exact ⟨h2.1, by omega, h2.2, h1.2.1, h1.2.2⟩
    · split at h <;> cases h
  · cases h

theorem loc_some_ext {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some (.ext k)) :
    n = c.ext ∧ off = 8 * k ∧ k < c.exts ∧ off < 2 ^ 15 ∧ n ≠ .r0 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        exact ⟨h2.1, by omega, h2.2, h1.2.1, h1.2.2⟩
      · cases h
  · cases h

section
variable {D : Dom α 64} {R : α → BitVec 64 → Prop} {c : Cfg} {ext : Nat → Option α}

/-- The facts about one step, and so about a block. -/
structure Post (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e' : Env α)
    (s s' : State) (writes : Reg → Prop) : Prop where
  rel : Rel R c ext e' s'
  ok : Ok c s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  base : s'.gpr c.base = s.gpr c.base
  ext : s'.gpr c.ext = s.gpr c.ext
  other : ∀ r, ¬ writes r → s'.gpr r = s.gpr r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : Reg → Prop}
    (p : Post R c ext e' s s' W) (h : ∀ r, W r → W' r) : Post R c ext e' s s' W' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw) }

theorem write_gpr (s : State) (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.write d v).gpr r = if r = d then v else s.gpr r := rfl

theorem okDst_ne {d : Reg} (h : okDst c d = true) : d ≠ c.base ∧ d ≠ c.ext := by
  simp only [okDst, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h

/-- Writing register `d` with a value related to `a` (if known) and equal to `cv` (if known). -/
theorem post_set {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg}
    {a : Option α} {cv : Option (BitVec 64)} {v : BitVec 64} (hv : ∀ x, a = some x → R x v)
    (hc : ∀ x, cv = some x → v = x) (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (e.set d a cv) s (s.write d v) (· = d) := by
  have hbase : (s.write d v).gpr c.base = s.gpr c.base := by
    rw [write_gpr, ite_eq_right_iff.mpr (fun h => absurd h.symm hb)]
  have hext : (s.write d v).gpr c.ext = s.gpr c.ext := by
    rw [write_gpr, ite_eq_right_iff.mpr (fun h => absurd h.symm he)]
  refine ⟨⟨fun r x h => ?_, fun k x hk h => ?_, fun k x hk h => ?_, fun r x h => ?_⟩,
    hok.congr hbase hext rfl rfl, rfl, rfl, rfl, rfl, hbase, hext, fun r hr => ?_, Frame.refl _ _⟩
  · simp only [Env.set] at h
    rw [write_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hv x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.reg r x h
  · rw [hbase]; exact hrel.slot k x hk h
  · rw [hext]; exact hrel.ext k x hk h
  · simp only [Env.set] at h
    rw [write_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hc x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.cst r x h
  · rw [write_gpr, ite_eq_right hr]

theorem const_ok {e : Env α} {s : State} (hD : D.Sound R) (hok : Ok c s) (hrel : Rel R c ext e s)
    {d : Reg} {v : BitVec 64} (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (constant D e d v) s (s.write d v) (· = d) :=
  post_set hok hrel (fun _ h => hD.const h) (fun _ h => Option.some.inj h) hb he

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => dstOf i = some r) := by
  cases i with
  | logic op d n m =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd
    refine ⟨_, exec_logic, ?_⟩
    split at h
    · rename_i x y hx hy
      cases h
      rw [hrel.cst n x hx, hrel.cst m y hy]
      cases op <;> exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
    · split at h
      · rename_i hnm
        obtain ⟨rfl, rfl⟩ := hnm
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
          (fun _ h => by cases h) hb he).writes fun r h => by simp [dstOf, h]
        cases hx
        simpa using hrel.reg n a ha
      · split at h
        · rename_i a b ha hb'
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
          have hRa := hrel.reg n a ha
          have hRb := hrel.reg m b hb'
          refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_)
            (fun _ h => by cases h) hb he).writes fun r h => by simp [dstOf, h]
          cases hx
          cases op
          · exact hD.and hRa hRb hr
          · exact hD.or hRa hRb hr
          · exact hD.xor hRa hRb hr
        · cases h
  | rotr sz d n sh =>
    cases sz with
    | w => simp [step] at h
    | d =>
      simp only [step] at h
      split at h
      · cases h
      rename_i hd
      simp only [not_or, Bool.not_eq_true', Bool.not_eq_false, Classical.not_not] at hd
      obtain ⟨hb, he⟩ := okDst_ne hd.1
      refine ⟨_, exec_rotr_d hd.2, ?_⟩
      split at h
      · rename_i x hx
        cases h
        rw [hrel.cst n x hx]
        exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
        refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_)
          (fun _ h => by cases h) hb he).writes fun r h => by simp [dstOf, h]
        cases hx
        exact hD.ror (hrel.reg n a ha) hr
  | lsr sz d n sh =>
    cases sz with
    | w => simp [step] at h
    | d =>
      simp only [step] at h
      split at h
      · cases h
      rename_i hd
      simp only [not_or, Bool.not_eq_true', Bool.not_eq_false, Classical.not_not] at hd
      obtain ⟨hb, he⟩ := okDst_ne hd.1
      refine ⟨_, exec_lsr_d hd.2, ?_⟩
      split at h
      · rename_i x hx
        cases h
        rw [hrel.cst n x hx]
        exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
        refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_)
          (fun _ h => by cases h) hb he).writes fun r h => by simp [dstOf, h]
        cases hx
        exact hD.shr (hrel.reg n a ha) hr
  | lsl d n sh =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Bool.not_eq_true', Bool.not_eq_false, Classical.not_not] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd.1
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨_, exec_lsl hd.2, ?_⟩
    rw [hrel.cst n x hx]
    exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
  | li d imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Bool.not_eq_true', Bool.not_eq_false, Classical.not_not] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd.1
    cases h
    exact ⟨_, exec_li hd.2, (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]⟩
  | lis d imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd
    cases h
    exact ⟨_, exec_lis, (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]⟩
  | ori d n imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨_, exec_ori, ?_⟩
    rw [hrel.cst n x hx]
    exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
  | oris d n imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨_, exec_oris, ?_⟩
    rw [hrel.cst n x hx]
    exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
  | addi d n imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Bool.not_eq_true', Bool.not_eq_false, Classical.not_not] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd.1
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨_, exec_addi hd.2.1 hd.2.2, ?_⟩
    rw [hrel.cst n x hx]
    exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
  | subi d n imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or, Bool.not_eq_true', Bool.not_eq_false, Classical.not_not] at hd
    obtain ⟨hb, he⟩ := okDst_ne hd.1
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨_, exec_subi hd.2.1 hd.2.2, ?_⟩
    rw [hrel.cst n x hx]
    exact (const_ok hD hok hrel hb he).writes fun r h => by simp [dstOf, h]
  | load sz t n off =>
    cases sz with
    | w => simp [step] at h
    | d =>
      simp only [step] at h
      split at h
      · cases h
      rename_i hd
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hd
      obtain ⟨hb, he⟩ := okDst_ne hd
      split at h
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hnb, hoff, hlt, h15, hn0⟩ := loc_some_slot hk
        subst hnb hoff
        obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
        have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.base) k) 8 :=
          ⟨r, List.mem_append_right _ hr, hc⟩
        refine ⟨_, exec_load_d hn0 ⟨h15, by omega_using []⟩ hin, ?_⟩
        refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
          (fun _ h => by cases h) hb he).writes fun r h => by simp [dstOf, h]
        cases hx
        exact hrel.slot k a hlt ha
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hne, hoff, hlt, h15, hn0⟩ := loc_some_ext hk
        subst hne hoff
        refine ⟨_, exec_load_d hn0 ⟨h15, by omega_using []⟩ (hok.extIn k hlt), ?_⟩
        refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
          (fun _ h => by cases h) hb he).writes fun r h => by simp [dstOf, h]
        cases hx
        exact hrel.ext k a hlt ha
      · cases h
  | store sz t n off =>
    cases sz with
    | w => simp [step] at h
    | d =>
      simp only [step] at h
      split at h
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hnb, hoff, hlt, h15, hn0⟩ := loc_some_slot hk
        subst hnb hoff
        have hin := hok.slotIn k hlt
        refine ⟨_, exec_store_d hn0 ⟨h15, by omega_using []⟩ hin, ?_⟩
        have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (wordAddr (s.gpr c.base) j) (64 / 8)
            (wordAddr (s.gpr c.base) k) (64 / 8) := fun j hj hjk =>
          slot_sep _ (by have := hok.slots; omega_using [hj, this]) (by have := hok.slots; omega_using [h15]) hjk
        refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_,
            fun r v h => hrel.cst r v h⟩,
          hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
        · simp only [Env.setSlot] at hjb
          split at hjb
          · rename_i hjk
            subst hjk
            rw [← Option.some.inj hjb]
            simpa [Mem.readW_writeW_self64] using hrel.reg t a ha
          · rename_i hjk
            rw [Mem.readW_writeW_sep (hsep j hj hjk) (by decide)]
            exact hrel.slot j b hj hjb
        · have hs : Mem.Sep (wordAddr (s.gpr c.ext) j) (64 / 8) (wordAddr (s.gpr c.base) k) (64 / 8) :=
            fun x h₁ h₂ => hok.sep k hlt j hj x h₂ h₁
          rw [Mem.readW_writeW_sep hs (by decide)]
          exact hrel.ext j b hj hjb
        · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
            (slot_contains _ hlt hok.slots)
      · cases h
  | _ => simp [step] at h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) (h : eval D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' (fun r => (is.all fun i => dstOf i != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.rd.trans p₁.rd, p.wr.trans p₁.wr, p.sp.trans p₁.sp, p.lr.trans p₁.lr,
      p.base.trans p₁.base, p.ext.trans p₁.ext, fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

/-- The machine runs a block that the abstract evaluator accepts, and the
result is the same whatever the domain: facts about it can be gathered
from several domains and relations. -/
theorem run_unique {s s₁ s₂ : State} {is : List Instr} (h₁ : runBlock isa is s = some s₁)
    (h₂ : runBlock isa is s = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-! ## Memory areas in regions -/

theorem contains_word {r : Region} {a : Addr} {off k n : Nat} (ha : a = r.base + BitVec.ofNat 64 off)
    (hk : off + 8 * k + 8 ≤ n) (hn : n ≤ r.len) (hlen : r.len < 2 ^ 64) :
    r.Contains (wordAddr a k) 8 := by
  simp only [Region.Contains, wordAddr, ha]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [hk, hn, hlen])]
  omega_using [hk, hn]

/-- `Ok` for slots at offset `off` of a writable region, and no external words. -/
theorem Ok.of_off {c : Cfg} {s : State} {r : Region} {off : Nat} (hr : r ∈ s.wr)
    (hb : s.gpr c.base = r.base + BitVec.ofNat 64 off) (hlen : off + 8 * c.slots ≤ r.len)
    (hn : r.len < 2 ^ 64) (he : c.exts = 0) : Ok c s where
  slotIn k hk := ⟨r, hr, contains_word hb (by omega_using [hlen, hk]) (Nat.le_refl _) hn⟩
  extIn k hk := by omega
  slots := by omega_using [hlen, hn]
  sep k _ j hj := by omega

/-- `Ok` for slots at the start of a writable region, and no external words. -/
theorem Ok.of_region {c : Cfg} {s : State} {r : Region} (hr : r ∈ s.wr)
    (hb : r.base = s.gpr c.base) (hlen : 8 * c.slots ≤ r.len) (hn : r.len < 2 ^ 64)
    (he : c.exts = 0) : Ok c s :=
  Ok.of_off (off := 0) hr (by rw [← hb]; simp) (by omega_using [hlen]) hn he

end VG.PPC64LE.StraightK
