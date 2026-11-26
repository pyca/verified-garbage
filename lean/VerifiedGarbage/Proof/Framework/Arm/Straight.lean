module

import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.Bitslice.Dom
public import VerifiedGarbage.Proof.Framework.Bitslice.Machine
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ARMv7: straight-line bitwise code, by evaluation

As `Framework/AArch64/Straight.lean`, for ARMv7: a block of `and`, `orr`,
`eor` (with a register, an immediate, or a register rotated or shifted
right as the second operand), `mov`, `add`/`sub` of known constants,
`movw`, `movt`, `ldr` and `str` instructions on registers and on two memory
areas (read-write *slots* `[base, #4k]`, `k < slots`, and read-only
*external words* `[ext, #4k]`, `k < exts`) is evaluated over an abstract
domain (`VG.Bitslice.Dom`) by `eval`. `run` says that the machine then runs
the block without faulting, and that its registers and memory words are
related to the abstract result as they were to the abstract initial values.

Constants are built with `mov` of an immediate, `movw` and `movt` (or an
immediate added to or subtracted from a known constant), so the evaluator
also tracks the registers whose concrete value it knows (`Env.cst`); such a
register's abstract value is the domain's constant, if the domain has one.

The evaluator rejects (`none`) any other instruction, any other memory
operand, any write of the two base registers and any use of an unknown
value.
-/

@[expose] public section

namespace VG.Arm.Straight

open VG.Bitslice

/-- The two memory areas: slots `[base, #4k]` for `k < slots` (read and
written), and external words `[ext, #4k]` for `k < exts` (only read). -/
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
  cst : Reg → Option (BitVec 32) := fun _ => none

variable {α : Type}

/-- Set register `d` to the abstract value `a` and the known value `c`. -/
def Env.set (e : Env α) (d : Reg) (a : Option α) (c : Option (BitVec 32)) : Env α :=
  { e with reg := fun r => if r = d then a else e.reg r,
           cst := fun r => if r = d then c else e.cst r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

/-- Where a memory operand points. -/
inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

/-- The slot or external word that `[n, #off]` addresses, if any. -/
def Cfg.loc (c : Cfg) (n : Reg) (off : Nat) : Option Where :=
  if off % 4 = 0 ∧ off < 4096 then
    if n = c.base ∧ off / 4 < c.slots then some (.slot (off / 4))
    else if n = c.ext ∧ off / 4 < c.exts then some (.ext (off / 4))
    else none
  else none

section
variable (D : Dom α 32) (c : Cfg) (ext : Nat → Option α)

def binop : DpOp → α → α → Option α
  | .eor => D.xor
  | .and => D.and
  | .orr => D.or
  | _ => fun _ _ => none

/-- A known constant. -/
def constant (e : Env α) (d : Reg) (v : BitVec 32) : Env α := e.set d (D.const v) (some v)

/-- The abstract value of a second operand. -/
def op2Abs (e : Env α) : Op2 → Option α
  | .imm v => if encodable v then D.const v else none
  | .reg r => e.reg r
  | .shifted r .ror n => if 1 ≤ n ∧ n ≤ 31 then (e.reg r).bind (D.ror n) else none
  | .shifted r .lsr n => if 1 ≤ n ∧ n ≤ 31 then (e.reg r).bind (D.shr n) else none
  | .shifted _ .lsl _ => none

/-- The known value of a second operand. -/
def op2Cst (e : Env α) : Op2 → Option (BitVec 32)
  | .imm v => if encodable v then some v else none
  | .reg r => e.cst r
  | .shifted .. => none

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .mov d o =>
    if d = c.base ∨ d = c.ext then none else
    match op2Cst e o with
    | some v => some (constant D e d v)
    | none => (op2Abs D e o).map fun a => e.set d (some a) none
  | .dp op d n o =>
    if d = c.base ∨ d = c.ext then none else
    match op with
    | .add => match e.cst n, op2Cst e o with
      | some x, some y => some (constant D e d (x + y))
      | _, _ => none
    | .sub => match e.cst n, op2Cst e o with
      | some x, some y => some (constant D e d (x - y))
      | _, _ => none
    | _ => match e.reg n, op2Abs D e o with
      | some a, some b => (binop D op a b).map fun r => e.set d (some r) none
      | _, _ => none
  | .movw d imm =>
    if d = c.base ∨ d = c.ext then none else some (constant D e d (imm.setWidth 32))
  | .movt d imm =>
    if d = c.base ∨ d = c.ext then none else
    match e.cst d with
    | some v => some (constant D e d (imm ++ v.extractLsb' 0 16 : BitVec 32))
    | none => none
  | .ldr t n off =>
    if t = c.base ∨ t = c.ext then none else
    match c.loc n off with
    | some (.slot k) => (e.slot k).map fun a => e.set t (some a) none
    | some (.ext k) => (ext k).map fun a => e.set t (some a) none
    | none => none
  | .str t n off =>
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

open VG.Bitslice.Machine (Op Idx bind Ent valK cstK val1 val2 cst1 cst2 mov1 cstK_eq)

instance : Idx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

/-- An instruction that `step` or `stepN` (`StraightNot.lean`) evaluates. -/
inductive Shape where
  | bad
  | mov (d : Reg) (o : Op2)
  | dp (op : DpOp) (d n : Reg) (o : Op2)
  | movw (d : Reg) (imm : BitVec 16)
  | movt (d : Reg) (imm : BitVec 16)
  | ldr (t n : Reg) (off : Nat)
  | str (t n : Reg) (off : Nat)
  | mvn (d : Reg) (o : Op2)

def shapeFn : Instr → Shape
  | .mov d o => .mov d o
  | .dp op d n o => .dp op d n o
  | .movw d imm => .movw d imm
  | .movt d imm => .movt d imm
  | .ldr t n off => .ldr t n off
  | .str t n off => .str t n off
  | .mvn d o => .mvn d o
  | _ => .bad

/-- `shapeFn`, with its cases closed (`inline_match%`). -/
def shape : Instr → Shape := inline_match% shapeFn

theorem shape_eq (i : Instr) : shape i = shapeFn i := by cases i <;> rfl

section
variable (D : Dom α 32) (c : Cfg) (ext : Nat → Option α)

/-- `Cfg.loc`. -/
noncomputable def locK (n : Reg) (off : Nat) (slot ext : Nat → Op Reg (Ent α) α) : Op Reg (Ent α) α :=
  .eq (Nat.mod off 4) 0 (.lt off 4096 (.area n c.base c.slots c.ext c.exts (Nat.div off 4) slot ext))

/-- A second operand: an encodable immediate, a register, or a function of one. -/
noncomputable def srcK (imm : BitVec 32 → Op Reg (Ent α) α) (reg : Reg → Op Reg (Ent α) α)
    (sh : (α → Option α) → Reg → Op Reg (Ent α) α) (o : Op2) : Op Reg (Ent α) α :=
  Op2.rec (fun v => Bool.rec .bad (imm v) (encodable v)) reg
    (fun r s n => .lt 0 n (.lt n 32 (Shift.rec .bad (sh (D.shr n) r) (sh (D.ror n) r) s))) o

/-- `d := f n o`, of abstract values. -/
noncomputable def valK2 (f : α → α → Option α) (d n : Reg) (o : Op2) : Op Reg (Ent α) α :=
  srcK D (fun v => .r1 (val1 fun a => bind (f a) (D.const v)) d n) (fun r => .r2 (val2 f) d n r)
    (fun g r => .r2 (val2 fun a b => bind (f a) (g b)) d n r) o

/-- `d := f o`, of abstract values. -/
noncomputable def valK1 (f : α → Option α) (d : Reg) (o : Op2) : Op Reg (Ent α) α :=
  srcK D (fun v => .r0 (valK (bind f (D.const v))) d) (fun r => .r1 (val1 f) d r)
    (fun g r => .r1 (val1 fun a => bind f (g a)) d r) o

/-- `d := f n o`, of known constants. -/
noncomputable def cstK2 (f : Nat → Nat → Nat) (d n : Reg) (o : Op2) : Op Reg (Ent α) α :=
  srcK D (fun v => .r1 (cst1 D fun u => f u v.toNat) d n) (fun r => .r2 (cst2 D f) d n r)
    (fun _ _ => .bad) o

noncomputable def movK (d : Reg) (o : Op2) : Op Reg (Ent α) α :=
  srcK D (fun v => .r0 (cstK D v.toNat) d) (fun r => .r1 (mov1 D) d r) (fun g r => .r1 (val1 g) d r) o

/-- `2 ^ 32`. -/
abbrev two32 : Nat := 4294967296

/-- What the instruction does, `bic` and `mvn` being given. -/
noncomputable def opW (bic : Reg → Reg → Op2 → Op Reg (Ent α) α) (mvn : Reg → Op2 → Op Reg (Ent α) α)
    (i : Instr) : Op Reg (Ent α) α :=
  Shape.rec (motive := fun _ => Op Reg (Ent α) α) .bad
    (fun d o => .dst c.base c.ext d (movK D d o))
    (fun op d n o => .dst c.base c.ext d (DpOp.rec
      (cstK2 D (fun u v => Nat.mod (Nat.add u v) two32) d n o)
      (cstK2 D (fun u v => Nat.mod (Nat.add (Nat.sub two32 v) u) two32) d n o)
      (valK2 D D.and d n o) (valK2 D D.or d n o) (valK2 D D.xor d n o) (bic d n o) op))
    (fun d imm => .dst c.base c.ext d (.r0 (cstK D imm.toNat) d))
    (fun d imm => .dst c.base c.ext d
      (.r1 (cst1 D fun v => Nat.lor (Nat.shiftLeft imm.toNat 16) (Nat.mod v 65536)) d d))
    (fun t n off => .dst c.base c.ext t
      (locK c n off (.ld (fun a => valK (some a)) t) fun k => .r0 (valK (ext k)) t))
    (fun t n off => locK c n off (fun k => .st (fun x => x.val) k t) fun _ => .bad)
    (fun d o => .dst c.base c.ext d (mvn d o))
    (shape i)

noncomputable def op : Instr → Op Reg (Ent α) α := opW D c ext (fun _ _ _ => .bad) (fun _ _ => .bad)

/-- The abstract state, as the kernel's evaluator has it. -/
def toM (e : Env α) : Machine.Env Reg (Ent α) α :=
  ⟨fun r => some ⟨e.reg r, (e.cst r).map BitVec.toNat⟩, e.slot⟩

def ofM (e : Machine.Env Reg (Ent α) α) : Env α :=
  ⟨fun r => (e.reg r).bind Ent.val, e.slot, fun r => (e.reg r).bind fun x => x.cst.map (BitVec.ofNat 32)⟩

theorem ofM_toM (e : Env α) : ofM (toM e) = e := by
  cases e with
  | mk r s k =>
    refine congrArg (Env.mk r s) (funext fun q => ?_)
    show (k q |>.map BitVec.toNat).map (BitVec.ofNat 32) = k q
    cases k q with
    | none => rfl
    | some v => exact congrArg some (BitVec.ofNat_toNat ..|>.trans (BitVec.setWidth_eq v))

theorem toM_set (e : Env α) (d : Reg) (a : Option α) (k : Option (BitVec 32)) :
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

theorem toM_cst {D : Dom α 32} (e : Env α) (d : Reg) (v : BitVec 32) :
    (cstK D v.toNat).map ((toM e).setReg d) = some (toM (constant D e d v)) := by
  rw [cstK_eq]; exact congrArg some (toM_set e d (D.const v) (some v))

theorem toM_cst' {D : Dom α 32} (e : Env α) (d : Reg) {n : Nat} {v : BitVec 32} (h : n = v.toNat) :
    (cstK D n).map ((toM e).setReg d) = some (toM (constant D e d v)) := by
  rw [h, toM_cst]

theorem locK_eq (n : Reg) (off : Nat) (slot ext : Nat → Op Reg (Ent α) α) :
    locK c n off slot ext = match c.loc n off with
      | some (.slot k) => slot k
      | some (.ext k) => ext k
      | none => .bad := by
  rw [locK, Op.eq_eq, Op.lt_eq, Op.area_eq, Cfg.loc]
  show (if off % 4 = 0 then if off < 4096 then
    (if n = c.base ∧ off / 4 < c.slots then slot (off / 4)
    else if n = c.ext ∧ off / 4 < c.exts then ext (off / 4) else .bad) else .bad else .bad) = _
  by_cases h2 : off % 4 = 0
  · rw [ite_eq_left h2]
    by_cases h1 : off < 4096
    · rw [ite_eq_left h1, ite_eq_left (show _ ∧ _ from ⟨h2, h1⟩)]
      by_cases hb : n = c.base ∧ off / 4 < c.slots
      · rw [ite_eq_left hb, ite_eq_left hb]
      · rw [ite_eq_right hb, ite_eq_right hb]
        by_cases he : n = c.ext ∧ off / 4 < c.exts
        · rw [ite_eq_left he, ite_eq_left he]
        · rw [ite_eq_right he, ite_eq_right he]
    · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.2]
  · rw [ite_eq_right h2, ite_eq_right fun h => h2 h.1]

variable {D c ext}

/-- A second operand that the evaluator accepts. -/
theorem srcK_step {e : Env α} {imm : BitVec 32 → Op Reg (Ent α) α} {reg : Reg → Op Reg (Ent α) α}
    {sh : (α → Option α) → Reg → Op Reg (Ent α) α} {o : Op2} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.step (toM e) (srcK D imm reg sh o) = some m) :
    (∃ v, op2Abs D e o = D.const v ∧ op2Cst e o = some v ∧ Machine.step (toM e) (imm v) = some m) ∨
    (∃ r, op2Abs D e o = e.reg r ∧ op2Cst e o = e.cst r ∧ Machine.step (toM e) (reg r) = some m) ∨
    (∃ g r, op2Abs D e o = (e.reg r).bind g ∧ op2Cst e o = none ∧ Machine.step (toM e) (sh g r) = some m) := by
  cases o with
  | imm v =>
    refine .inl ⟨v, ?_⟩
    cases hv : encodable v with
    | false => change Machine.step _ (Bool.rec _ _ (encodable v)) = _ at h; rw [hv] at h; cases h
    | true =>
      change Machine.step _ (Bool.rec _ _ (encodable v)) = _ at h; rw [hv] at h
      exact ⟨by simp only [op2Abs, hv, ite_true], by simp only [op2Cst, hv, ite_true], h⟩
  | reg r => exact .inr (.inl ⟨r, rfl, rfl, h⟩)
  | shifted r s n =>
    obtain ⟨h0, h⟩ := Machine.step_lt h
    obtain ⟨hn, h⟩ := Machine.step_lt h
    have hn' : 1 ≤ n ∧ n ≤ 31 := ⟨h0, Nat.le_of_lt_succ hn⟩
    refine .inr (.inr ?_)
    cases s with
    | lsl => cases h
    | lsr => exact ⟨D.shr n, r, by simp only [op2Abs]; exact ite_eq_left hn', rfl, h⟩
    | ror => exact ⟨D.ror n, r, by simp only [op2Abs]; exact ite_eq_left hn', rfl, h⟩

theorem toM_reg (e : Env α) (n : Reg) : (toM e).reg n = some ⟨e.reg n, (e.cst n).map BitVec.toNat⟩ := rfl

theorem val1_eq (f : α → Option α) (x : Ent α) : val1 f x = valK (x.val.bind f) := by
  obtain ⟨_ | a, _⟩ := x <;> rfl

theorem val2_eq (f : α → α → Option α) (x y : Ent α) :
    val2 f x y = valK (x.val.bind fun a => y.val.bind (f a)) := by
  obtain ⟨_ | a, _⟩ := x <;> obtain ⟨_ | b, _⟩ := y <;> rfl

theorem valK2_step {e : Env α} {f : α → α → Option α} {d n : Reg} {o : Op2}
    {m : Machine.Env Reg (Ent α) α} (h : Machine.step (toM e) (valK2 D f d n o) = some m) :
    (((e.reg n).bind fun a => (op2Abs D e o).bind (f a)).map fun r => e.set d (some r) none).map toM =
      some m := by
  rw [← toM_val]
  rcases srcK_step h with ⟨v, ha, -, h⟩ | ⟨r, ha, -, h⟩ | ⟨g, r, ha, -, h⟩
  · change (val1 _ _).map _ = _ at h
    rw [val1_eq] at h
    rw [ha, ← h]
    simp only [Machine.bind_eq]
  · change (val2 _ _ _).map _ = _ at h
    rw [val2_eq] at h
    rw [ha, ← h]
  · change (val2 _ _ _).map _ = _ at h
    rw [val2_eq] at h
    rw [ha, ← h]
    simp only [Machine.bind_eq, Option.bind_assoc]

theorem valK1_step {e : Env α} {f : α → Option α} {d : Reg} {o : Op2}
    {m : Machine.Env Reg (Ent α) α} (h : Machine.step (toM e) (valK1 D f d o) = some m) :
    (((op2Abs D e o).bind f).map fun r => e.set d (some r) none).map toM = some m := by
  rw [← toM_val]
  rcases srcK_step h with ⟨v, ha, -, h⟩ | ⟨r, ha, -, h⟩ | ⟨g, r, ha, -, h⟩
  · change (valK _).map _ = _ at h
    rw [Machine.bind_eq] at h
    rw [ha, ← h]
  · change (val1 _ _).map _ = _ at h
    rw [val1_eq] at h
    rw [ha, ← h]
  · change (val1 _ _).map _ = _ at h
    rw [val1_eq] at h
    rw [ha, ← h]
    simp only [Machine.bind_eq, Option.bind_assoc]

theorem cstK2_step {e : Env α} {f : Nat → Nat → Nat} {g : BitVec 32 → BitVec 32 → BitVec 32}
    (hf : ∀ u v : BitVec 32, f u.toNat v.toNat = (g u v).toNat) {d n : Reg} {o : Op2}
    {m : Machine.Env Reg (Ent α) α} (h : Machine.step (toM e) (cstK2 D f d n o) = some m) :
    (match e.cst n, op2Cst e o with
      | some x, some y => some (constant D e d (g x y))
      | _, _ => none).map toM = some m := by
  rcases srcK_step h with ⟨v, -, ha, h⟩ | ⟨r, -, ha, h⟩ | ⟨_, r, -, -, h⟩
  · change (cst1 D _ ⟨_, (e.cst n).map _⟩).map _ = _ at h
    rw [ha]
    cases hn : e.cst n with
    | none => rw [hn] at h; cases h
    | some u => rw [hn] at h; rw [← h]; exact (toM_cst' e d (hf u v)).symm
  · change (cst2 D _ ⟨_, (e.cst n).map _⟩ ⟨_, (e.cst r).map _⟩).map _ = _ at h
    rw [ha]
    cases hn : e.cst n with
    | none => rw [hn] at h; cases h
    | some u =>
      cases hr : e.cst r with
      | none => rw [hn, hr] at h; cases h
      | some v => rw [hn, hr] at h; rw [← h]; exact (toM_cst' e d (hf u v)).symm
  · cases h

theorem movK_step {e : Env α} {d : Reg} {o : Op2} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.step (toM e) (movK D d o) = some m) :
    (match op2Cst e o with
      | some v => some (constant D e d v)
      | none => (op2Abs D e o).map fun a => e.set d (some a) none).map toM = some m := by
  rcases srcK_step h with ⟨v, -, ha, h⟩ | ⟨r, ha, hc, h⟩ | ⟨g, r, ha, hc, h⟩
  · rw [ha, ← h]; exact (toM_cst e d v).symm
  · change (mov1 D ⟨e.reg r, (e.cst r).map _⟩).map _ = _ at h
    rw [ha, hc]
    cases hr : e.cst r with
    | none => rw [hr] at h; rw [← h]; exact (toM_val e d _).symm
    | some v => rw [hr] at h; rw [← h]; exact (toM_cst e d v).symm
  · change (val1 _ _).map _ = _ at h
    rw [val1_eq] at h
    rw [ha, hc, ← h]; exact (toM_val e d _).symm

/-- What the kernel's evaluator computes, `step` does, `bic` and `mvn` aside. -/
theorem step_of_opW {bic : Reg → Reg → Op2 → Op Reg (Ent α) α} {mvn : Reg → Op2 → Op Reg (Ent α) α}
    {e : Env α} {i : Instr} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.step (toM e) (opW D c ext bic mvn i) = some m) :
    (step D c ext e i).map toM = some m ∨
    (∃ d n o, i = .dp .bic d n o ∧ ¬ (d = c.base ∨ d = c.ext) ∧ Machine.step (toM e) (bic d n o) = some m) ∨
    (∃ d o, i = .mvn d o ∧ ¬ (d = c.base ∨ d = c.ext) ∧ Machine.step (toM e) (mvn d o) = some m) := by
  rw [opW, shape_eq] at h
  cases i with
  | mov d o =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    refine .inl ?_
    simp only [step]; rw [ite_eq_right hd]; exact movK_step h
  | dp op d n o =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    have hv {f : α → α → Option α} (hop : binop D op = f) (h : Machine.step (toM e) (valK2 D f d n o) = some m) :
        (match e.reg n, op2Abs D e o with
          | some a, some b => (binop D op a b).map fun r => e.set d (some r) none
          | _, _ => none).map toM = some m := by
      rw [hop, ← valK2_step h]
      cases e.reg n <;> cases op2Abs D e o <;> rfl
    cases op with
    | add =>
      refine .inl ?_
      simp only [step]; rw [ite_eq_right hd]
      exact cstK2_step (g := (· + ·)) (fun u v => (BitVec.toNat_add ..).symm) h
    | sub =>
      refine .inl ?_
      simp only [step]; rw [ite_eq_right hd]
      exact cstK2_step (g := (· - ·)) (fun u v => by rw [BitVec.toNat_sub]; rfl) h
    | and => refine .inl ?_; simp only [step]; rw [ite_eq_right hd]; exact hv rfl h
    | orr => refine .inl ?_; simp only [step]; rw [ite_eq_right hd]; exact hv rfl h
    | eor => refine .inl ?_; simp only [step]; rw [ite_eq_right hd]; exact hv rfl h
    | bic => exact .inr (.inl ⟨d, n, o, rfl, hd, h⟩)
  | movw d imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    refine .inl ?_
    simp only [step]; rw [ite_eq_right hd, ← h]
    refine (toM_cst' e d ?_).symm
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans imm.isLt (by decide))]
  | movt d imm =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    refine .inl ?_
    simp only [step]; rw [ite_eq_right hd]
    change (cst1 D _ ⟨_, (e.cst d).map _⟩).map _ = _ at h
    cases hn : e.cst d with
    | some v =>
      rw [hn] at h; rw [← h]
      refine (toM_cst' e d ?_).symm
      rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]; rfl
    | none => rw [hn] at h; cases h
  | ldr t n off =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    refine .inl ?_
    simp only [step]; rw [ite_eq_right hd]
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
  | str t n off =>
    refine .inl ?_
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
  | mvn d o =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    exact .inr (.inr ⟨d, o, rfl, hd, h⟩)
  | _ => cases h

theorem step_of_op {e : Env α} {i : Instr} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.step (toM e) (op D c ext i) = some m) : (step D c ext e i).map toM = some m := by
  rcases step_of_opW h with h | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
  · exact h
  · cases h
  · cases h

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
variable (D : Dom α 32) (c : Cfg) (ext : Nat → Option α)

/-- Evaluates the block and checks `post` of the result, for the kernel. -/
noncomputable def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  Machine.run (Kernel.toM e) 4 (Nat.log2 c.slots + 1) (Kernel.op D c ext) (fun e => post (Kernel.ofM e)) is

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

/-- The address of word `k` (slot or external word) from the base `b`. -/
abbrev wordAddr (b : BitVec 32) (k : Nat) : Addr := State.addr (b + BitVec.ofNat 32 (4 * k))

/-- The machine state's registers, slots and external words are related by
`R` to the abstract ones that are known, and the known constants are the
registers' values. -/
structure Rel (R : α → BitVec 32 → Prop) (c : Cfg) (ext : Nat → Option α) (e : Env α)
    (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.gpr r)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    R a (s.mem.readW (wordAddr (s.gpr c.base) k) 32)
  ext : ∀ k a, k < c.exts → ext k = some a → R a (s.mem.readW (wordAddr (s.gpr c.ext) k) 32)
  cst : ∀ r v, e.cst r = some v → s.gpr r = v

/-- What the machine needs for the memory areas: they are accessible, the
slots do not wrap around, and the external words do not overlap the slots. -/
structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (wordAddr (s.gpr c.base) k) 4
  extIn : ∀ k < c.exts, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.ext) k) 4
  slots : (s.gpr c.base).toNat + 4 * c.slots ≤ 2 ^ 32
  sep : ∀ k < c.slots, ∀ j < c.exts,
    Mem.Sep (wordAddr (s.gpr c.base) k) 4 (wordAddr (s.gpr c.ext) j) 4

/-- The slot area. -/
def slotRegion (c : Cfg) (s : State) : Region := ⟨State.addr (s.gpr c.base), 4 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (he : s'.gpr c.ext = s.gpr c.ext) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  extIn k hk := by rw [he, hrd, hwr]; exact h.extIn k hk
  slots := by rw [hb]; exact h.slots
  sep k hk j hj := by rw [hb, he]; exact h.sep k hk j hj

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

/-- Word `k` from `b`, when it does not wrap around. -/
theorem wordAddr_toNat (b : BitVec 32) {k : Nat} (h : b.toNat + 4 * k < 2 ^ 32) :
    (wordAddr b k).toNat = b.toNat + 4 * k := by
  rw [wordAddr, toNat_addr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * k) (by omega_using [h]),
    Nat.mod_eq_of_lt h]

theorem slot_sep (b : BitVec 32) {j k : Nat} (hj : b.toNat + 4 * j < 2 ^ 32)
    (hk : b.toNat + 4 * k < 2 ^ 32) (h : j ≠ k) :
    Mem.Sep (wordAddr b j) 4 (wordAddr b k) 4 := by
  intro x h₁ h₂
  have e1 := wordAddr_toNat b hj
  have e2 := wordAddr_toNat b hk
  generalize wordAddr b j = A at h₁ e1
  generalize wordAddr b k = B at h₂ e2
  have : j < k ∨ k < j := by omega_using [h]
  rcases this with h' | h' <;> bv_omega

theorem slot_contains (b : BitVec 32) {n k : Nat} (hk : k < n) (hn : b.toNat + 4 * n ≤ 2 ^ 32) :
    (⟨State.addr b, 4 * n⟩ : Region).Contains (wordAddr b k) (32 / 8) := by
  simp only [Region.Contains]
  have e1 := wordAddr_toNat b (k := k) (by omega_using [hk, hn])
  have e2 := toNat_addr b
  generalize wordAddr b k = A at e1
  generalize State.addr b = B at e2
  rw [show (32 : Nat) / 8 = 4 from rfl]
  have : (A - B).toNat = 4 * k := by bv_omega
  omega_using [hk, this]

theorem loc_some_slot {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some (.slot k)) :
    n = c.base ∧ off = 4 * k ∧ k < c.slots ∧ off < 4096 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      exact ⟨h2.1, by omega_using [h1], h2.2, h1.2⟩
    · split at h <;> cases h
  · cases h

theorem loc_some_ext {c : Cfg} {n : Reg} {off k : Nat} (h : c.loc n off = some (.ext k)) :
    n = c.ext ∧ off = 4 * k ∧ k < c.exts ∧ off < 4096 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        exact ⟨h2.1, by omega_using [h1], h2.2, h1.2⟩
      · cases h
  · cases h

section
variable {D : Dom α 32} {R : α → BitVec 32 → Prop} {c : Cfg} {ext : Nat → Option α}

/-- The facts about one step, and so about a block. -/
structure Post (R : α → BitVec 32 → Prop) (c : Cfg) (ext : Nat → Option α) (e' : Env α)
    (s s' : State) (writes : Reg → Prop) : Prop where
  rel : Rel R c ext e' s'
  ok : Ok c s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  base : s'.gpr c.base = s.gpr c.base
  ext : s'.gpr c.ext = s.gpr c.ext
  other : ∀ r, ¬ writes r → s'.gpr r = s.gpr r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : Reg → Prop}
    (p : Post R c ext e' s s' W) (h : ∀ r, W r → W' r) : Post R c ext e' s s' W' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw) }

theorem setReg_gpr (s : State) (d : Reg) (v : BitVec 32) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then v else s.gpr r := rfl

/-- Writing register `d` with a value related to `a` (if known) and equal to `cv` (if known). -/
theorem post_set {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg}
    {a : Option α} {cv : Option (BitVec 32)} {v : BitVec 32} (hv : ∀ x, a = some x → R x v)
    (hc : ∀ x, cv = some x → v = x) (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (e.set d a cv) s (s.setReg d v) (· = d) := by
  have hbase : (s.setReg d v).gpr c.base = s.gpr c.base := by
    rw [setReg_gpr, ite_eq_right_iff.mpr (fun h => absurd h.symm hb)]
  have hext : (s.setReg d v).gpr c.ext = s.gpr c.ext := by
    rw [setReg_gpr, ite_eq_right_iff.mpr (fun h => absurd h.symm he)]
  refine ⟨⟨fun r x h => ?_, fun k x hk h => ?_, fun k x hk h => ?_, fun r x h => ?_⟩,
    hok.congr hbase hext rfl rfl, rfl, rfl, rfl, hbase, hext, fun r hr => ?_, Frame.refl _ _⟩
  · simp only [Env.set] at h
    rw [setReg_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hv x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.reg r x h
  · rw [hbase]; exact hrel.slot k x hk h
  · rw [hext]; exact hrel.ext k x hk h
  · simp only [Env.set] at h
    rw [setReg_gpr]
    split at h
    · rename_i hrd; rw [ite_eq_left hrd]; exact hc x h
    · rename_i hrd; rw [ite_eq_right hrd]; exact hrel.cst r x h
  · rw [setReg_gpr, ite_eq_right hr]

theorem const_ok {e : Env α} {s : State} (hD : D.Sound R) (hok : Ok c s) (hrel : Rel R c ext e s)
    {d : Reg} {v : BitVec 32} (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (constant D e d v) s (s.setReg d v) (· = d) :=
  post_set hok hrel (fun _ h => hD.const h) (fun _ h => Option.some.inj h) hb he

theorem op2Abs_ok (hD : D.Sound R) {e : Env α} {s : State} (hrel : Rel R c ext e s) {o : Op2}
    {a : α} (h : op2Abs D e o = some a) : ∃ v, o.eval s = some v ∧ R a v := by
  cases o with
  | imm v =>
    simp only [op2Abs] at h
    split at h
    · rename_i hv; exact ⟨v, by simp [Op2.eval, hv], hD.const h⟩
    · cases h
  | reg r => exact ⟨_, rfl, hrel.reg r a h⟩
  | shifted r sh n =>
    cases sh with
    | lsl => simp [op2Abs] at h
    | ror =>
      simp only [op2Abs] at h
      split at h
      · rename_i hn
        obtain ⟨b, hb, hr⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, by simp [Op2.eval, hn], hD.ror (hrel.reg r b hb) hr⟩
      · cases h
    | lsr =>
      simp only [op2Abs] at h
      split at h
      · rename_i hn
        obtain ⟨b, hb, hr⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨_, by simp [Op2.eval, hn], hD.shr (hrel.reg r b hb) hr⟩
      · cases h

theorem op2Cst_ok {e : Env α} {s : State} (hrel : Rel R c ext e s) {o : Op2} {v : BitVec 32}
    (h : op2Cst e o = some v) : o.eval s = some v := by
  cases o with
  | imm w =>
    simp only [op2Cst] at h
    split at h
    · rename_i hw; cases h; simp [Op2.eval, hw]
    · cases h
  | reg r => simp only [op2Cst] at h; simp [Op2.eval, hrel.cst r v h]
  | shifted => simp [op2Cst] at h

theorem addr_word {s : State} {n : Reg} {k : Nat} :
    State.addr (s.gpr n + BitVec.ofNat 32 (4 * k)) = wordAddr (s.gpr n) k := rfl

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => dstOf i = some r) := by
  cases i with
  | mov d o =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    split at h
    · rename_i v hv
      cases h
      refine ⟨s.setReg d v, by simp [exec, op2Cst_ok hrel hv], ?_⟩
      exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
    · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨v, hv, hR⟩ := op2Abs_ok hD hrel ha
      refine ⟨_, by simp only [exec, hv, Option.map_some]; rfl, ?_⟩
      exact (post_set hok hrel (a := some a) (cv := none) (fun x hx => by cases hx; exact hR)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
  | dp op d n o =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    cases op with
    | add =>
      simp only at h
      split at h
      · rename_i x y hx hy
        cases h
        refine ⟨_, by simp only [exec, op2Cst_ok hrel hy, hrel.cst n x hx, Option.map_some]; rfl, ?_⟩
        exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      · cases h
    | sub =>
      simp only at h
      split at h
      · rename_i x y hx hy
        cases h
        refine ⟨_, by simp only [exec, op2Cst_ok hrel hy, hrel.cst n x hx, Option.map_some]; rfl, ?_⟩
        exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      · cases h
    | bic =>
      simp only at h
      split at h <;> simp [binop] at h
    | and | orr | eor =>
      simp only at h
      split at h
      · rename_i a b ha hb
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨v, hv, hR⟩ := op2Abs_ok hD hrel hb
        have hRa := hrel.reg n a ha
        refine ⟨_, by simp only [exec, hv, Option.map_some]; rfl, ?_⟩
        refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_) (fun _ h => by cases h)
          hd.1 hd.2).writes fun r h => by simp [dstOf, h]
        cases hx
        simp only [binop] at hr
        first
        | exact hD.and hRa hR hr
        | exact hD.or hRa hR hr
        | exact hD.xor hRa hR hr
      · cases h
  | movw d imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    cases h
    exact ⟨_, rfl, (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]⟩
  | movt d imm =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    split at h
    · rename_i v hv
      cases h
      refine ⟨_, rfl, ?_⟩
      rw [hrel.cst d v hv]
      exact (const_ok hD hok hrel hd.1 hd.2).writes fun r h => by simp [dstOf, h]
    · cases h
  | ldr t n off =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_slot hk
      subst hb hoff
      obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.base) k) 4 :=
        ⟨r, List.mem_append_right _ hr, hc⟩
      refine ⟨_, exec_ldr h32 hin, ?_⟩
      refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      cases hx
      exact hrel.slot k a hlt ha
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_ext hk
      subst hb hoff
      refine ⟨_, exec_ldr h32 (hok.extIn k hlt), ?_⟩
      refine (post_set hok hrel (a := some a) (cv := none) (fun x hx => ?_)
        (fun _ h => by cases h) hd.1 hd.2).writes fun r h => by simp [dstOf, h]
      cases hx
      exact hrel.ext k a hlt ha
    · cases h
  | str t n off =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h32⟩ := loc_some_slot hk
      subst hb hoff
      have hin := hok.slotIn k hlt
      refine ⟨_, exec_str h32 hin, ?_⟩
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (wordAddr (s.gpr c.base) j) (32 / 8)
          (wordAddr (s.gpr c.base) k) (32 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega_using [hj, this]) (by have := hok.slots; omega_using [hlt, this]) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_,
          fun r v h => hrel.cst r v h⟩,
        hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          have := Mem.readW_writeW_self32 s.mem (wordAddr (s.gpr c.base) j) (s.gpr t)
          rw [addr_word, this]
          exact hrel.reg t a ha
        · rename_i hjk
          have := Mem.readW_writeW_sep (m := s.mem) (v := s.gpr t) (hsep j hj hjk) (by decide)
          rw [addr_word, this]
          exact hrel.slot j b hj hjb
      · have hs : Mem.Sep (wordAddr (s.gpr c.ext) j) (32 / 8) (wordAddr (s.gpr c.base) k) (32 / 8) :=
          fun x h₁ h₂ => hok.sep k hlt j hj x h₂ h₁
        have := Mem.readW_writeW_sep (m := s.mem) (v := s.gpr t) hs (by decide)
        rw [addr_word, this]
        exact hrel.ext j b hj hjb
      · exact (Frame.refl [slotRegion c s] s.mem).writeW (List.mem_singleton_self _) (s.gpr t)
          (slot_contains _ hlt hok.slots)
    all_goals cases h
  | _ => simp [step] at h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) (h : eval D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' (fun r => (is.all fun i => !clobbers i r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.rd.trans p₁.rd, p.wr.trans p₁.wr, p.sp.trans p₁.sp, p.base.trans p₁.base,
      p.ext.trans p₁.ext, fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r fun h => hr.1 (by simp [clobbers_of_dstOf h]))
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

theorem add_ofNat_ofNat (b : BitVec 32) (x y : Nat) :
    b + BitVec.ofNat 32 x + BitVec.ofNat 32 y = b + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- An access at an offset of a region that does not wrap around. -/
theorem contains_off {b : BitVec 32} {len off n : Nat} (hfit : b.toNat + len ≤ 2 ^ 32)
    (h : off + n ≤ len) (hn : 0 < n) :
    (⟨State.addr b, len⟩ : Region).Contains (State.addr (b + BitVec.ofNat 32 off)) n := by
  rw [addr_add (by omega_using [hfit, h, hn])]
  simp only [Region.Contains]
  rw [show State.addr b + BitVec.ofNat 64 off - State.addr b = BitVec.ofNat 64 off by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hfit, h])]
  exact h

theorem in_off {rs : List Region} {b : BitVec 32} {len off n : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ rs) (hfit : b.toNat + len ≤ 2 ^ 32)
    (h : off + n ≤ len) (hn : 0 < n) : InRegions rs (State.addr (b + BitVec.ofNat 32 off)) n :=
  ⟨_, hr, contains_off hfit h hn⟩

/-- `Ok` for slots at offset `off` of a writable region, and no external words. -/
theorem Ok.of_off {c : Cfg} {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (hb : s.gpr c.base = b + BitVec.ofNat 32 off) (hlen : off + 4 * c.slots ≤ len)
    (he : c.exts = 0) : Ok c s where
  slotIn k hk := by
    rw [hb, wordAddr, add_ofNat_ofNat]; exact in_off hr hfit (by omega_using [hlen, hk]) (by omega_using [])
  extIn k hk := by omega
  slots := by
    rcases Nat.eq_zero_or_pos c.slots with h0 | h0
    · rw [h0]; have := (s.gpr c.base).isLt; omega_using []
    · rw [hb, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega_using [hfit, hlen, h0]),
        Nat.mod_eq_of_lt (by omega_using [hfit, hlen, h0])]; omega_using [hfit, hlen]
  sep k _ j hj := by omega

/-- `Ok` for external words at offset `off` of a readable region, and no slots. -/
theorem Ok.of_ext {c : Cfg} {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.rd ++ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (he : s.gpr c.ext = b + BitVec.ofNat 32 off) (hlen : off + 4 * c.exts ≤ len)
    (hs : c.slots = 0) : Ok c s where
  slotIn k hk := by omega
  extIn k hk := by
    rw [he, wordAddr, add_ofNat_ofNat]; exact in_off hr hfit (by omega_using [hlen, hk]) (by omega_using [])
  slots := by rw [hs]; have := (s.gpr c.base).isLt; omega_using []
  sep k hk := by omega

end VG.Arm.Straight
