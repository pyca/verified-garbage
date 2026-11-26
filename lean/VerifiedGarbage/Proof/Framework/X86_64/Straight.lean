module

import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Bitslice.Dom
public import VerifiedGarbage.Proof.Framework.Bitslice.Machine
import VerifiedGarbage.Proof.Framework.InlineMatch
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# x86-64: straight-line bitwise code, by evaluation

A block of 64-bit `mov`, `xor`, `and`, `or`, `ror`, `shr` and `movabs`
instructions on registers and on two memory areas (read-write *slots*
`[base + 8k]`, `k < slots`, and read-only *external words*
`[ext + 8k]`, `k < exts`) is evaluated over an abstract domain
(`VG.Bitslice.Dom`) by `eval`. `run` says that the machine then runs the
block without faulting, and that its registers and memory words are related
to the abstract result as they were to the abstract initial values. The
concrete block is never symbolically executed: a `decide` on `eval` over a
domain whose values the kernel evaluates quickly (bit masks, truth tables)
proves what it computes.

The evaluator rejects (`none`) any other instruction, any other memory
operand, any write of the two base registers and any use of an unknown
value.
-/

@[expose] public section

namespace VG.X86_64.Straight

open VG.Bitslice

/-- The two memory areas: slots `[base + 8k]` for `k < slots` (read and
written), and external words `[ext + 8k]` for `k < exts` (only read). -/
structure Cfg where
  base : Reg
  slots : Nat
  ext : Reg
  exts : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the registers and slots; `none` if unknown. -/
structure Env (α : Type) where
  reg : Reg → Option α
  slot : Nat → Option α

variable {α : Type}

def Env.setReg (e : Env α) (d : Reg) (v : α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

/-- Where a memory operand points. -/
inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

/-- The slot or external word that a memory operand addresses, if any. -/
def Cfg.loc (c : Cfg) (m : MemOp) : Option Where :=
  if m.index = none ∧ 0 ≤ m.disp ∧ m.disp % 8 = 0 then
    if m.base = c.base ∧ m.disp.toNat / 8 < c.slots then some (.slot (m.disp.toNat / 8))
    else if m.base = c.ext ∧ m.disp.toNat / 8 < c.exts then some (.ext (m.disp.toNat / 8))
    else none
  else none

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

def absSrc (e : Env α) : Src → Option α
  | .reg r => e.reg r
  | .imm v => D.const (v.signExtend 64)
  | .mem m => match c.loc m with
    | some (.slot k) => e.slot k
    | some (.ext k) => ext k
    | none => none

def binop : AluOp → Option (α → α → Option α)
  | .xor => some D.xor
  | .and => some D.and
  | .or => some D.or
  | _ => none

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .mov d src => if d = c.base ∨ d = c.ext then none else (absSrc D c ext e src).map (e.setReg d)
  | .store m r => match c.loc m with
    | some (.slot k) => (e.reg r).map (e.setSlot k)
    | _ => none
  | .alu op d src =>
    if d = c.base ∨ d = c.ext then none else
    match binop D op, e.reg d, absSrc D c ext e src with
    | some f, some a, some b => (f a b).map (e.setReg d)
    | _, _, _ => none
  | .shift op d n =>
    if d = c.base ∨ d = c.ext ∨ ¬(1 ≤ n ∧ n ≤ 63) then none else
    match e.reg d with
    | some a => (match op with | .ror => D.ror n a | .shr => D.shr n a | .shl => none).map (e.setReg d)
    | none => none
  | .movImm64 d v => if d = c.base ∨ d = c.ext then none else (D.const v).map (e.setReg d)
  | _ => none

/-- The block's effect on the abstract values. -/
def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c ext e i).bind (eval is)

end

/-! ## The evaluator the kernel runs (`Framework/Bitslice/Machine.lean`) -/

namespace Kernel

open VG.Bitslice.Machine (Op Idx bind bind2)

instance : Idx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

/-- An instruction that `step` evaluates. -/
inductive Shape where
  | bad
  | mov (d : Reg) (src : Src)
  | store (m : MemOp) (r : Reg)
  | alu (op : AluOp) (d : Reg) (src : Src)
  | shift (op : ShiftOp) (d : Reg) (n : Nat)
  | movImm64 (d : Reg) (v : BitVec 64)

def shapeFn : Instr → Shape
  | .mov d src => .mov d src
  | .store m r => .store m r
  | .alu op d src => .alu op d src
  | .shift op d n => .shift op d n
  | .movImm64 d v => .movImm64 d v
  | _ => .bad

/-- `shapeFn`, with its cases closed (`inline_match%`). -/
def shape : Instr → Shape := inline_match% shapeFn

theorem shape_eq (i : Instr) : shape i = shapeFn i := by cases i <;> rfl

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

/-- `Cfg.loc`. -/
noncomputable def locK (m : MemOp) (slot ext : Nat → Op Reg α α) : Op Reg α α :=
  Option.rec
    (Int.rec
      (fun d => .eq (Nat.mod d 8) 0 (.area m.base c.base c.slots c.ext c.exts (Nat.div d 8) slot ext))
      (fun _ => .bad) m.disp)
    (fun _ => .bad) m.index

noncomputable def binopK (op : AluOp) : Option (α → α → Option α) :=
  AluOp.rec none none none none (some D.and) (some D.or) (some D.xor) none none op

noncomputable def shiftK (op : ShiftOp) (n : Nat) : α → Option α :=
  ShiftOp.rec (D.ror n) (D.shr n) (fun _ => none) op

/-- `d := f src`. -/
noncomputable def movK (d : Reg) (src : Src) : Op Reg α α :=
  Src.rec (fun r => .r1 some d r) (fun v => .r0 (D.const (v.signExtend 64)) d)
    (fun m => locK c m (.ld some d) fun k => .r0 (ext k) d) src

/-- `d := f d src`. -/
noncomputable def aluK (f : α → α → Option α) (d : Reg) (src : Src) : Op Reg α α :=
  Src.rec (fun r => .r2 f d d r) (fun v => .r1 (fun a => bind (f a) (D.const (v.signExtend 64))) d d)
    (fun m => locK c m (.rs f d d) fun k => .r1 (fun a => bind (f a) (ext k)) d d) src

noncomputable def op (i : Instr) : Op Reg α α :=
  Shape.rec (motive := fun _ => Op Reg α α) .bad
    (fun d src => .dst c.base c.ext d (movK D c ext d src))
    (fun m r => locK c m (fun k => .st some k r) fun _ => .bad)
    (fun op d src => .dst c.base c.ext d (Option.rec .bad (fun f => aluK D c ext f d src) (binopK D op)))
    (fun op d n => .dst c.base c.ext d (.lt 0 n (.lt n 64 (.r1 (shiftK D op n) d d))))
    (fun d v => .dst c.base c.ext d (.r0 (D.const v) d))
    (shape i)

/-- The abstract state, as the kernel's evaluator has it. -/
def toM (e : Env α) : Machine.Env Reg α α := ⟨e.reg, e.slot⟩

def ofM (e : Machine.Env Reg α α) : Env α := ⟨e.reg, e.slot⟩

theorem toM_setReg (e : Env α) (d : Reg) (a : α) : (toM e).setReg d a = toM (e.setReg d a) := by
  refine congrArg (fun f => (⟨f, _⟩ : Machine.Env Reg α α)) (funext fun r => ?_)
  show (if Idx.ix r = Idx.ix d then _ else _) = _
  by_cases h : r = d
  · subst h; simp only [Env.setReg, ite_true]
  · rw [ite_eq_right fun e => h (Idx.ix_inj e)]; simp only [toM, Env.setReg, ite_eq_right h]

theorem toM_map (e : Env α) (d : Reg) (a : Option α) :
    a.map ((toM e).setReg d) = (a.map (e.setReg d)).map toM := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (toM_setReg e d a)

theorem locK_eq (m : MemOp) (slot ext : Nat → Op Reg α α) :
    locK c m slot ext = match c.loc m with
      | some (.slot k) => slot k
      | some (.ext k) => ext k
      | none => .bad := by
  obtain ⟨b, i, sc, d⟩ := m
  cases i with
  | some i => rw [Cfg.loc, ite_eq_right (fun h => by cases h.1)]; rfl
  | none =>
    cases d with
    | negSucc d => rw [Cfg.loc, ite_eq_right (fun h => absurd h.2.1 (by simp))]; rfl
    | ofNat d =>
      have e : ((Int.ofNat d) % 8 = 0) = (d % 8 = 0) := by
        rw [show Int.ofNat d % 8 = ((d % 8 : Nat) : Int) from rfl]; exact propext Int.natCast_eq_zero
      have hl : c.loc ⟨b, none, sc, Int.ofNat d⟩ = if d % 8 = 0 then
          if b = c.base ∧ d / 8 < c.slots then some (.slot (d / 8))
          else if b = c.ext ∧ d / 8 < c.exts then some (.ext (d / 8)) else none
          else none :=
        ite_congr (propext ⟨fun h => e.mp h.2.2, fun h => ⟨rfl, Int.natCast_nonneg d, e.mpr h⟩⟩)
          (fun _ => rfl) fun _ => rfl
      show Op.eq (d % 8) 0 (.area b c.base c.slots c.ext c.exts (d / 8) slot ext) = _
      rw [hl, Op.eq_eq, Op.area_eq]
      by_cases h1 : d % 8 = 0
      · rw [ite_eq_left h1, ite_eq_left h1]
        by_cases hb : b = c.base ∧ d / 8 < c.slots
        · rw [ite_eq_left hb, ite_eq_left hb]
        · rw [ite_eq_right hb, ite_eq_right hb]
          by_cases he : b = c.ext ∧ d / 8 < c.exts
          · rw [ite_eq_left he, ite_eq_left he]
          · rw [ite_eq_right he, ite_eq_right he]
      · rw [ite_eq_right h1, ite_eq_right h1]

variable {D c ext}

theorem movK_step {e : Env α} {d : Reg} {src : Src} {m : Machine.Env Reg α α}
    (h : Machine.step (toM e) (movK D c ext d src) = some m) :
    ((absSrc D c ext e src).map (e.setReg d)).map toM = some m := by
  rw [← toM_map]
  cases src with
  | reg r => rw [← h]; exact congrArg _ (Option.bind_fun_some (e.reg r)).symm
  | imm v => exact h
  | mem mo =>
    change Machine.step (toM e) (locK c mo _ _) = _ at h
    rw [locK_eq] at h
    simp only [absSrc]
    cases hl : c.loc mo with
    | none => rw [hl] at h; cases h
    | some w =>
      rw [hl] at h
      cases w with
      | slot k => rw [← h]; exact congrArg _ (Option.bind_fun_some (e.slot k)).symm
      | ext k => exact h

theorem aluK_step {e : Env α} {f : α → α → Option α} {d : Reg} {src : Src} {m : Machine.Env Reg α α}
    (h : Machine.step (toM e) (aluK D c ext f d src) = some m) :
    (((e.reg d).bind fun a => (absSrc D c ext e src).bind (f a)).map (e.setReg d)).map toM = some m := by
  rw [← toM_map]
  cases src with
  | reg r => exact h
  | imm v =>
    rw [← h]
    exact congrArg (Option.map _) (congrArg _ (funext fun a => (Machine.bind_eq ..).symm))
  | mem mo =>
    change Machine.step (toM e) (locK c mo _ _) = _ at h
    rw [locK_eq] at h
    simp only [absSrc]
    cases hl : c.loc mo with
    | none => rw [hl] at h; cases h
    | some w =>
      rw [hl] at h
      cases w with
      | slot k => exact h
      | ext k =>
        rw [← h]
        exact congrArg (Option.map _) (congrArg _ (funext fun a => (Machine.bind_eq ..).symm))

/-- What the kernel's evaluator computes, `step` does. -/
theorem step_of_op {e : Env α} {i : Instr} {m : Machine.Env Reg α α}
    (h : Machine.step (toM e) (op D c ext i) = some m) : (step D c ext e i).map toM = some m := by
  rw [op, shape_eq] at h
  cases i with
  | mov d src =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right hd]; exact movK_step h
  | store mo r =>
    simp only [step]
    change Machine.step (toM e) (locK c mo _ _) = _ at h
    rw [locK_eq] at h
    cases hl : c.loc mo with
    | none => rw [hl] at h; cases h
    | some w =>
      rw [hl] at h
      cases w with
      | slot k =>
        change ((e.reg r).bind some).map _ = _ at h
        show ((e.reg r).map _).map toM = _
        rw [← h]; cases e.reg r <;> rfl
      | ext k => cases h
  | alu op d src =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right hd]
    have e1 : binopK D op = binop D op := by cases op <;> rfl
    cases hf : binop D op with
    | none => rw [e1, hf] at h; cases h
    | some f =>
      rw [e1, hf] at h
      rw [← aluK_step h]
      cases e.reg d <;> cases absSrc D c ext e src <;> rfl
  | shift op d n =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨h0, h⟩ := Machine.step_lt h
    obtain ⟨hn, h⟩ := Machine.step_lt h
    simp only [step]; rw [ite_eq_right (Machine.not_dst hd ⟨h0, Nat.le_of_lt_succ hn⟩)]
    change ((e.reg d).bind _).map _ = _ at h
    cases hr : e.reg d with
    | none => rw [hr] at h; cases h
    | some a =>
      rw [hr] at h; rw [← h]
      show _ = (shiftK D op n a).map _
      rw [toM_map]; cases op <;> rfl
  | movImm64 d v =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right hd, ← toM_map]; exact h
  | _ => cases h

/-- What the kernel's evaluator computes, `eval` does. -/
theorem eval_of_op {is : List Instr} {e : Env α} {m : Machine.Env Reg α α}
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
  Machine.run (Kernel.toM e) 4 (Nat.log2 c.slots + 1) (Kernel.op D c ext) (fun e => post (Kernel.ofM e)) is

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c ext is e post = true) : ∃ e', eval D c ext is e = some e' ∧ post e' = true := by
  obtain ⟨m, hm, hp⟩ := Machine.run_sound h
  obtain ⟨e', he, rfl⟩ := Kernel.eval_of_op hm
  exact ⟨e', he, hp⟩

theorem check_mono {is : List Instr} {e : Env α} {p q : Env α → Bool}
    (hpq : ∀ e, p e = true → q e = true) (h : check D c ext is e p = true) :
    check D c ext is e q = true := Machine.run_mono (fun _ => hpq _) h

end

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` (or external word `k`) of the base address `b`. -/
abbrev wordAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (8 * k)

/-- The machine state's registers, slots and external words are related by
`R` to the abstract ones that are known. -/
structure Rel (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e : Env α)
    (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.gpr r)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    R a (s.mem.readW (wordAddr (s.gpr c.base) k) 64)
  ext : ∀ k a, k < c.exts → ext k = some a → R a (s.mem.readW (wordAddr (s.gpr c.ext) k) 64)

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

theorem loc_some_slot {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some (.slot k)) :
    m.base = c.base ∧ m.index = none ∧ m.disp = ((8 * k : Nat) : Int) ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      refine ⟨h2.1, h1.1, ?_, h2.2⟩
      obtain ⟨-, h3, h4⟩ := h1
      omega_using [h3, h4]
    · split at h <;> cases h
  · cases h

theorem loc_some_ext {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some (.ext k)) :
    m.base = c.ext ∧ m.index = none ∧ m.disp = ((8 * k : Nat) : Int) ∧ k < c.exts := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        refine ⟨h2.1, h1.1, ?_, h2.2⟩
        obtain ⟨-, h3, h4⟩ := h1
        omega_using [h3, h4]
      · cases h
  · cases h

theorem ea_of {s : State} {m : MemOp} {b : Reg} {k : Nat} (hb : m.base = b) (hi : m.index = none)
    (hd : m.disp = ((8 * k : Nat) : Int)) : s.ea m = wordAddr (s.gpr b) k := by
  simp only [State.ea, hi, hb, hd, wordAddr]
  congr 1

section
variable {D : Dom α 64} {R : α → BitVec 64 → Prop} {c : Cfg} {ext : Nat → Option α}

theorem absSrc_ok (hD : D.Sound R) {e : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {src : Src} {a : α} (h : absSrc D c ext e src = some a) :
    ∃ v, readSrc s src = some v ∧ R a v := by
  cases src with
  | reg r => exact ⟨_, rfl, hrel.reg r a h⟩
  | imm v => exact ⟨_, rfl, hD.const h⟩
  | mem m =>
    simp only [absSrc] at h
    split at h
    · rename_i k hk
      obtain ⟨hb, hi, hd, hlt⟩ := loc_some_slot hk
      have hea := ea_of (s := s) hb hi hd
      refine ⟨_, ?_, hrel.slot k a hlt h⟩
      obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.base) k) 8 :=
        ⟨r, List.mem_append_right _ hr, hc⟩
      simp [readSrc, State.load64, hea, hin]
    · rename_i k hk
      obtain ⟨hb, hi, hd, hlt⟩ := loc_some_ext hk
      have hea := ea_of (s := s) hb hi hd
      refine ⟨_, ?_, hrel.ext k a hlt h⟩
      simp [readSrc, State.load64, hea, hok.extIn k hlt]
    · cases h

/-- The facts about one step, and so about a block. -/
structure Post (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e' : Env α)
    (s s' : State) (writes : Reg → Prop) : Prop where
  rel : Rel R c ext e' s'
  ok : Ok c s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  base : s'.gpr c.base = s.gpr c.base
  ext : s'.gpr c.ext = s.gpr c.ext
  other : ∀ r, ¬ writes r → s'.gpr r = s.gpr r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : Reg → Prop}
    (p : Post R c ext e' s s' W) (h : ∀ r, W r → W' r) : Post R c ext e' s s' W' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw) }

theorem rel_setReg {e : Env α} {s : State} (hrel : Rel R c ext e s) {d : Reg} {a : α}
    {v : BitVec 64} (hv : R a v) (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Rel R c ext (e.setReg d a) (s.setReg d v) where
  reg r b h := by
    simp only [Env.setReg, State.setReg] at h ⊢
    split at h
    · cases h; simp_all
    · simp_all [hrel.reg r b h]
  slot k b hk h := by
    have := hrel.slot k b hk h
    simpa [State.setReg, Ne.symm hb] using this
  ext k b hk h := by
    have := hrel.ext k b hk h
    simpa [State.setReg, Ne.symm he] using this

theorem post_setReg {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg}
    {a : α} {v : BitVec 64} (hv : R a v) (hb : d ≠ c.base) (he : d ≠ c.ext) (s₁ : State)
    (hs₁ : s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) :
    Post R c ext (e.setReg d a) s (s₁.setReg d v) (· = d) := by
  obtain ⟨hg, hm, hrd, hwr⟩ := hs₁
  have hrel' : Rel R c ext e s₁ :=
    ⟨fun r a h => hg ▸ hrel.reg r a h, fun k a hk h => hg ▸ hm ▸ hrel.slot k a hk h,
      fun k a hk h => hg ▸ hm ▸ hrel.ext k a hk h⟩
  have hbase : (s₁.setReg d v).gpr c.base = s.gpr c.base := by
    simp [State.setReg, Ne.symm hb, hg]
  have hext : (s₁.setReg d v).gpr c.ext = s.gpr c.ext := by
    simp [State.setReg, Ne.symm he, hg]
  refine ⟨rel_setReg hrel' hv hb he, hok.congr hbase hext hrd hwr, hrd, hwr, hbase, hext,
    fun r hr => ?_, ?_⟩
  · simp [State.setReg, hr, hg]
  · simp only [State.setReg]; rw [hm]; exact Frame.refl _ _

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => i.dst = some r) := by
  cases i with
  | mov d src =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or] at hd
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨v, hv, hR⟩ := absSrc_ok hD hok hrel ha
      simp only [reduceExec, hv, Option.map_some, Option.some.injEq, exists_eq_left']
      exact (post_setReg hok hrel hR hd.1 hd.2 s ⟨rfl, rfl, rfl, rfl⟩).writes
        fun r h => by simp [reduceInstrDst, h]
  | store m r =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hi, hd, hlt⟩ := loc_some_slot hk
      have hea := ea_of (s := s) hb hi hd
      have hin := hok.slotIn k hlt
      simp only [reduceExec, State.store64, hea, hin, ite_true, Option.some.injEq, exists_eq_left']
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (wordAddr (s.gpr c.base) j) (64 / 8)
          (wordAddr (s.gpr c.base) k) (64 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega_using [hj, this]) (by have := hok.slots; omega_using [hlt, this]) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_⟩,
        hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          simpa [Mem.readW_writeW_self64] using hrel.reg r a ha
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
  | alu op d src =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or] at hd
      split at h
      · rename_i f a b hf ha hb
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨v, hv, hR⟩ := absSrc_ok hD hok hrel hb
        have hRa := hrel.reg d a ha
        cases op <;> simp only [binop, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
          simp only [reduceExec, execAlu, hv, Option.bind_some, Option.some.injEq, exists_eq_left']
        · exact Post.writes (post_setReg hok hrel (hD.and hRa hR hr) hd.1 hd.2
            (arithFlags s _ false false) ⟨rfl, rfl, rfl, rfl⟩) fun r h => by simp [reduceInstrDst, h]
        · exact Post.writes (post_setReg hok hrel (hD.or hRa hR hr) hd.1 hd.2
            (arithFlags s _ false false) ⟨rfl, rfl, rfl, rfl⟩) fun r h => by simp [reduceInstrDst, h]
        · exact Post.writes (post_setReg hok hrel (hD.xor hRa hR hr) hd.1 hd.2
            (arithFlags s _ false false) ⟨rfl, rfl, rfl, rfl⟩) fun r h => by simp [reduceInstrDst, h]
      · cases h
  | shift op d n =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or, Classical.not_not] at hd
      obtain ⟨hdb, hde, hn⟩ := hd
      split at h
      · rename_i a ha
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        have hRa := hrel.reg d a ha
        cases op <;> simp only [reduceExec, execShift, hn, and_self, ite_true, Option.some.injEq,
          exists_eq_left']
        · exact Post.writes (post_setReg hok hrel (hD.ror hRa hr) hdb hde
            (s.setFlags _ _ _ _) ⟨rfl, rfl, rfl, rfl⟩) fun r h => by simp [reduceInstrDst, h]
        · exact Post.writes (post_setReg hok hrel (hD.shr hRa hr) hdb hde
            (s.setFlags _ _ _ _) ⟨rfl, rfl, rfl, rfl⟩) fun r h => by simp [reduceInstrDst, h]
        · cases hr
      · cases h
  | movImm64 d v =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or] at hd
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [reduceExec, Option.some.injEq, exists_eq_left']
      exact (post_setReg hok hrel (hD.const ha) hd.1 hd.2 s ⟨rfl, rfl, rfl, rfl⟩).writes
        fun r h => by simp [reduceInstrDst, h]
  | _ => simp [step] at h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) (h : eval D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' (fun r => (is.all fun i => i.dst != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.rd.trans p₁.rd, p.wr.trans p₁.wr, p.base.trans p₁.base, p.ext.trans p₁.ext,
      fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

end VG.X86_64.Straight

namespace VG.X86_64.Straight

/-- `Ok` for slots at the start of a writable region `r` of `s.wr` and no
external words. -/
theorem Ok.of_region {c : Cfg} {s : State} {r : Region} (hr : r ∈ s.wr)
    (hb : r.base = s.gpr c.base) (hlen : 8 * c.slots ≤ r.len) (hn : 8 * c.slots < 2 ^ 64)
    (he : c.exts = 0) : Ok c s where
  slotIn k hk := ⟨r, hr, by
    have := slot_contains (s.gpr c.base) hk hn
    simp only [Region.Contains] at this ⊢
    rw [hb]; omega_using [hlen, this]⟩
  extIn k hk := by omega
  slots := hn
  sep k _ j hj := by omega

/-- The machine runs a block that the abstract evaluator accepts, and the
result is the same whatever the domain: facts about it can be gathered
from several domains and relations. -/
theorem run_unique {s s₁ s₂ : State} {is : List Instr} (h₁ : runBlock isa is s = some s₁)
    (h₂ : runBlock isa is s = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

end VG.X86_64.Straight

namespace VG.X86_64.Straight

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

/-- `Ok` for external words at offset `off` of a readable region, and no slots. -/
theorem Ok.of_ext {c : Cfg} {s : State} {r : Region} {off : Nat} (hr : r ∈ s.rd ++ s.wr)
    (hb : s.gpr c.ext = r.base + BitVec.ofNat 64 off) (hlen : off + 8 * c.exts ≤ r.len)
    (hn : r.len < 2 ^ 64) (hs : c.slots = 0) : Ok c s where
  slotIn k hk := by omega
  extIn k hk := ⟨r, hr, contains_word hb (by omega_using [hlen, hk]) (Nat.le_refl _) hn⟩
  slots := by omega_using [hs]
  sep k hk := by omega

end VG.X86_64.Straight
