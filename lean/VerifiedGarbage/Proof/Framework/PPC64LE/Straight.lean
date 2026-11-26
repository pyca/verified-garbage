module

import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Bitslice.Dom
public import VerifiedGarbage.Proof.Framework.Bitslice.Machine
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# PPC64LE: straight-line bitwise code, by evaluation

As on x86-64 (`Proof/Framework/X86_64/Straight.lean`): a block of `ld`,
`std`, `and`, `or`, `xor`, `rotrdi`, `srdi` and `mr` (`addi d, n, 0`)
instructions on 64-bit registers and on two memory areas (read-write
*slots* `8k(base)`, `k < slots`, and read-only *external words* `8k(ext)`,
`k < exts`) is evaluated over an abstract domain (`VG.Bitslice.Dom`) by
`eval`. `run` says that the machine then runs the block without faulting,
and that its registers and memory words are related to the abstract result
as they were to the abstract initial values. The concrete block is never
symbolically executed: a `decide` on `eval` over a domain whose values the
kernel evaluates quickly proves what it computes.

The evaluator rejects (`none`) any other instruction, any other memory
operand, any write of the two base registers and any use of an unknown
value.
-/

@[expose] public section

namespace VG.PPC64LE.Straight

open VG.Bitslice

/-- The two memory areas: slots `8k(base)` for `k < slots` (read and
written), and external words `8k(ext)` for `k < exts` (only read). The
base registers are not `r0`, which a displacement form reads as 0. -/
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

/-- The slot or external word that `off(b)` addresses, if any. -/
def Cfg.loc (c : Cfg) (b : Reg) (off : Nat) : Option Where :=
  if b ≠ .r0 ∧ off < 2 ^ 15 ∧ off % 8 = 0 then
    if b = c.base ∧ off / 8 < c.slots then some (.slot (off / 8))
    else if b = c.ext ∧ off / 8 < c.exts then some (.ext (off / 8))
    else none
  else none

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

def binop : LogicOp → α → α → Option α
  | .xor => D.xor
  | .and => D.and
  | .or => D.or

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .load .d d b off =>
    if d = c.base ∨ d = c.ext then none else
    match c.loc b off with
    | some (.slot k) => (e.slot k).map (e.setReg d)
    | some (.ext k) => (ext k).map (e.setReg d)
    | none => none
  | .store .d r b off => match c.loc b off with
    | some (.slot k) => (e.reg r).map (e.setSlot k)
    | _ => none
  | .logic op d n m =>
    if d = c.base ∨ d = c.ext then none else
    match e.reg n, e.reg m with
    | some a, some b => (binop D op a b).map (e.setReg d)
    | _, _ => none
  | .rotr .d d n sh =>
    if d = c.base ∨ d = c.ext ∨ ¬(1 ≤ sh ∧ sh ≤ 63) then none else
    match e.reg n with
    | some a => (D.ror sh a).map (e.setReg d)
    | none => none
  | .lsr .d d n sh =>
    if d = c.base ∨ d = c.ext ∨ ¬(1 ≤ sh ∧ sh ≤ 63) then none else
    match e.reg n with
    | some a => (D.shr sh a).map (e.setReg d)
    | none => none
  | .addi d n 0 =>
    if d = c.base ∨ d = c.ext ∨ n = .r0 then none else (e.reg n).map (e.setReg d)
  | _ => none

/-- The block's effect on the abstract values. -/
def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c ext e i).bind (eval is)

end

/-! ## The evaluator the kernel runs (`Framework/Bitslice/Machine.lean`) -/

namespace Kernel

open VG.Bitslice.Machine (Op Idx)

instance : Idx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

/-- An instruction that `step` evaluates. -/
inductive Shape where
  | bad
  | load (d b : Reg) (off : Nat)
  | store (r b : Reg) (off : Nat)
  | logic (op : LogicOp) (d n m : Reg)
  | rotr (d n : Reg) (sh : Nat)
  | lsr (d n : Reg) (sh : Nat)
  | addi (d n : Reg) (imm : Nat)

def shapeFn : Instr → Shape
  | .load .d d b off => .load d b off
  | .store .d r b off => .store r b off
  | .logic op d n m => .logic op d n m
  | .rotr .d d n sh => .rotr d n sh
  | .lsr .d d n sh => .lsr d n sh
  | .addi d n imm => .addi d n imm
  | _ => .bad

/-- `shapeFn`, with its cases closed (`inline_match%`). -/
def shape : Instr → Shape := inline_match% shapeFn

theorem shape_eq (i : Instr) : shape i = shapeFn i := by
  cases i <;> first | rfl | (rename Size => sz; cases sz <;> rfl)

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

/-- `Cfg.loc`. -/
noncomputable def locK (n : Reg) (off : Nat) (slot ext : Nat → Op Reg α α) : Op Reg α α :=
  .ne n .r0 (.lt off 32768 (.eq (Nat.mod off 8) 0
    (.area n c.base c.slots c.ext c.exts (Nat.div off 8) slot ext)))

noncomputable def binopK (op : LogicOp) : α → α → Option α := LogicOp.rec D.and D.or D.xor op

noncomputable def op (i : Instr) : Op Reg α α :=
  Shape.rec (motive := fun _ => Op Reg α α) .bad
    (fun d b off => .dst c.base c.ext d (locK c b off (.ld some d) fun k => .r0 (ext k) d))
    (fun r b off => locK c b off (fun k => .st some k r) fun _ => .bad)
    (fun op d n m => .dst c.base c.ext d (.r2 (binopK D op) d n m))
    (fun d n sh => .dst c.base c.ext d (.lt 0 sh (.lt sh 64 (.r1 (D.ror sh) d n))))
    (fun d n sh => .dst c.base c.ext d (.lt 0 sh (.lt sh 64 (.r1 (D.shr sh) d n))))
    (fun d n imm => .eq imm 0 (.dst c.base c.ext d (.ne n .r0 (.r1 some d n))))
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

theorem locK_eq (n : Reg) (off : Nat) (slot ext : Nat → Op Reg α α) :
    locK c n off slot ext = match c.loc n off with
      | some (.slot k) => slot k
      | some (.ext k) => ext k
      | none => .bad := by
  rw [locK, Op.ne_eq, Op.eq_eq, Op.lt_eq, Op.area_eq, Cfg.loc]
  show (if n = .r0 then .bad else if off < 32768 then if off % 8 = 0 then
    (if n = c.base ∧ off / 8 < c.slots then slot (off / 8)
    else if n = c.ext ∧ off / 8 < c.exts then ext (off / 8) else .bad) else .bad else .bad) = _
  by_cases h0 : n = .r0
  · rw [ite_eq_left h0, ite_eq_right fun h => h.1 h0]
  · rw [ite_eq_right h0]
    by_cases h2 : off < 32768
    · rw [ite_eq_left h2]
      by_cases h1 : off % 8 = 0
      · rw [ite_eq_left h1, ite_eq_left (show _ ∧ _ ∧ _ from ⟨h0, h2, h1⟩)]
        by_cases hb : n = c.base ∧ off / 8 < c.slots
        · rw [ite_eq_left hb, ite_eq_left hb]
        · rw [ite_eq_right hb, ite_eq_right hb]
          by_cases he : n = c.ext ∧ off / 8 < c.exts
          · rw [ite_eq_left he, ite_eq_left he]
          · rw [ite_eq_right he, ite_eq_right he]
      · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.2.2]
    · rw [ite_eq_right h2, ite_eq_right fun h => h2 h.2.1]

variable {D c ext}

/-- What the kernel's evaluator computes, `step` does. -/
theorem step_of_op {e : Env α} {i : Instr} {m : Machine.Env Reg α α}
    (h : Machine.step (toM e) (op D c ext i) = some m) : (step D c ext e i).map toM = some m := by
  rw [op, shape_eq] at h
  cases i with
  | load sz d b off =>
    cases sz
    · cases h
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right hd]
    rw [locK_eq] at h
    cases hl : c.loc b off with
    | none => rw [hl] at h; cases h
    | some w =>
      rw [hl] at h
      cases w with
      | slot k =>
        show ((e.slot k).map _).map toM = _
        rw [← toM_map, ← h]; exact congrArg _ (Option.bind_fun_some (e.slot k)).symm
      | ext k => show ((ext k).map _).map toM = _; rw [← toM_map]; exact h
  | store sz r b off =>
    cases sz
    · cases h
    simp only [step]
    change Machine.step (toM e) (locK c b off _ _) = _ at h
    rw [locK_eq] at h
    cases hl : c.loc b off with
    | none => rw [hl] at h; cases h
    | some w =>
      rw [hl] at h
      cases w with
      | slot k =>
        change ((e.reg r).bind some).map _ = _ at h
        show ((e.reg r).map _).map toM = _
        rw [← h]; cases e.reg r <;> rfl
      | ext k => cases h
  | logic op d n m =>
    obtain ⟨hd, h⟩ := Machine.step_dst h
    simp only [step]; rw [ite_eq_right hd]
    change ((e.reg n).bind fun x => (e.reg m).bind _).map _ = _ at h
    cases hn : e.reg n with
    | none => rw [hn] at h; cases h
    | some a =>
      cases hm : e.reg m with
      | none => rw [hn, hm] at h; cases h
      | some b =>
        rw [hn, hm] at h
        show ((binop D op a b).map _).map toM = _
        rw [← toM_map, ← h]; cases op <;> rfl
  | rotr sz d n sh =>
    cases sz
    · cases h
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨h0, h⟩ := Machine.step_lt h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]; rw [ite_eq_right (Machine.not_dst hd ⟨h0, Nat.le_of_lt_succ hs⟩)]
    change ((e.reg n).bind _).map _ = _ at h
    cases hr : e.reg n with
    | none => rw [hr] at h; cases h
    | some a => rw [hr] at h; show ((D.ror sh a).map _).map toM = _; rw [← toM_map]; exact h
  | lsr sz d n sh =>
    cases sz
    · cases h
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨h0, h⟩ := Machine.step_lt h
    obtain ⟨hs, h⟩ := Machine.step_lt h
    simp only [step]; rw [ite_eq_right (Machine.not_dst hd ⟨h0, Nat.le_of_lt_succ hs⟩)]
    change ((e.reg n).bind _).map _ = _ at h
    cases hr : e.reg n with
    | none => rw [hr] at h; cases h
    | some a => rw [hr] at h; show ((D.shr sh a).map _).map toM = _; rw [← toM_map]; exact h
  | addi d n imm =>
    obtain ⟨rfl, h⟩ := Machine.step_eq h
    obtain ⟨hd, h⟩ := Machine.step_dst h
    obtain ⟨h0, h⟩ := Machine.step_ne h
    simp only [step]; rw [ite_eq_right fun x => x.elim (fun x => hd (.inl x)) fun x => x.elim (fun x => hd (.inr x)) h0]
    rw [← toM_map, ← h]; exact congrArg _ (Option.bind_fun_some (e.reg n)).symm
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
  Machine.run (Kernel.toM e) 5 (Nat.log2 c.slots + 1) (Kernel.op D c ext) (fun e => post (Kernel.ofM e)) is

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

theorem loc_some_slot {c : Cfg} {b : Reg} {off k : Nat} (h : c.loc b off = some (.slot k)) :
    b = c.base ∧ b ≠ .r0 ∧ off = 8 * k ∧ off < 2 ^ 15 ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      exact ⟨h2.1, h1.1, by omega, h1.2.1, h2.2⟩
    · split at h <;> cases h
  · cases h

theorem loc_some_ext {c : Cfg} {b : Reg} {off k : Nat} (h : c.loc b off = some (.ext k)) :
    b = c.ext ∧ b ≠ .r0 ∧ off = 8 * k ∧ off < 2 ^ 15 ∧ k < c.exts := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        exact ⟨h2.1, h1.1, by omega, h1.2.1, h2.2⟩
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

theorem post_write {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg}
    {a : α} {v : BitVec 64} (hv : R a v) (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (e.setReg d a) s (s.write d v) (· = d) := by
  have hbase : (s.write d v).gpr c.base = s.gpr c.base := by
    simp [State.write, Ne.symm hb]
  have hext : (s.write d v).gpr c.ext = s.gpr c.ext := by
    simp [State.write, Ne.symm he]
  refine ⟨⟨fun r b h => ?_, fun k b hk h => ?_, fun k b hk h => ?_⟩,
    hok.congr hbase hext rfl rfl, rfl, rfl, rfl, rfl, hbase, hext, fun r hr => ?_, Frame.refl _ _⟩
  · simp only [Env.setReg, State.write] at h ⊢
    split at h
    · cases h; simp_all
    · simp_all [hrel.reg r b h]
  · rw [hbase]; exact hrel.slot k b hk h
  · rw [hext]; exact hrel.ext k b hk h
  · simp [State.write, hr]

/-- The `Instr.dst` of the instructions `eval` accepts. -/
def dst : Instr → Option Reg
  | .load _ d _ _ => some d
  | .logic _ d _ _ => some d
  | .rotr _ d _ _ => some d
  | .lsr _ d _ _ => some d
  | .addi d _ _ => some d
  | _ => none

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => dst i = some r) := by
  cases i with
  | load sz d b off =>
    cases sz
    · simp [step] at h
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or] at hd
      split at h
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hb, hb0, hoff, ho, hlt⟩ := loc_some_slot hk
        subst hb hoff
        obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
        have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.base) k) 8 :=
          ⟨r, List.mem_append_right _ hr, hc⟩
        refine ⟨_, exec_load_d hb0 ⟨ho, by omega_using []⟩ hin, ?_⟩
        exact (post_write hok hrel (hrel.slot k a hlt ha) hd.1 hd.2).writes fun r h => by simp [dst, h]
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hb, hb0, hoff, ho, hlt⟩ := loc_some_ext hk
        subst hb hoff
        refine ⟨_, exec_load_d hb0 ⟨ho, by omega_using []⟩ (hok.extIn k hlt), ?_⟩
        exact (post_write hok hrel (hrel.ext k a hlt ha) hd.1 hd.2).writes fun r h => by simp [dst, h]
      · cases h
  | store sz r b off =>
    cases sz
    · simp [step] at h
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hb0, hoff, ho, hlt⟩ := loc_some_slot hk
      subst hb hoff
      have hin := hok.slotIn k hlt
      refine ⟨_, exec_store_d hb0 ⟨ho, by omega_using []⟩ hin, ?_⟩
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (wordAddr (s.gpr c.base) j) (64 / 8)
          (wordAddr (s.gpr c.base) k) (64 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega_using [hj, this]) (by have := hok.slots; omega_using [ho]) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_⟩,
        hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
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
  | logic op d n m =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or] at hd
      split at h
      · rename_i a b ha hb
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        have hRa := hrel.reg n a ha
        have hRb := hrel.reg m b hb
        refine ⟨_, exec_logic, ?_⟩
        cases op <;> simp only [binop] at hr
        · exact (post_write hok hrel (hD.and hRa hRb hr) hd.1 hd.2).writes fun r h => by simp [dst, h]
        · exact (post_write hok hrel (hD.or hRa hRb hr) hd.1 hd.2).writes fun r h => by simp [dst, h]
        · exact (post_write hok hrel (hD.xor hRa hRb hr) hd.1 hd.2).writes fun r h => by simp [dst, h]
      · cases h
  | rotr sz d n sh =>
    cases sz
    · simp [step] at h
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or, Classical.not_not] at hd
      obtain ⟨hdb, hde, hn⟩ := hd
      split at h
      · rename_i a ha
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_rotr_d (by omega_using [hn]), ?_⟩
        exact (post_write hok hrel (hD.ror (hrel.reg n a ha) hr) hdb hde).writes
          fun r h => by simp [dst, h]
      · cases h
  | lsr sz d n sh =>
    cases sz
    · simp [step] at h
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or, Classical.not_not] at hd
      obtain ⟨hdb, hde, hn⟩ := hd
      split at h
      · rename_i a ha
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_lsr_d (by omega_using [hn]), ?_⟩
        exact (post_write hok hrel (hD.shr (hrel.reg n a ha) hr) hdb hde).writes
          fun r h => by simp [dst, h]
      · cases h
  | addi d n imm =>
    cases imm with
    | succ _ => simp [step] at h
    | zero =>
      simp only [step] at h
      split at h
      · cases h
      · rename_i hd
        simp only [not_or] at hd
        obtain ⟨hdb, hde, hn⟩ := hd
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_addi hn (by decide), ?_⟩
        rw [BitVec.add_zero]
        exact (post_write hok hrel (hrel.reg n a ha) hdb hde).writes fun r h => by simp [dst, h]
  | _ => simp [step] at h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) (h : eval D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' (fun r => (is.all fun i => dst i != some r) = false) := by
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

end VG.PPC64LE.Straight
