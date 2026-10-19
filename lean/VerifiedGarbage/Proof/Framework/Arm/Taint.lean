module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import Batteries.Logic
public import VerifiedGarbage.TCB.Arm.Isa
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Taint tracking for ARMv7

The abstract state is the list of registers known to be public, whether the
flags are public, and what is known about memory. Memory is secret unless
known otherwise: an address must be computed from public registers, and a
value loaded from memory is secret unless it comes from a *public slot* or
from the stack arguments.

As on x86-64 (`VG.X86_64.Taint`), public slots let public values survive a
round trip through memory, e.g. registers saved and restored by inlined
code. They are byte ranges of the writable regions `s.wr` (identified by
index) that hold the same bytes in both runs. To keep them sound in the
presence of stores of secrets, the analysis knows lower bounds on the lengths
of the writable regions (`lens`, whose regions are then pairwise disjoint, the
same in both runs, and within the 32-bit address space; a bound of `0` means
the length is unknown, e.g. of a buffer of variable length, and the region has
no slots) and which registers hold the base address of which region
(`bases`). A store through such a register, within the bound, can only change
bytes of its own region at the store's offset; any other store of a secret
forgets every slot.

The analysis `taint` checks (`stepKM`) keeps the slots as runs of public
bytes: a public store merges into the runs it touches (`mergeSlot`), a store
of a secret cuts the bytes it writes out of the runs (`cutSlots`), the meet
of two taints keeps the bytes in runs of both (`interSlots`), and one taint is
below another if each of its runs is within one of the other's (`leC`). This
keeps the slot lists short: code that stores many public words next to each
other (a key schedule, a stack frame) has one run, not a slot per word, which
the kernel would compare and search at every later step. It is sound because
each step is the slot-per-store `step` from a taint with the same public
bytes (`stepKM_spec`).

The first `args` bytes at `sp` (the stack arguments) are public, the same
address in both runs, and outside every writable region, so no store changes
them; `argBases` records which of those words are the base address of a
writable region.
-/

@[expose] public section

namespace VG.Arm.Taint

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

structure T where
  regs : RegSet Reg
  flags : Bool
  /-- Lower bounds on the lengths of the writable regions `s.wr`, in order
  (`0` if unknown); `[]` if nothing is known about the regions. -/
  lens : List Nat := []
  /-- `(r, i)`: register `r` holds the base address of writable region `i`. -/
  bases : List (Reg × Nat) := []
  /-- `(i, o, n)`: the `n` bytes at offset `o` of writable region `i` are public. -/
  slots : List (Nat × Nat × Nat) := []
  /-- The first `args` bytes at `sp` are public and never written. -/
  argLen : Nat := 0
  /-- `(o, i)`: the stack word at `sp + o` is the base address of writable region `i`. -/
  argBases : List (Nat × Nat) := []
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

/-- Writable region `i`. -/
def region (s : State) (i : Nat) : Region := s.wr.getD i ⟨0, 0⟩

/-- The address of byte `k` of writable region `i`. -/
def byteAddr (s : State) (i k : Nat) : Addr := (region s i).base + BitVec.ofNat 64 k

/-- The address of byte `k` of the stack arguments. -/
def argByte (s : State) (k : Nat) : Addr := State.addr s.sp + BitVec.ofNat 64 k

/-- The registers `regs` and, if `flags`, the flags are the same in both states. -/
def AgreeRF (regs : RegSet Reg) (flags : Bool) (s₁ s₂ : State) : Prop :=
  (∀ r ∈ regs, s₁.gpr r = s₂.gpr r) ∧
  (flags = true → s₁.n = s₂.n ∧ s₁.z = s₂.z ∧ s₁.c = s₂.c ∧ s₁.v = s₂.v)

/-- What `τ` says about each state on its own. -/
structure Wf (τ : T) (s : State) : Prop where
  lens : τ.lens ≠ [] →
    List.Forall₂ (fun r l => l ≤ r.len) s.wr τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32
  bases : ∀ p ∈ τ.bases, State.addr (s.gpr p.1) = (region s p.2).base
  args : 0 < τ.argLen →
    s.sp.toNat + τ.argLen ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, τ.argLen⟩ r
  argBases : ∀ p ∈ τ.argBases, p.1 + 4 ≤ τ.argLen ∧
    State.addr (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 p.1)) 32) = (region s p.2).base

/-- Every slot lies within its region. -/
def SlotsOk (τ : T) : Prop := ∀ sl ∈ τ.slots, sl.2.1 + sl.2.2 ≤ τ.lens.getD sl.1 0

def SlotsAgree (τ : T) (s₁ s₂ : State) : Prop :=
  ∀ sl ∈ τ.slots, ∀ k, sl.2.1 ≤ k → k < sl.2.1 + sl.2.2 →
    s₁.mem (byteAddr s₁ sl.1 k) = s₂.mem (byteAddr s₂ sl.1 k)

structure Agree (τ : T) (s₁ s₂ : State) : Prop where
  rf : AgreeRF τ.regs τ.flags s₁ s₂
  wr : τ.lens ≠ [] → s₁.wr = s₂.wr
  wf₁ : Wf τ s₁
  wf₂ : Wf τ s₂
  ok : SlotsOk τ
  slots : SlotsAgree τ s₁ s₂
  sp : 0 < τ.argLen → s₁.sp = s₂.sp
  argMem : ∀ k < τ.argLen, s₁.mem (argByte s₁ k) = s₂.mem (argByte s₂ k)

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

/-- The known region bases after writing `d`. -/
def kill (τ : T) (d : Reg) : List (Reg × Nat) := τ.bases.filter (·.1 != d)

def op2Pub (τ : T) : Op2 → Bool
  | .imm _ => true
  | .reg r | .shifted r _ _ => pub τ r

/-- The region and offset addressed by `[n, #off]`, if known. -/
def addrOf (τ : T) (n : Reg) (off : Nat) : Option (Nat × Nat) :=
  (τ.bases.find? (·.1 == n)).map fun p => (p.2, off)

/-- `w` bytes at `[n, #off]` are within a public slot. -/
def slotPub (τ : T) (n : Reg) (off w : Nat) : Bool :=
  match addrOf τ n off with
  | some (i, d) => τ.slots.any fun sl => sl.1 == i && sl.2.1 ≤ d && d + w ≤ sl.2.1 + sl.2.2
  | none => false

/-- The known region bases after `mov d, op2`. -/
def movBases (τ : T) (d : Reg) : Op2 → List (Reg × Nat)
  | .reg r => kill τ d ++ (τ.bases.filter (·.1 == r)).map fun p => (d, p.2)
  | _ => kill τ d

/-- The public slots after storing `w` bytes at `[n, #off]`, a public value iff `p`. -/
def storeSlots (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOf τ n off with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      let kept := τ.slots.filter fun sl => p || sl.1 != i || d + w ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ d
      if p then (i, d, w) :: kept else kept
    else if p then τ.slots else []
  | none => if p then τ.slots else []

/-- The known region bases after `ldr t, [sp, #off]`. -/
def spBases (τ : T) (t : Reg) (off : Nat) : List (Reg × Nat) :=
  kill τ t ++ (τ.argBases.filter fun p => p.1 == off).map fun p => (t, p.2)

def storeStep (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  if pub τ n then some { τ with slots := storeSlots τ n off w p } else none

def step (τ : T) : Instr → Option T
  | .mov d op2 => some { τ with regs := set τ d (op2Pub τ op2), bases := movBases τ d op2 }
  | .dp _ d n op2 => some { τ with regs := set τ d (pub τ n && op2Pub τ op2), bases := kill τ d }
  | .adds d n op2 | .subs d n op2 =>
    let p := pub τ n && op2Pub τ op2
    some { τ with regs := set τ d p, flags := p, bases := kill τ d }
  | .adc d n op2 =>
    some { τ with regs := set τ d (pub τ n && op2Pub τ op2 && τ.flags), bases := kill τ d }
  | .cmp n op2 => some { τ with flags := pub τ n && op2Pub τ op2 }
  | .movw d _ => some { τ with regs := set τ d true, bases := kill τ d }
  -- Nor does it track the addresses of statics.
  | .adrSym d _ => some { τ with regs := set τ d false, bases := kill τ d }
  | .addSp d _ => some { τ with regs := set τ d (decide (0 < τ.argLen)), bases := kill τ d }
  | .movt d _ => some { τ with regs := set τ d (pub τ d), bases := kill τ d }
  | .rev d m => some { τ with regs := set τ d (pub τ m), bases := kill τ d }
  | .mul d n m => some { τ with regs := set τ d (pub τ n && pub τ m), bases := kill τ d }
  | .mla d n m a => some { τ with regs := set τ d (pub τ n && pub τ m && pub τ a), bases := kill τ d }
  -- A long multiply, which writes two registers, is not analysed: code with
  -- one is proven constant time otherwise.
  | .umaal .. => none
  | .ldr t n off =>
    if pub τ n then some { τ with regs := set τ t (slotPub τ n off 4), bases := kill τ t } else none
  | .str t n off => storeStep τ n off 4 (pub τ t)
  | .ldrb t n _ => if pub τ n then some { τ with regs := set τ t false, bases := kill τ t } else none
  | .strb t n off => storeStep τ n off 1 (pub τ t)
  | .ldrSp t off =>
    if off + 4 ≤ τ.argLen then some { τ with regs := set τ t true, bases := spBases τ t off } else none
  -- Frames are not analysed.
  | .push _ | .pop .. | .alloc _ | .free _ => none

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []
  argLen := if τ₁.argLen = τ₂.argLen then τ₁.argLen else 0
  argBases := if τ₁.argLen = τ₂.argLen then τ₁.argBases.filter (τ₂.argBases.contains ·) else []

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.all (σ.slots.contains ·) && τ.argLen == σ.argLen &&
    τ.argBases.all (σ.argBases.contains ·)

/-! ## Soundness -/

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := Iff.rfl

section
variable {τ : T} {s₁ s₂ : State}

theorem Agree.reg (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) : s₁.gpr r = s₂.gpr r :=
  h.rf.1 r (pub_iff.mp hr)

theorem Agree.op2 (h : Agree τ s₁ s₂) {o : Op2} (ho : op2Pub τ o = true) : o.eval s₁ = o.eval s₂ := by
  cases o with
  | imm v => rfl
  | reg r => simp only [Op2.eval, h.reg ho]
  | shifted r sh n => simp only [Op2.eval, h.reg ho]

theorem op2_some (h : Agree τ s₁ s₂) {o : Op2} {y₁ y₂ : BitVec 32}
    (e₁ : o.eval s₁ = some y₁) (e₂ : o.eval s₂ = some y₂) : op2Pub τ o = true → y₁ = y₂ :=
  fun ho => by rw [h.op2 ho, e₂] at e₁; cases e₁; rfl

end

theorem regs_set {τ : T} {s₁ s₂ : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} {p : Bool} {v₁ v₂ : BitVec 32} (hv : p = true → v₁ = v₂) :
    ∀ r ∈ set τ d p, (s₁.setReg d v₁).gpr r = (s₂.setReg d v₂).gpr r := by
  intro r hr
  simp only [State.setReg]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, RegSet.mem_insert] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hr
    simp [hr.1, h r hr.2]

theorem setReg_ne {s : State} {d r : Reg} {v : BitVec 32} (h : r ≠ d) : (s.setReg d v).gpr r = s.gpr r := by
  simp [State.setReg, h]

/-! ### Keeping what is known about memory -/

theorem Wf.keep {τ τ' : T} {s s' : State} (hw : Wf τ s) (hl : τ'.lens = τ.lens)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases) (hwr : s'.wr = s.wr)
    (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hb : ∀ p ∈ τ'.bases, State.addr (s'.gpr p.1) = (region s' p.2).base) : Wf τ' s' where
  lens h := by rw [hwr, hl]; exact hw.lens (hl ▸ h)
  bases := hb
  args h := by rw [hwr, hsp, hargs]; exact hw.args (hargs ▸ h)
  argBases p h := by
    rw [hargs, hsp, hm]
    simp only [region, hwr]
    exact hw.argBases p (hab ▸ h)

theorem Agree.keep {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr) (hm₁ : s₁'.mem = s₁.mem) (hm₂ : s₂'.mem = s₂.mem)
    (hsp₁ : s₁'.sp = s₁.sp) (hsp₂ : s₂'.sp = s₂.sp)
    (hb₁ : ∀ p ∈ τ'.bases, State.addr (s₁'.gpr p.1) = (region s₁' p.2).base)
    (hb₂ : ∀ p ∈ τ'.bases, State.addr (s₂'.gpr p.1) = (region s₂' p.2).base) : Agree τ' s₁' s₂' where
  rf := hrf
  wr h := by rw [hw₁, hw₂]; exact ha.wr (hl ▸ h)
  wf₁ := ha.wf₁.keep hl hargs hab hw₁ hm₁ hsp₁ hb₁
  wf₂ := ha.wf₂.keep hl hargs hab hw₂ hm₂ hsp₂ hb₂
  ok sl h := by rw [hl]; exact ha.ok sl (hs ▸ h)
  slots sl h k h₁ h₂ := by
    simp only [byteAddr, region, hw₁, hw₂, hm₁, hm₂]
    exact ha.slots sl (hs ▸ h) k h₁ h₂
  sp h := by rw [hsp₁, hsp₂]; exact ha.sp (hargs ▸ h)
  argMem k hk := by
    simp only [argByte, hsp₁, hsp₂, hm₁, hm₂]
    exact ha.argMem k (hargs ▸ hk)

theorem kill_bases {τ : T} {s s' : State} (hw : Wf τ s) (hwr : s'.wr = s.wr) {d : Reg}
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) :
    ∀ p ∈ kill τ d, State.addr (s'.gpr p.1) = (region s' p.2).base := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [hg _ hp.2, hw.bases p hp.1]
  simp [region, hwr]

theorem kill_setReg {τ : T} {s : State} (hw : Wf τ s) (d : Reg) (v : BitVec 32) :
    ∀ p ∈ kill τ d, State.addr ((s.setReg d v).gpr p.1) = (region (s.setReg d v) p.2).base :=
  kill_bases (s' := s.setReg d v) hw rfl fun _ h => setReg_ne h

theorem movBases_ok {τ : T} {s : State} (hw : Wf τ s) {d : Reg} {o : Op2} {v : BitVec 32}
    (hv : o.eval s = some v) :
    ∀ p ∈ movBases τ d o, State.addr ((s.setReg d v).gpr p.1) = (region (s.setReg d v) p.2).base := by
  cases o with
  | reg r =>
    simp only [Op2.eval, Option.some.injEq] at hv
    subst hv
    intro p hp
    simp only [movBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
    rcases hp with hp | ⟨q, ⟨hq, rfl⟩, rfl⟩
    · exact kill_setReg hw d _ p hp
    · simp only [State.setReg, ite_true]
      exact hw.bases q hq
  | imm _ => exact kill_setReg hw d _
  | shifted _ _ _ => exact kill_setReg hw d _

/-! ### Region addresses -/

theorem addrOf_some {τ : T} {n : Reg} {off i d : Nat} (h : addrOf τ n off = some (i, d)) :
    (n, i) ∈ τ.bases ∧ off = d := by
  unfold addrOf at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨q, hq, rfl, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hq
  have hb := List.find?_some hq
  simp only [beq_iff_eq] at hb
  exact ⟨by rw [← hb]; exact hm, rfl⟩

theorem lens_ne {τ : T} {i n : Nat} (h : 0 < n) (hn : n ≤ τ.lens.getD i 0) : τ.lens ≠ [] := by
  rintro h'; simp [h'] at hn; omega

theorem forall₂_length {rs : List Region} {ls : List Nat}
    (h : List.Forall₂ (fun r l => l ≤ r.len) rs ls) : rs.length = ls.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem forall₂_getD {rs : List Region} {ls : List Nat}
    (h : List.Forall₂ (fun r l => l ≤ r.len) rs ls) (i : Nat) : ls.getD i 0 ≤ (rs.getD i ⟨0, 0⟩).len := by
  induction h generalizing i with
  | nil => simp
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih i

theorem region_len {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) (i : Nat) :
    τ.lens.getD i 0 ≤ (region s i).len :=
  forall₂_getD (hw.lens hne).1 i

theorem region_mem {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) {i : Nat}
    (hi : 0 < τ.lens.getD i 0) : ∃ h : i < s.wr.length, region s i = s.wr[i] := by
  have hl := forall₂_length (hw.lens hne).1
  have : i < τ.lens.length := by
    by_contra h'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi; simp at hi
  have hi' : i < s.wr.length := hl ▸ this
  exact ⟨hi', by simp [region, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']⟩

/-- Region `i` lies within the 32-bit address space. -/
theorem region_bound {τ : T} {s : State} (hw : Wf τ s) {i : Nat} (hi : 0 < τ.lens.getD i 0) :
    (region s i).base.toNat + τ.lens.getD i 0 ≤ 2 ^ 32 := by
  have hne := lens_ne hi (Nat.le_refl _)
  obtain ⟨hi', hr⟩ := region_mem hw hne hi
  have hl := region_len hw hne i
  have hb := (hw.lens hne).2.2 _ (List.getElem_mem hi')
  rw [← hr] at hb
  omega

theorem ea_of_addrOf {τ : T} {s : State} (hw : Wf τ s) {n : Reg} {off i d : Nat}
    (h : addrOf τ n off = some (i, d)) (hd : d < τ.lens.getD i 0) :
    State.addr (s.gpr n + BitVec.ofNat 32 off) = byteAddr s i d := by
  obtain ⟨hb, rfl⟩ := addrOf_some h
  have hbd := region_bound hw (i := i) (by omega)
  have e := hw.bases _ hb
  simp only at e
  have hn : (s.gpr n).toNat = (region s i).base.toNat := by
    rw [← e, State.addr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (s.gpr n).isLt; omega)]
  rw [addr_add (by omega), e]
  rfl

theorem byteAddr_add (s : State) (i d k : Nat) :
    byteAddr s i d + BitVec.ofNat 64 k = byteAddr s i (d + k) := by
  simp only [byteAddr, BitVec.ofNat_add]
  rw [BitVec.add_assoc]

/-- Slots live in regions of the same address in both runs. -/
theorem Agree.byteAddr_eq {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {sl : Nat × Nat × Nat}
    (h : sl ∈ τ.slots) {k : Nat} (hk : k < sl.2.1 + sl.2.2) :
    byteAddr s₁ sl.1 k = byteAddr s₂ sl.1 k := by
  have := ha.ok sl h
  simp only [byteAddr, region, ha.wr (lens_ne (n := sl.2.1 + sl.2.2) (by omega) this)]

/-- A load of a word from a public slot. -/
theorem Agree.readW {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {n : Reg} {off : Nat}
    (hp : slotPub τ n off 4 = true) :
    s₁.mem.readW (State.addr (s₁.gpr n + BitVec.ofNat 32 off)) 32 =
      s₂.mem.readW (State.addr (s₂.gpr n + BitVec.ofNat 32 off)) 32 := by
  unfold slotPub at hp
  split at hp <;> [skip; cases hp]
  rename_i i d h
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨sl, hsl, ⟨rfl, ho⟩, hd⟩ := hp
  have hok := ha.ok sl hsl
  rw [ea_of_addrOf ha.wf₁ h (by omega), ea_of_addrOf ha.wf₂ h (by omega),
    ha.byteAddr_eq hsl (k := d) (by omega)]
  refine Mem.readW_congr fun k hk => ?_
  rw [byteAddr_add]
  have := ha.slots sl hsl (d + k) (by omega) (by omega)
  rwa [ha.byteAddr_eq hsl (k := d + k) (by omega)] at this

/-! ### Stores -/

/-- A store of `n` bytes at offset `d` of region `i` does not change byte `k`
of region `j`, if that is another region or outside `[d, d + n)`. -/
theorem write_other {τ : T} {s : State} (hw : Wf τ s) {i d n j k : Nat} (hn : 0 < n)
    (hd : d + n ≤ τ.lens.getD i 0) (hk : k < τ.lens.getD j 0) (hsep : j ≠ i ∨ k < d ∨ d + n ≤ k)
    (V : BitVec (8 * n)) :
    s.mem.write (byteAddr s i d) n V (byteAddr s j k) = s.mem (byteAddr s j k) := by
  have hne := lens_ne (n := d + n) (by omega) hd
  obtain ⟨-, hdisj, -⟩ := hw.lens hne
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega)
  obtain ⟨hj, hrj⟩ := region_mem hw hne (i := j) (by omega)
  have hli := region_len hw hne i
  have hlj := region_len hw hne j
  have hbi := region_bound hw (i := i) (by omega)
  have hbj := region_bound hw (i := j) (by omega)
  apply Mem.write_apply
  intro hlt
  by_cases hji : j = i
  · subst hji
    have hsep := hsep.resolve_left (· rfl)
    have h : byteAddr s j k - byteAddr s j d = BitVec.ofNat 64 k - BitVec.ofNat 64 d :=
      Offset.add_sub_add_left _ _ _
    exact Offset.not_lt_sub_ofNat hsep (by omega) hn (by omega) (h ▸ hlt)
  · have hA : (region s i).Contains (byteAddr s i d) n := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hX : (region s j).Contains (byteAddr s j k) 1 := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hXi := hA.byte hlt
    rw [List.pairwise_iff_getElem] at hdisj
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · exact hdisj j i hj hi h _ (hrj ▸ hX) (hri ▸ hXi)
    · exact hdisj i j hi hj h _ (hri ▸ hXi) (hrj ▸ hX)

theorem write_same {m₁ m₂ : Mem} {A X : Addr} {n : Nat} (V : BitVec (8 * n)) (h : m₁ X = m₂ X) :
    m₁.write A n V X = m₂.write A n V X := by
  simp only [Mem.write]; split <;> [rfl; exact h]

theorem storeSlots_ok {τ : T} (hok : SlotsOk τ) (n : Reg) (off w : Nat) (p : Bool) :
    SlotsOk { τ with slots := storeSlots τ n off w p } := by
  intro sl hsl
  simp only [storeSlots] at hsl
  split at hsl
  · split at hsl
    · split at hsl
      · rcases List.mem_cons.mp hsl with rfl | hsl
        · assumption
        · exact hok sl (List.mem_filter.mp hsl).1
      · exact hok sl (List.mem_filter.mp hsl).1
    · split at hsl <;> [exact hok sl hsl; cases hsl]
  · split at hsl <;> [exact hok sl hsl; cases hsl]

/-- A write within a writable region leaves the stack arguments alone. -/
theorem write_arg {τ : T} {s : State} (hw : Wf τ s) {A : Addr} {n : Nat} (hA : InRegions s.wr A n)
    (V : BitVec (8 * n)) {k : Nat} (hk : k < τ.argLen) : s.mem.write A n V (argByte s k) = s.mem (argByte s k) := by
  obtain ⟨hsp, hd⟩ := hw.args (by omega)
  obtain ⟨r, hr, hc⟩ := hA
  apply Mem.write_apply
  intro hlt
  refine hd r hr _ ?_ (hc.byte hlt)
  simp only [Region.Contains, argByte]
  rw [Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The stack argument word at offset `o`, byte by byte. -/
theorem argWord {τ : T} {s : State} (hw : Wf τ s) {o : Nat} (ho : o + 4 ≤ τ.argLen) (k : Nat) :
    State.addr (s.sp + BitVec.ofNat 32 o) + BitVec.ofNat 64 k = argByte s (o + k) := by
  have := (hw.args (by omega)).1
  rw [addr_add (by omega), argByte, BitVec.ofNat_add, BitVec.add_assoc]

theorem Wf.store {τ : T} {s : State} (hw : Wf τ s) {A : Addr} {n : Nat} (hA : InRegions s.wr A n)
    (V : BitVec (8 * n)) (τ' : T) (hl : τ'.lens = τ.lens) (hb : τ'.bases = τ.bases)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases) :
    Wf τ' { s with mem := s.mem.write A n V } where
  lens h := hl ▸ hw.lens (hl ▸ h)
  bases p h := hw.bases p (hb ▸ h)
  args h := hargs ▸ hw.args (hargs ▸ h)
  argBases p h := by
    obtain ⟨hp, he⟩ := hw.argBases p (hab ▸ h)
    rw [hargs]
    refine ⟨hp, ?_⟩
    simp only [region] at he ⊢
    rw [← he]
    refine congrArg State.addr ?_
    refine Mem.readW_congr fun k hk => ?_
    rw [argWord hw hp]
    exact write_arg hw hA V (by omega)

/-- A store of `n` bytes at `[r, #off]`, of the same value in both runs if `p`. -/
theorem Agree.store {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {r : Reg} {off : Nat}
    (hr : pub τ r = true) {n : Nat} (hn : 0 < n) {V₁ V₂ : BitVec (8 * n)} {p : Bool}
    (hv : p = true → V₁ = V₂)
    (hA₁ : InRegions s₁.wr (State.addr (s₁.gpr r + BitVec.ofNat 32 off)) n)
    (hA₂ : InRegions s₂.wr (State.addr (s₂.gpr r + BitVec.ofNat 32 off)) n) :
    Agree { τ with slots := storeSlots τ r off n p }
      { s₁ with mem := s₁.mem.write (State.addr (s₁.gpr r + BitVec.ofNat 32 off)) n V₁ }
      { s₂ with mem := s₂.mem.write (State.addr (s₂.gpr r + BitVec.ofNat 32 off)) n V₂ } where
  rf := ha.rf
  wr := ha.wr
  wf₁ := ha.wf₁.store hA₁ V₁ _ rfl rfl rfl rfl
  wf₂ := ha.wf₂.store hA₂ V₂ _ rfl rfl rfl rfl
  ok := storeSlots_ok ha.ok r off n p
  sp := ha.sp
  argMem k hk := by
    simp only [argByte] at *
    rw [show State.addr s₁.sp + BitVec.ofNat 64 k = argByte s₁ k from rfl,
      show State.addr s₂.sp + BitVec.ofNat 64 k = argByte s₂ k from rfl,
      write_arg ha.wf₁ hA₁ V₁ hk, write_arg ha.wf₂ hA₂ V₂ hk]
    exact ha.argMem k hk
  slots := by
    intro sl hsl k hk₁ hk₂
    simp only [byteAddr]
    have hA : s₁.gpr r = s₂.gpr r := ha.reg hr
    have same : sl ∈ τ.slots → p = true →
        s₁.mem.write (State.addr (s₁.gpr r + BitVec.ofNat 32 off)) n V₁ (byteAddr s₁ sl.1 k) =
          s₂.mem.write (State.addr (s₂.gpr r + BitVec.ofNat 32 off)) n V₂ (byteAddr s₂ sl.1 k) :=
      fun h hp => by
        rw [hA, hv hp, ha.byteAddr_eq h hk₂]
        exact write_same _ (ha.byteAddr_eq h hk₂ ▸ ha.slots sl h k hk₁ hk₂)
    show s₁.mem.write _ n V₁ (byteAddr s₁ sl.1 k) = s₂.mem.write _ n V₂ (byteAddr s₂ sl.1 k)
    simp only [storeSlots] at hsl
    split at hsl
    · rename_i i d had
      split at hsl
      · rename_i hfit
        have e₁ := ea_of_addrOf ha.wf₁ had (by omega)
        have e₂ := ea_of_addrOf ha.wf₂ had (by omega)
        have hsl' : (p = true ∧ sl = (i, d, n)) ∨ (sl ∈ τ.slots ∧
            (p = true ∨ sl.1 ≠ i ∨ d + n ≤ sl.2.1 ∨ sl.2.1 + sl.2.2 ≤ d)) := by
          split at hsl
          · rename_i hp
            rcases List.mem_cons.mp hsl with h | h
            · exact .inl ⟨hp, h⟩
            · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, or_assoc] at h
              exact .inr h
          · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, or_assoc] at hsl
            exact .inr hsl
        rcases hsl' with ⟨hp, rfl⟩ | ⟨h, hsep⟩
        · simp only at hk₁ hk₂
          simp only [e₁, e₂, Mem.write, hv hp]
          have hd : ∀ s : State, byteAddr s i k - byteAddr s i d = BitVec.ofNat 64 (k - d) :=
            fun s => (Offset.add_sub_add_left _ _ _).trans (Offset.ofNat_sub_ofNat (by omega))
          have hlt : (BitVec.ofNat 64 (k - d)).toNat < n := by
            rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
          rw [hd, hd]; simp only [hlt, ite_true]
        · by_cases hp : p = true
          · exact same h hp
          have hsep : sl.1 ≠ i ∨ k < d ∨ d + n ≤ k := by
            rcases hsep with h' | h' | h' | h'
            · exact absurd h' hp
            · exact .inl h'
            · exact .inr (.inr (by omega))
            · exact .inr (.inl (by omega))
          have hk := ha.ok sl h
          rw [e₁, e₂, write_other ha.wf₁ hn hfit (by omega) hsep,
            write_other ha.wf₂ hn hfit (by omega) hsep]
          exact ha.slots sl h k hk₁ hk₂
      · split at hsl <;> [exact same hsl ‹_›; cases hsl]
    · split at hsl <;> [exact same hsl ‹_›; cases hsl]

/-! ### Instructions that write a register -/

/-- The register an instruction writes, if it writes one (`cmp` and stores
do not; a frame's pop writes its register). -/
def dst : Instr → Option Reg
  | .mov d _ | .dp _ d _ _ | .adds d _ _ | .adc d _ _ | .subs d _ _ | .movw d _ | .movt d _ | .rev d _
  | .addSp d _ | .mul d _ _ | .mla d _ _ _ | .ldr d _ _ | .ldrb d _ _ | .ldrSp d _ | .pop d _ | .adrSym d _ => some d
  | .cmp .. | .str .. | .strb .. | .push _ | .alloc _ | .free _ | .umaal .. => none

theorem exec_dst {i : Instr} {d : Reg} (hd : dst i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases i <;> simp only [dst, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;>
  simp only [exec, Option.map_eq_some_iff, State.load32, State.load8] at h <;>
  (repeat' split at h) <;>
  (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
  first
  | (subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩)
  | (obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => by simp [State.setReg, addFlags, subFlags, h]⟩)
  | (cases h)

theorem Agree.write {τ τ' : T} {i : Instr} {d : Reg} (hd : dst i = some d) {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hargs : τ'.argLen = τ.argLen) (hab : τ'.argBases = τ.argBases)
    (hb : ∀ p ∈ τ'.bases, p ∈ kill τ d) : Agree τ' s₁' s₂' := by
  obtain ⟨hw₁, hm₁, hsp₁, hg₁⟩ := exec_dst hd e₁
  obtain ⟨hw₂, hm₂, hsp₂, hg₂⟩ := exec_dst hd e₂
  exact ha.keep hrf hl hs hargs hab hw₁ hw₂ hm₁ hm₂ hsp₁ hsp₂
    (fun p h => kill_bases ha.wf₁ hw₁ hg₁ p (hb p h)) (fun p h => kill_bases ha.wf₂ hw₂ hg₂ p (hb p h))

theorem setReg_flags (s : State) (d : Reg) (x : BitVec 32) :
    (s.setReg d x).n = s.n ∧ (s.setReg d x).z = s.z ∧ (s.setReg d x).c = s.c ∧ (s.setReg d x).v = s.v :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem spBases_ok {τ : T} {s : State} (hw : Wf τ s) {t : Reg} {off : Nat} :
    ∀ p ∈ spBases τ t off, State.addr ((s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)).gpr p.1) =
      (region (s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) p.2).base := by
  intro p hp
  simp only [spBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
  rcases hp with hp | ⟨q, ⟨hq, hqo⟩, rfl⟩
  · exact kill_setReg hw t _ p hp
  · have := (hw.argBases q hq).2
    rw [hqo] at this
    simp only [State.setReg, ite_true, region] at this ⊢
    exact this

theorem ldrSp_sound {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {t : Reg} {off : Nat}
    (ho : off + 4 ≤ τ.argLen) :
    Agree { τ with regs := set τ t true, bases := spBases τ t off }
      (s₁.setReg t (s₁.mem.readW (State.addr (s₁.sp + BitVec.ofNat 32 off)) 32))
      (s₂.setReg t (s₂.mem.readW (State.addr (s₂.sp + BitVec.ofNat 32 off)) 32)) := by
  have hsp := ha.sp (by omega)
  have hv : s₁.mem.readW (State.addr (s₁.sp + BitVec.ofNat 32 off)) 32 =
      s₂.mem.readW (State.addr (s₂.sp + BitVec.ofNat 32 off)) 32 := by
    rw [hsp]
    refine Mem.readW_congr fun k hk => ?_
    have := ha.argMem (off + k) (by omega)
    simp only [argByte, hsp] at this
    rw [argWord ha.wf₂ ho]
    exact this
  exact ha.keep ⟨regs_set (d := t) (p := true) ha.rf.1 fun _ => hv, fun hf => ha.rf.2 hf⟩ rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl (spBases_ok ha.wf₁) (spBases_ok ha.wf₂)

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop | alloc | free | umaal => simp only [step, reduceCtorEq] at hs
  | mov d o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    exact ⟨rfl, ha.keep ⟨regs_set ha.rf.1 (op2_some ha h₁ h₂), fun hf => ha.rf.2 hf⟩ rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl (movBases_ok ha.wf₁ h₁) (movBases_ok ha.wf₂ h₂)⟩
  | dp op d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
  | adds d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set (fun r hr => by simpa [addFlags] using ha.rf.1 r hr) fun hp => ?_, fun hp => ?_⟩ <;>
    · simp only [Bool.and_eq_true] at hp
      rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
      try simp [addFlags, State.setReg]
  | adc d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.1.2, ha.reg hp.1.1, (ha.rf.2 hp.2).2.2.1]
  | subs d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨regs_set (fun r hr => by simpa [subFlags] using ha.rf.1 r hr) fun hp => ?_, fun hp => ?_⟩ <;>
    · simp only [Bool.and_eq_true] at hp
      rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
      try simp [subFlags, State.setReg]
  | cmp n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨rfl, ha.keep ⟨fun r hr => by simpa [subFlags] using ha.rf.1 r hr, fun hp => ?_⟩ rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl (fun p h => by simpa [subFlags, region] using ha.wf₁.bases p h)
      (fun p h => by simpa [subFlags, region] using ha.wf₂.bases p h)⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
    simp [subFlags]
  | addSp d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hi
    simp only [hi, ite_true, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨regs_set (d := d) (p := decide (0 < τ.argLen)) ha.rf.1 ?_, fun hf => ha.rf.2 hf⟩
    intro hp
    rw [ha.sp (of_decide_eq_true hp)]
  | movw d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set (d := d) (p := true) ha.rf.1 fun _ => rfl, fun hf => ha.rf.2 hf⟩
  | adrSym d name =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set (d := d) (p := false) ha.rf.1 (fun h => nomatch h), fun hf => ha.rf.2 hf⟩
  | movt d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set ha.rf.1 fun hp => by rw [ha.reg hp], fun hf => ha.rf.2 hf⟩
  | rev d m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set ha.rf.1 fun hp => by rw [ha.reg hp], fun hf => ha.rf.2 hf⟩
  | mul d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.reg hp.1, ha.reg hp.2]
  | mla d n m a =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.reg hp.1.1, ha.reg hp.1.2, ha.reg hp.2]
  | ldr t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load32] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    refine ⟨regs_set ha.rf.1 fun hp => ?_, fun hf => ha.rf.2 hf⟩
    split at hx₁ <;> [skip; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    exact ha.readW hp
  | str t n off =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 4) hn (by decide) (fun hp => by rw [ha.reg hp]) h₁ h₂
  | ldrb t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ha.write rfl e₁ e₂ ?_ rfl rfl rfl rfl fun _ h => h⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨x₁, -, rfl⟩ := e₁; obtain ⟨x₂, -, rfl⟩ := e₂
    exact ⟨regs_set (p := false) ha.rf.1 (fun h => by cases h), fun hf => ha.rf.2 hf⟩
  | strb t n off =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 1) hn (by decide) (fun hp => by rw [ha.reg hp]) h₁ h₂
  | ldrSp t off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i ho; cases hs
    have hsp := ha.sp (by omega)
    refine ⟨by simp only [addrs, hsp], ?_⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load32] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [skip; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    exact ldrSp_sound ha ho

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨-, hz, -, -⟩ := ha.rf.2 hc
  cases c <;> simp [eval, hz]

/-! ### Meets -/

theorem Wf.meet_left {τ₁ τ₂ : T} {s : State} (h : Wf τ₁ s) : Wf (meet τ₁ τ₂) s where
  lens hne := by
    by_cases he : τ₁.lens = τ₂.lens
    · simp only [meet, he, ite_true] at hne ⊢; exact he ▸ h.lens (he ▸ hne)
    · simp [meet, he] at hne
  bases p hp := h.bases p (List.mem_filter.mp hp).1
  args hpos := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hpos ⊢; exact he ▸ h.args (he ▸ hpos)
    · simp [meet, he] at hpos
  argBases p hp := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hp ⊢; exact he ▸ h.argBases p (List.mem_filter.mp hp).1
    · simp [meet, he] at hp

theorem Wf.meet_right {τ₁ τ₂ : T} {s : State} (h : Wf τ₂ s) : Wf (meet τ₁ τ₂) s where
  lens hne := by
    by_cases he : τ₁.lens = τ₂.lens
    · simp only [meet, he, ite_true] at hne ⊢; exact h.lens hne
    · simp [meet, he] at hne
  bases p hp := h.bases p (by simpa using (List.mem_filter.mp hp).2)
  args hpos := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hpos ⊢; exact h.args hpos
    · simp [meet, he] at hpos
  argBases p hp := by
    by_cases he : τ₁.argLen = τ₂.argLen
    · simp only [meet, he, ite_true] at hp ⊢; exact h.argBases p (by simpa using (List.mem_filter.mp hp).2)
    · simp [meet, he] at hp

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).1,
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.1)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [exact h.wr hne; exact absurd rfl hne]
  wf₁ := h.wf₁.meet_left
  wf₂ := h.wf₂.meet_left
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact he ▸ h.ok sl (List.mem_filter.mp hsl).1
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (List.mem_filter.mp hsl).1; cases hsl]
  sp hpos := by
    simp only [meet] at hpos
    split at hpos <;> [exact h.sp hpos; cases hpos]
  argMem k hk := by
    simp only [meet] at hk
    split at hk <;> [exact h.argMem k hk; cases hk]

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).2,
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.2)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [rename_i he; exact absurd rfl hne]
    exact h.wr (he ▸ hne)
  wf₁ := h.wf₁.meet_right
  wf₂ := h.wf₂.meet_right
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact h.ok sl (by simpa using (List.mem_filter.mp hsl).2)
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (by simpa using (List.mem_filter.mp hsl).2); cases hsl]
  sp hpos := by
    simp only [meet] at hpos
    split at hpos <;> [rename_i he; cases hpos]
    exact h.sp (he ▸ hpos)
  argMem k hk := by
    simp only [meet] at hk
    split at hk <;> [rename_i he; cases hk]
    exact h.argMem k (he ▸ hk)

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, ha⟩, hab⟩ := hle
  refine ⟨⟨fun r h' => h.rf.1 r (RegSet.mem_of_subset hr h'), fun hf' => h.rf.2 ?_⟩, fun hne => h.wr (hl ▸ hne),
    ⟨fun hne => hl ▸ h.wf₁.lens (hl ▸ hne), fun p hp => h.wf₁.bases p (hb p hp),
      fun hp => ha ▸ h.wf₁.args (ha ▸ hp), fun p hp => ha ▸ h.wf₁.argBases p (hab p hp)⟩,
    ⟨fun hne => hl ▸ h.wf₂.lens (hl ▸ hne), fun p hp => h.wf₂.bases p (hb p hp),
      fun hp => ha ▸ h.wf₂.args (ha ▸ hp), fun p hp => ha ▸ h.wf₂.argBases p (hab p hp)⟩,
    fun sl hsl => hl ▸ h.ok sl (hs sl hsl), fun sl hsl => h.slots sl (hs sl hsl),
    fun hp => h.sp (ha ▸ hp), fun k hk => h.argMem k (ha ▸ hk)⟩
  rcases hf with hf | hf
  · simp [hf'] at hf
  · exact hf

/-! ## Evaluation by the kernel

The kernel evaluates `step` and `le` for every instruction and every hint of
a check (`VG.Taint.check`). `stepK` and `leK` are the same functions written
with the functions of `VG.KList`, which the kernel evaluates several times
faster. -/

open VG.KList (any all filter find? map append)

/-- `a == b`, by the registers' indices. -/
def regEq (a b : Reg) : Bool := Nat.beq a.ctorIdx b.ctorIdx

theorem regEq_eq (a b : Reg) : regEq a b = (a == b) := by
  rw [regEq, KList.beq_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => RegIdx.idx_inj h, fun h => h ▸ rfl⟩

def setK (τ : T) (r : Reg) (p : Bool) : RegSet Reg := bif p then τ.regs.insert r else τ.regs.erase r

def killK (τ : T) (d : Reg) : List (Reg × Nat) := filter (fun p => !regEq p.1 d) τ.bases

def addrOfK (τ : T) (n : Reg) (off : Nat) : Option (Nat × Nat) :=
  (find? (fun p => regEq p.1 n) τ.bases).map fun p => (p.2, off)

def slotPubK (τ : T) (n : Reg) (off w : Nat) : Bool :=
  match addrOfK τ n off with
  | some (i, d) =>
    any τ.slots fun sl => Nat.beq sl.1 i && Nat.ble sl.2.1 d && Nat.ble (d + w) (sl.2.1 + sl.2.2)
  | none => false

def movBasesK (τ : T) (d : Reg) : Op2 → List (Reg × Nat)
  | .reg r => append (killK τ d) (map (fun p => (d, p.2)) (filter (fun p => regEq p.1 r) τ.bases))
  | _ => killK τ d

def storeSlotsK (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOfK τ n off with
  | some (i, d) =>
    bif Nat.ble (d + w) (τ.lens.getD i 0) then
      let kept := filter (fun sl => p || !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 ||
        Nat.ble (sl.2.1 + sl.2.2) d) τ.slots
      bif p then (i, d, w) :: kept else kept
    else bif p then τ.slots else []
  | none => bif p then τ.slots else []

def spBasesK (τ : T) (t : Reg) (off : Nat) : List (Reg × Nat) :=
  append (killK τ t) (map (fun p => (t, p.2)) (filter (fun p => Nat.beq p.1 off) τ.argBases))

def storeStepK (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  bif pub τ n then some { τ with slots := storeSlotsK τ n off w p } else none

def stepK (τ : T) : Instr → Option T
  | .mov d op2 => some { τ with regs := setK τ d (op2Pub τ op2), bases := movBasesK τ d op2 }
  | .dp _ d n op2 => some { τ with regs := setK τ d (pub τ n && op2Pub τ op2), bases := killK τ d }
  | .adds d n op2 | .subs d n op2 =>
    let p := pub τ n && op2Pub τ op2
    some { τ with regs := setK τ d p, flags := p, bases := killK τ d }
  | .adc d n op2 =>
    some { τ with regs := setK τ d (pub τ n && op2Pub τ op2 && τ.flags), bases := killK τ d }
  | .cmp n op2 => some { τ with flags := pub τ n && op2Pub τ op2 }
  | .movw d _ => some { τ with regs := setK τ d true, bases := killK τ d }
  | .adrSym d _ => some { τ with regs := setK τ d false, bases := killK τ d }
  | .addSp d _ => some { τ with regs := setK τ d (decide (0 < τ.argLen)), bases := killK τ d }
  | .movt d _ => some { τ with regs := setK τ d (pub τ d), bases := killK τ d }
  | .rev d m => some { τ with regs := setK τ d (pub τ m), bases := killK τ d }
  | .mul d n m => some { τ with regs := setK τ d (pub τ n && pub τ m), bases := killK τ d }
  | .mla d n m a => some { τ with regs := setK τ d (pub τ n && pub τ m && pub τ a), bases := killK τ d }
  | .umaal .. => none
  | .ldr t n off =>
    bif pub τ n then some { τ with regs := setK τ t (slotPubK τ n off 4), bases := killK τ t } else none
  | .str t n off => storeStepK τ n off 4 (pub τ t)
  | .ldrb t n _ => bif pub τ n then some { τ with regs := setK τ t false, bases := killK τ t } else none
  | .strb t n off => storeStepK τ n off 1 (pub τ t)
  | .ldrSp t off =>
    bif Nat.ble (off + 4) τ.argLen then some { τ with regs := setK τ t true, bases := spBasesK τ t off }
    else none
  | .push _ | .pop .. | .alloc _ | .free _ => none

/-- `l.contains a`, for a known base address. -/
def memB (a : Reg × Nat) (l : List (Reg × Nat)) : Bool := any l fun b => regEq a.1 b.1 && Nat.beq a.2 b.2

/-- `l.contains a`, for a slot. -/
def mem3 (a : Nat × Nat × Nat) (l : List (Nat × Nat × Nat)) : Bool :=
  any l fun b => Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2

/-- `l.contains a`, for a known base address among the arguments. -/
def mem2 (a : Nat × Nat) (l : List (Nat × Nat)) : Bool := any l fun b => Nat.beq a.1 b.1 && Nat.beq a.2 b.2

def leK (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    all τ.bases (memB · σ.bases) && all τ.slots (mem3 · σ.slots) && Nat.beq τ.argLen σ.argLen &&
    all τ.argBases (mem2 · σ.argBases)

section
open KList

theorem setK_eq : setK = set := by
  funext τ r p; simp only [setK, set, Bool.cond_eq_ite]

theorem killK_eq : killK = kill := by
  funext τ d; simp only [killK, kill, filter_eq, regEq_eq]; rfl

theorem addrOfK_eq : addrOfK = addrOf := by
  funext τ n off; simp only [addrOfK, addrOf, find?_eq, regEq_eq]

theorem slotPubK_eq : slotPubK = slotPub := by
  funext τ n off w; simp only [slotPubK, slotPub, addrOfK_eq]
  rcases addrOf τ n off with _ | ⟨i, d⟩ <;> simp only [any_eq, beq_eq, ble_eq]

theorem movBasesK_eq : movBasesK = movBases := by
  funext τ d op2
  cases op2 <;> simp only [movBasesK, movBases, killK_eq, append_eq, map_eq, filter_eq, regEq_eq]

theorem storeSlotsK_eq : storeSlotsK = storeSlots := by
  funext τ n off w p; simp only [storeSlotsK, storeSlots, addrOfK_eq]
  rcases addrOf τ n off with _ | ⟨i, d⟩ <;>
    simp only [filter_eq, beq_eq, ble_eq, Bool.cond_eq_ite, decide_eq_true_eq, bne]

theorem spBasesK_eq : spBasesK = spBases := by
  funext τ t off; simp only [spBasesK, spBases, killK_eq, append_eq, map_eq, filter_eq, beq_eq]

theorem storeStepK_eq : storeStepK = storeStep := by
  funext τ n off w p; simp only [storeStepK, storeStep, storeSlotsK_eq, Bool.cond_eq_ite]

theorem stepK_eq : stepK = step := by
  funext τ i
  cases i <;> simp only [stepK, step, setK_eq, killK_eq, movBasesK_eq, slotPubK_eq, storeStepK_eq,
    spBasesK_eq, ble_eq, Bool.cond_eq_ite, decide_eq_true_eq]

theorem memB_eq (a : Reg × Nat) (l : List (Reg × Nat)) : memB a l = l.contains a := by
  simp only [memB, any_eq, beq_eq, regEq_eq, List.contains_eq_any_beq]
  rfl

theorem mem3_eq (a : Nat × Nat × Nat) (l : List (Nat × Nat × Nat)) : mem3 a l = l.contains a := by
  simp only [mem3, any_eq, beq_eq, List.contains_eq_any_beq]
  congr; funext b; rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Prod.ext_iff, and_assoc]

theorem mem2_eq (a : Nat × Nat) (l : List (Nat × Nat)) : mem2 a l = l.contains a := by
  simp only [mem2, any_eq, beq_eq, List.contains_eq_any_beq]
  rfl

theorem leK_eq : leK = le := by
  funext τ σ
  simp only [leK, le, memB_eq, mem3_eq, mem2_eq, all_eq, beq_eq]

end

end VG.Arm.Taint

namespace VG.Arm

namespace Taint

/-- Whether a call leaves `r` unchanged (all but `lr` and `r12`). -/
def callKeeps (r : Reg) : Bool := r != .lr && r != .r12

/-- A call leaves unknown values in `lr`, `r12` and the condition flags. -/
def callStep (τ : T) : T :=
  { τ with
    regs := (τ.regs.erase .lr).erase .r12
    flags := false
    bases := τ.bases.filter (callKeeps ·.1) }

theorem call_gpr {s s' : State} (e : isa.call s = some s') {r : Reg} (h : callKeeps r = true) :
    s'.gpr r = s.gpr r := by
  simp only [callKeeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simp only [isa, call, Option.some.injEq] at e; subst e
  simp [State.setReg, h.1, h.2]

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : some (callStep τ) = some τ') (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  cases hs
  have hr₁ := e₁; have hr₂ := e₂
  simp only [isa, call, Option.some.injEq] at hr₁ hr₂
  subst hr₁ hr₂
  refine ⟨rfl, ha.keep ⟨fun r hr => ?_, by simp [callStep]⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun p hp => ?_) (fun p hp => ?_)⟩
  · simp only [callStep, RegSet.mem_erase] at hr
    obtain ⟨h12, hlr, hr⟩ := hr
    have hk : callKeeps r = true := by simp [callKeeps, hlr, h12]
    rw [call_gpr e₁ hk, call_gpr e₂ hk]; exact ha.rf.1 r hr
  · simp only [callStep, List.mem_filter] at hp
    rw [call_gpr e₁ hp.2]; exact ha.wf₁.bases p hp.1
  · simp only [callStep, List.mem_filter] at hp
    rw [call_gpr e₂ hp.2]; exact ha.wf₂.bases p hp.1

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : some τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂) :
    isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Agree τ' c₁ c₂ := by
  cases hs
  simp only [isa, ret] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ⟨rfl, ha⟩

/-! ## Stores of public values, without repeats -/

/-- The slots after a store, without adding one that is there. -/
def storeSlotsKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOfK τ n off with
  | some (i, d) =>
    bif Nat.ble (d + w) (τ.lens.getD i 0) then
      bif p then (bif mem3 (i, d, w) τ.slots then τ.slots else (i, d, w) :: τ.slots)
      else KList.filter (fun sl => p || !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 ||
        Nat.ble (sl.2.1 + sl.2.2) d) τ.slots
    else bif p then τ.slots else []
  | none => bif p then τ.slots else []

def storeStepKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  bif pub τ n then some { τ with slots := storeSlotsKD τ n off w p } else none

/-- An instruction transfer function, independent of the incoming taint. -/
structure Step where
  run : T → Option T

/-- Classify an instruction before substituting its incoming taint, so the
kernel can share the classification between checks from different taints.
Stores retain the duplicate-slot optimization of `storeStepKD`. -/
def stepKDFn : Instr → Step
  | .mov d op2 => ⟨fun τ => some { τ with regs := setK τ d (op2Pub τ op2), bases := movBasesK τ d op2 }⟩
  | .dp _ d n op2 => ⟨fun τ => some { τ with regs := setK τ d (pub τ n && op2Pub τ op2), bases := killK τ d }⟩
  | .adds d n op2 | .subs d n op2 => ⟨fun τ =>
    let p := pub τ n && op2Pub τ op2
    some { τ with regs := setK τ d p, flags := p, bases := killK τ d }⟩
  | .adc d n op2 => ⟨fun τ =>
    some { τ with regs := setK τ d (pub τ n && op2Pub τ op2 && τ.flags), bases := killK τ d }⟩
  | .cmp n op2 => ⟨fun τ => some { τ with flags := pub τ n && op2Pub τ op2 }⟩
  | .movw d _ => ⟨fun τ => some { τ with regs := setK τ d true, bases := killK τ d }⟩
  | .adrSym d _ => ⟨fun τ => some { τ with regs := setK τ d false, bases := killK τ d }⟩
  | .addSp d _ => ⟨fun τ => some { τ with regs := setK τ d (decide (0 < τ.argLen)), bases := killK τ d }⟩
  | .movt d _ => ⟨fun τ => some { τ with regs := setK τ d (pub τ d), bases := killK τ d }⟩
  | .rev d m => ⟨fun τ => some { τ with regs := setK τ d (pub τ m), bases := killK τ d }⟩
  | .mul d n m => ⟨fun τ => some { τ with regs := setK τ d (pub τ n && pub τ m), bases := killK τ d }⟩
  | .mla d n m a => ⟨fun τ => some { τ with regs := setK τ d (pub τ n && pub τ m && pub τ a), bases := killK τ d }⟩
  | .umaal .. => ⟨fun _ => none⟩
  | .ldr t n off => ⟨fun τ =>
    bif pub τ n then some { τ with regs := setK τ t (slotPubK τ n off 4), bases := killK τ t } else none⟩
  | .str t n off => ⟨fun τ => storeStepKD τ n off 4 (pub τ t)⟩
  | .ldrb t n _ => ⟨fun τ => bif pub τ n then some { τ with regs := setK τ t false, bases := killK τ t } else none⟩
  | .strb t n off => ⟨fun τ => storeStepKD τ n off 1 (pub τ t)⟩
  | .ldrSp t off => ⟨fun τ =>
    bif Nat.ble (off + 4) τ.argLen then some { τ with regs := setK τ t true, bases := spBasesK τ t off }
    else none⟩
  | .push _ | .pop .. | .alloc _ | .free _ => ⟨fun _ => none⟩

/-- Apply the preclassified instruction to the incoming taint. -/
def stepKD (τ : T) (i : Instr) : Option T := (stepKDFn i).run τ


/-- The same taints, but for repeated slots. -/
structure Sim (a b : T) : Prop where
  regs : a.regs = b.regs
  flags : a.flags = b.flags
  lens : a.lens = b.lens
  bases : a.bases = b.bases
  slots : ∀ x, x ∈ a.slots ↔ x ∈ b.slots
  argLen : a.argLen = b.argLen
  argBases : a.argBases = b.argBases

theorem Sim.refl (a : T) : Sim a a := ⟨rfl, rfl, rfl, rfl, fun _ => Iff.rfl, rfl, rfl⟩

theorem Sim.agree {a b : T} {s₁ s₂ : State} (h : Sim a b) (hb : Agree b s₁ s₂) : Agree a s₁ s₂ := by
  refine le_sound ?_ hb
  have hs : ∀ x ∈ a.slots, x ∈ b.slots := fun x hx => (h.slots x).mp hx
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem, h.regs, h.flags, h.lens, h.bases, h.argLen, h.argBases, RegSet.subset_eq,
    Nat.and_self, beq_self_eq_true]
  have hf : b.flags = false ∨ b.flags = true := by cases b.flags <;> simp
  exact ⟨⟨⟨⟨⟨⟨trivial, hf⟩, trivial⟩, fun _ hx => hx⟩, hs⟩, trivial⟩, fun _ hx => hx⟩

theorem mem_storeSlotsKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) (x : Nat × Nat × Nat) :
    x ∈ storeSlotsKD τ n off w p ↔ x ∈ storeSlots τ n off w p := by
  rw [← storeSlotsK_eq]
  unfold storeSlotsKD storeSlotsK
  cases addrOfK τ n off with
  | none => exact Iff.rfl
  | some id =>
    obtain ⟨i, d⟩ := id
    simp only
    cases Nat.ble (d + w) (τ.lens.getD i 0) <;> cases p <;> simp only [Bool.cond_false, Bool.cond_true]
    rw [show KList.filter (fun sl => true || !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 ||
      Nat.ble (sl.2.1 + sl.2.2) d) τ.slots = τ.slots by
        simp only [KList.filter_eq, Bool.true_or]; exact List.filter_eq_self.mpr fun _ _ => rfl]
    cases hm : mem3 (i, d, w) τ.slots
    · exact Iff.rfl
    · rw [mem3_eq, List.contains_iff_mem] at hm
      simp only [Bool.cond_true, List.mem_cons, iff_or_self]
      rintro rfl; exact hm

theorem stepKD_spec (τ : T) (i : Instr) :
    (stepKD τ i = none ∧ step τ i = none) ∨ ∃ a b, stepKD τ i = some a ∧ step τ i = some b ∧ Sim a b := by
  have st : ∀ n off w p, (storeStepKD τ n off w p = none ∧ storeStep τ n off w p = none) ∨
      ∃ a b, storeStepKD τ n off w p = some a ∧ storeStep τ n off w p = some b ∧ Sim a b := by
    intro n off w p
    unfold storeStepKD storeStep
    cases pub τ n
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨_, _, rfl, rfl, ⟨rfl, rfl, rfl, rfl, mem_storeSlotsKD τ n off w p, rfl, rfl⟩⟩
  have other : ∀ {i}, stepKD τ i = stepK τ i →
      (stepKD τ i = none ∧ step τ i = none) ∨ ∃ a b, stepKD τ i = some a ∧ step τ i = some b ∧ Sim a b := by
    intro i e
    rw [e, stepK_eq]
    cases step τ i
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨_, _, rfl, rfl, Sim.refl _⟩
  cases i
  case str t n off => exact st n off 4 _
  case strb t n off => exact st n off 1 _
  all_goals exact other rfl

/-! ## Stores of public values, merged

A public store adds a slot. Stored one after the other (a table of constants,
a buffer), adjacent public slots would make a list that grows with every store,
which every later store and load searches: `stepKM`'s stores merge the new
slot with the slots of its region that it overlaps or touches, so that a run of
public bytes is one slot. `Arm.taint` compares and meets its taints by
containment in a slot (`leC`, `meetC`), which merged slots keep. -/

/-- Whether the slots `s` and `x` are of the same region and overlap or touch. -/
def touches (s x : Nat × Nat × Nat) : Bool :=
  Nat.beq s.1 x.1 && Nat.ble s.2.1 (x.2.1 + x.2.2) && Nat.ble x.2.1 (s.2.1 + s.2.2)

/-- The slot of the bytes of the slots `s` and `x`, if they touch. -/
def joinSlot (s x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (s.1, min s.2.1 x.2.1, max (s.2.1 + s.2.2) (x.2.1 + x.2.2) - min s.2.1 x.2.1)

/-- The slots `l` with the slot `x`, merged with those it touches. -/
def mergeSlot (x : Nat × Nat × Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => [x]
  | s :: l => bif touches s x then mergeSlot (joinSlot s x) l else s :: mergeSlot x l

/-- Byte `k` of region `i` is in the slot `s`. -/
def InSlot (s : Nat × Nat × Nat) (i k : Nat) : Prop := s.1 = i ∧ s.2.1 ≤ k ∧ k < s.2.1 + s.2.2

theorem mem_mergeSlot : ∀ (l : List (Nat × Nat × Nat)) (x y : Nat × Nat × Nat), y ∈ mergeSlot x l →
    y ∈ l ∨ (y.1 = x.1 ∧ x.2.2 ≤ y.2.2 ∧
      ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 → InSlot x x.1 k ∨ ∃ z ∈ l, InSlot z x.1 k)
  | [], x, y, h => by
    simp only [mergeSlot, List.mem_singleton] at h
    subst h
    exact .inr ⟨rfl, Nat.le_refl _, fun k h₁ h₂ => .inl ⟨rfl, h₁, h₂⟩⟩
  | s :: l, x, y, h => by
    simp only [mergeSlot] at h
    cases ht : touches s x
    · simp only [ht, Bool.cond_false, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      · rcases mem_mergeSlot l x y h with h | ⟨e, hw, hk⟩
        · exact .inl (List.mem_cons_of_mem _ h)
        · refine .inr ⟨e, hw, fun k h₁ h₂ => ?_⟩
          rcases hk k h₁ h₂ with h | ⟨z, hz, hk⟩
          · exact .inl h
          · exact .inr ⟨z, List.mem_cons_of_mem _ hz, hk⟩
    · simp only [ht, Bool.cond_true] at h
      simp only [touches, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at ht
      obtain ⟨⟨hi, ha⟩, hb⟩ := ht
      rcases mem_mergeSlot l (joinSlot s x) y h with h | ⟨e, hw, hk⟩
      · exact .inl (List.mem_cons_of_mem _ h)
      · simp only [joinSlot] at e hw hk ⊢
        refine .inr ⟨e.trans hi, by omega, fun k h₁ h₂ => ?_⟩
        rcases hk k h₁ h₂ with ⟨-, h₃, h₄⟩ | ⟨z, hz, hk⟩
        · dsimp only at h₃ h₄
          by_cases hx : x.2.1 ≤ k ∧ k < x.2.1 + x.2.2
          · exact .inl ⟨rfl, hx⟩
          · refine .inr ⟨s, List.mem_cons_self .., hi, ?_, ?_⟩ <;> omega
        · exact .inr ⟨z, List.mem_cons_of_mem _ hz, hk.1.trans hi, hk.2⟩

/-- The parts of the slot `sl` outside the bytes `d` to `d + w` of region `i`. -/
def cutSlot (i d w : Nat) (sl : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  bif !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 || Nat.ble (sl.2.1 + sl.2.2) d then [sl]
  else (bif Nat.blt sl.2.1 d then [(i, sl.2.1, d - sl.2.1)] else []) ++
    (bif Nat.blt (d + w) (sl.2.1 + sl.2.2) then [(i, d + w, sl.2.1 + sl.2.2 - (d + w))] else [])

theorem lt_of_ble_false {a b : Nat} (h : Nat.ble a b = false) : b < a :=
  Nat.gt_of_not_le fun h' => by rw [← Nat.ble_eq] at h'; rw [h'] at h; cases h

/-- The slots `l` without the bytes `d` to `d + w` of region `i`. -/
def cutSlots (i d w : Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | sl :: l => cutSlot i d w sl ++ cutSlots i d w l

theorem mem_cutSlots {i d w : Nat} : ∀ {l : List (Nat × Nat × Nat)} {y : Nat × Nat × Nat},
    y ∈ cutSlots i d w l → (y.1 ≠ i ∨ d + w ≤ y.2.1 ∨ y.2.1 + y.2.2 ≤ d) ∧
      (y ∈ l ∨ ∃ z ∈ l, 0 < y.2.2 ∧ y.1 = z.1 ∧ z.2.1 ≤ y.2.1 ∧ y.2.1 + y.2.2 ≤ z.2.1 + z.2.2)
  | [], _, h => (List.not_mem_nil h).elim
  | sl :: l, y, h => by
    rcases List.mem_append.mp h with h | h
    · unfold cutSlot at h
      cases hc : (!Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 || Nat.ble (sl.2.1 + sl.2.2) d)
      · rw [hc, Bool.cond_false] at h
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Nat.beq_eq] at hc
        obtain ⟨⟨hi, h₁⟩, h₂⟩ := hc
        have h₁ := lt_of_ble_false h₁
        have h₂ := lt_of_ble_false h₂
        rcases List.mem_append.mp h with h | h
        · cases hl : Nat.blt sl.2.1 d
          · rw [hl, Bool.cond_false] at h; exact (List.not_mem_nil h).elim
          · rw [hl, Bool.cond_true, List.mem_singleton] at h
            subst h
            simp only [Nat.blt_eq] at hl
            exact ⟨.inr (.inr (by dsimp only; omega)),
              .inr ⟨sl, List.mem_cons_self .., by dsimp only; omega, hi.symm, by dsimp only; omega,
                by dsimp only; omega⟩⟩
        · cases hl : Nat.blt (d + w) (sl.2.1 + sl.2.2)
          · rw [hl, Bool.cond_false] at h; exact (List.not_mem_nil h).elim
          · rw [hl, Bool.cond_true, List.mem_singleton] at h
            subst h
            simp only [Nat.blt_eq] at hl
            exact ⟨.inr (.inl (by dsimp only; omega)),
              .inr ⟨sl, List.mem_cons_self .., by dsimp only; omega, hi.symm, by dsimp only; omega,
                by dsimp only; omega⟩⟩
      · rw [hc, Bool.cond_true, List.mem_singleton] at h
        subst h
        simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq] at hc
        refine ⟨?_, .inl (List.mem_cons_self ..)⟩
        rcases hc with (hc | hc) | hc
        · exact .inl fun e => by rw [e] at hc; simp [Nat.beq_refl] at hc
        · exact .inr (.inl hc)
        · exact .inr (.inr hc)
    · obtain ⟨h₁, h₂⟩ := mem_cutSlots h
      refine ⟨h₁, ?_⟩
      rcases h₂ with h₂ | ⟨z, hz, h₂⟩
      · exact .inl (List.mem_cons_of_mem _ h₂)
      · exact .inr ⟨z, List.mem_cons_of_mem _ hz, h₂⟩

/-- The slots after a store, the public bytes merged into their runs, and the
parts of the slots it does not overwrite kept. -/
def storeSlotsKM (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOfK τ n off with
  | some (i, d) =>
    bif Nat.ble (d + w) (τ.lens.getD i 0) then
      bif p then mergeSlot (i, d, w) τ.slots else cutSlots i d w τ.slots
    else bif p then τ.slots else []
  | none => bif p then τ.slots else []

/-- The taint `τ` with its slots cut around the bytes a store to `[n, #off]`
writes: the same bytes known, in slots that the store's spec step keeps. -/
def cutT (τ : T) (n : Reg) (off w : Nat) : T :=
  { τ with slots := match addrOfK τ n off with
    | some (i, d) => cutSlots i d w τ.slots
    | none => τ.slots }

def storeStepKM (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  bif pub τ n then some { τ with slots := storeSlotsKM τ n off w p } else none

/-- `stepKD`, with the stores of `storeStepKM`. -/
def stepKM (τ : T) : Instr → Option T
  | .str t n off => storeStepKM τ n off 4 (pub τ t)
  | .strb t n off => storeStepKM τ n off 1 (pub τ t)
  | i => stepKD τ i

/-- `a` is `b` but for its slots, each of which is one of `b`'s or has its
bytes in `b`'s. -/
structure Cover (a b : T) : Prop where
  regs : a.regs = b.regs
  flags : a.flags = b.flags
  lens : a.lens = b.lens
  bases : a.bases = b.bases
  argLen : a.argLen = b.argLen
  argBases : a.argBases = b.argBases
  slots : ∀ y ∈ a.slots, y ∈ b.slots ∨
    (0 < y.2.2 ∧ ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 → ∃ z ∈ b.slots, InSlot z y.1 k)

/-- `Agree`, with other slots: each within the regions' lengths, with the
same bytes in both states. -/
theorem Agree.setSlots {t : T} {s₁ s₂ : State} (h : Agree t s₁ s₂) {sl : List (Nat × Nat × Nat)}
    (hok : ∀ y ∈ sl, y.2.1 + y.2.2 ≤ t.lens.getD y.1 0)
    (hag : ∀ y ∈ sl, ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 →
      s₁.mem (byteAddr s₁ y.1 k) = s₂.mem (byteAddr s₂ y.1 k)) :
    Agree { t with slots := sl } s₁ s₂ where
  rf := h.rf
  wr := h.wr
  wf₁ := ⟨h.wf₁.lens, h.wf₁.bases, h.wf₁.args, h.wf₁.argBases⟩
  wf₂ := ⟨h.wf₂.lens, h.wf₂.bases, h.wf₂.args, h.wf₂.argBases⟩
  ok := hok
  slots := hag
  sp := h.sp
  argMem := h.argMem

/-- The slot `y`'s bytes are in slots of `l`, within the regions' lengths
`ls`: it is within its region's. -/
theorem bound_of_cover {ls : List Nat} {l : List (Nat × Nat × Nat)}
    (hl : ∀ z ∈ l, z.2.1 + z.2.2 ≤ ls.getD z.1 0) {y : Nat × Nat × Nat} (hw : 0 < y.2.2)
    (hc : ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 → ∃ z ∈ l, InSlot z y.1 k) :
    y.2.1 + y.2.2 ≤ ls.getD y.1 0 := by
  obtain ⟨z, hz, e, h₁, h₂⟩ := hc (y.2.1 + y.2.2 - 1) (by omega) (by omega)
  have := hl z hz
  rw [e] at this
  omega

/-- The bytes of `y` agree if they are in slots that agree. -/
theorem agree_of_cover {s₁ s₂ : State} {l : List (Nat × Nat × Nat)}
    (hl : ∀ z ∈ l, ∀ k, z.2.1 ≤ k → k < z.2.1 + z.2.2 →
      s₁.mem (byteAddr s₁ z.1 k) = s₂.mem (byteAddr s₂ z.1 k))
    {y : Nat × Nat × Nat} (hc : ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 → ∃ z ∈ l, InSlot z y.1 k) :
    ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 → s₁.mem (byteAddr s₁ y.1 k) = s₂.mem (byteAddr s₂ y.1 k) := by
  intro k h₁ h₂
  obtain ⟨z, hz, e, h₃, h₄⟩ := hc k h₁ h₂
  rw [← e]
  exact hl z hz k h₃ h₄

theorem Cover.agree {a b : T} {s₁ s₂ : State} (h : Cover a b) (hb : Agree b s₁ s₂) :
    Agree a s₁ s₂ := by
  have e : a = { b with slots := a.slots } := by
    obtain ⟨_, _, _, _, _, _, _⟩ := a
    obtain ⟨_, _, _, _, _, _, _⟩ := b
    obtain ⟨hr, hf, hl, hbs, ha, hab, -⟩ := h
    simp only at hr hf hl hbs ha hab
    subst hr hf hl hbs ha hab
    rfl
  rw [e]
  refine hb.setSlots (fun y hy => ?_) (fun y hy => ?_)
  · rcases h.slots y hy with hy | ⟨hw, hc⟩
    · exact hb.ok y hy
    · exact bound_of_cover hb.ok hw hc
  · rcases h.slots y hy with hy | ⟨-, hc⟩
    · exact hb.slots y hy
    · exact agree_of_cover hb.slots hc

theorem Sim.cover {a b : T} (h : Sim a b) : Cover a b :=
  ⟨h.regs, h.flags, h.lens, h.bases, h.argLen, h.argBases, fun y hy => .inl ((h.slots y).mp hy)⟩

theorem filter_true_eq {α : Type} (l : List α) : l.filter (fun _ => true) = l :=
  List.filter_eq_self.mpr fun _ _ => rfl

theorem addrOf_slots (τ : T) (l : List (Nat × Nat × Nat)) (n : Reg) (off : Nat) :
    addrOf { τ with slots := l } n off = addrOf τ n off := rfl

theorem storeSlotsKM_false (τ : T) (n : Reg) (off w : Nat) :
    storeSlotsKM τ n off w false = storeSlots (cutT τ n off w) n off w false := by
  unfold storeSlotsKM storeSlots cutT
  rw [addrOf_slots, addrOfK_eq]
  cases addrOf τ n off with
  | none => rfl
  | some id =>
    obtain ⟨i, d⟩ := id
    dsimp only
    cases hb : Nat.ble (d + w) (τ.lens.getD i 0)
    · have hb' : ¬ d + w ≤ τ.lens.getD i 0 := fun h' => by rw [← Nat.ble_eq] at h'; rw [h'] at hb; cases hb
      simp only [Bool.cond_false, hb', ite_false, Bool.false_eq_true]
    · have hb' : d + w ≤ τ.lens.getD i 0 := Nat.ble_eq ▸ hb
      simp only [Bool.cond_true, Bool.cond_false, hb', ite_true, Bool.false_eq_true, ite_false]
      refine (List.filter_eq_self.mpr fun y hy => ?_).symm
      simp only [Bool.false_or, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
      rcases (mem_cutSlots hy).1 with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h

theorem cutT_cover (τ : T) (n : Reg) (off w : Nat) : Cover (cutT τ n off w) τ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
  unfold cutT at hy
  dsimp only at hy
  split at hy
  · rcases (mem_cutSlots hy).2 with h | ⟨z, hz, h₀, e, h₁, h₂⟩
    · exact .inl h
    · exact .inr ⟨h₀, fun k h₃ h₄ => ⟨z, hz, e.symm, by omega, by omega⟩⟩
  · exact .inl hy

theorem storeSlotsKM_cover (τ : T) (n : Reg) (off w : Nat) (hw : 0 < w)
    (y : Nat × Nat × Nat) (hy : y ∈ storeSlotsKM τ n off w true) :
    y ∈ storeSlots τ n off w true ∨ (0 < y.2.2 ∧ ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 →
      ∃ z ∈ storeSlots τ n off w true, InSlot z y.1 k) := by
  unfold storeSlotsKM at hy
  unfold storeSlots
  rw [addrOfK_eq] at hy
  cases ha : addrOf τ n off with
  | none =>
    rw [ha] at hy
    simp only [Bool.cond_true, ite_true] at hy ⊢
    exact .inl hy
  | some id =>
    obtain ⟨i, d⟩ := id
    rw [ha] at hy
    simp only at hy ⊢
    cases hb : Nat.ble (d + w) (τ.lens.getD i 0)
    · have hb' : ¬ d + w ≤ τ.lens.getD i 0 := fun h' => by rw [← Nat.ble_eq] at h'; rw [h'] at hb; cases hb
      simp only [hb, Bool.cond_false, hb', ite_false, Bool.cond_true, ite_true] at hy ⊢
      exact .inl hy
    · have hb' : d + w ≤ τ.lens.getD i 0 := Nat.ble_eq ▸ hb
      simp only [hb, Bool.cond_true, hb', ite_true, Bool.true_or, filter_true_eq] at hy ⊢
      rcases mem_mergeSlot τ.slots (i, d, w) y hy with h | ⟨e, hw', hk⟩
      · exact .inl (List.mem_cons_of_mem _ h)
      · refine .inr ⟨by simp only at hw'; omega, fun k h₁ h₂ => ?_⟩
        rw [e]
        rcases hk k h₁ h₂ with h | ⟨z, hz, h⟩
        · exact ⟨_, List.mem_cons_self .., h⟩
        · exact ⟨z, List.mem_cons_of_mem _ hz, h⟩

theorem storeStep_pub {τ : T} {n : Reg} {off w : Nat} {p : Bool} (h : pub τ n = true) :
    storeStep τ n off w p = some { τ with slots := storeSlots τ n off w p } := by
  simp only [storeStep, h, ↓reduceIte]

/-- `stepKM` is the spec's `step` from a taint that knows the same bytes,
up to slots that cover the same bytes. -/
theorem stepKM_spec (τ : T) (i : Instr) :
    stepKM τ i = none ∨ ∃ τ₀ a b, Cover τ₀ τ ∧ stepKM τ i = some a ∧ step τ₀ i = some b ∧ Cover a b := by
  have st : ∀ n off w t, 0 < w → storeStepKM τ n off w (pub τ t) = none ∨
      ∃ τ₀ a b, Cover τ₀ τ ∧ storeStepKM τ n off w (pub τ t) = some a ∧
        storeStep τ₀ n off w (pub τ₀ t) = some b ∧ Cover a b := by
    intro n off w t hw
    unfold storeStepKM
    cases hp : pub τ n
    · exact .inl rfl
    · cases ht : pub τ t
      · refine .inr ⟨cutT τ n off w, { τ with slots := storeSlotsKM τ n off w false },
          { cutT τ n off w with slots := storeSlots (cutT τ n off w) n off w false },
          cutT_cover τ n off w, rfl, ?_, ?_⟩
        · rw [show pub (cutT τ n off w) t = false from ht]
          exact storeStep_pub (τ := cutT τ n off w) hp
        · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => .inl ?_⟩
          dsimp only at hy ⊢
          rw [storeSlotsKM_false] at hy
          exact hy
      · refine .inr ⟨τ, { τ with slots := storeSlotsKM τ n off w true },
          { τ with slots := storeSlots τ n off w true }, (Sim.refl τ).cover, rfl, ?_,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, storeSlotsKM_cover τ n off w hw⟩⟩
        rw [ht]
        exact storeStep_pub hp
  have other : ∀ {i}, stepKM τ i = stepKD τ i →
      stepKM τ i = none ∨ ∃ τ₀ a b, Cover τ₀ τ ∧ stepKM τ i = some a ∧ step τ₀ i = some b ∧ Cover a b := by
    intro i e
    rw [e]
    rcases stepKD_spec τ i with h | ⟨a, b, h₁, h₂, hab⟩
    · exact .inl h.1
    · exact .inr ⟨τ, a, b, (Sim.refl τ).cover, h₁, h₂, hab.cover⟩
  cases i
  case str t n off => exact st n off 4 t (by decide)
  case strb t n off => exact st n off 1 t (by decide)
  all_goals exact other rfl

/-- `s` contains the slot `x`. -/
def containsSlot (s x : Nat × Nat × Nat) : Bool :=
  Nat.beq s.1 x.1 && Nat.ble s.2.1 x.2.1 && Nat.ble (x.2.1 + x.2.2) (s.2.1 + s.2.2)

theorem containsSlot_cover {s x : Nat × Nat × Nat} (h : containsSlot s x = true) :
    ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 → InSlot s x.1 k := by
  simp only [containsSlot, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  intro k h₁ h₂
  exact ⟨h.1.1, by omega, by omega⟩

/-- `le`, with each slot of `τ` contained in one of `σ`. -/
def leC (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    KList.all τ.bases (memB · σ.bases) &&
    KList.all τ.slots (fun x => KList.any σ.slots (containsSlot · x)) && Nat.beq τ.argLen σ.argLen &&
    KList.all τ.argBases (mem2 · σ.argBases)

theorem leC_sound {τ σ : T} {s₁ s₂ : State} (hle : leC τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  have hle' := hle
  simp only [leC, Bool.and_eq_true, KList.all_eq, KList.any_eq, List.all_eq_true, List.any_eq_true,
    memB_eq, mem2_eq, List.contains_iff_mem, beq_iff_eq, Nat.beq_eq] at hle'
  obtain ⟨⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, ha⟩, hab⟩ := hle'
  have h₀ : le { τ with slots := [] } σ = true := by
    simp only [le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq, hr, hf, hl,
      true_and, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨hb, ha⟩, hab⟩
  have h₁ := le_sound h₀ h
  have hc : ∀ y ∈ τ.slots, ∀ k, y.2.1 ≤ k → k < y.2.1 + y.2.2 → ∃ z ∈ σ.slots, InSlot z y.1 k :=
    fun y hy k h₁ h₂ => by
      obtain ⟨z, hz, hzy⟩ := hs y hy
      exact ⟨z, hz, containsSlot_cover hzy k h₁ h₂⟩
  refine h₁.setSlots (fun y hy => ?_) (fun y hy => agree_of_cover h.slots (hc y hy))
  obtain ⟨z, hz, hzy⟩ := hs y hy
  simp only [containsSlot, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hzy
  have := h.ok z hz
  show y.2.1 + y.2.2 ≤ τ.lens.getD y.1 0
  rw [hl, ← hzy.1.1]
  omega

/-- The bytes of both slots `x` and `z`, as a slot, if there are any. -/
def interSlot (x z : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  bif Nat.beq x.1 z.1 && Nat.blt (max x.2.1 z.2.1) (min (x.2.1 + x.2.2) (z.2.1 + z.2.2)) then
    [(x.1, max x.2.1 z.2.1, min (x.2.1 + x.2.2) (z.2.1 + z.2.2) - max x.2.1 z.2.1)]
  else []

/-- The bytes of the slot `x` in the slots `l`. -/
def interAll (x : Nat × Nat × Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | z :: l => interSlot x z ++ interAll x l

/-- The bytes in both slots of `l₁` and slots of `l₂`. -/
def interSlots : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [], _ => []
  | x :: l, l₂ => interAll x l₂ ++ interSlots l l₂

theorem mem_interSlot {x z y : Nat × Nat × Nat} (h : y ∈ interSlot x z) :
    0 < y.2.2 ∧ y.1 = x.1 ∧ y.1 = z.1 ∧ x.2.1 ≤ y.2.1 ∧ y.2.1 + y.2.2 ≤ x.2.1 + x.2.2 ∧
      z.2.1 ≤ y.2.1 ∧ y.2.1 + y.2.2 ≤ z.2.1 + z.2.2 := by
  unfold interSlot at h
  cases hc : (Nat.beq x.1 z.1 && Nat.blt (max x.2.1 z.2.1) (min (x.2.1 + x.2.2) (z.2.1 + z.2.2)))
  · rw [hc, Bool.cond_false] at h; exact (List.not_mem_nil h).elim
  · rw [hc, Bool.cond_true, List.mem_singleton] at h
    subst h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
    dsimp only
    exact ⟨by omega, rfl, hc.1, by omega, by omega, by omega, by omega⟩

theorem mem_interAll {x y : Nat × Nat × Nat} : ∀ {l : List (Nat × Nat × Nat)},
    y ∈ interAll x l → ∃ z ∈ l, y ∈ interSlot x z
  | [], h => (List.not_mem_nil h).elim
  | z :: l, h => by
    rcases List.mem_append.mp h with h | h
    · exact ⟨z, List.mem_cons_self .., h⟩
    · obtain ⟨z', hz, h⟩ := mem_interAll h
      exact ⟨z', List.mem_cons_of_mem _ hz, h⟩

theorem mem_interSlots {l₂ : List (Nat × Nat × Nat)} {y : Nat × Nat × Nat} :
    ∀ {l₁ : List (Nat × Nat × Nat)}, y ∈ interSlots l₁ l₂ → ∃ x ∈ l₁, ∃ z ∈ l₂, y ∈ interSlot x z
  | [], h => (List.not_mem_nil h).elim
  | x :: l, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨z, hz, h⟩ := mem_interAll h
      exact ⟨x, List.mem_cons_self .., z, hz, h⟩
    · obtain ⟨x', hx, z, hz, h⟩ := mem_interSlots h
      exact ⟨x', List.mem_cons_of_mem _ hx, z, hz, h⟩

/-- `meet`, with the bytes public in both: the intersections of their slots. -/
def meetC (τ₁ τ₂ : T) : T :=
  { meet τ₁ τ₂ with
    slots := if τ₁.lens = τ₂.lens then interSlots τ₁.slots τ₂.slots else [] }

/-- `meetC` agrees where `meet` does and the taint `τ`, each of whose slots
contains one of the meet's, does. -/
theorem meetC_of {τ₁ τ₂ τ : T} {s₁ s₂ : State} (hm : Agree (meet τ₁ τ₂) s₁ s₂) (h : Agree τ s₁ s₂)
    (hl : τ₁.lens = τ₂.lens → (meet τ₁ τ₂).lens = τ.lens)
    (hs : ∀ y ∈ interSlots τ₁.slots τ₂.slots, ∃ z ∈ τ.slots, 0 < y.2.2 ∧ y.1 = z.1 ∧
      z.2.1 ≤ y.2.1 ∧ y.2.1 + y.2.2 ≤ z.2.1 + z.2.2) :
    Agree (meetC τ₁ τ₂) s₁ s₂ := by
  refine hm.setSlots (fun y hy => ?_) (fun y hy => ?_)
  · split at hy <;> [skip; cases hy]
    rename_i he
    obtain ⟨z, hz, -, e, -, h₂⟩ := hs y hy
    rw [hl he, e]
    have := h.ok z hz
    omega
  · split at hy <;> [skip; cases hy]
    obtain ⟨z, hz, -, e, h₁, h₂⟩ := hs y hy
    exact agree_of_cover h.slots fun k h₃ h₄ => ⟨z, hz, e.symm, by omega, by omega⟩

theorem meet_lens_of {τ₁ τ₂ : T} (he : τ₁.lens = τ₂.lens) :
    (meet τ₁ τ₂).lens = τ₁.lens ∧ (meet τ₁ τ₂).lens = τ₂.lens := by
  simp only [meet, he, ↓reduceIte, and_self]

theorem meetC_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meetC τ₁ τ₂) s₁ s₂ :=
  meetC_of (meet_left h) h (fun he => (meet_lens_of he).1) fun y hy => by
    obtain ⟨x, hx, z, -, hi⟩ := mem_interSlots hy
    obtain ⟨h₀, e, -, h₁, h₂, -⟩ := mem_interSlot hi
    exact ⟨x, hx, h₀, e, h₁, h₂⟩

theorem meetC_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meetC τ₁ τ₂) s₁ s₂ :=
  meetC_of (meet_right h) h (fun he => (meet_lens_of he).2) fun y hy => by
    obtain ⟨x, -, z, hz, hi⟩ := mem_interSlots hy
    obtain ⟨h₀, -, e, -, -, h₁, h₂⟩ := mem_interSlot hi
    exact ⟨z, hz, h₀, e, h₁, h₂⟩

end Taint

/-- Taint tracking for ARMv7. -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.stepKM
  step_sound {τ τ' i s₁ s₂ s₁' s₂'} ha hs e₁ e₂ := by
    rcases Taint.stepKM_spec τ i with h | ⟨τ₀, a, b, h₀, h₁, h₂, hab⟩
    · rw [h] at hs; cases hs
    · rw [h₁] at hs; cases hs
      obtain ⟨h₃, h₄⟩ := Taint.step_sound (h₀.agree ha) h₂ e₁ e₂
      exact ⟨h₃, hab.agree h₄⟩
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet := Taint.meetC
  meet_left := Taint.meetC_left
  meet_right := Taint.meetC_right
  le := Taint.leC
  le_sound h := Taint.leC_sound h
  call τ := some (Taint.callStep τ)
  call_sound := Taint.call_sound
  ret τ := some τ
  ret_sound := Taint.ret_sound
  -- Frames are not analysed.
  push _ _ := none
  push_sound _ h := by cases h
  pop _ _ := none
  pop_sound _ h := by cases h

/-- The taint in which exactly the registers `rs` are public. -/
def Taint.ofRegs (rs : List Reg) : Taint.T := { regs := RegSet.ofList rs, flags := false }

theorem Taint.agree_ofRegs {rs : List Reg} {s₁ s₂ : State}
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : Taint.Agree (Taint.ofRegs rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp h := absurd h (Nat.lt_irrefl 0)
  argMem _ h := absurd h (Nat.not_lt_zero _)

end VG.Arm
