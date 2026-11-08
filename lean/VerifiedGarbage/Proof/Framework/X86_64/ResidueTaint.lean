module

public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# Taint tracking through stack frames, for returning without residue (x86-64)

`rtaint` is the x86-64 taint analysis (`X86_64.taint`) extended to the stack
a function uses: the `stack` bytes below the stack pointer on entry (the
*window*). It follows the frames code allocates (`alloc` and `free`; frames
of pushed registers are not handled) as writable regions at the head of `wr`,
whose public bytes the base analysis tracks as slots, and the calls and
returns of the code, whose return addresses it keeps apart from the frames
(`ras`). The bytes of the window outside every writable region are equal in
both runs but those listed in `sec` (window indices from its base, the stack
pointer on entry minus `stack`): when a frame is freed, its bytes that are
not public are added to `sec`. So at the end of a function, the bytes of its
window that may differ between two runs are those `sec` lists: those its
code must zero to leave no residue.

Instructions are the base analysis's (`X86_64.taint.step`), with the same
soundness proof, and must not write the stack pointer; `ResidueTaintSound.lean`
proves the rest. On top of it, the analysis knows:

* upper bounds of registers (`ub`), from constants, `and` with a constant,
  and `cmp x, d; cmovb d, x`, which keeps the bound of `d`;
* which regions an indexed store may reach: one whose base register points
  into a region and whose index register is bounded writes only within
  `[lo, hi)` of that region, and leaves its other slots public;
* pointers kept in public slots (`mb`): a 64-bit store of a register holding
  an address in a region, reloaded later, holds it again;
* zeroing idioms (`xor r, r`, `pxor x, x`) and vector stores of public
  registers.
-/

@[expose] public section

namespace VG.X86_64.RTaint

open VG.X86_64 VG.X86_64.Taint

/-! ## Intervals of window indices -/

/-- Index `j` is in one of the intervals `(lo, n)` of `l`. -/
def InSec (l : List (Nat × Nat)) (j : Nat) : Prop := ∃ p ∈ l, p.1 ≤ j ∧ j < p.1 + p.2

/-- `[a, a + n)` minus `[c, c + m)`, as at most two intervals. -/
def sub1 (c m : Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  let a := p.1
  let e := p.1 + p.2
  (if a < min e c then [(a, min e c - a)] else []) ++
    (if max a (c + m) < e then [(max a (c + m), e - max a (c + m))] else [])

/-- The intervals of `ps` minus every interval of `l`. -/
def gaps (l : List (Nat × Nat)) (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  l.foldl (fun acc q => acc.flatMap (sub1 q.1 q.2)) ps

theorem mem_sub1 {c m j : Nat} {p : Nat × Nat} :
    (∃ q ∈ sub1 c m p, q.1 ≤ j ∧ j < q.1 + q.2) ↔ (p.1 ≤ j ∧ j < p.1 + p.2 ∧ ¬ (c ≤ j ∧ j < c + m)) := by
  simp only [sub1, List.mem_append]
  constructor
  · rintro ⟨q, hq, h₁, h₂⟩
    rcases hq with hq | hq <;> split at hq <;> simp at hq <;> subst hq <;> simp at h₁ h₂ <;> omega
  · rintro ⟨h₁, h₂, h₃⟩
    by_cases hc : j < c
    · refine ⟨(p.1, min (p.1 + p.2) c - p.1), .inl ?_, by simp; omega, by simp; omega⟩
      simp only [show p.1 < min (p.1 + p.2) c by omega, ↓reduceIte, List.mem_singleton]
    · refine ⟨(max p.1 (c + m), p.1 + p.2 - max p.1 (c + m)), .inr ?_, by simp; omega, by simp; omega⟩
      simp only [show max p.1 (c + m) < p.1 + p.2 by omega, ↓reduceIte, List.mem_singleton]

theorem mem_gaps {j : Nat} : ∀ (l ps : List (Nat × Nat)),
    InSec (gaps l ps) j ↔ InSec ps j ∧ ¬ InSec l j
  | [], ps => by simp [gaps, InSec]
  | q :: l, ps => by
    show InSec (gaps l (ps.flatMap (sub1 q.1 q.2))) j ↔ _
    rw [mem_gaps l]
    simp only [InSec, List.mem_flatMap, List.mem_cons]
    constructor
    · rintro ⟨⟨r, ⟨p, hp, hr⟩, h⟩, hn⟩
      have := mem_sub1.mp ⟨r, hr, h⟩
      exact ⟨⟨p, hp, this.1, this.2.1⟩, fun ⟨p', hp', h'⟩ => by
        rcases hp' with rfl | hp'
        · exact this.2.2 h'
        · exact hn ⟨p', hp', h'⟩⟩
    · rintro ⟨⟨p, hp, h⟩, hn⟩
      obtain ⟨r, hr, h'⟩ := mem_sub1.mpr ⟨h.1, h.2, fun h' => hn ⟨q, .inl rfl, h'⟩⟩
      exact ⟨⟨r, ⟨p, hp, hr⟩, h'⟩, fun ⟨p', hp', h'⟩ => hn ⟨p', .inr hp', h'⟩⟩

/-! ## The domain -/

structure FT where
  /-- `false`: nothing is known (`meet` of incompatible taints). -/
  ok : Bool
  t : Taint.T
  /-- How many of the writable regions, at their head, are frames. -/
  nfr : Nat
  /-- The stack pointer on entry minus the current one. -/
  depth : Nat
  /-- The bytes of the window below the current stack pointer. -/
  room : Nat
  /-- Window indices that may differ between the runs, outside writable regions. -/
  sec : List (Nat × Nat)
  /-- Window indices of the return addresses of the calls in progress, innermost first. -/
  ras : List Nat
  /-- Upper bounds of registers' values, in both runs. -/
  ub : List (Reg × Nat) := []
  /-- The flags are those of `cmp a, b` (64-bit), in both runs. -/
  fl : Option (Reg × Reg) := none
  /-- `(i, d, j, k)`: the 8 bytes at offset `d` of region `i` hold the address
  of byte `k` of region `j`, in both runs. -/
  mb : List (Nat × Nat × Nat × Nat) := []
  deriving DecidableEq, Lean.ToExpr

/-- The base of the window. -/
def wb (s : State) (τ : FT) : Addr := s.gpr .rsp - BitVec.ofNat 64 τ.room

/-- The address of window index `j`. -/
def wa (s : State) (τ : FT) (j : Nat) : Addr := wb s τ + BitVec.ofNat 64 j

/-- The 8 bytes at window index `j`. -/
def raSlot (s : State) (τ : FT) (j : Nat) : Region := ⟨wa s τ j, 8⟩

/-- What `τ` says of one state alone. -/
structure One (τ : FT) (s : State) : Prop where
  ub : ∀ p ∈ τ.ub, (s.gpr p.1).toNat ≤ p.2
  fl : ∀ a b, τ.fl = some (a, b) → s.cf = some (decide ((s.gpr a).toNat < (s.gpr b).toNat))
  mb : ∀ e ∈ τ.mb, s.mem.readW (byteAddr s e.1 e.2.1) 64 = (region s e.2.2.1).base + BitVec.ofNat 64 e.2.2.2

structure RInv (τ : FT) (s₁ s₂ : State) : Prop where
  base : Taint.Agree τ.t s₁ s₂
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  unk : s₁.unknowns = s₂.unknowns
  wr : s₁.wr = s₂.wr
  lens : τ.t.lens = [] → s₁.wr = []
  nfr : τ.nfr ≤ s₁.wr.length
  room : τ.room ≤ (s₁.gpr .rsp).toNat
  top : (s₁.gpr .rsp).toNat + τ.depth < 2 ^ 64
  frames : ∀ i < τ.nfr, Region.Sub (region s₁ i) ⟨s₁.gpr .rsp, τ.depth⟩
  others : ∀ i, τ.nfr ≤ i → i < s₁.wr.length →
    (region s₁ i).Disjoint ⟨wb s₁ τ, τ.room + τ.depth⟩
  rasIn : ∀ j ∈ τ.ras, τ.room ≤ j ∧ j + 8 ≤ τ.room + τ.depth
  rasSorted : τ.ras.Pairwise fun a b => a + 8 ≤ b
  rasFr : ∀ j ∈ τ.ras, ∀ i < τ.nfr, (region s₁ i).Disjoint (raSlot s₁ τ j)
  dead : ∀ j < τ.room + τ.depth, ¬ InSec τ.sec j →
    (∀ r ∈ s₁.wr, ¬ r.Contains (wa s₁ τ j) 1) → s₁.mem (wa s₁ τ j) = s₂.mem (wa s₂ τ j)
  mbFit : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0
  one₁ : One τ s₁
  one₂ : One τ s₂

def Agree (τ : FT) (s₁ s₂ : State) : Prop := τ.ok = true → RInv τ s₁ s₂

/-- No knowledge. -/
def none' : FT := ⟨false, {regs := .empty, flags := false}, 0, 0, 0, [], [], [], none, []⟩

/-! ## Transfer functions -/

/-- The bound of `r`, if known. -/
def ubOf (l : List (Reg × Nat)) (r : Reg) : Option Nat := (l.find? (·.1 == r)).map (·.2)

/-- Bounds after an instruction that writes the registers `clobbers` says. -/
def ubKill (l : List (Reg × Nat)) (i : Instr) : List (Reg × Nat) := l.filter fun p => !Taint.clobbers i p.1

/-- The bound an instruction gives the register it writes, if any. -/
def ubNew (τ : FT) : Instr → Option (Reg × Nat)
  | .mov d (.imm v) => if v.msb then none else some (d, v.toNat)
  | .mov32 d (.imm v) => some (d, v.toNat)
  | .alu .and d (.imm v) => if v.msb then none else some (d, v.toNat)
  | .alu32 .and d (.imm v) => some (d, v.toNat)
  | .cmov .b d (.reg x) =>
    if τ.fl == some (x, d) then (ubOf τ.ub d).map (d, ·) else none
  | _ => none

/-- The memory an instruction may write: its operand and width. -/
def storeW : Instr → Option (MemOp × Nat)
  | .store m _ => some (m, 8)
  | .store32 m _ => some (m, 4)
  | .store8 m _ => some (m, 1)
  | .store16 m _ => some (m, 2)
  | .movdquStore m _ => some (m, 16)
  | .vmovdquStore .l128 m _ => some (m, 16)
  | .vmovdquStore .l256 m _ => some (m, 32)
  | .vmovdqu32Store m _ => some (m, 64)
  | .evStore m _ => some (m, 32)
  | .stmxcsr m => some (m, 4)
  | _ => none

/-- Whether an instruction may write memory: those of `storeW`, and the
masked stores. -/
def writesMem (i : Instr) : Bool :=
  (storeW i).isSome || match i with
    | .kStore .. | .kStore8 .. => true
    | _ => false

/-- The bytes `[lo, hi)` of region `ri` that a store through `m` of `w` bytes
may write, if its base register points into region `ri` and its index
register is bounded. -/
def idxRange (τ : FT) (m : MemOp) (w : Nat) : Option (Nat × Nat × Nat) :=
  match m.index with
  | some x =>
    match τ.t.bases.find? (·.1 == m.base), ubOf τ.ub x with
    | some (_, ri, k), some B =>
      if m.scale = 1 ∧ 0 ≤ m.disp ∧ k + m.disp.toNat + B + w ≤ τ.t.lens.getD ri 0 then
        some (ri, k + m.disp.toNat, k + m.disp.toNat + B + w)
      else none
    | _, _ => none
  | none => none

/-- The bytes `[lo, hi)` of region `ri` a store may write, if known. -/
def storeRange (τ : FT) (m : MemOp) (w : Nat) : Option (Nat × Nat × Nat) :=
  match addrOf τ.t m with
  | some (ri, d) => if d + w ≤ τ.t.lens.getD ri 0 then some (ri, d, d + w) else none
  | none => idxRange τ m w

def mbKill (mb : List (Nat × Nat × Nat × Nat)) (ri lo hi : Nat) : List (Nat × Nat × Nat × Nat) :=
  mb.filter fun e => e.1 != ri || e.2.1 + 8 ≤ lo || hi ≤ e.2.1

def mbAfter (τ : FT) (i : Instr) : List (Nat × Nat × Nat × Nat) :=
  match storeW i with
  | some (m, w) =>
    match storeRange τ m w with
    | some (ri, lo, hi) =>
      let kept := mbKill τ.mb ri lo hi
      match i with
      | .store _ r =>
        match τ.t.bases.find? (·.1 == r), addrOf τ.t m with
        | some (_, pj, pk), some _ => (ri, lo, pj, pk) :: kept
        | _, _ => kept
      | _ => kept
    | none => []
  | none => if writesMem i then [] else τ.mb

/-- The value a store writes is public: a register (or its low bytes) the
base analysis says is, or an SSE register `xregs` says is. -/
def storePub (t : Taint.T) : Instr → Bool
  | .store _ r | .store8 _ r => pub t r
  | .movdquStore _ x => xpub t x
  | _ => false

/-- The base taint after a store whose index register is bounded: only the
slots of `[lo, hi)` of region `ri` are dropped (none if the value is public). -/
def idxStore (t : Taint.T) (ri lo hi : Nat) (p : Bool) : Taint.T :=
  { t with slots := if p then t.slots else t.slots.filter fun sl => sl.1 != ri || hi ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ lo }

/-- The base taint after a store the base analysis is less precise about:
an indexed store whose index register is bounded, or a vector store of a
public register. -/
def special (τ : FT) (i : Instr) : Option Taint.T :=
  match i with
  | .store m _ | .store8 m _ | .movdquStore m _ =>
    match m.index, storeW i with
    | some _, some (_, w) =>
      match idxRange τ m w with
      | some (ri, lo, hi) => if memPub τ.t m then some (idxStore τ.t ri lo hi (storePub τ.t i)) else none
      | none => none
    | none, _ =>
      match i with
      | .movdquStore m x => if xpub τ.t x then storeStep τ.t m 16 true else none
      | _ => none
    | _, _ => none
  | _ => none

/-- What the analysis adds to the base analysis's taint `t'` after `i`:
zeroing idioms, and loads of pointers from public slots. -/
def post (τ : FT) (i : Instr) (t' : Taint.T) : Taint.T :=
  match i with
  | .alu .xor d (.reg d') | .alu32 .xor d (.reg d') =>
    if d == d' then { t' with regs := t'.regs.insert d } else t'
  | .xop (.bin .pxor x x') => if x == x' then { t' with xregs := t'.xregs.insert x } else t'
  | .mov d (.mem m) =>
    match addrOf τ.t m with
    | some (ri, o) =>
      match τ.mb.find? (fun e => e.1 == ri && e.2.1 == o) with
      | some e => { t' with bases := (d, e.2.2.1, e.2.2.2) :: t'.bases }
      | none => t'
    | none => t'
  | _ => t'

/-- The base taint after `i`. -/
def baseStep (τ : FT) (i : Instr) : Option Taint.T :=
  match special τ i with
  | some t' => some t'
  | none => (X86_64.taint.step τ.t i).map (post τ i)

def step (τ : FT) (i : Instr) : Option FT :=
  if τ.ok && !isa.writesSp i then
    match baseStep τ i with
    | some t' =>
      if t'.lens == τ.t.lens then
        some { τ with
          t := t'
          ub := (ubNew τ i).toList ++ ubKill τ.ub i
          fl := match i with
            | .alu .cmp a (.reg b) => some (a, b)
            | _ => none
          mb := mbAfter τ i }
      else none
    | none => none
  else none

def meet (τ₁ τ₂ : FT) : FT :=
  if τ₁.ok && τ₂.ok && τ₁.nfr == τ₂.nfr && τ₁.depth == τ₂.depth && τ₁.room == τ₂.room &&
      τ₁.ras == τ₂.ras && τ₁.t.lens == τ₂.t.lens then
    { τ₁ with
      t := Taint.meet τ₁.t τ₂.t
      sec := τ₁.sec ++ τ₂.sec
      ub := τ₁.ub.filterMap fun p => (ubOf τ₂.ub p.1).map fun n => (p.1, max p.2 n)
      fl := if τ₁.fl == τ₂.fl then τ₁.fl else none
      mb := τ₁.mb.filter (τ₂.mb.contains ·) }
  else none'

def le (τ σ : FT) : Bool :=
  !τ.ok || (σ.ok && τ.nfr == σ.nfr && τ.depth == σ.depth && τ.room == σ.room && τ.ras == σ.ras &&
    Taint.leK τ.t σ.t && σ.sec.all (τ.sec.contains ·) &&
    τ.ub.all (fun p => (ubOf σ.ub p.1).any (· ≤ p.2)) &&
    (τ.fl.isNone || τ.fl == σ.fl) && τ.mb.all (σ.mb.contains ·))

/-- The base taint after a write of the stack pointer by a call or a return. -/
def killSp (t : Taint.T) : Taint.T := { t with bases := kill t .rsp, lo := .empty }

def callF (τ : FT) : Option FT :=
  if τ.ok && 8 ≤ τ.room then
    some ⟨true, killSp τ.t, τ.nfr, τ.depth + 8, τ.room - 8, τ.sec, (τ.room - 8) :: τ.ras,
      τ.ub.filter (·.1 != .rsp), none, τ.mb⟩
  else none

def retF (τ : FT) : Option FT :=
  if τ.ok && τ.ras.head? == some τ.room && 8 ≤ τ.depth then
    some ⟨true, killSp τ.t, τ.nfr, τ.depth - 8, τ.room + 8, τ.sec, τ.ras.tail,
      τ.ub.filter (·.1 != .rsp), none, τ.mb⟩
  else none

/-- The base taint with a frame of `b` bytes pushed at the head of the
writable regions, whose public bytes are `fs` (slots of region 0). -/
def shiftIn (t : Taint.T) (b : Nat) (fs : List (Nat × Nat × Nat)) : Taint.T :=
  { t with
    lens := b :: t.lens
    bases := (.rsp, 0, 0) :: (kill t .rsp).map fun p => (p.1, p.2.1 + 1, p.2.2)
    slots := fs ++ t.slots.map fun sl => (sl.1 + 1, sl.2)
    lo := .empty }

/-- The base taint with the frame at the head of the writable regions popped. -/
def shiftOut (t : Taint.T) : Taint.T :=
  { t with
    lens := t.lens.tail
    bases := (kill t .rsp).filterMap fun p => if p.2.1 = 0 then none else some (p.1, p.2.1 - 1, p.2.2)
    slots := t.slots.filterMap fun sl => if sl.1 = 0 then none else some (sl.1 - 1, sl.2)
    lo := .empty }

/-- `[a, a + n)` cut into pieces of at most 16 bytes, from `a` up (`fuel` pieces at most). -/
def split16 : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | _ + 1, _, 0 => []
  | f + 1, a, n + 1 => if n + 1 ≤ 16 then [(a, n + 1)] else (a, 16) :: split16 f (a + 16) (n + 1 - 16)

/-- The public bytes of a new frame of `b` bytes at window index `a`, as slots
of region 0 of at most 16 bytes (the base analysis drops a whole slot when a
secret is stored into any of its bytes). -/
def newSlots (sec : List (Nat × Nat)) (a b : Nat) : List (Nat × Nat × Nat) :=
  ((gaps sec [(a, b)]).flatMap fun p => split16 (p.2 / 16 + 1) p.1 p.2).map fun p => (0, p.1 - a, p.2)

def pushF (τ : FT) : Instr → Option FT
  | .alloc b =>
    if τ.ok && 0 < b && b < 4096 && b % 8 == 0 && b ≤ τ.room then
      some ⟨true, shiftIn τ.t b (newSlots τ.sec (τ.room - b) b), τ.nfr + 1, τ.depth + b, τ.room - b, τ.sec,
        τ.ras, τ.ub.filter (·.1 != .rsp), none, τ.mb.map fun e => (e.1 + 1, e.2.1, e.2.2.1 + 1, e.2.2.2)⟩
    else none
  | _ => none

/-- The window intervals of the public slots of region 0 of a frame at window index `a`. -/
def frameSlots (t : Taint.T) (a : Nat) : List (Nat × Nat) :=
  t.slots.filterMap fun sl => if sl.1 = 0 then some (a + sl.2.1, sl.2.2) else none

def popF (τ : FT) : Instr → Option FT
  | .free b =>
    if τ.ok && 1 ≤ τ.nfr && τ.t.lens.head? == some b && b ≤ τ.depth && τ.ras.all (τ.room + b ≤ ·) then
      let sec' := τ.sec ++ gaps (frameSlots τ.t τ.room) [(τ.room, b)]
      let mb' := τ.mb.filterMap fun e =>
        if e.1 = 0 ∨ e.2.2.1 = 0 then none else some (e.1 - 1, e.2.1, e.2.2.1 - 1, e.2.2.2)
      some ⟨true, shiftOut τ.t, τ.nfr - 1, τ.depth - b, τ.room + b, sec', τ.ras,
        τ.ub.filter (·.1 != .rsp), none, mb'⟩
    else none
  | _ => none

end VG.X86_64.RTaint
