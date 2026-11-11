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
(`ras`). It keeps the window index of each frame's base (`fw`), so that after
a return, whose stack pointer the base analysis forgets as a call does, it
knows the stack pointer again as an offset into the innermost frame
(`spBase`), and stores through it after a call reach that frame's slots. The bytes of the window outside every writable region are equal in
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
  registers;
* the stack arguments (the argument area, `an` bytes from 8 above the stack
  pointer on entry): which of their bytes are public (`sa`), and which hold
  the address of a region (`sp`), so that a load of one through the stack
  pointer (`argOff`) gives a public value or a pointer. The code cannot
  write them: they are in no writable region (`aFree`), and above the window,
  which they do not wrap around into (`aTop`).
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
  /-- The window index of the base of each frame, innermost first. -/
  fw : List Nat := []
  /-- The length of the argument area: the stack arguments, from 8 bytes above
  the stack pointer on entry (above the return address). -/
  an : Nat := 0
  /-- `(o, n)`: the `n` bytes at offset `o` of the argument area are the same
  in both runs. -/
  sa : List (Nat × Nat) := []
  /-- `(o, i, k)`: the 8 bytes at offset `o` of the argument area hold the
  address of byte `k` of region `i`, in both runs. -/
  sp : List (Nat × Nat × Nat) := []
  deriving DecidableEq, Lean.ToExpr

/-- The base of the window. -/
def wb (s : State) (τ : FT) : Addr := s.gpr .rsp - BitVec.ofNat 64 τ.room

/-- The address of window index `j`. -/
def wa (s : State) (τ : FT) (j : Nat) : Addr := wb s τ + BitVec.ofNat 64 j

/-- The 8 bytes at window index `j`. -/
def raSlot (s : State) (τ : FT) (j : Nat) : Region := ⟨wa s τ j, 8⟩

/-- The address of byte `o` of the argument area: the stack pointer on entry
plus `8 + o`, as an index past the window. -/
def aa (s : State) (τ : FT) (o : Nat) : Addr := wa s τ (τ.room + τ.depth + 8 + o)

/-- What `τ` says of one state alone. -/
structure One (τ : FT) (s : State) : Prop where
  ub : ∀ p ∈ τ.ub, (s.gpr p.1).toNat ≤ p.2
  fl : ∀ a b, τ.fl = some (a, b) → s.cf = some (decide ((s.gpr a).toNat < (s.gpr b).toNat))
  mb : ∀ e ∈ τ.mb, s.mem.readW (byteAddr s e.1 e.2.1) 64 = (region s e.2.2.1).base + BitVec.ofNat 64 e.2.2.2
  sp : ∀ e ∈ τ.sp, s.mem.readW (aa s τ e.1) 64 = (region s e.2.1).base + BitVec.ofNat 64 e.2.2

/-- The bytes of the argument area that `sa` says are public are the same in
both runs. -/
def SaEq (τ : FT) (s₁ s₂ : State) : Prop :=
  ∀ e ∈ τ.sa, ∀ k, e.1 ≤ k → k < e.1 + e.2 → s₁.mem (aa s₁ τ k) = s₂.mem (aa s₂ τ k)

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
  fw : ∀ i (h : i < τ.fw.length), (region s₁ i).base = wa s₁ τ τ.fw[i]
  aTop : 0 < τ.an → (s₁.gpr .rsp).toNat + τ.depth + 8 + τ.an ≤ 2 ^ 64
  aFree : ∀ k < τ.an, ∀ r ∈ s₁.wr, ¬ r.Contains (aa s₁ τ k) 1
  saFit : ∀ e ∈ τ.sa, e.1 + e.2 ≤ τ.an
  saEq : SaEq τ s₁ s₂
  spFit : ∀ e ∈ τ.sp, e.1 + 8 ≤ τ.an

def Agree (τ : FT) (s₁ s₂ : State) : Prop := τ.ok = true → RInv τ s₁ s₂

/-- No knowledge. -/
def none' : FT := ⟨false, {regs := .empty, flags := false}, 0, 0, 0, [], [], [], none, [], [], 0, [], []⟩

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
  | .evStore m _ | .e5ExtractStore m _ _ => some (m, 32)
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

/-- The offset into the argument area of a memory operand `[rsp + disp]`,
if it is at or above the argument area. -/
def argOff (τ : FT) (m : MemOp) : Option Nat :=
  if m.base = .rsp ∧ m.index = none ∧ ((τ.depth + 8 : Nat) : Int) ≤ m.disp then
    some (m.disp.toNat - (τ.depth + 8))
  else none

/-- The `w` bytes at offset `o` of the argument area are the same in both runs. -/
def saPub (τ : FT) (o w : Nat) : Bool := τ.sa.any fun e => e.1 ≤ o && o + w ≤ e.1 + e.2

/-- What the analysis adds to the taint `t'` after a load from the argument
area: a public value, or a pointer into a region. -/
def argPost (τ : FT) (i : Instr) (t' : Taint.T) : Taint.T :=
  match i with
  | .mov d (.mem m) =>
    match argOff τ m with
    | some o =>
      let t'' := if saPub τ o 8 then { t' with regs := t'.regs.insert d } else t'
      match τ.sp.find? (·.1 == o) with
      | some e => { t'' with bases := (d, e.2.1, e.2.2) :: t''.bases }
      | none => t''
    | none => t'
  | .mov32 d (.mem m) =>
    match argOff τ m with
    | some o => if saPub τ o 4 then { t' with regs := t'.regs.insert d } else t'
    | none => t'
  | _ => t'

/-- The base taint after `i`. -/
def baseStep (τ : FT) (i : Instr) : Option Taint.T :=
  match special τ i with
  | some t' => some t'
  | none => (X86_64.taint.step τ.t i).map fun t' => argPost τ i (post τ i t')

/-- The flags after `i`: those of `cmp a, b` (64-bit), or nothing known. -/
def flOf : Instr → Option (Reg × Reg)
  | .alu .cmp a (.reg b) => some (a, b)
  | _ => none

def step (τ : FT) (i : Instr) : Option FT :=
  if τ.ok && !isa.writesSp i then
    match baseStep τ i with
    | some t' =>
      if t'.lens == τ.t.lens then
        some { τ with
          t := t'
          ub := (ubNew τ i).toList ++ ubKill τ.ub i
          fl := flOf i
          mb := mbAfter τ i }
      else none
    | none => none
  else none

def meet (τ₁ τ₂ : FT) : FT :=
  if τ₁.ok && τ₂.ok && τ₁.nfr == τ₂.nfr && τ₁.depth == τ₂.depth && τ₁.room == τ₂.room &&
      τ₁.ras == τ₂.ras && τ₁.t.lens == τ₂.t.lens && τ₁.fw == τ₂.fw && τ₁.an == τ₂.an then
    { τ₁ with
      t := Taint.meet τ₁.t τ₂.t
      sec := τ₁.sec ++ τ₂.sec
      ub := τ₁.ub.filterMap fun p => (ubOf τ₂.ub p.1).map fun n => (p.1, max p.2 n)
      fl := if τ₁.fl == τ₂.fl then τ₁.fl else none
      mb := τ₁.mb.filter (τ₂.mb.contains ·)
      sa := τ₁.sa.filter (τ₂.sa.contains ·)
      sp := τ₁.sp.filter (τ₂.sp.contains ·) }
  else none'

def le (τ σ : FT) : Bool :=
  !τ.ok || (σ.ok && τ.nfr == σ.nfr && τ.depth == σ.depth && τ.room == σ.room && τ.ras == σ.ras &&
    Taint.leK τ.t σ.t && σ.sec.all (τ.sec.contains ·) &&
    τ.ub.all (fun p => (ubOf σ.ub p.1).any (· ≤ p.2)) &&
    (τ.fl.isNone || τ.fl == σ.fl) && τ.mb.all (σ.mb.contains ·) && τ.fw == σ.fw && τ.an == σ.an &&
    τ.sa.all (σ.sa.contains ·) && τ.sp.all (σ.sp.contains ·))

/-- The base taint after a write of the stack pointer by a call or a return. -/
def killSp (t : Taint.T) : Taint.T := { t with bases := kill t .rsp, lo := .empty }

def callF (τ : FT) : Option FT :=
  if τ.ok && 8 ≤ τ.room then
    some ⟨true, killSp τ.t, τ.nfr, τ.depth + 8, τ.room - 8, τ.sec, (τ.room - 8) :: τ.ras,
      τ.ub.filter (·.1 != .rsp), none, τ.mb, τ.fw, τ.an, τ.sa, τ.sp⟩
  else none

/-- The stack pointer after a return, as an offset into the innermost frame
(region 0) if it is at or above that frame's base: the window index of the
stack pointer is then `room + 8`. -/
def spBase (τ : FT) : List (Reg × Nat × Nat) :=
  match τ.fw.head? with
  | some a => if a ≤ τ.room + 8 then [(.rsp, 0, τ.room + 8 - a)] else []
  | none => []

def retF (τ : FT) : Option FT :=
  if τ.ok && τ.ras.head? == some τ.room && 8 ≤ τ.depth then
    some ⟨true, { killSp τ.t with bases := spBase τ ++ kill τ.t .rsp }, τ.nfr, τ.depth - 8, τ.room + 8,
      τ.sec, τ.ras.tail, τ.ub.filter (·.1 != .rsp), none, τ.mb, τ.fw, τ.an, τ.sa, τ.sp⟩
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
        τ.ras, τ.ub.filter (·.1 != .rsp), none, τ.mb.map fun e => (e.1 + 1, e.2.1, e.2.2.1 + 1, e.2.2.2),
        (τ.room - b) :: τ.fw, τ.an, τ.sa, τ.sp.map fun e => (e.1, e.2.1 + 1, e.2.2)⟩
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
      let sp' := τ.sp.filterMap fun e => if e.2.1 = 0 then none else some (e.1, e.2.1 - 1, e.2.2)
      some ⟨true, shiftOut τ.t, τ.nfr - 1, τ.depth - b, τ.room + b, sec', τ.ras,
        τ.ub.filter (·.1 != .rsp), none, mb', τ.fw.tail, τ.an, τ.sa, sp'⟩
    else none
  | _ => none

/-! ## Evaluation by the kernel

The kernel evaluates `step`, `le` and `meet` at every instruction, hint and
join of a check (`VG.Taint.check`). `stepF`, `leF` and `meetF` are the same
functions (`ResidueTaintSound.lean` proves each equal to its model, so the
analysis and its results are the same) written for the kernel:

* `stepFn i` classifies the instruction `i` before the taint is substituted,
  as the base analysis's `Taint.stepKDFn` does, so that the kernel unfolds
  the matches on `i` once per instruction rather than once per check of it.
  Most instructions (`isPlain`) need none of what the analysis adds to the
  base analysis: their step is the base step (`fastFn`), with the bounds of
  the register they write dropped. Stores without an index register only
  need the pointers in slots (`fastStore`), and look for the slot of a
  public value with `mem3R`; loads (`mov r, [m]`) need `post` only when a
  slot holds a pointer (`fastLoad`); constants, `mul` and `mulx` only change
  bounds (`fastU`).
* `leF` compares lists of slots in one pass when one is a sublist of the
  other in order (`subl`), as a hint's taints usually are of the analysis's,
  and compares numbers with `Nat.beq`.
* `meetF` keeps the slots as they are when both sides have the same
  (`eqs3`), as the two branches of an `ite` often do.

As in `VG.KList`, the functions written with `List.rec`, which Lean's
compiler does not compile, are `@[implemented_by]` the library's functions
they equal, for the hints computed in compiled code (`keep_for%`,
`taint_decide`); the kernel checks what those compute. -/

/-- An instruction's transfer function, independent of the incoming taint
(`Taint.Step` for the residue analysis). -/
structure RStep where
  run : FT → Option FT

/-- Instructions whose step is the base analysis's alone: no store, no load
of a pointer from a slot (`post`) or of the argument area (`argPost`: a load
`[rsp + disp]` without an index), no bound (`ubNew`) or flags (`flOf`), no
zeroing idiom, and no write of registers other than `Taint.dstOf`'s. -/
def isPlain : Instr → Bool
  | .store .. | .store32 .. | .store8 .. | .store16 .. | .movdquStore .. | .vmovdquStore ..
  | .vmovdqu32Store .. | .evStore .. | .e5ExtractStore .. | .stmxcsr _ | .kStore .. | .kStore8 .. => false
  | .mov _ (.mem _) | .mov _ (.imm _) | .mov32 _ (.imm _) => false
  | .mov32 _ (.mem m) => !(regEq m.base .rsp && m.index.isNone)
  | .alu .and _ (.imm _) | .alu32 .and _ (.imm _) => false
  | .alu .xor d (.reg d') | .alu32 .xor d (.reg d') => d != d'
  | .alu .cmp _ (.reg _) => false
  | .xop (.bin .pxor _ _) => false
  | .cmov .. | .mul _ | .mulx .. => false
  | .push _ | .pop .. | .alloc _ | .free _ | .callr _ => false
  | _ => true

/-- `ubKill ub i`, for an `i` that writes the register `d` alone. -/
def ubDrop (d : Option Reg) (ub : List (Reg × Nat)) : List (Reg × Nat) :=
  match ub, d with
  | [], _ => []
  | ub, some d => KList.filter (fun p => !regEq p.1 d) ub
  | ub, none => ub

def natsEqC (a b : List Nat) : Bool := a == b

/-- `a == b`, with `List.rec` and `Nat.beq`. -/
@[implemented_by natsEqC] def natsEq (a b : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.casesOn (motive := fun _ => Bool) b true fun _ _ => false)
    (fun x _ ih b => List.casesOn (motive := fun _ => Bool) b false fun y b' => Nat.beq x y && ih b') a b

/-- `step` of an instruction `isPlain` says is, whose base step is `b` and
which writes the register `d`. -/
def fastFn (b : Taint.Step) (d : Option Reg) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, mb, fw, an, sa, sp⟩ =>
    bif ok then
      match b.run t with
      | some t' =>
        bif natsEq t'.lens t.lens then
          some ⟨true, t', nfr, depth, room, sec, ras, ubDrop d ub, none, mb, fw, an, sa, sp⟩
        else none
      | none => none
    else none⟩

/-- `mbAfter` of a store of `w` bytes at `m`, from the register `src` if a
64-bit store. -/
def mbStore (τ : FT) (m : MemOp) (w : Nat) (src : Option Reg) : List (Nat × Nat × Nat × Nat) :=
  match storeRange τ m w with
  | some (ri, lo, hi) =>
    match src with
    | some r =>
      match τ.t.bases.find? (·.1 == r), addrOf τ.t m with
      | some (_, pj, pk), some _ => (ri, lo, pj, pk) :: mbKill τ.mb ri lo hi
      | _, _ => mbKill τ.mb ri lo hi
    | none => mbKill τ.mb ri lo hi
  | none => []

def mem3RC (i d w : Nat) (l : List (Nat × Nat × Nat)) : Bool := Taint.mem3 (i, d, w) l

/-- `Taint.mem3 (i, d, w) l`, with `List.rec` and `Bool.rec`, comparing the
offset first: the kernel evaluates it about twice as fast (a store of a
public value scans every slot for it, and a frame has hundreds). -/
@[implemented_by mem3RC] def mem3R (i d w : Nat) (l : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun b _ ih =>
    Bool.rec ih (Bool.rec ih (Bool.rec ih true (Nat.beq w b.2.2)) (Nat.beq i b.1)) (Nat.beq d b.2.1)) l

/-- `Taint.storeSlotsKD`, with `mem3R`. -/
def storeSlotsR (τ : Taint.T) (m : MemOp) (w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match Taint.addrOfK τ m with
  | some (i, d) =>
    bif Nat.ble (d + w) (τ.lens.getD i 0) then
      bif p then (bif mem3R i d w τ.slots then τ.slots else (i, d, w) :: τ.slots)
      else VG.Taint.filterKeep (fun sl => !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 ||
        Nat.ble (sl.2.1 + sl.2.2) d) τ.slots
    else bif p then τ.slots else []
  | none => bif p then τ.slots else []

/-- The base step of a store of `w` bytes of `r` at `m` (`Taint.stepKDFn`'s),
with `storeSlotsR`. -/
def storeR (m : MemOp) (w : Nat) (r : Reg) : Taint.Step := ⟨fun τ =>
  match τ with
  | ⟨rg, f, l, b, _, lo, x⟩ => bif memPub τ m then some ⟨rg, f, l, b, storeSlotsR τ m w (pub τ r), lo, x⟩ else none⟩

/-- `step` of a store without an index register, whose base step is `b`. -/
def fastStore (b : Taint.Step) (m : MemOp) (w : Nat) (src : Option Reg) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, _, fw, an, sa, sp⟩ =>
    bif ok then
      match b.run t with
      | some t' =>
        bif natsEq t'.lens t.lens then
          some ⟨true, t', nfr, depth, room, sec, ras, ub, none, mbStore τ m w src, fw, an, sa, sp⟩
        else none
      | none => none
    else none⟩

/-- `step` of an instruction that adds nothing to the base step `b` but the
bounds `u` gives (`ubNew` and `ubKill`). -/
def fastU (b : Taint.Step) (u : List (Reg × Nat) → List (Reg × Nat)) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, mb, fw⟩ =>
    bif ok then
      match b.run t with
      | some t' =>
        bif natsEq t'.lens t.lens then some ⟨true, t', nfr, depth, room, sec, ras, u ub, none, mb, fw⟩
        else none
      | none => none
    else none⟩

/-- `ubKill ub i`, for an `i` that writes the registers `a` and `b` alone
(`mul`, `mulx`). -/
def ubDrop2 (a b : Reg) (ub : List (Reg × Nat)) : List (Reg × Nat) :=
  match ub with
  | [] => []
  | ub => KList.filter (fun p => !(regEq p.1 a || regEq p.1 b)) ub

/-- `step` of a load `i` = `mov d, [m]`, whose base step is `b`: `post` only
if a slot holds a pointer (`mb`), and nothing else but the base step. -/
def fastLoad (b : Taint.Step) (d : Reg) (i : Instr) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, mb, fw⟩ =>
    bif ok then
      match b.run t with
      | some t' =>
        bif natsEq t'.lens t.lens then
          some ⟨true, (match mb with | [] => t' | _ => post τ i t'), nfr, depth, room, sec, ras,
            ubDrop (some d) ub, none, mb, fw⟩
        else none
      | none => none
    else none⟩

/-- `step · i`, classifying `i` first. -/
def stepFn (i : Instr) : RStep :=
  bif isa.writesSp i then ⟨fun _ => none⟩
  else bif isPlain i then fastFn (Taint.stepKDFn i) (Taint.dstOf i)
  else match i with
    | .store m r => bif m.index.isNone then fastStore (storeR m 8 r) m 8 (some r) else ⟨(step · i)⟩
    | .store32 m r => bif m.index.isNone then fastStore (storeR m 4 r) m 4 none else ⟨(step · i)⟩
    | .store8 m r => bif m.index.isNone then fastStore (storeR m 1 r) m 1 none else ⟨(step · i)⟩
    | .store16 m r => bif m.index.isNone then fastStore (storeR m 2 r) m 2 none else ⟨(step · i)⟩
    | .mov d (.mem _) => fastLoad (Taint.stepKDFn i) d i
    | .mov d (.imm v) =>
      fastU (Taint.stepKDFn i) fun ub => bif v.msb then ubDrop (some d) ub else (d, v.toNat) :: ubDrop (some d) ub
    | .mov32 d (.imm v) => fastU (Taint.stepKDFn i) fun ub => (d, v.toNat) :: ubDrop (some d) ub
    | .mul _ => fastU (Taint.stepKDFn i) (ubDrop2 .rax .rdx)
    | .mulx hi lo _ => fastU (Taint.stepKDFn i) (ubDrop2 hi lo)
    | _ => ⟨(step · i)⟩

/-- `step`, for the kernel (`stepF_eq`). -/
def stepF (τ : FT) (i : Instr) : Option FT := (stepFn i).run τ

/-- `a = b`, for pairs, slots and pointers in slots. -/
def eq2 (a b : Nat × Nat) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2

def eq3 (a b : Nat × Nat × Nat) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2

def eq4 (a b : Nat × Nat × Nat × Nat) : Bool :=
  Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2.1 b.2.2.1 && Nat.beq a.2.2.2 b.2.2.2

def sublC : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if eq3 a b then sublC as bs else sublC (a :: as) bs

/-- `as` is a sublist of `bs` (in order), in one pass over both. -/
@[implemented_by sublC] def subl (as bs : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool)
    (fun as => List.casesOn (motive := fun _ => Bool) as true fun _ _ => false)
    (fun b _ ih as => List.casesOn (motive := fun _ => Bool) as true fun a as' =>
      bif eq3 a b then ih as' else ih as) bs as

/-- `as.all (bs.contains ·)`, in one pass if `as` is a sublist of `bs`. -/
def slotsLe (as bs : List (Nat × Nat × Nat)) : Bool := subl as bs || KList.all as (mem3 · bs)

/-- `Taint.leK`, with `slotsLe`. -/
def leKF (τ σ : Taint.T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && natsEq τ.lens σ.lens &&
    KList.all τ.bases (memB · σ.bases) && slotsLe τ.slots σ.slots && τ.lo.subset σ.lo &&
    τ.xregs.subset σ.xregs

/-- `ubOf`, with `KList` and `regEq`. -/
def ubOfK (l : List (Reg × Nat)) (r : Reg) : Option Nat := (KList.find? (fun p => regEq p.1 r) l).map (·.2)

/-- `le`, for the kernel (`leF_eq`). -/
def leF (τ σ : FT) : Bool :=
  !τ.ok || (σ.ok && Nat.beq τ.nfr σ.nfr && Nat.beq τ.depth σ.depth && Nat.beq τ.room σ.room &&
    natsEq τ.ras σ.ras && leKF τ.t σ.t && KList.all σ.sec (fun p => KList.any τ.sec (eq2 p)) &&
    KList.all τ.ub (fun p => (ubOfK σ.ub p.1).any (Nat.ble · p.2)) &&
    (τ.fl.isNone || τ.fl == σ.fl) && KList.all τ.mb (fun e => KList.any σ.mb (eq4 e)) && natsEq τ.fw σ.fw &&
    Nat.beq τ.an σ.an && KList.all τ.sa (fun e => KList.any σ.sa (eq2 e)) && KList.all τ.sp (mem3 · σ.sp))

def eqs3C (as bs : List (Nat × Nat × Nat)) : Bool := as == bs

/-- `as = bs`, for slots. -/
@[implemented_by eqs3C] def eqs3 (as bs : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool)
    (fun bs => List.casesOn (motive := fun _ => Bool) bs true fun _ _ => false)
    (fun a _ ih bs => List.casesOn (motive := fun _ => Bool) bs false fun b bs' => eq3 a b && ih bs') as bs

/-- `Taint.meet`, keeping the slots as they are when both sides have the same. -/
def meetT (τ₁ τ₂ : Taint.T) : Taint.T :=
  match τ₁, τ₂ with
  | ⟨r₁, f₁, l₁, b₁, s₁, lo₁, x₁⟩, ⟨r₂, f₂, l₂, b₂, s₂, lo₂, x₂⟩ =>
    bif natsEq l₁ l₂ then
      ⟨r₁.inter r₂, f₁ && f₂, l₁, KList.filter (memB · b₂) b₁,
        bif eqs3 s₁ s₂ then s₁ else KList.filter (mem3 · s₂) s₁, lo₁.inter lo₂, x₁.inter x₂⟩
    else ⟨r₁.inter r₂, f₁ && f₂, [], KList.filter (memB · b₂) b₁, [], lo₁.inter lo₂, x₁.inter x₂⟩

/-- `meet`, for the kernel (`meetF_eq`). -/
def meetF (τ₁ τ₂ : FT) : FT :=
  bif τ₁.ok && τ₂.ok && Nat.beq τ₁.nfr τ₂.nfr && Nat.beq τ₁.depth τ₂.depth && Nat.beq τ₁.room τ₂.room &&
      natsEq τ₁.ras τ₂.ras && natsEq τ₁.t.lens τ₂.t.lens && natsEq τ₁.fw τ₂.fw && Nat.beq τ₁.an τ₂.an then
    { τ₁ with
      t := meetT τ₁.t τ₂.t
      sec := τ₁.sec ++ τ₂.sec
      ub := τ₁.ub.filterMap fun p => (ubOfK τ₂.ub p.1).map fun n => (p.1, max p.2 n)
      fl := if τ₁.fl == τ₂.fl then τ₁.fl else none
      mb := KList.filter (fun e => KList.any τ₂.mb (eq4 e)) τ₁.mb
      sa := KList.filter (fun e => KList.any τ₂.sa (eq2 e)) τ₁.sa
      sp := KList.filter (mem3 · τ₂.sp) τ₁.sp }
  else none'

end VG.X86_64.RTaint
