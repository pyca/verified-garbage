import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.Slots
import VerifiedGarbage.Proof.Framework.NativeHintOps
import VerifiedGarbage.TCB.X86.Target

/-! Executable x86 taint operations, separated from their soundness proofs. -/
namespace VG.NativeHints.X86
open VG.X86

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

structure T where
  regs : RegSet Reg
  flags : Bool
  /-- Lower bounds on the lengths of the writable regions `s.wr`, in order (`0` if
  unknown); `[]` if nothing is known about the regions. -/
  lens : List Nat := []
  /-- `(r, i, k)`: `r + k` is the base address of writable region `i`. -/
  bases : List (Reg × Nat × Nat) := []
  /-- The public bytes of the writable regions. -/
  slots : Slots := .empty
  /-- `(j, o, i)`: the word at offset `o` of writable region `j` is the base address
  of writable region `i`. -/
  wbases : List (Nat × Nat × Nat) := []
  /-- The first `argLen` bytes at `esp` are never written, and those from `esp + 4` on are public. -/
  argLen : Nat := 0
  /-- `(o, i)`: the word at `o` bytes above the stack pointer on entry is the base address
  of writable region `i`. -/
  argBases : List (Nat × Nat) := []
  /-- The stack between `esp` and the stack pointer on entry, from `esp` up: a frame of
  `n` bytes (`some n`), which is one of the writable regions, or a return address (`none`). -/
  stk : List (Option Nat) := []
  /-- The `room` bytes below the stack pointer on entry lie outside every writable region
  but the frames of `stk`. -/
  room : Nat := 0
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

/-- Writable region `i`. -/
def region (s : State) (i : Nat) : Region := s.wr.getD i ⟨0, 0⟩

/-- The address of byte `k` of writable region `i`. -/
def byteAddr (s : State) (i k : Nat) : Addr := (region s i).base + BitVec.ofNat 64 k

/-- The address of byte `k` above `esp`. -/
def argByte (s : State) (k : Nat) : Addr := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k

/-- The size of an item of the stack: a frame of `n` bytes, or a return address. -/
def itemSize : Option Nat → Nat
  | some n => n
  | none => 4

/-- The size of the stack `stk`: how far `esp` is below the stack pointer on entry. -/
def depth : List (Option Nat) → Nat
  | [] => 0
  | x :: xs => itemSize x + depth xs

/-- The frames of the stack `xs`, the first at offset `o` above `esp` and the
writable region `j`: each frame's region, offset and size. -/
def frameList : List (Option Nat) → Nat → Nat → List (Nat × Nat × Nat)
  | [], _, _ => []
  | some n :: xs, j, o => (j, o, n) :: frameList xs (j + 1) (o + n)
  | none :: xs, j, o => frameList xs j (o + 4)

/-- The number of frames of the stack. -/
def nframes : List (Option Nat) → Nat
  | [] => 0
  | some _ :: xs => nframes xs + 1
  | none :: xs => nframes xs

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

/-- The known region bases after writing `d`. -/
def kill (τ : T) (d : Reg) : List (Reg × Nat × Nat) := τ.bases.filter (·.1 != d)

/-- The address `m` accesses is public. -/
def memPub (τ : T) (m : MemOp) : Bool := pub τ m.base

/-- The region and offset addressed by `m`, if known. -/
def addrOf (τ : T) (m : MemOp) : Option (Nat × Nat) :=
  (τ.bases.find? fun p => p.1 == m.base && p.2.2 ≤ m.disp).map fun p => (p.2.1, m.disp - p.2.2)

/-- `w` bytes at `m` are within a public slot. -/
def slotPub (τ : T) (m : MemOp) (w : Nat) : Bool :=
  match addrOf τ m with
  | some (i, d) => τ.slots.covers i d w
  | none => false

/-- `w` bytes at `m` are within the stack arguments. -/
def argPub (τ : T) (m : MemOp) (w : Nat) : Bool :=
  m.base == .esp && depth τ.stk + 4 ≤ m.disp && m.disp + w ≤ depth τ.stk + τ.argLen

/-- The addresses the operand accesses are public. -/
def srcOk (τ : T) : Src → Bool
  | .mem m => memPub τ m
  | _ => true

/-- The operand's value is public (memory operands aside). -/
def srcPub (τ : T) : Src → Bool
  | .reg r => pub τ r
  | .imm _ => true
  | .mem _ => false

/-- A word memory operand is public. -/
def loadPub (τ : T) : Src → Bool
  | .mem m => slotPub τ m 4 || argPub τ m 4
  | _ => false

/-- The regions whose base address a word loaded from `m` is. -/
def loadBases (τ : T) (m : MemOp) : List Nat :=
  (match addrOf τ m with
    | some (j, o) => (τ.wbases.filter fun p => p.1 == j && p.2.1 == o).map (·.2.2)
    | none => []) ++
  (if m.base == .esp then (τ.argBases.filter (depth τ.stk + ·.1 == m.disp)).map (·.2) else [])

/-- The known region bases after `mov d, src`. -/
def movBases (τ : T) (d : Reg) : Src → List (Reg × Nat × Nat)
  | .reg r => kill τ d ++ (τ.bases.filter (·.1 == r)).map fun p => (d, p.2)
  | .mem m => kill τ d ++ (loadBases τ m).map fun i => (d, i, 0)
  | .imm _ => kill τ d

/-- The regions whose base address register `r` holds. -/
def regBases (τ : T) (r : Reg) : List Nat :=
  (τ.bases.filter fun p => p.1 == r && p.2.2 == 0).map (·.2.1)

/-- The public slots after storing `w` bytes at `m`, a public value iff `p`. -/
def storeSlots (τ : T) (m : MemOp) (w : Nat) (p : Bool) : Slots :=
  match addrOf τ m with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      if p then τ.slots.add i d w else τ.slots.remove i d w
    else if p then τ.slots else .empty
  | none => if p then τ.slots else .empty

/-- The known base-address words after storing `w` bytes at `m`, the base
address of each region in `nb`. -/
def storeWbases (τ : T) (m : MemOp) (w : Nat) (nb : List Nat) : List (Nat × Nat × Nat) :=
  match addrOf τ m with
  | some (j, d) =>
    if d + w ≤ τ.lens.getD j 0 then
      (τ.wbases.filter fun p => p.1 != j || d + w ≤ p.2.1 || p.2.1 + 4 ≤ d) ++ nb.map fun i => (j, d, i)
    else []
  | none => []

def storeStep (τ : T) (m : MemOp) (w : Nat) (p : Bool) (nb : List Nat) : Option T :=
  if memPub τ m then some { τ with slots := storeSlots τ m w p, wbases := storeWbases τ m w nb }
  else none

def usesCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

def writes : AluOp → Bool
  | .cmp | .test => false
  | _ => true

/-- `mul r`: `eax`, `edx` and the flags are functions of the old `eax` and
`r` (SF and ZF become undefined in both runs). -/
def mulStep (τ : T) (r : Reg) : T :=
  let p := pub τ .eax && pub τ r
  { τ with regs := if p then (τ.regs.insert .eax).insert .edx else (τ.regs.erase .eax).erase .edx,
           flags := p, bases := (kill τ .eax).filter (·.1 != .edx) }

def step (τ : T) : Instr → Option T
  | .mov d src =>
    if d != .esp && srcOk τ src then
      some { τ with regs := set τ d (srcPub τ src || loadPub τ src), bases := movBases τ d src }
    else none
  | .store m r => storeStep τ m 4 (pub τ r) (regBases τ r)
  | .alu op d src =>
    if d != .esp && srcOk τ src then
      let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
      some { τ with regs := if writes op then set τ d p else τ.regs, flags := p, bases := kill τ d }
    else none
  -- The result is a function of the old value of `d`, and so are the
  -- flags that change.
  | .shift _ d _ =>
    if d != .esp then some { τ with flags := τ.flags && pub τ d, bases := kill τ d } else none
  | .bswap d => if d != .esp then some { τ with bases := kill τ d } else none
  | .movzx8 d m =>
    if d != .esp && memPub τ m then some { τ with regs := set τ d false, bases := kill τ d } else none
  | .store8 m r => storeStep τ m 1 (pub τ r.reg) []
  | .mul r => some (mulStep τ r)
  -- A frame's push and pop are analysed by the `push` and `pop` hooks
  -- (`pushStep`, `popStep`), not here; the SSE instructions are not analysed.
  | .symPush .. | .push _ | .pop .. | .alloc _ | .free _ | .movdquLoad .. | .movdquStore .. | .movqLoad .. | .movqStore .. | .xop _ | .mop _ | .mmxStore .. | .mmxEnter | .emms => none

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.inter τ₂.slots else .empty
  wbases := if τ₁.lens = τ₂.lens then τ₁.wbases.filter (τ₂.wbases.contains ·) else []
  argLen := if τ₁.argLen = τ₂.argLen ∧ τ₁.stk = τ₂.stk then τ₁.argLen else 0
  argBases := if τ₁.argLen = τ₂.argLen ∧ τ₁.stk = τ₂.stk then
    τ₁.argBases.filter (τ₂.argBases.contains ·) else []
  stk := if τ₁.stk = τ₂.stk then τ₁.stk else []
  room := if τ₁.stk = τ₂.stk then min τ₁.room τ₂.room else 0

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.subset σ.slots &&
    τ.wbases.all (σ.wbases.contains ·) && τ.argLen == σ.argLen &&
    τ.argBases.all (σ.argBases.contains ·) && τ.stk == σ.stk && decide (τ.room ≤ σ.room)

/-- The known region bases of `esp`: those of the frames of the stack, the
outermost first (so that `addrOf` finds, for an offset, the frame it is in). -/
def stkBases (stk : List (Option Nat)) : List (Reg × Nat × Nat) :=
  ((frameList stk 0 0).map fun p => (.esp, p.1, p.2.1)).reverse

/-- A call stores its return address below `esp`, within the bytes that the
stack may use, and so outside every writable region and the arguments. -/
def callStep (τ : T) : Option T :=
  if pub τ .esp && decide (depth τ.stk + 4 ≤ τ.room) then
    some { τ with stk := none :: τ.stk, bases := kill τ .esp ++ stkBases (none :: τ.stk) }
  else none

/-- A return loads its return address from `[esp]`. -/
def retStep (τ : T) : Option T :=
  match τ.stk with
  | none :: stk =>
    if pub τ .esp then some { τ with stk := stk, bases := kill τ .esp ++ stkBases stk } else none
  | _ => none

/-- A frame's pop removes the frame at `esp` (the first writable region) and
loads its register from it: a secret. -/
def popStep (τ : T) : Instr → Option T
  | .pop r _ =>
    match τ.stk with
    | some _ :: stk =>
      if pub τ .esp then
        some { τ with
          regs := τ.regs.erase r
          stk := stk
          lens := τ.lens.tail
          bases := ((τ.bases.filter fun p => p.1 != .esp && p.1 != r && p.2.1 != 0).map
            fun p => (p.1, p.2.1 - 1, p.2.2)) ++ stkBases stk
          slots := τ.slots.pop
          wbases := (τ.wbases.filter fun p => p.1 != 0 && p.2.2 != 0).map
            fun p => (p.1 - 1, p.2.1, p.2.2 - 1)
          argBases := (τ.argBases.filter (·.2 != 0)).map fun p => (p.1, p.2 - 1) }
      else none
    | _ => none
  | _ => none

/-- The public slots of a frame's push `push rs`, the first register at `o - 4`. -/
def pushSlots (τ : T) : List Reg → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | r :: rs, o => (if pub τ r then [(0, o - 4, 4)] else []) ++ pushSlots τ rs (o - 4)

/-- The base-address words of a frame's push `push rs`, the first register at `o - 4`
(the other regions' indices move up by one). -/
def pushWbases (τ : T) : List Reg → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | r :: rs, o => (regBases τ r).map (fun i => (0, o - 4, i + 1)) ++ pushWbases τ rs (o - 4)

/-- The analysis after a frame's push `push rs`: the frame is writable region `0`
and the others move up by one. -/
def pushed (τ : T) (rs : List Reg) : T :=
  let n := 4 * rs.length
  { τ with
    stk := some n :: τ.stk
    lens := n :: τ.lens
    bases := (kill τ .esp).map (fun p => (p.1, p.2.1 + 1, p.2.2)) ++ stkBases (some n :: τ.stk)
    slots := τ.slots.push ((Slots.ofList (pushSlots τ rs n)).get 0)
    wbases := pushWbases τ rs n ++ τ.wbases.map fun p => (p.1 + 1, p.2.1, p.2.2 + 1)
    argBases := τ.argBases.map fun p => (p.1, p.2 + 1) }

/-- A frame's push stores its registers below `esp`, within the bytes that the
stack may use, which become a new writable region. -/
def pushStep (τ : T) : Instr → Option T
  | .push rs =>
    if pub τ .esp && τ.lens != [] && decide (depth τ.stk + 4 * rs.length ≤ τ.room) then
      some (pushed τ rs)
    else none
  | _ => none

def storeHint (τ : T) (m : MemOp) (w : Nat) (p : Bool) (nb : List Nat) : Option T :=
  if pub τ m.base then
    some { τ with slots := storeSlots τ m w p, wbases := storeWbases τ m w nb }
  else none

def stepHint (τ : T) : Instr → Option T
  | .store m r => storeHint τ m 4 (pub τ r) (regBases τ r)
  | .store8 m r => storeHint τ m 1 (pub τ r.reg) []
  | i => step τ i

def hintOps : VG.NativeHintOps isa where
  T := T
  step := stepHint
  condPub τ _ := τ.flags
  meet := meet
  le := le
  call := callStep
  ret := retStep
  push := pushStep
  pop := popStep

end VG.NativeHints.X86

namespace VG.NativeHints.X86.provider
/-- An untrusted native hint; `Taint.check` still checks every interval. -/
def hintOfSize := VG.NativeHintOps.hintOfSize VG.NativeHints.X86.hintOps
def hintWeakOfSize := VG.NativeHintOps.hintWeakOfSize VG.NativeHints.X86.hintOps
end VG.NativeHints.X86.provider
