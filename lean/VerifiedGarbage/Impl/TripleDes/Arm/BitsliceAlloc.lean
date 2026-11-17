module

public import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# Register allocation of the DES S-box circuits on ARMv7

Compiles a circuit (`Bitslice.Gate`s on 32-bit words) to three-operand ARM
instructions (`and`, `orr`, `eor`, `bic`), with the words in registers and,
when the registers run out, in 4-byte slots `[sb, #4k]` of a scratch buffer
whose base is in the register `sb`. Both operands of a gate must be in
registers: one that is only in a slot is loaded first. A gate's result goes
to the register of an operand that dies there, else to a free register;
when none is free, the value whose next use is farthest away is evicted,
and stored to a slot unless it is in one.

A value is kept as it is or complemented (its *polarity*), whichever the
instruction that computes it gives: `¬a` is `a` with the other polarity and
takes no instruction, and each gate is the one instruction that computes it
or its complement from its operands as they are kept (`a ∧ b` from `¬a` and
`¬b` is `¬(a ∨ b)`: `orr`). An output that ends complemented is inverted
(`mvn`).

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm.Bitslice

open VG.Arm VG.Impl.TripleDes.Bitslice

/-- A variable, complemented if `neg`. -/
structure Lit where
  var : Nat
  neg : Bool
  deriving DecidableEq, Repr

/-- A gate on literals: `and`, `or` or `xor` of `a` and `b`. -/
structure LGate where
  dst : Nat
  op : Op
  a : Lit
  b : Lit

/-- The literal a variable stands for: itself, or what a `not` gate made it. -/
def resolve (sub : List (Nat × Lit)) (v : Nat) : Lit :=
  ((sub.find? (·.1 == v)).map (·.2)).getD ⟨v, false⟩

/-- The gates without `not` (a literal of its operand) and `andn` (`and` of
a complemented literal), and the literal of each variable a `not` defined. -/
def lower : List (Nat × Lit) → List Gate → List LGate × List (Nat × Lit)
  | sub, [] => ([], sub)
  | sub, g :: gs =>
    let a := resolve sub g.a
    let b := resolve sub g.b
    match g.op with
    | .not => lower ((g.dst, ⟨a.var, !a.neg⟩) :: sub) gs
    | .andn => let r := lower sub gs; (⟨g.dst, .and, a, ⟨b.var, !b.neg⟩⟩ :: r.1, r.2)
    | op => let r := lower sub gs; (⟨g.dst, op, a, b⟩ :: r.1, r.2)

/-- The allocation state. -/
structure Alloc where
  /-- The variable each register holds. -/
  regs : List (Reg × Nat)
  /-- The variable each slot holds. -/
  slots : List (Nat × Nat)
  /-- The variables kept complemented. -/
  negs : List Nat
  free : List Reg
  freeSlots : List Nat
  /-- The instructions so far, most recent first. -/
  code : List Instr
  /-- Whether a register and a slot were found whenever one was needed. -/
  ok : Bool

namespace Alloc

variable (sb : Reg)

def regOf (a : Alloc) (v : Nat) : Option Reg := (a.regs.find? (·.2 == v)).map (·.1)

def slotOf (a : Alloc) (v : Nat) : Option Nat := (a.slots.find? (·.2 == v)).map (·.1)

/-- How many gates until one reads the variable (their number if none does). -/
def nextUse (rest : List LGate) (v : Nat) : Nat :=
  (rest.findIdx? fun g => g.a.var == v || g.b.var == v).getD rest.length

/-- Whether the variable is read by a later gate or is an output. -/
def live (rest : List LGate) (outs : List Nat) (v : Nat) : Bool :=
  outs.contains v || rest.any fun g => g.a.var == v || g.b.var == v

def emit (a : Alloc) (i : Instr) : Alloc := { a with code := i :: a.code }

/-- Forget a dead variable, freeing its register and slot. -/
def kill (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    free := match a.regOf v with | some r => r :: a.free | none => a.free
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with | some k => k :: a.freeSlots | none => a.freeSlots }

/-- Evict the variable in register `r`, storing it if it is in no slot. -/
def evict (a : Alloc) (r : Reg) (v : Nat) : Alloc :=
  let a := { a with regs := a.regs.filter (·.1 != r) }
  match a.slotOf v with
  | some _ => a
  | none => match a.freeSlots with
    | k :: ks => emit { a with slots := (k, v) :: a.slots, freeSlots := ks } (.str r sb (4 * k))
    | [] => { a with ok := false }

/-- A free register, evicting the value read farthest away (an output that
no gate reads last of all), but none of `keep`. -/
def getReg (a : Alloc) (rest : List LGate) (keep : List Nat) : Alloc × Reg :=
  match a.free with
  | r :: rs => ({ a with free := rs }, r)
  | [] =>
    let cands := a.regs.filter fun p => !keep.contains p.2
    let best := cands.foldl (fun (b : Option (Reg × Nat)) p =>
      match b with
      | none => some p
      | some q => if nextUse rest p.2 > nextUse rest q.2 then some p else some q) none
    match best with
    | some (r, v) => (evict sb a r v, r)
    | none => ({ a with ok := false }, sb)

/-- Make sure the variable is in a register, loading it from its slot. -/
def load (a : Alloc) (rest : List LGate) (keep : List Nat) (v : Nat) : Alloc × Reg :=
  match a.regOf v with
  | some r => (a, r)
  | none =>
    let (a, r) := getReg sb a rest keep
    let a := match a.slotOf v with
      | some k => emit a (.ldr r sb (4 * k))
      | none => { a with ok := false }
    ({ a with regs := (r, v) :: a.regs }, r)

/-- The instruction of a gate on the registers `p` and `q`, whose values are
complemented if `np` and `nq`, and whether its result is complemented. -/
def opInstr (op : Op) (d p q : Reg) (np nq : Bool) : Instr × Bool :=
  match op, np, nq with
  | .and, false, false => (.dp .and d p (.reg q), false)
  | .and, true, true => (.dp .orr d p (.reg q), true)
  | .and, false, true => (.dp .bic d p (.reg q), false)
  | .and, true, false => (.dp .bic d q (.reg p), false)
  | .or, false, false => (.dp .orr d p (.reg q), false)
  | .or, true, true => (.dp .and d p (.reg q), true)
  | .or, false, true => (.dp .bic d q (.reg p), true)
  | .or, true, false => (.dp .bic d p (.reg q), true)
  | _, np, nq => (.dp .eor d p (.reg q), np != nq)

/-- Compile one gate, `rest` being the gates after it. -/
def gate (outs : List Nat) (a : Alloc) (g : LGate) (rest : List LGate) : Alloc :=
  let here := g :: rest
  let (a, ra) := load sb a here [g.a.var, g.b.var] g.a.var
  let (a, rb) := load sb a here [g.a.var, g.b.var] g.b.var
  let na := g.a.neg != a.negs.contains g.a.var
  let nb := g.b.neg != a.negs.contains g.b.var
  let aDead := !live rest outs g.a.var
  let bDead := !live rest outs g.b.var
  let a := if aDead then kill a g.a.var else a
  let a := if bDead then kill a g.b.var else a
  let (a, rd) :=
    if aDead then ({ a with free := a.free.filter (· != ra) }, ra)
    else if bDead then ({ a with free := a.free.filter (· != rb) }, rb)
    else getReg sb a rest [g.a.var, g.b.var]
  let (i, n) := opInstr g.op rd ra rb na nb
  let a := emit a i
  { a with regs := (rd, g.dst) :: a.regs, negs := if n then g.dst :: a.negs else a.negs }

/-- Compile the gates. -/
def gates (outs : List Nat) : Alloc → List LGate → Alloc
  | a, [] => a
  | a, g :: gs => gates outs (gate sb outs a g gs) gs

/-- Each output into a register, as it is (not complemented). -/
def place (a : Alloc) : List Lit → Alloc
  | [] => a
  | o :: outs =>
    let (a, r) := load sb a [] (o.var :: outs.map (·.var)) o.var
    let a := if o.neg != a.negs.contains o.var then emit a (.mvn r (.reg r)) else a
    place { a with negs := if o.neg then o.var :: a.negs.filter (· != o.var) else a.negs.filter (· != o.var) } outs

end Alloc

/-- The code of a circuit whose inputs (variables `0 … 5`) start in the
registers `ins`, the registers `free` being free and the slots `spill` of
the buffer at `sb` too; the registers its outputs `outs` end in; and whether
the registers and slots sufficed and the outputs are four variables in four
registers. -/
def compile (sb : Reg) (gs : List Gate) (ins : List Reg) (outs : List Nat) (free : List Reg)
    (spill : List Nat) : List Instr × List Reg × Bool :=
  let (lgs, sub) := lower [] gs
  let os := outs.map (resolve sub)
  let ov := os.map (·.var)
  let a : Alloc :=
    { regs := ins.zipIdx, slots := [], negs := [], free, freeSlots := spill, code := [], ok := true }
  let a := Alloc.gates sb ov a lgs
  let a := Alloc.place sb a os
  let rs := ov.map fun v => (a.regOf v).getD sb
  (a.code.reverse, rs, a.ok && ov.eraseDups.length == outs.length && rs.eraseDups.length == outs.length &&
    !rs.contains sb)

end VG.Impl.TripleDes.Arm.Bitslice
