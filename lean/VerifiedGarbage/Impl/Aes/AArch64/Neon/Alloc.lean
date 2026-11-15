module

public import VerifiedGarbage.Impl.Aes.Circuit
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Register allocation of Boolean circuits on AdvSIMD registers

As `Impl/Aes/AArch64/Alloc.lean`, for circuits applied to 128-bit words:
compiles a circuit (`Circuit.Gate`s) to three-operand AdvSIMD instructions
(`eor`, `and`, `not`), with the words in vector registers and, when the
registers run out, in 16-byte slots `[sb, #16k]` of a scratch buffer. Both
operands of a gate must be in registers: an operand that is only in a slot
is loaded first. A gate's result goes to its output register if that is
free, otherwise to the register of an operand that dies there if there is
one, and otherwise to a free register. When no register is free, the value
whose next use is farthest away (Belady) is evicted, and spilled to a slot
unless it is already in one. `a ⊕ ¬b` is `eor` then `not`.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Neon

open VG.AArch64 VG.Impl.Aes.Circuit

/-- The allocation state. -/
structure Alloc where
  /-- The variable each register holds. -/
  regs : List (VReg × Nat)
  /-- The variable each slot holds. -/
  slots : List (Nat × Nat)
  free : List VReg
  freeSlots : List Nat
  /-- The instructions so far, most recent first. -/
  code : List Instr

namespace Alloc

variable (sb : Reg)

def regOf (a : Alloc) (v : Nat) : Option VReg := (a.regs.find? (·.2 == v)).map (·.1)

def slotOf (a : Alloc) (v : Nat) : Option Nat := (a.slots.find? (·.2 == v)).map (·.1)

/-- Whether the variable is used by a later gate or is an output. -/
def live (rest : Rest) (outs : List (Nat × VReg)) (v : Nat) : Bool :=
  outs.any (·.1 == v) || rest.reads v

/-- Forget a dead variable, freeing its register and slot. -/
def kill (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    free := match a.regOf v with | some r => r :: a.free | none => a.free
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with | some k => k :: a.freeSlots | none => a.freeSlots }

def emit (a : Alloc) (i : Instr) : Alloc := { a with code := i :: a.code }

/-- Evict the variable in register `r`, spilling it if it is in no slot. -/
def evict (a : Alloc) (r : VReg) (v : Nat) : Alloc :=
  let a := { a with regs := a.regs.filter (·.1 != r) }
  match a.slotOf v with
  | some _ => a
  | none => match a.freeSlots with
    | k :: ks =>
      emit { a with slots := (k, v) :: a.slots, freeSlots := ks } (.strq r sb (16 * k))
    | [] => a

/-- A free register, evicting the value used farthest away, but not one of `keep`. -/
def getReg (a : Alloc) (rest : Rest) (keep : List Nat) : Alloc × VReg :=
  match a.free with
  | r :: rs => ({ a with free := rs }, r)
  | [] =>
    let cands := a.regs.filter fun p => !keep.contains p.2
    let best := cands.foldl (fun (b : Option (VReg × Nat)) p =>
      match b with
      | none => some p
      | some q => if rest.nextUse p.2 > rest.nextUse q.2 then some p else some q) none
    match best with
    | some (r, v) => (evict sb a r v, r)
    | none => (a, .v0)

/-- Make sure the variable is in a register, loading it from its slot. -/
def load (a : Alloc) (rest : Rest) (keep : List Nat) (v : Nat) : Alloc × VReg :=
  match a.regOf v with
  | some r => (a, r)
  | none =>
    let (a, r) := getReg sb a rest keep
    let a := emit a (.ldrq r sb (16 * (a.slotOf v).getD 0))
    ({ a with regs := (r, v) :: a.regs }, r)

def opInstrs (op : Op) (d p q : VReg) : List Instr :=
  match op with
  | .xor => [.vop (.logic .eor d p q)]
  | .and => [.vop (.logic .and d p q)]
  | .xnor => [.vop (.logic .eor d p q), .vop (.not d d)]

/-- Compile one gate, `here` being it and the gates after it. -/
def gate (outs : List (Nat × VReg)) (a : Alloc) (g : Gate) (here : Rest) : Alloc :=
  let rest := here.tail
  let (a, ra) := load sb a here [g.a, g.b] g.a
  let (a, rb) := load sb a here [g.a, g.b] g.b
  let aDead := !live rest outs g.a
  let bDead := !live rest outs g.b
  let a := if aDead then kill a g.a else a
  let a := if bDead then kill a g.b else a
  let target := (outs.find? (·.1 == g.dst)).map (·.2)
  let (a, rd) :=
    match target with
    | some r => if a.free.contains r then ({ a with free := a.free.filter (· != r) }, r)
      else if aDead then ({ a with free := a.free.filter (· != ra) }, ra)
      else if bDead then ({ a with free := a.free.filter (· != rb) }, rb)
      else getReg sb a rest [g.a, g.b]
    | none =>
    if aDead then ({ a with free := a.free.filter (· != ra) }, ra)
    else if bDead then ({ a with free := a.free.filter (· != rb) }, rb)
    else getReg sb a rest [g.a, g.b]
  let a := (opInstrs g.op rd ra rb).foldl emit a
  { a with regs := (rd, g.dst) :: a.regs }

/-- Compile the gates. -/
def gates (outs : List (Nat × VReg)) : Rest → Alloc → List Gate → Alloc
  | _, a, [] => a
  | r, a, g :: gs => gates outs r.tail (gate sb outs a g r) gs

/-- Move each output to its register. -/
def place (a : Alloc) : List (Nat × VReg) → Alloc
  | [] => a
  | (v, r) :: outs =>
    if a.regOf v = some r then place a outs else
    -- Evict whatever is in `r`.
    let a := match a.regs.find? (·.1 == r) with
      | some (_, u) => evict sb a r u
      | none => { a with free := a.free.filter (· != r) }
    let a := match a.regOf v with
      | some r' => emit a (.vop (.mov r r'))
      | none => emit a (.ldrq r sb (16 * (a.slotOf v).getD 0))
    let a := { a with regs := (r, v) :: a.regs.filter (·.2 != v) }
    place a outs

end Alloc

/-- The code of a circuit whose inputs `ins` start in their registers, the
registers `free` being free, leaving the outputs `outs` in their registers;
`spill` are the slots of `sb` it may spill to. -/
def compile (sb : Reg) (gs : List Gate) (ins outs : List (Nat × VReg)) (free : List VReg)
    (spill : List Nat) : List Instr :=
  let init : Alloc :=
    { regs := ins.map (fun (v, r) => (r, v)), slots := [], free := free, freeSlots := spill, code := [] }
  let a := Alloc.gates sb outs (Rest.ofGates gs) init gs
  (Alloc.place sb a outs).code.reverse

end VG.Impl.Aes.AArch64.Neon
