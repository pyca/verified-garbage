module

public import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Register allocation of the DES S-box circuits on PPC64LE

Compiles a circuit (`Bitslice.Gate`s on 64-bit words) to three-operand
`and`, `or` and `xor` instructions, with every word in a register, as on
RISC-V (`Impl/TripleDes/RISCV64/BitsliceAlloc.lean`). A gate's result goes
to the register of an operand that dies there, else to a free register. The
model has no AND-NOT: `a ∧ ¬b` is `(a ∨ b) ⊕ b` (in place of a dead `a`, or
in a free register), or `¬b ∧ a` in place of a dead `b`; `¬a` is `a ⊕ ones`,
the register `ones` holding all ones. There are no spills: `ok` says whether
the free registers sufficed, which each use checks.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE.Bitslice

open VG.PPC64LE VG.Impl.TripleDes.Bitslice

/-- The allocation state. -/
structure Alloc where
  /-- The variable each register holds. -/
  regs : List (Reg × Nat)
  free : List Reg
  /-- The instructions so far, most recent first. -/
  code : List Instr
  /-- Whether every operand was in a register and a free one was found
  whenever one was needed. -/
  ok : Bool

namespace Alloc

def has (a : Alloc) (v : Nat) : Bool := (a.regs.find? (·.2 == v)).isSome

def regOf (a : Alloc) (v : Nat) : Reg := ((a.regs.find? (·.2 == v)).map (·.1)).getD .r0

/-- Whether the variable is used by a later gate or is an output. -/
def live (rest : List Gate) (outs : List Nat) (v : Nat) : Bool :=
  outs.contains v || rest.any fun g => g.a == v || g.b == v

/-- Forget a dead variable, freeing its register unless it is `keep`. -/
def drop (a : Alloc) (v : Nat) (keep : Reg) : Alloc :=
  let r := a.regOf v
  { a with regs := a.regs.filter (·.2 != v), free := if r == keep then a.free else r :: a.free }

/-- A free register. -/
def fresh (a : Alloc) : Alloc × Reg :=
  match a.free with
  | r :: rs => ({ a with free := rs }, r)
  | [] => ({ a with ok := false }, .r0)

/-- Compile one gate, `rest` being the gates after it. -/
def gate (ones : Reg) (outs : List Nat) (a : Alloc) (g : Gate) (rest : List Gate) : Alloc :=
  let aDead := !live rest outs g.a
  let bDead := !live rest outs g.b && g.b != g.a
  let xa := a.regOf g.a
  let rb := a.regOf g.b
  let ok := a.has g.a && a.has g.b
  let (a, d, is) : Alloc × Reg × List Instr := match g.op with
    | .not =>
      if aDead then (a, xa, [.logic .xor xa xa ones])
      else let (a, d) := a.fresh; (a, d, [.logic .xor d xa ones])
    | .andn =>
      if aDead then (a, xa, [.logic .or xa xa rb, .logic .xor xa xa rb])
      else if bDead then (a, rb, [.logic .xor rb rb ones, .logic .and rb rb xa])
      else let (a, d) := a.fresh; (a, d, [.logic .or d xa rb, .logic .xor d d rb])
    | op =>
      let lop : LogicOp := match op with | .and => .and | .or => .or | _ => .xor
      if aDead then (a, xa, [.logic lop xa xa rb])
      else if bDead then (a, rb, [.logic lop rb xa rb])
      else let (a, d) := a.fresh; (a, d, [.logic lop d xa rb])
  let a := if aDead then a.drop g.a d else a
  let a := if bDead then a.drop g.b d else a
  { a with regs := (d, g.dst) :: a.regs, code := is.reverse ++ a.code, ok := a.ok && ok }

/-- Compile the gates. -/
def gates (ones : Reg) (outs : List Nat) : Alloc → List Gate → Alloc
  | a, [] => a
  | a, g :: gs => gates ones outs (gate ones outs a g gs) gs

end Alloc

/-- The code of a circuit whose inputs (variables `0 … 5`) start in the
registers `ins`, the registers `free` being free and `ones` holding all
ones, the registers of its outputs `outs`, and whether the registers
sufficed. -/
def compile (gs : List Gate) (ins : List Reg) (outs : List Nat) (free : List Reg) (ones : Reg) :
    List Instr × List Reg × Bool :=
  let a : Alloc := { regs := ins.zipIdx, free := free, code := [], ok := true }
  let a := Alloc.gates ones outs a gs
  (a.code.reverse, outs.map a.regOf, a.ok)

end VG.Impl.TripleDes.PPC64LE.Bitslice
