module

public import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
public import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
public import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
public meta import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.TCB.Code

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

/-!
# Scalar register allocation for the short DES S-box circuits

The same circuits serve the AdvSIMD bitsliced implementation. Lower AND-NOT
into NOT and AND, then reuse the AES allocator's loads, spills and liveness
queries. OR is a single scalar instruction. Nothing here is trusted: the
S-box proofs check the allocated instructions on all 64 inputs, including
spills and output placement.
-/

namespace ScalarAlloc

open VG.AArch64
open VG.Impl.Aes.AArch64 (Alloc)
open VG.Impl.Aes.Circuit (Rest)

inductive Op
  | and | or | xor | not

structure Gate where
  dst : Nat
  op : Op
  a : Nat
  b : Nat

/-- Fresh temporaries are above every variable in the eight circuits. -/
def lower (g : Bitslice.Gate) : List Gate :=
  match g.op with
  | .and => [⟨g.dst, .and, g.a, g.b⟩]
  | .or => [⟨g.dst, .or, g.a, g.b⟩]
  | .xor => [⟨g.dst, .xor, g.a, g.b⟩]
  | .not => [⟨g.dst, .not, g.a, g.a⟩]
  | .andn => [⟨1000 + g.dst, .not, g.b, g.b⟩, ⟨g.dst, .and, g.a, 1000 + g.dst⟩]

/-- Only operands and their order matter to the liveness analysis. -/
def reads (g : Gate) : VG.Impl.Aes.Circuit.Gate := ⟨g.dst, .xor, g.a, g.b⟩

def opInstr (op : Op) (d p q : Reg) : Instr :=
  match op with
  | .and => .logic .and .x d p q
  | .or => .logic .orr .x d p q
  | .xor => .logic .eor .x d p q
  | .not => .logic .eor .x d p .x9

def gate (outs : List (Nat × Reg)) (a : Alloc) (g : Gate) (here : Rest) : Alloc :=
  let rest := here.tail
  let (a, ra) := Alloc.load .x2 a here [g.a, g.b] g.a
  let (a, rb) := Alloc.load .x2 a here [g.a, g.b] g.b
  let aDead := !Alloc.live rest outs g.a
  let bDead := !Alloc.live rest outs g.b
  -- The result goes to its output register if that is free, and otherwise to
  -- the register of an operand that dies here.
  let a := if aDead then Alloc.kill a g.a else a
  let a := if bDead then Alloc.kill a g.b else a
  let target := (outs.find? (·.1 == g.dst)).map (·.2)
  let (a, rd) :=
    match target with
    | some r => if a.free.contains r then ({ a with free := a.free.filter (· != r) }, r)
      else if aDead then ({ a with free := a.free.filter (· != ra) }, ra)
      else if bDead then ({ a with free := a.free.filter (· != rb) }, rb)
      else Alloc.getReg .x2 a rest [g.a, g.b]
    | none =>
    if aDead then ({ a with free := a.free.filter (· != ra) }, ra)
    else if bDead then ({ a with free := a.free.filter (· != rb) }, rb)
    else Alloc.getReg .x2 a rest [g.a, g.b]
  let a := Alloc.emit a (opInstr g.op rd ra rb)
  { a with regs := (rd, g.dst) :: a.regs }

def gates (outs : List (Nat × Reg)) : Rest → Alloc → List Gate → Alloc
  | _, a, [] => a
  | r, a, g :: gs => gates outs r.tail (gate outs a g r) gs

/-- Allocate in x3..x8 and x10..x17, with x9 holding all ones. Spills
stay within the existing block scratch region (slots 4..51). -/
def compile (gs : List Bitslice.Gate) (ins outs : List (Nat × Reg)) : List Instr :=
  let gs := gs.flatMap lower
  let a : Alloc := {
    regs := ins.map (fun (v, r) => (r, v)), slots := [],
    free := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
    freeSlots := List.range' 4 48, code := [] }
  let a := gates outs (Rest.ofGates (gs.map reads)) a gs
  let a := Alloc.place .x2 a outs
  [.movz .x .x9 0 0, .subImm .x .x9 .x9 1] ++ a.code.reverse

end ScalarAlloc

def q : Nat → Reg
  | 0 => .x3 | 1 => .x4 | 2 => .x5 | 3 => .x6 | 4 => .x7 | _ => .x8

def sboxIns : List (Nat × Reg) := (List.range 6).map fun i => (i, q i)

def sboxOuts (i : Nat) : List (Nat × Reg) :=
  (List.range 4).map fun j => ((Bitslice.outputs i).getD j 0, q j)

/-! The code of the S-boxes, as `ScalarAlloc.compile` allocates the short circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-- The allocated short circuit for S-box 1. -/
def sboxCode0 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .eor .x .x10 .x4 .x9,
  .logic .and .x .x10 .x8 .x10, .logic .eor .x .x11 .x5 .x10, .logic .orr .x .x12 .x6 .x3,
  .logic .eor .x .x13 .x8 .x6, .logic .and .x .x14 .x12 .x13, .logic .eor .x .x15 .x5 .x14,
  .logic .eor .x .x16 .x11 .x9, .logic .and .x .x16 .x15 .x16, .logic .eor .x .x17 .x4 .x3,
  .str .x .x7 .x2 32, .logic .eor .x .x7 .x6 .x17, .logic .eor .x .x7 .x7 .x9,
  .logic .and .x .x7 .x11 .x7, .logic .orr .x .x14 .x3 .x14, .logic .eor .x .x7 .x7 .x14,
  .logic .eor .x .x14 .x16 .x9, .logic .and .x .x14 .x7 .x14, .logic .orr .x .x3 .x8 .x3,
  .str .x .x14 .x2 40, .logic .orr .x .x14 .x7 .x3, .logic .eor .x .x15 .x15 .x9,
  .logic .and .x .x15 .x4 .x15, .str .x .x4 .x2 48, .logic .eor .x .x4 .x14 .x15,
  .logic .eor .x .x3 .x3 .x9, .logic .and .x .x5 .x5 .x3, .logic .eor .x .x5 .x15 .x5,
  .logic .eor .x .x13 .x13 .x9, .logic .and .x .x13 .x17 .x13, .logic .orr .x .x5 .x5 .x13,
  .logic .eor .x .x10 .x10 .x9, .logic .and .x .x6 .x6 .x10, .logic .eor .x .x10 .x11 .x14,
  .logic .eor .x .x6 .x6 .x9, .logic .and .x .x10 .x10 .x6, .logic .eor .x .x6 .x10 .x9,
  .logic .and .x .x7 .x12 .x7, .logic .eor .x .x6 .x6 .x7, .ldr .x .x7 .x2 32,
  .logic .eor .x .x13 .x7 .x9, .logic .and .x .x4 .x4 .x13, .logic .eor .x .x4 .x4 .x6,
  .logic .eor .x .x10 .x17 .x10, .logic .orr .x .x15 .x15 .x10, .logic .eor .x .x15 .x12 .x15,
  .logic .eor .x .x8 .x8 .x15, .logic .eor .x .x6 .x6 .x8, .logic .orr .x .x16 .x16 .x7,
  .logic .eor .x .x16 .x16 .x6, .logic .eor .x .x12 .x12 .x14, .logic .orr .x .x12 .x5 .x12,
  .logic .eor .x .x12 .x8 .x12, .logic .orr .x .x17 .x17 .x6, .logic .eor .x .x17 .x12 .x17,
  .ldr .x .x6 .x2 40, .logic .orr .x .x14 .x6 .x7, .logic .eor .x .x14 .x14 .x17,
  .ldr .x .x17 .x2 48, .logic .orr .x .x17 .x17 .x11, .logic .eor .x .x12 .x12 .x9,
  .logic .and .x .x17 .x17 .x12, .logic .and .x .x6 .x6 .x8, .logic .eor .x .x17 .x17 .x6,
  .logic .orr .x .x17 .x17 .x7, .logic .eor .x .x3 .x17 .x5, .addImm .x .x5 .x14 0,
  .addImm .x .x6 .x16 0]

/-- The allocated short circuit for S-box 2. -/
def sboxCode1 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .eor .x .x10 .x7 .x4,
  .logic .eor .x .x11 .x3 .x9, .logic .and .x .x11 .x8 .x11, .logic .eor .x .x11 .x11 .x9,
  .logic .and .x .x11 .x4 .x11, .logic .orr .x .x12 .x7 .x11, .logic .eor .x .x13 .x3 .x9,
  .logic .and .x .x13 .x10 .x13, .logic .and .x .x14 .x8 .x10, .logic .eor .x .x4 .x4 .x14,
  .logic .eor .x .x14 .x13 .x9, .logic .and .x .x14 .x4 .x14, .logic .and .x .x15 .x6 .x3,
  .logic .eor .x .x11 .x11 .x13, .logic .and .x .x11 .x12 .x11, .logic .eor .x .x13 .x15 .x9,
  .logic .and .x .x13 .x11 .x13, .logic .and .x .x16 .x6 .x11, .logic .eor .x .x8 .x8 .x9,
  .logic .eor .x .x8 .x16 .x8, .logic .eor .x .x3 .x3 .x10, .logic .eor .x .x17 .x15 .x9,
  .logic .and .x .x17 .x3 .x17, .str .x .x14 .x2 32, .logic .eor .x .x14 .x8 .x17,
  .logic .eor .x .x13 .x13 .x9, .logic .and .x .x13 .x5 .x13, .logic .eor .x .x13 .x13 .x14,
  .logic .eor .x .x17 .x17 .x9, .logic .and .x .x7 .x7 .x17, .logic .eor .x .x4 .x4 .x7,
  .logic .eor .x .x17 .x4 .x9, .logic .and .x .x8 .x8 .x17, .logic .eor .x .x6 .x6 .x3,
  .logic .eor .x .x8 .x8 .x6, .logic .eor .x .x17 .x5 .x9, .logic .and .x .x17 .x12 .x17,
  .logic .eor .x .x17 .x17 .x8, .logic .eor .x .x16 .x16 .x7, .logic .orr .x .x6 .x6 .x16,
  .logic .eor .x .x12 .x12 .x14, .logic .orr .x .x15 .x15 .x12, .logic .eor .x .x16 .x6 .x15,
  .logic .eor .x .x11 .x11 .x14, .logic .eor .x .x8 .x8 .x11, .logic .and .x .x15 .x15 .x8,
  .logic .and .x .x10 .x10 .x6, .logic .eor .x .x15 .x15 .x10, .logic .orr .x .x10 .x15 .x5,
  .logic .eor .x .x10 .x10 .x16, .logic .eor .x .x4 .x4 .x9, .logic .and .x .x15 .x15 .x4,
  .logic .orr .x .x3 .x3 .x12, .logic .eor .x .x15 .x15 .x3, .ldr .x .x3 .x2 32,
  .logic .orr .x .x3 .x3 .x5, .logic .eor .x .x3 .x3 .x15, .addImm .x .x4 .x10 0,
  .addImm .x .x5 .x13 0, .addImm .x .x6 .x17 0]

/-- The allocated short circuit for S-box 3. -/
def sboxCode2 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .eor .x .x10 .x7 .x9,
  .logic .and .x .x10 .x8 .x10, .logic .eor .x .x11 .x6 .x3, .logic .orr .x .x12 .x10 .x11,
  .logic .eor .x .x13 .x5 .x3, .logic .eor .x .x14 .x8 .x9, .logic .and .x .x14 .x13 .x14,
  .logic .eor .x .x15 .x12 .x14, .logic .eor .x .x16 .x7 .x11, .logic .eor .x .x17 .x3 .x9,
  .logic .and .x .x17 .x16 .x17, .logic .eor .x .x12 .x12 .x17, .logic .eor .x .x17 .x12 .x9,
  .logic .and .x .x17 .x15 .x17, .str .x .x10 .x2 32, .logic .and .x .x10 .x3 .x15,
  .logic .orr .x .x10 .x5 .x10, .logic .and .x .x10 .x8 .x10, .logic .eor .x .x10 .x16 .x10,
  .str .x .x17 .x2 40, .logic .eor .x .x17 .x4 .x9, .logic .and .x .x17 .x15 .x17,
  .logic .eor .x .x17 .x17 .x10, .logic .and .x .x11 .x11 .x13, .logic .eor .x .x13 .x8 .x5,
  .str .x .x17 .x2 48, .logic .eor .x .x17 .x12 .x13, .logic .orr .x .x17 .x6 .x17,
  .logic .eor .x .x11 .x11 .x9, .logic .and .x .x17 .x17 .x11, .logic .orr .x .x14 .x14 .x13,
  .logic .eor .x .x13 .x14 .x9, .logic .and .x .x13 .x10 .x13, .logic .and .x .x3 .x5 .x3,
  .logic .eor .x .x11 .x7 .x9, .logic .and .x .x11 .x3 .x11, .logic .eor .x .x13 .x13 .x11,
  .logic .and .x .x12 .x12 .x13, .logic .orr .x .x3 .x16 .x3, .logic .eor .x .x12 .x12 .x9,
  .logic .and .x .x3 .x3 .x12, .logic .eor .x .x8 .x8 .x3, .logic .and .x .x17 .x17 .x4,
  .logic .eor .x .x17 .x17 .x8, .logic .eor .x .x15 .x15 .x9, .logic .orr .x .x7 .x7 .x15,
  .logic .orr .x .x6 .x6 .x7, .logic .eor .x .x16 .x16 .x6, .logic .eor .x .x14 .x14 .x16,
  .ldr .x .x6 .x2 40, .logic .eor .x .x6 .x6 .x9, .logic .and .x .x6 .x4 .x6,
  .logic .eor .x .x6 .x6 .x14, .logic .and .x .x5 .x5 .x15, .logic .eor .x .x10 .x10 .x5,
  .logic .orr .x .x16 .x16 .x10, .ldr .x .x10 .x2 32, .logic .eor .x .x10 .x10 .x8,
  .logic .eor .x .x16 .x16 .x10, .logic .orr .x .x13 .x13 .x4, .logic .eor .x .x4 .x13 .x16,
  .ldr .x .x3 .x2 48, .addImm .x .x5 .x17 0]

/-- The allocated short circuit for S-box 4. -/
def sboxCode3 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .eor .x .x8 .x8 .x6,
  .logic .eor .x .x6 .x6 .x4, .logic .orr .x .x10 .x7 .x5, .logic .eor .x .x10 .x4 .x10,
  .logic .eor .x .x10 .x10 .x9, .logic .and .x .x10 .x6 .x10, .logic .eor .x .x11 .x7 .x9,
  .logic .and .x .x11 .x6 .x11, .logic .eor .x .x12 .x5 .x11, .logic .orr .x .x13 .x8 .x12,
  .logic .eor .x .x14 .x10 .x9, .logic .and .x .x13 .x13 .x14, .logic .eor .x .x14 .x7 .x13,
  .logic .and .x .x12 .x12 .x14, .logic .eor .x .x15 .x12 .x9, .logic .and .x .x6 .x6 .x15,
  .logic .eor .x .x8 .x8 .x14, .logic .eor .x .x6 .x6 .x9, .logic .and .x .x6 .x8 .x6,
  .logic .eor .x .x10 .x10 .x6, .logic .eor .x .x7 .x7 .x5, .logic .orr .x .x4 .x4 .x11,
  .logic .eor .x .x8 .x8 .x4, .logic .eor .x .x4 .x7 .x9, .logic .and .x .x4 .x8 .x4,
  .logic .eor .x .x13 .x13 .x4, .logic .eor .x .x4 .x10 .x9, .logic .and .x .x4 .x3 .x4,
  .logic .eor .x .x6 .x4 .x13, .logic .eor .x .x13 .x13 .x9, .logic .eor .x .x4 .x3 .x9,
  .logic .and .x .x4 .x10 .x4, .logic .eor .x .x5 .x4 .x13, .logic .eor .x .x10 .x10 .x13,
  .logic .eor .x .x7 .x7 .x9, .logic .and .x .x10 .x10 .x7, .logic .orr .x .x12 .x12 .x10,
  .logic .eor .x .x8 .x8 .x12, .logic .orr .x .x12 .x14 .x3, .logic .eor .x .x4 .x12 .x8,
  .logic .and .x .x3 .x3 .x14, .logic .eor .x .x3 .x3 .x8]

/-- The allocated short circuit for S-box 5. -/
def sboxCode4 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .orr .x .x10 .x8 .x6,
  .logic .eor .x .x11 .x3 .x9, .logic .and .x .x11 .x10 .x11, .logic .eor .x .x12 .x8 .x11,
  .logic .eor .x .x13 .x6 .x12, .logic .orr .x .x14 .x5 .x13, .logic .eor .x .x15 .x5 .x9,
  .logic .and .x .x11 .x11 .x15, .logic .eor .x .x6 .x6 .x11, .logic .and .x .x11 .x4 .x6,
  .logic .orr .x .x13 .x8 .x13, .logic .eor .x .x11 .x11 .x13, .logic .eor .x .x11 .x5 .x11,
  .logic .eor .x .x3 .x3 .x11, .logic .orr .x .x15 .x12 .x3, .logic .and .x .x16 .x4 .x15,
  .logic .eor .x .x17 .x12 .x16, .str .x .x12 .x2 32, .logic .and .x .x12 .x5 .x13,
  .logic .eor .x .x17 .x17 .x12, .logic .eor .x .x12 .x8 .x9, .logic .and .x .x15 .x15 .x12,
  .logic .eor .x .x12 .x6 .x15, .logic .eor .x .x4 .x4 .x14, .logic .eor .x .x12 .x12 .x9,
  .logic .and .x .x12 .x4 .x12, .logic .eor .x .x12 .x12 .x9, .str .x .x5 .x2 40,
  .logic .eor .x .x5 .x7 .x9, .logic .and .x .x12 .x12 .x5, .logic .eor .x .x12 .x12 .x11,
  .logic .eor .x .x11 .x16 .x9, .logic .and .x .x11 .x6 .x11, .logic .eor .x .x15 .x15 .x4,
  .logic .orr .x .x15 .x17 .x15, .logic .eor .x .x11 .x11 .x9, .logic .and .x .x15 .x15 .x11,
  .logic .eor .x .x11 .x15 .x9, .logic .and .x .x11 .x14 .x11, .logic .and .x .x3 .x3 .x15,
  .logic .eor .x .x4 .x4 .x3, .logic .and .x .x13 .x6 .x13, .logic .orr .x .x13 .x4 .x13,
  .logic .eor .x .x16 .x16 .x13, .logic .and .x .x16 .x16 .x7, .logic .eor .x .x3 .x16 .x17,
  .logic .eor .x .x8 .x8 .x10, .logic .eor .x .x15 .x15 .x8, .ldr .x .x8 .x2 40,
  .logic .and .x .x8 .x8 .x4, .logic .eor .x .x15 .x15 .x8, .logic .orr .x .x11 .x11 .x7,
  .logic .eor .x .x11 .x11 .x15, .logic .eor .x .x6 .x14 .x6, .logic .eor .x .x15 .x15 .x9,
  .logic .and .x .x6 .x6 .x15, .ldr .x .x15 .x2 32, .logic .eor .x .x15 .x15 .x4,
  .logic .eor .x .x6 .x6 .x15, .logic .and .x .x14 .x14 .x7, .logic .eor .x .x5 .x14 .x6,
  .addImm .x .x4 .x12 0, .addImm .x .x6 .x11 0]

/-- The allocated short circuit for S-box 6. -/
def sboxCode5 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .eor .x .x10 .x7 .x4,
  .logic .orr .x .x11 .x7 .x3, .logic .and .x .x11 .x8 .x11, .logic .eor .x .x10 .x10 .x11,
  .logic .eor .x .x12 .x3 .x10, .logic .eor .x .x13 .x12 .x9, .logic .and .x .x13 .x4 .x13,
  .logic .and .x .x12 .x8 .x12, .logic .eor .x .x14 .x7 .x12, .logic .eor .x .x15 .x8 .x6,
  .logic .orr .x .x16 .x14 .x15, .logic .eor .x .x17 .x10 .x16, .str .x .x12 .x2 32,
  .logic .and .x .x12 .x6 .x17, .str .x .x10 .x2 40, .logic .eor .x .x10 .x3 .x9,
  .logic .and .x .x10 .x12 .x10, .logic .orr .x .x14 .x13 .x14, .str .x .x13 .x2 48,
  .logic .eor .x .x13 .x10 .x14, .str .x .x10 .x2 56, .logic .and .x .x10 .x13 .x5,
  .logic .eor .x .x10 .x10 .x17, .logic .eor .x .x16 .x7 .x16, .str .x .x10 .x2 64,
  .logic .eor .x .x10 .x16 .x9, .logic .and .x .x10 .x3 .x10, .logic .eor .x .x6 .x6 .x10,
  .logic .eor .x .x10 .x12 .x9, .logic .and .x .x10 .x4 .x10, .logic .orr .x .x10 .x6 .x10,
  .logic .orr .x .x7 .x7 .x15, .logic .eor .x .x13 .x13 .x7, .logic .orr .x .x11 .x11 .x10,
  .logic .eor .x .x13 .x13 .x11, .logic .orr .x .x17 .x8 .x17, .logic .and .x .x14 .x14 .x17,
  .logic .eor .x .x14 .x6 .x14, .ldr .x .x17 .x2 56, .logic .eor .x .x17 .x17 .x9,
  .logic .and .x .x17 .x14 .x17, .ldr .x .x11 .x2 48, .logic .orr .x .x11 .x11 .x5,
  .logic .eor .x .x11 .x11 .x17, .ldr .x .x17 .x2 40, .logic .eor .x .x17 .x17 .x14,
  .logic .eor .x .x17 .x17 .x9, .logic .and .x .x4 .x4 .x17, .logic .eor .x .x7 .x7 .x9,
  .logic .eor .x .x16 .x16 .x7, .logic .eor .x .x4 .x4 .x16, .logic .eor .x .x7 .x5 .x9,
  .logic .and .x .x4 .x4 .x7, .logic .eor .x .x4 .x4 .x13, .ldr .x .x13 .x2 32,
  .logic .eor .x .x3 .x3 .x13, .logic .eor .x .x8 .x8 .x6, .logic .and .x .x3 .x3 .x8,
  .logic .eor .x .x12 .x12 .x16, .logic .eor .x .x3 .x3 .x12, .logic .eor .x .x5 .x5 .x9,
  .logic .and .x .x10 .x10 .x5, .logic .eor .x .x6 .x10 .x3, .ldr .x .x3 .x2 64,
  .str .x .x4 .x2 32, .addImm .x .x4 .x11 0, .ldr .x .x5 .x2 32]

/-- The allocated short circuit for S-box 7. -/
def sboxCode6 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .eor .x .x10 .x5 .x4,
  .logic .eor .x .x11 .x6 .x10, .logic .and .x .x12 .x3 .x11, .logic .and .x .x13 .x5 .x10,
  .logic .eor .x .x14 .x7 .x13, .logic .and .x .x15 .x12 .x14, .logic .and .x .x16 .x3 .x13,
  .logic .eor .x .x17 .x6 .x16, .str .x .x13 .x2 32, .logic .orr .x .x13 .x14 .x17,
  .logic .eor .x .x10 .x3 .x10, .str .x .x3 .x2 40, .logic .eor .x .x3 .x13 .x10,
  .str .x .x6 .x2 48, .logic .eor .x .x6 .x15 .x9, .logic .and .x .x6 .x8 .x6,
  .logic .eor .x .x3 .x6 .x3, .logic .eor .x .x11 .x11 .x9, .logic .and .x .x11 .x4 .x11,
  .logic .orr .x .x6 .x14 .x11, .logic .eor .x .x17 .x12 .x17, .logic .eor .x .x6 .x6 .x17,
  .logic .eor .x .x12 .x12 .x10, .logic .eor .x .x10 .x12 .x9, .logic .and .x .x5 .x5 .x10,
  .logic .eor .x .x10 .x5 .x9, .logic .and .x .x10 .x14 .x10, .logic .eor .x .x4 .x4 .x17,
  .logic .eor .x .x10 .x10 .x4, .logic .eor .x .x16 .x16 .x9, .logic .and .x .x12 .x12 .x16,
  .logic .orr .x .x5 .x5 .x12, .logic .eor .x .x13 .x7 .x13, .logic .and .x .x13 .x10 .x13,
  .logic .eor .x .x13 .x5 .x13, .logic .and .x .x16 .x13 .x8, .logic .eor .x .x4 .x16 .x10,
  .ldr .x .x16 .x2 48, .logic .eor .x .x16 .x16 .x9, .logic .and .x .x14 .x14 .x16,
  .logic .orr .x .x12 .x12 .x14, .ldr .x .x14 .x2 32, .logic .orr .x .x14 .x14 .x10,
  .logic .and .x .x12 .x12 .x14, .logic .eor .x .x13 .x13 .x12, .logic .eor .x .x11 .x11 .x5,
  .ldr .x .x5 .x2 40, .logic .and .x .x5 .x5 .x11, .logic .orr .x .x15 .x15 .x5,
  .logic .eor .x .x12 .x12 .x15, .logic .eor .x .x5 .x8 .x9, .logic .and .x .x5 .x12 .x5,
  .logic .eor .x .x5 .x5 .x6, .logic .and .x .x7 .x7 .x15, .logic .eor .x .x6 .x6 .x9,
  .logic .eor .x .x7 .x7 .x6, .logic .eor .x .x12 .x12 .x7, .logic .orr .x .x13 .x13 .x8,
  .logic .eor .x .x13 .x13 .x12, .str .x .x5 .x2 40, .addImm .x .x5 .x13 0,
  .ldr .x .x6 .x2 40]

/-- The allocated short circuit for S-box 8. -/
def sboxCode7 : List Instr := [
  .movz .x .x9 0 0, .subImm .x .x9 .x9 1, .logic .eor .x .x10 .x7 .x9,
  .logic .and .x .x10 .x6 .x10, .logic .eor .x .x11 .x6 .x9, .logic .and .x .x11 .x4 .x11,
  .logic .eor .x .x11 .x5 .x11, .logic .and .x .x12 .x8 .x11, .logic .eor .x .x13 .x10 .x9,
  .logic .and .x .x13 .x12 .x13, .logic .eor .x .x14 .x11 .x9, .logic .and .x .x14 .x7 .x14,
  .logic .orr .x .x15 .x8 .x14, .logic .eor .x .x16 .x6 .x9, .logic .and .x .x16 .x7 .x16,
  .logic .eor .x .x16 .x4 .x16, .logic .and .x .x17 .x15 .x16, .logic .orr .x .x12 .x12 .x17,
  .logic .eor .x .x11 .x11 .x9, .logic .eor .x .x17 .x17 .x11, .logic .eor .x .x15 .x15 .x9,
  .logic .and .x .x6 .x6 .x15, .logic .eor .x .x17 .x17 .x6, .logic .eor .x .x10 .x10 .x17,
  .logic .orr .x .x6 .x13 .x3, .logic .eor .x .x6 .x6 .x10, .logic .eor .x .x10 .x8 .x10,
  .logic .and .x .x15 .x4 .x10, .logic .eor .x .x17 .x7 .x17, .logic .eor .x .x15 .x15 .x17,
  .logic .eor .x .x14 .x14 .x15, .logic .eor .x .x15 .x12 .x15, .logic .orr .x .x7 .x7 .x15,
  .logic .eor .x .x4 .x4 .x10, .logic .eor .x .x7 .x7 .x4, .logic .and .x .x12 .x12 .x3,
  .logic .eor .x .x4 .x12 .x7, .logic .eor .x .x16 .x16 .x14, .logic .orr .x .x17 .x5 .x17,
  .logic .eor .x .x17 .x16 .x17, .logic .eor .x .x8 .x8 .x17, .logic .and .x .x8 .x8 .x3,
  .logic .eor .x .x8 .x8 .x14, .logic .eor .x .x5 .x5 .x9, .logic .and .x .x16 .x16 .x5,
  .logic .and .x .x7 .x7 .x16, .logic .eor .x .x13 .x13 .x17, .logic .eor .x .x7 .x7 .x13,
  .logic .orr .x .x7 .x7 .x3, .logic .eor .x .x7 .x7 .x14, .addImm .x .x3 .x8 0,
  .addImm .x .x5 .x6 0, .addImm .x .x6 .x7 0]

def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun i => sboxCode i ==
  ScalarAlloc.compile (Bitslice.box i) sboxIns (sboxOuts i)

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

end VG.Impl.TripleDes.AArch64
