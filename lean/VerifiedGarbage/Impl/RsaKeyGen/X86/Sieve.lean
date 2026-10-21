module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-! # A prepared small-prime sieve on baseline i686

The divisor and inverse pairs live in one read-only static, shared by all
candidates. Each trial consumes complete native words. A rejected candidate
may stop at its first divisor; accepted candidates visit the same full table.
The candidate contract releases rejected candidates, so this early exit must
be justified by that contract's leakage proof when the sieve is integrated.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Sieve
open VG VG.X86

structure Slots where
  candidate : Nat
  ending : Nat
  cursor : Nat
  remaining : Nat
  hit : Nat

def stackSlots : Slots := ⟨0, 4, 8, 12, 16⟩
def slot (d : Nat) : MemOp := ⟨.esp, d⟩

def loadPrime (l : Slots) : List Instr :=
  [.mov .edx (.mem (slot l.cursor)), .mov .ebx (.mem ⟨.edx, 0⟩), .mov .esi (.mem ⟨.edx, 4⟩),
    .mov .edi (.mem (slot l.candidate)), .mov .ebp (.imm 0)]

def saveHit (l : Slots) : List Instr :=
  [.store (slot l.hit) .eax, .mov .ecx (.reg .eax), .alu .sub .ecx (.imm 1)]

def advanceCursor (l : Slots) : List Instr :=
  [.mov .edx (.mem (slot l.cursor)), .alu .add .edx (.imm 8), .store (slot l.cursor) .edx]

def advanceCount (l : Slots) : List Instr :=
  [.mov .eax (.mem (slot l.remaining)), .alu .sub .eax (.imm 1), .alu .and .eax (.reg .ecx),
    .store (slot l.remaining) .eax, .alu .cmp .eax (.imm 0)]

/-- Record the trial bit, then set the next count to zero on a hit. -/
def advance (l : Slots) : List Instr := saveHit l ++ advanceCursor l ++ advanceCount l

def step (l : Slots) : Prog isa :=
  .seq (.block (loadPrime l)) (.seq (Trial.divisor l.ending) (.block (advance l)))

def loop (l : Slots) : Prog isa :=
  .seq (.loop (step l) .ne) (.block [.mov .eax (.mem (slot l.hit))])

/-- Save the input pointer and public end before obtaining the static address. -/
def candidateSlots (l : Slots) (w : Nat) : List Instr :=
  [.store (slot l.candidate) .edi, .mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 (8 * w))),
    .store (slot l.ending) .eax]

def tableAddress : Prog isa :=
  .frame (.symPush .eax TrialTable32.symbol) (.block []) (.pop .ecx 1)

def tableCount (w : Nat) : Nat := if w ≤ 16 then 512 else 1024

def tableSlots (l : Slots) (w : Nat) : List Instr :=
  [.store (slot l.cursor) .eax, .mov .eax (.imm (BitVec.ofNat 32 (tableCount w))),
    .store (slot l.remaining) .eax, .mov .eax (.imm 0), .store (slot l.hit) .eax]

/-- The caller reserves the five disjoint stack words named by l. EDI starts
at the candidate. The symbol-address prefix uses four further stack bytes. -/
def body (l : Slots) (w : Nat) : Prog isa :=
  .seq (.block (candidateSlots l w)) (.seq tableAddress (.seq (.block (tableSlots l w)) (loop l)))

end VG.Impl.RsaKeyGen.X86.Sieve
