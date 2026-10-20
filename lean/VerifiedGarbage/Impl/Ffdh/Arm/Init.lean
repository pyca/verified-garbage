module

public import VerifiedGarbage.TCB.Arm.Isa

/-! Native FFDH controller initialization on ARMv7. The public controller
words remain 64 bits wide, including the 2^32 attempt budget at 8192 bits. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm
open VG VG.Arm

/-- Clear the four public 64-bit controller words and return failure. -/
def clearController : Prog isa := .block [
  .mov .r3 (.imm 0),
  .str .r3 .r0 0, .str .r3 .r0 4, .str .r3 .r0 8, .str .r3 .r0 12,
  .str .r3 .r0 16, .str .r3 .r0 20, .str .r3 .r0 24, .str .r3 .r0 28,
  .mov .r0 (.imm 0)]

/-- Compare the public input in r1 against a 16-bit unsigned bound. -/
def boundTest (b : BitVec 16) : List Instr := [
  .mov .r12 (.imm 0), .movw .r3 b, .cmp .r1 (.reg .r3),
  .adc .r3 .r12 (.imm 0), .cmp .r3 (.imm 0)]

/-- The unsigned public input in r1 lies between the inclusive bounds.
Only caller-saved r3 and r12 are used. -/
def boundedController (lo hi : BitVec 16) (accept : Prog isa) : Prog isa :=
  .seq (.block (boundTest lo)) (.ite .eq clearController
    (.seq (.block (boundTest hi)) (.ite .ne clearController accept)))

namespace Generation

/-- Initialize bits^2*64, ceil(bits/8), the entropy cap, and the first
request. Splitting the product before shifting preserves the high word. -/
def budget : Prog isa := .block [
  .mul .r3 .r1 .r1,
  .mov .r12 (.shifted .r3 .lsr 26),
  .mov .r3 (.shifted .r3 .lsl 6), .str .r3 .r0 0, .str .r12 .r0 4]

def width : Prog isa := .block [
  .mov .r2 (.imm 0),
  .dp .add .r3 .r1 (.imm 7), .mov .r3 (.shifted .r3 .lsr 3),
  .str .r3 .r0 8, .str .r2 .r0 12]

def entropy : Prog isa := .block [
  .dp .add .r12 .r3 (.shifted .r3 .lsl 15), .str .r12 .r0 16, .str .r2 .r0 20]

def request : Prog isa := .block [
  .mov .r12 (.shifted .r3 .lsl 9), .str .r12 .r0 24, .str .r2 .r0 28,
  .mov .r0 (.imm 1)]

def initializeState : Prog isa := .seq budget (.seq width (.seq entropy request))

def generator : Prog isa :=
  .seq (.block [.cmp .r2 (.imm 2)]) (.ite .eq initializeState
    (.seq (.block [.cmp .r2 (.imm 5)]) (.ite .eq initializeState clearController)))

def init : Prog isa := boundedController 512 8193 generator

end Generation

namespace KeyGeneration

def initializeState : Prog isa := .block [
  .mov .r3 (.imm 128), .mov .r12 (.imm 0),
  .str .r3 .r0 0, .str .r12 .r0 4, .str .r3 .r0 8, .str .r12 .r0 12,
  .str .r1 .r0 16, .str .r12 .r0 20,
  .str .r1 .r0 24, .str .r12 .r0 28, .mov .r0 (.imm 1)]

def init : Prog isa := boundedController 64 1025 initializeState

end KeyGeneration
end VG.Impl.Ffdh.Arm
