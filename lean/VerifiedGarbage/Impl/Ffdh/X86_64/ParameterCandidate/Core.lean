module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessRange
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Load
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue

/-! # One FFDH parameter candidate on x86-64

The outer 32-word header keeps the arguments and random-tape position.
The shared Miller–Rabin workspace follows it. Its normal link at slot 16
points back to the outer header and survives every prepared round call.
The output buffer temporarily holds q and sampled witnesses; p is restored
from the original random prefix only when needed.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open Crt (ws stk sLink leave wsNew)
open VG.Impl.RsaKeyGen.X86_64.Candidate (kFlag)

def oOut : Nat := 6
def oLen : Nat := 7
def oUsedP : Nat := 8
def oBits : Nat := 9
def oGen : Nat := 10
def oRandStart : Nat := 11
def oRandPtr : Nat := 12
def oRandLeft : Nat := 13
def oUsed : Nat := 14
def oWitnessBits : Nat := 15
def oWitnessLen : Nat := 16
def oChecks : Nat := 17
def oIndex : Nat := 18
def oStatus : Nat := 19
def oInner : Nat := 20

/-- Save the ABI arguments and callee-saved registers in the outer header. -/
def entry : List Instr :=
  [.mov .rax (.mem (stk 2)), .mov .r10 (.mem (stk 1))] ++ Domain.save .rax ++
  [.mov32 .r8 (.reg .r8), .store (ws .rax oOut) .rdi, .store (ws .rax oLen) .rsi,
   .store (ws .rax oUsedP) .rdx, .store (ws .rax oBits) .rcx, .store (ws .rax oGen) .r8,
   .store (ws .rax oRandStart) .r9, .store (ws .rax oRandPtr) .r9,
   .store (ws .rax oRandLeft) .r10, .mov32 .r10 (.imm 0), .store (ws .rax oUsed) .r10,
   .store (ws .rax oStatus) .r10, .mov .rdi (.reg .rax)]

def status (n : Nat) : Prog isa :=
  .block [.mov32 .rax (.imm (BitVec.ofNat 32 n)), .store (hdr oStatus) .rax]

def innerStatus (n : Nat) : Prog isa := .seq (.block [leave]) (status n)

/-- Reconstruct p without consuming any additional randomness. -/
def shapeOriginal : Prog isa := seqs [
  .block [.mov .rbp (.reg .rdi), .mov .rax (.mem (hdr oOut)), .mov .rsi (.mem (hdr oRandStart)),
    .mov .rcx (.mem (hdr oLen)), .mov .rdx (.mem (hdr oBits)), .mov .rdi (.reg .rax)],
  shape, .block [.mov .rdi (.reg .rbp)]]

def halveOutput : Prog isa := seqs [
  .block [.mov .rbp (.reg .rdi), .mov .rax (.mem (hdr oOut)), .mov .rcx (.mem (hdr oLen)), .mov .rdi (.reg .rax)],
  halve, .block [.mov .rdi (.reg .rbp)]]

/-- Consume p's initial random prefix. -/
def consumeCandidate : List Instr :=
  [.mov .rcx (.mem (hdr oLen)), .mov .rax (.mem (hdr oRandPtr)), .alu .add .rax (.reg .rcx),
   .store (hdr oRandPtr) .rax, .mov .rax (.mem (hdr oRandLeft)), .alu .sub .rax (.reg .rcx),
   .store (hdr oRandLeft) .rax, .store (hdr oUsed) .rcx]

/-- Width and witness policy for the bit length already in RDX. -/
def phaseWidth : List Instr :=
  [.store (hdr oWitnessBits) .rdx, .mov .rcx (.reg .rdx), .alu .add .rcx (.imm 7), .shift .shr .rcx 3,
   .store (hdr oWitnessLen) .rcx, .mov32 .rax (.imm 64), .mov32 .rcx (.imm 128),
   .alu .cmp .rdx (.imm 2049), .cmov .ae .rax (.reg .rcx), .store (hdr oChecks) .rax,
   .mov .rax (.reg .rdi), .alu .add .rax (.imm 256)]

/-- Set the actual modulus width and independent uniform-witness count. -/
def phaseHead (q : Bool) : List Instr :=
  [.mov .rdx (.mem (hdr oBits))] ++ (if q then [.alu .sub .rdx (.imm 1)] else []) ++ phaseWidth

def phaseSetup (q : Bool) : Prog isa := .seq (.block (phaseHead q))
  (.seq (seqs (wsNew oInner oWitnessLen)) (.block [.mov .rdi (.mem (hdr oInner))]))

/-- Load the p-sized output buffer using this modulus's own word width. -/
def loadOutput : Prog isa := .seq
  (.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax oOut)), .mov .rcx (.mem (ws .rax oLen))])
  loadCandidate

/-- The available tape is tested before any sampled bytes are read. -/
def drawHead : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov .rcx (.mem (ws .rax oRandLeft)),
   .alu .cmp .rcx (.mem (ws .rax oWitnessLen))]

/-- Terminate the rejection loop with status 0 and ZF clear. -/
def drawShort : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov32 .rdx (.imm 0), .store (ws .rax oStatus) .rdx, .alu .cmp .rdx (.imm 1)]

/-- Advance the tape and switch temporarily to the witness byte buffer. -/
def drawSetup : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax oRandPtr)),
   .mov .rcx (.mem (ws .rax oWitnessLen)), .mov .rdx (.mem (ws .rax oWitnessBits)),
   .mov .r8 (.reg .rsi), .alu .add .r8 (.reg .rcx), .store (ws .rax oRandPtr) .r8,
   .mov .r8 (.mem (ws .rax oRandLeft)), .alu .sub .r8 (.reg .rcx), .store (ws .rax oRandLeft) .r8,
   .mov .r8 (.mem (ws .rax oUsed)), .alu .add .r8 (.reg .rcx), .store (ws .rax oUsed) .r8,
   .mov .rbp (.reg .rdi), .mov .rdi (.mem (ws .rax oOut))]

/-- Return to the modulus workspace and load the masked witness. -/
def drawLoad : List Instr :=
  [.mov .rdi (.reg .rbp), .mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax oOut)),
   .mov .rcx (.mem (ws .rax oWitnessLen))]

/-- MOV and STORE preserve the range check's ZF, which drives rejection. -/
def drawFinish : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov32 .rdx (.imm 1), .store (ws .rax oStatus) .rdx]

def cutRestore : Prog isa := .seq witnessCut (.block drawLoad)

def cutLoad : Prog isa := .seq cutRestore (loadNumber aXm)

def drawPrefix : Prog isa := .seq (.block drawSetup) cutLoad

def drawSample : Prog isa := seqs [drawPrefix, witnessRange, .block drawFinish]

def drawBody : Prog isa := .seq (.block drawHead) (.ite .b (.block drawShort) drawSample)

/-- Retry out-of-range witnesses until acceptance or exhaustion of the tape. -/
def drawWitness : Prog isa := .loop drawBody .e

def roundFail : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov32 .rdx (.imm 2), .store (ws .rax oStatus) .rdx]

/-- Count only accepted, passing rounds. Status 4 requests another witness. -/
def roundPass : List Instr :=
  [.mov .r9 (.mem (hdr sLink)), .mov .rcx (.mem (ws .r9 oIndex)), .alu .add .rcx (.imm 1),
   .store (ws .r9 oIndex) .rcx, .alu .cmp .rcx (.mem (ws .r9 oChecks)),
   .mov32 .rax (.imm 4), .mov32 .rdx (.imm 1), .cmov .ae .rax (.reg .rdx), .store (ws .r9 oStatus) .rax]

def roundResult : Prog isa := .seq
  (.block [.mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)])
  (.ite .e (.block roundFail) (.block roundPass))

variable (mul : Nat → Nat → Nat → Prog isa) (r2 round : Prog isa)

def statusTest : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov .rcx (.mem (ws .rax oStatus)), .alu .test .rcx (.reg .rcx)]

def statusMore : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov .rcx (.mem (ws .rax oStatus)), .alu .cmp .rcx (.imm 4)]

def roundRun : Prog isa := .seq (.block statusTest)
  (.ite .e (.block []) (.seq (witnessRound mul round) roundResult))

def roundBody : Prog isa := seqs [drawWitness, roundRun mul round, .block statusMore]

def roundInit : List Instr :=
  [.mov .rax (.mem (hdr sLink)), .mov32 .rcx (.imm 0), .store (ws .rax oIndex) .rcx]

/-- The round count is per modulus, so a 2049-bit p uses 128 rounds while
its 2048-bit q uses 64. -/
def rounds : Prog isa := .seq (.block roundInit)
  (.loop (roundBody mul round) .e)

/-- Shared modulus preparation and uniform witness policy for both phases. -/
def modulusPolicy : Prog isa := .seq (prepareModulus mul r2) (rounds mul round)

/-- Return to the outer frame and test whether a modulus passed. -/
def leaveStatus : Prog isa := .block [leave, .mov .rax (.mem (hdr oStatus)), .alu .cmp .rax (.imm 1)]

/-- The p test follows the successful q test; restore p again for output. -/
def testP : Prog isa := seqs [shapeOriginal, phaseSetup false, loadOutput, modulusPolicy mul r2 round, leaveStatus,
  .ite .e shapeOriginal (.block [])]

def testQ : Prog isa := seqs [halveOutput, phaseSetup true, loadOutput, primeCheck,
  .ite .e (seqs [modulusPolicy mul r2 round,
    leaveStatus,
    .ite .e (testP mul r2 round) (.block [])]) (innerStatus 2)]

/-- Apply the requested generator's candidate congruence policy. -/
def generatorPolicy : Prog isa := .seq
  (.block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax oGen))]) generatorCheck

/-- Trial checks before the independent q and p witness policies. -/
def candidateFilter : Prog isa := seqs [phaseSetup false, loadOutput, generatorPolicy,
  .ite .e (.seq primeCheck (.ite .e (.seq (.block [leave]) (testQ mul r2 round)) (innerStatus 2))) (innerStatus 2)]

def testCandidate : Prog isa := seqs [shapeOriginal, .block consumeCandidate, candidateFilter mul r2 round]

/-- Clear rejected outputs, write the consumed count (zero on exhaustion),
and restore the ABI's callee-saved registers. -/
def finish : Prog isa := seqs [
  .block [.mov .rax (.mem (hdr oStatus)), .alu .cmp .rax (.imm 1)],
  .ite .e (.block []) (Keys.zeroOut oOut oLen),
  .block ([.mov .rax (.mem (hdr oStatus)), .mov .rdx (.mem (hdr oUsedP)), .mov .rcx (.mem (hdr oUsed)),
    .alu .test .rax (.reg .rax), .cmov .e .rcx (.reg .rax), .store (at0 .rdx) .rcx] ++ exit)]

def body : Prog isa := .seq
  (.block (entry ++ [.mov .rax (.mem (hdr oRandLeft)), .alu .cmp .rax (.mem (hdr oLen))]))
  (.ite .b (.block []) (testCandidate mul r2 round))

def code : Prog isa := .seq (body mul r2 round) finish

end VG.Impl.Ffdh.X86_64.ParameterCandidate
