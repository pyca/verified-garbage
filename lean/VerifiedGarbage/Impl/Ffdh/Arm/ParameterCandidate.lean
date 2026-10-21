module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Impl.Ffdh.Arm.CandidatePrepare
public import VerifiedGarbage.Impl.Ffdh.Arm.CallerRows
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16
public import VerifiedGarbage.Impl.Bignum.Arm.TwoPower
public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
public import VerifiedGarbage.Impl.Rsa.Arm.Recover
public import VerifiedGarbage.Impl.RsaKeyGen.Primes

/-! One safe-prime parameter candidate on ARMv7. The 72-byte local frame
keeps the arguments and public search state. The modulus is shaped in the
output buffer, tested as q in place, and reloaded as p. Both phases use
the workspace width of p, including when q occupies one fewer limb.

The shared RSA Miller–Rabin round owns the expensive exponentiation. The
candidate's random tape is public under the existing parameter contract,
so decomposition of n-1 may stop at its first odd quotient. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Impl.Bignum.Arm

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | p :: ps => .seq p (seqs ps)

-- Locals: workspace 0, out 4, modulus source 8, width 12, tape 16/20,
-- bits 24, generator 28, used pointer 32, capacity 36, consumed 40,
-- phase bits 44, witness width 48, checks 52, passed 56, temporary 60/64.
def save (r : Reg) (slot : Nat) : List Instr := [.addSp .r12 0, .str r .r12 slot]

def entry : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 4, .str .r0 .r12 8, .str .r1 .r12 12,
    .str .r2 .r12 32, .str .r3 .r12 24,
    .ldrSp .r0 128, .str .r0 .r12 28,
    .ldrSp .r0 132, .str .r0 .r12 16,
    .ldrSp .r0 136, .str .r0 .r12 20,
    .ldrSp .r0 140, .str .r0 .r12 0,
    .ldrSp .r0 144, .str .r0 .r12 36,
    .mov .r0 (.imm 0), .str .r0 .r12 40]

def clearOutput : Prog isa := .seq
  (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) Domain.GenerateKey.zeros

/-- Write the consumed count in r3 as a complete u64 and return status. -/
def finish (status : Nat) : List Instr :=
  [.ldrSp .r2 32, .str .r3 .r2 0, .mov .r1 (.imm 0), .str .r1 .r2 4,
    .mov .r0 (.imm (BitVec.ofNat 32 status))]

def finNone : Prog isa := .seq clearOutput (.block ([.mov .r3 (.imm 0)] ++ finish 0))
def finRejected : Prog isa := .seq clearOutput (.block ([.ldrSp .r3 40] ++ finish 2))
def finAccepted : Prog isa := .block ([.ldrSp .r3 40] ++ finish 1)

def geFlag : List Instr :=
  [.subs .r3 .r1 (.reg .r2), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]

def initialRoom : List Instr := [.ldrSp .r1 20, .ldrSp .r2 12] ++ geFlag
def witnessRoom : List Instr :=
  [.ldrSp .r1 20, .ldrSp .r2 40, .dp .sub .r1 .r1 (.reg .r2), .ldrSp .r2 48] ++ geFlag

def maskStep : List Instr :=
  [.dp .add .r7 .r7 (.reg .r7), .dp .add .r7 .r7 (.imm 1), .subs .r6 .r6 (.imm 1)]

def shapeFirst : List Instr :=
  [.ldrSp .r4 4, .ldrb .r3 .r4 0, .dp .and .r3 .r3 (.reg .r7),
    .mov .r9 (.shifted .r7 .lsr 1), .dp .add .r9 .r9 (.imm 1),
    .dp .orr .r3 .r3 (.reg .r9), .strb .r3 .r4 0]

def shapeLast : List Instr :=
  [.ldrSp .r5 12, .dp .add .r4 .r4 (.reg .r5), .dp .sub .r4 .r4 (.imm 1),
    .ldrb .r3 .r4 0, .dp .orr .r3 .r3 (.imm 1), .strb .r3 .r4 0]

def shapeMaskHead : List Instr :=
  [.ldrSp .r6 24, .dp .sub .r6 .r6 (.imm 1), .dp .and .r6 .r6 (.imm 7),
    .dp .add .r6 .r6 (.imm 1), .mov .r7 (.imm 0)]

def shapeMasks : Prog isa := .seq (.block shapeMaskHead) (.loop (.block maskStep) .ne)

def shapeCopyHead : List Instr := [.ldrSp .r0 4, .ldrSp .r1 16, .ldrSp .lr 12]

def shapeCopy : Prog isa := .seq (.block shapeCopyHead) copyBytes

/-- Copy the first k tape bytes, mask to bits, and set the high and low bits. -/
def shapeP : Prog isa := seqs [
  shapeCopy,
  shapeMasks,
  .block shapeFirst, .block shapeLast]

/-- The small-prime table is beyond the 28 arrays the shared round uses. -/
def tablePointer : List Instr :=
  [.ldrSp .r0 0, .ldrSp .r7 12, .dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3),
    .dp .add .r7 .r7 (.imm 2), .mov .r7 (.shifted .r7 .lsl 3),
    .mov .r11 (.imm 34), .mul .r11 .r11 .r7, .dp .add .r11 .r11 (.reg .r0),
    .dp .add .r11 .r11 (.imm 256)]

/-- RSA's requested-width trial bound, shared by p and q. -/
def trialCount (octets : Nat) : Nat := if octets ≤ 128 then 512 else 1024

def tableWrites (count : Nat) : List Instr := (List.range count).flatMap fun j =>
  [.movw .r1 (BitVec.ofNat 16 (VG.Impl.RsaKeyGen.tabEntry j)), .str .r1 .r11 (4 * j)]

def tableWrite : List Instr := tablePointer ++ tableWrites 1024

/-- Consume the next least-significant radix-2^16 digit of the big-endian
buffer ending at r0, with r1 octets left. The final odd octet is zero-padded. -/
def trialDigitHead : List Instr :=
  [.dp .sub .r0 .r0 (.imm 1), .ldrb .r5 .r0 0, .subs .r1 .r1 (.imm 1)]

def trialDigitHigh : List Instr :=
  [.dp .sub .r0 .r0 (.imm 1), .ldrb .r7 .r0 0,
    .dp .orr .r5 .r5 (.shifted .r7 .lsl 8), .dp .sub .r1 .r1 (.imm 1)]

def trialDigit : Prog isa := .seq (.block trialDigitHead)
  (.ite .eq (.block []) (.block trialDigitHigh))

/-- Set up RSA’s negative inverse, the input end pointer and zero accumulator. -/
def trialStart : List Instr := [.mov .r3 (.reg .r7), .mov .r4 (.reg .r3)] ++
    TrialDivision16.newton ++ TrialDivision16.newton ++ TrialDivision16.newton ++
    [.mov .r5 (.imm 0), .dp .sub .r4 .r5 (.reg .r4),
      .mov .r4 (.shifted .r4 .lsl 16), .mov .r4 (.shifted .r4 .lsr 16),
      .ldrSp .r0 4, .ldrSp .r1 12, .dp .add .r0 .r0 (.reg .r1), .mov .r2 (.imm 0)]

def trialStep : Prog isa := .seq trialDigit
  (.block (TrialDivision16.redc ++ [.cmp .r1 (.imm 0)]))

def trialFlag : Prog isa := .seq (.block [.cmp .r2 (.imm 0)])
  (.ite .eq (.block []) (.block [.cmp .r2 (.reg .r3)]))

/-- Trial division by the odd prime in r7 using RSA's radix-2^16 reducer.
Read octet pairs backwards, with a zero high octet for an odd byte length.
The final accumulator is below twice the prime, so zero or the prime
means divisibility. Z reports that result; r10/r11 remain the sieve cursor. -/
def trialSmall : Prog isa := seqs [.block trialStart, .loop trialStep .ne, trialFlag]

/-- Test p-1 with the same reducer, seeding its carry with the divisor minus one. -/
def trialOffsetInit : List Instr := [.dp .sub .r2 .r3 (.imm 1)]

def trialOffset : Prog isa := seqs [.block trialStart, .block trialOffsetInit,
  .loop trialStep .ne, trialFlag]

/-- Short public residue comparisons, unrolled by the emitter. -/
def residueEquals : List Nat → Prog isa
  | [] => .block []
  | [v] => .block [.cmp .r2 (.imm (BitVec.ofNat 32 v))]
  | v :: rest => .seq (.block [.cmp .r2 (.imm (BitVec.ofNat 32 v))])
      (.ite .eq (.block []) (residueEquals rest))

/-- For odd p, Z iff q=(p-1)/2 is odd. Reject even q before any trial division. -/
def qOdd : List Instr := [.ldrSp .r4 4, .ldrSp .r5 12, .dp .add .r4 .r4 (.reg .r5),
  .dp .sub .r4 .r4 (.imm 1), .ldrb .r2 .r4 0, .dp .and .r2 .r2 (.imm 3), .cmp .r2 (.imm 3)]

def residueLow : List Instr := [.ldrSp .r4 4, .ldrSp .r5 12, .dp .add .r4 .r4 (.reg .r5),
  .dp .sub .r4 .r4 (.imm 1), .ldrb .r2 .r4 0, .dp .and .r2 .r2 (.imm 7), .cmp .r2 (.imm 3)]

/-- Test a short list of residues using RSA's shared trial reducer. -/
def residuePrime (prime : Nat) (values : List Nat) : Prog isa :=
  seqs [.block [.mov .r7 (.imm (BitVec.ofNat 32 prime))], trialSmall, residueEquals values]

/-- For odd p, p mod 24 = 11 iff p mod 8 = 3 and p mod 3 = 2.
The shared reducer's radix is 1 modulo both 3 and 5. -/
def residue2 : Prog isa := .seq (.block residueLow)
  (.ite .eq (residuePrime 3 [2, 5]) (.block []))

/-- For odd p, p mod 10 is 3 or 7 iff p mod 5 is 3 or 2. -/
def residue5 : Prog isa := residuePrime 5 [2, 3, 7, 8]

def residue : Prog isa := .seq (.block [.ldrSp .r1 28, .cmp .r1 (.imm 2)]) (.ite .eq residue2 residue5)

def sieveInitRegisters : List Instr :=
  [.mov .r10 (.reg .r11), .ldrSp .r11 12, .subs .r11 .r11 (.imm 129),
    .mov .r11 (.imm 0), .adc .r11 .r11 (.imm 0), .mov .r11 (.shifted .r11 .lsl 9),
    .dp .add .r11 .r11 (.imm 512), .mov .r1 (.imm 0)]

def sieveInitTail : List Instr := sieveInitRegisters ++ save .r1 64

def sieveInit : Prog isa := .seq (.block tablePointer) (.block sieveInitTail)

def sieveEntry : List Instr := [.ldr .r7 .r10 0, .dp .add .r10 .r10 (.imm 4)]

def sieveFlag : Prog isa :=
  .ite .eq (.block ([.mov .r1 (.imm 1)] ++ save .r1 64)) (.block [])

def sieveCount : List Instr := [.subs .r11 .r11 (.imm 1)]

def sieveActiveStep : Prog isa := seqs [.block sieveEntry, trialSmall, sieveFlag, .block sieveCount]

def sieveFinish : List Instr := [.ldrSp .r1 64, .cmp .r1 (.imm 0)]

/-- Once a divisor has been found, jump directly to the table end. -/
def sieveSkip : List Instr :=
  [.dp .add .r10 .r10 (.shifted .r11 .lsl 2), .subs .r11 .r11 (.reg .r11)]

def sieveStep : Prog isa := .seq (.block sieveFinish) (.ite .eq sieveActiveStep (.block sieveSkip))

def sieve : Prog isa := seqs [sieveInit, .loop sieveStep .ne, .block sieveFinish]

def pairEntry : List Instr := [.ldr .r7 .r10 0]
def pairAdvance : List Instr := [.dp .add .r10 .r10 (.imm 4)]

/-- Test p and q against each prime before advancing the public table cursor. -/
def pairTrials : Prog isa := seqs [.block pairEntry, trialSmall,
  .ite .eq (.block []) (.seq (.block pairEntry) trialOffset)]

def pairActiveStep : Prog isa := seqs [pairTrials, sieveFlag, .block (pairAdvance ++ sieveCount)]
def pairStep : Prog isa := .seq (.block sieveFinish) (.ite .eq pairActiveStep (.block sieveSkip))
def pairSieve : Prog isa := seqs [sieveInit, .loop pairStep .ne, .block sieveFinish]

def halfByte : List Instr :=
  [.ldrb .r3 .r0 0, .mov .r1 (.shifted .r3 .lsr 1), .dp .orr .r1 .r1 (.reg .r2),
    .dp .and .r2 .r3 (.imm 1), .mov .r2 (.shifted .r2 .lsl 7), .strb .r1 .r0 0,
    .dp .add .r0 .r0 (.imm 1), .subs .lr .lr (.imm 1)]

/-- q = floor(p/2) in place; Z iff q is even. -/
def halveQ : Prog isa := seqs [
  .block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)],
  .loop (.block halfByte) .ne,
  .block [.dp .and .r1 .r1 (.imm 1), .cmp .r1 (.imm 0)]]

def keyContext : List Instr :=
  [.ldrSp .r0 0, .dp .add .r8 .r0 (.imm 96), .ldr .r9 .r0 48,
    .mov .r9 (.shifted .r9 .lsl 1), .dp .add .r9 .r9 (.imm 2)] ++ Rsa.Arm.Keys.stride

def keyStride : List Instr := [.str .r7 .r0 224, .mov .r1 (.imm 0), .str .r1 .r0 228]

def montKeyArrays : Prog isa := seqs [
  .block (Rsa.Arm.Recover.clrTop 0), .block (Rsa.Arm.Recover.clrTop 1),
  Rsa.Arm.Keys.copy 9 1, Rsa.Arm.Keys.sub3 10 0 9]

def montKeySetup : Prog isa := .seq (.block (keyContext ++ keyStride)) montKeyArrays

def montPrep : Prog isa := seqs [
  .block [.ldrSp .r0 0, .ldrSp .r6 12], VG.Impl.Ffdh.Arm.CandidatePrepare.code,
  .seq (smallConst 1 1) (montOp 1 1 4), montKeySetup]

def phaseBitHead (q : Bool) : List Instr :=
  [.ldrSp .r3 24] ++ (if q then [.dp .sub .r3 .r3 (.imm 1)] else []) ++ save .r3 44

def phaseWidth : List Instr :=
  [.dp .add .r4 .r3 (.imm 7), .mov .r4 (.shifted .r4 .lsr 3)] ++ save .r4 48

def phaseChecks : List Instr :=
  [.dp .sub .r3 .r3 (.imm 1), .subs .r3 .r3 (.imm 2048), .mov .r5 (.imm 0),
    .adc .r5 .r5 (.imm 0), .mov .r5 (.shifted .r5 .lsl 6), .dp .add .r5 .r5 (.imm 64)] ++ save .r5 52

def phasePassed : List Instr := [.mov .r1 (.imm 0)] ++ save .r1 56

def phaseHead (q : Bool) : List Instr := phaseBitHead q ++ phaseWidth ++ phaseChecks ++ phasePassed

def halfCountTail : List Instr :=
  [.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] ++ save .r1 60 ++
    Rsa.Arm.Keys.ptr .r0 29 ++ [.ldr .r1 .r0 0, .dp .and .r1 .r1 (.imm 1), .cmp .r1 (.imm 0)]

def halfCountStep : Prog isa := seqs [
  .block [.mov .r11 (.imm 0)], Rsa.Arm.Keys.half 29, .block halfCountTail]

def exponentHalfTail : List Instr := [.ldrSp .r1 64, .subs .r1 .r1 (.imm 1)] ++ save .r1 64

def exponentHalf : Prog isa := seqs [
  .block [.mov .r11 (.imm 0)], Rsa.Arm.Keys.half 27, .block exponentHalfTail]

def expCountInit : Prog isa := seqs [Rsa.Arm.Keys.copy 29 0,
  .block (Rsa.Arm.Keys.clrLow 29), .block ([.mov .r1 (.imm 0)] ++ save .r1 60)]

def expDecompose : Prog isa := .seq expCountInit (.loop halfCountStep .eq)

def exponentSigmaHead : List Instr := [.ldrSp .r1 60, .dp .and .r1 .r1 (.imm 3), .cmp .r1 (.imm 0)]

def exponentSigma : Prog isa := seqs [.block exponentSigmaHead,
  .ite .eq (.block [.mov .r1 (.imm 4)]) (.block []), .block (save .r1 64)]

def exponentPowerStore : List Instr := Rsa.Arm.Keys.ptr .r0 27 ++
  [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 8), .str .r2 .r0 0, .str .r3 .r0 4]

/-- The compact round's exponent and its complete u64 decomposition word. -/
def expSetup : Prog isa := seqs [expDecompose,
  exponentSigma, Rsa.Arm.Keys.copy 27 0, .loop exponentHalf .ne,
  .block ([.ldrSp .r1 60] ++ TwoPower.code),
  .block exponentPowerStore]

def witnessMaskHead : List Instr :=
  [.ldrSp .r6 44, .dp .sub .r6 .r6 (.imm 1), .mov .r5 (.shifted .r6 .lsr 5),
    .dp .and .r6 .r6 (.imm 31), .dp .add .r6 .r6 (.imm 1)]

def witnessMaskStore : List Instr :=
  [.ldrSp .r0 0, .ldr .r4 .r0 72, .dp .add .r4 .r4 (.shifted .r5 .lsl 2),
    .ldr .r3 .r4 0, .dp .and .r3 .r3 (.reg .r7), .str .r3 .r4 0]

def witnessMaskBits : Prog isa := .seq (.block [.mov .r1 (.reg .r6)])
  (.seq (.block TwoPower.code) (.block [.dp .sub .r7 .r2 (.imm 1)]))

/-- Mask the highest native word occupied by a witness, including at a
32- or 64-bit width boundary. Import has already cleared the higher words. -/
def witnessMask : Prog isa := seqs [.block witnessMaskHead, witnessMaskBits, .block witnessMaskStore]

def sampleWitness : Prog isa := .seq (importOperand 1) witnessMask

def onPassHead : List Instr := [.ldrSp .r1 56, .dp .add .r1 .r1 (.imm 1), .ldrSp .r2 52, .cmp .r1 (.reg .r2)]

def onPassFinish : List Instr := save .r1 56 ++ [.cmp .r3 (.imm 4)]

def onPass : Prog isa := seqs [.block onPassHead,
  .ite .eq (.block [.mov .r3 (.imm 1)]) (.block [.mov .r3 (.imm 4)]),
  .block onPassFinish]

def roundKernel (name : String) (body : Prog isa) : Prog isa := seqs [
  montOp 5 1 4, .block [.ldrSp .r0 0, .ldrSp .r1 36], .call name body]

def round (name : String) (body : Prog isa) : Prog isa := seqs [roundKernel name body,
  .block [.cmp .r0 (.imm 0)],
  .ite .eq (.block [.mov .r3 (.imm 2), .cmp .r3 (.imm 4)]) onPass]

def drawArgs : List Instr :=
  [.ldrSp .r0 0, .ldrSp .r4 16, .ldrSp .r1 40, .ldrSp .r6 48,
    .dp .add .r4 .r4 (.reg .r1), .dp .add .r1 .r1 (.reg .r6)]

def drawHead : Prog isa := .seq (.block drawArgs) (.block (save .r1 40))

def drawSample : Prog isa := .seq drawHead sampleWitness

def drawRange : Prog isa := .seq drawSample (VG.Impl.Ffdh.Arm.inRange 1)

def draw (name : String) (body : Prog isa) : Prog isa := seqs [
  drawRange,
  .block [.cmp .r11 (.imm 0)],
  .ite .eq (.block [.mov .r3 (.imm 4), .cmp .r3 (.imm 4)]) (round name body)]

def witnessStep (name : String) (body : Prog isa) : Prog isa :=
  seqs [.block witnessRoom,
    .ite .eq (.block [.mov .r3 (.imm 0), .cmp .r3 (.imm 4)]) (draw name body)]

def millerRabin (name : String) (body : Prog isa) : Prog isa := .loop (witnessStep name body) .eq

def phasePrepared : Prog isa := .seq montPrep expSetup

def phaseRun (name : String) (body : Prog isa) : Prog isa := .seq phasePrepared (millerRabin name body)

def test (q : Bool) (name : String) (body : Prog isa) : Prog isa := .seq (.block (phaseHead q)) (phaseRun name body)

/-- Limit p's first phase to one witness, or finish its remaining witnesses. -/
def phaseLimit (first : Bool) : List Instr :=
  (if first then [.mov .r1 (.imm 1)] else [.ldrSp .r1 52, .dp .sub .r1 .r1 (.imm 1)]) ++ save .r1 52

def testLimited (first : Bool) (name : String) (body : Prog isa) : Prog isa :=
  .seq (.block (phaseHead false ++ phaseLimit first)) (phaseRun name body)

def result : Prog isa := seqs [
  .block [.cmp .r3 (.imm 0)], .ite .eq finNone
    (seqs [.block [.cmp .r3 (.imm 1)], .ite .eq finAccepted finRejected])]

def limitedFinal (name : String) (body : Prog isa) : Prog isa :=
  seqs [shapeP, testLimited false name body, result]

def afterScreenedQ (name : String) (body : Prog isa) : Prog isa := seqs [
  test true name body, .block [.cmp .r3 (.imm 1)],
  .ite .eq (limitedFinal name body) result]

def screenedQ (name : String) (body : Prog isa) : Prog isa :=
  .seq halveQ (afterScreenedQ name body)

def screenedTests (name : String) (body : Prog isa) : Prog isa := seqs [
  shapeP, testLimited true name body, .block [.cmp .r3 (.imm 1)],
  .ite .eq (screenedQ name body) result]

def tests (name : String) (body : Prog isa) : Prog isa := screenedTests name body

def screenQ (name : String) (body : Prog isa) : Prog isa := seqs [halveQ,
  .ite .eq finRejected (seqs [sieve, .ite .eq (tests name body) finRejected])]

def screenPair (name : String) (body : Prog isa) : Prog isa := seqs [.block tableWrite, pairSieve,
  .ite .eq (tests name body) finRejected]

def screenP (name : String) (body : Prog isa) : Prog isa := seqs [.block qOdd,
  .ite .eq (screenPair name body) finRejected]

def main (name : String) (body : Prog isa) : Prog isa := seqs [
  .block ([.ldrSp .r1 12] ++ save .r1 40), shapeP, residue,
  .ite .eq (screenP name body) finRejected]

def code (name : String) (body : Prog isa) : Prog isa := VG.Impl.Ffdh.Arm.framed
  (seqs [.block entry, .block initialRoom, .ite .eq finNone (main name body)])

/-- A selected shared round keeps its exact call body. The caller's own
Montgomery conversions follow the backend's UMAAL requirement as well. -/
def optimizedCode (umaal : Bool) (name : String) (body : Prog isa) : Prog isa :=
  if umaal then callerRows (code name body) else code name body

end VG.Impl.Ffdh.Arm.ParameterCandidate
