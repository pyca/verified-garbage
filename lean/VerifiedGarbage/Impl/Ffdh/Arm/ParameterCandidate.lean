module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16
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
    .ldrSp .r0 144, .str .r0 .r12 36]

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

/-- Copy the first k tape bytes, mask to bits, and set the high and low bits. -/
def shapeP : Prog isa := seqs [
  .block [.ldrSp .r0 4, .ldrSp .r1 16, .ldrSp .lr 12], copyBytes,
  .block [.ldrSp .r6 24, .dp .sub .r6 .r6 (.imm 1), .dp .and .r6 .r6 (.imm 7),
    .dp .add .r6 .r6 (.imm 1), .mov .r7 (.imm 0)],
  .loop (.block maskStep) .ne,
  .block [.ldrSp .r4 4, .ldrb .r3 .r4 0, .dp .and .r3 .r3 (.reg .r7),
    .mov .r9 (.shifted .r7 .lsr 1), .dp .add .r9 .r9 (.imm 1),
    .dp .orr .r3 .r3 (.reg .r9), .strb .r3 .r4 0,
    .ldrSp .r5 12, .dp .add .r4 .r4 (.reg .r5), .dp .sub .r4 .r4 (.imm 1),
    .ldrb .r3 .r4 0, .dp .orr .r3 .r3 (.imm 1), .strb .r3 .r4 0]]

/-- One binary remainder step, selecting the subtraction without a branch. -/
def modBit : List Instr :=
  [.mov .r1 (.shifted .r2 .lsr 7), .dp .and .r1 .r1 (.imm 1),
    .dp .add .r3 .r3 (.reg .r3), .dp .add .r3 .r3 (.reg .r1),
    .subs .r1 .r3 (.reg .r7), .mov .r8 (.imm 0), .adc .r8 .r8 (.imm 0),
    .mov .r9 (.imm 0), .dp .sub .r8 .r9 (.reg .r8),
    .dp .eor .r1 .r1 (.reg .r3), .dp .and .r1 .r1 (.reg .r8),
    .dp .eor .r3 .r3 (.reg .r1), .mov .r2 (.shifted .r2 .lsl 1), .subs .r6 .r6 (.imm 1)]

/-- Output mod the small positive divisor in r7, in r3; keeps r10/r11. -/
def remSmall : Prog isa := seqs [
  .block [.ldrSp .r4 4, .ldrSp .r5 12, .mov .r3 (.imm 0)],
  .loop (seqs [.block [.ldrb .r2 .r4 0, .mov .r6 (.imm 8)],
    .loop (.block modBit) .ne,
    .block [.dp .add .r4 .r4 (.imm 1), .subs .r5 .r5 (.imm 1)]]) .ne]

def residue : Prog isa := seqs [
  .block [.ldrSp .r1 28, .cmp .r1 (.imm 2)],
  .ite .eq (.block [.mov .r7 (.imm 24)]) (.block [.mov .r7 (.imm 10)]),
  remSmall,
  .block [.ldrSp .r1 28, .cmp .r1 (.imm 2)],
  .ite .eq (.block [.cmp .r3 (.imm 11)])
    (.block [.dp .orr .r3 .r3 (.imm 4), .cmp .r3 (.imm 7)])]

/-- The small-prime table is beyond the 28 arrays the shared round uses. -/
def tablePointer : List Instr :=
  [.ldrSp .r0 0, .ldrSp .r7 12, .dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3),
    .dp .add .r7 .r7 (.imm 2), .mov .r7 (.shifted .r7 .lsl 3),
    .mov .r11 (.imm 34), .mul .r11 .r11 .r7, .dp .add .r11 .r11 (.reg .r0),
    .dp .add .r11 .r11 (.imm 256)]

def tableWrite : List Instr := tablePointer ++ (List.range 53).flatMap fun j =>
  [.mov .r1 (.imm (BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry j))), .str .r1 .r11 (4 * j)]

/-- Consume the next least-significant radix-2^16 digit of the big-endian
buffer ending at r0, with r1 octets left. The final odd octet is zero-padded. -/
def trialDigitHead : List Instr :=
  [.dp .sub .r0 .r0 (.imm 1), .ldrb .r5 .r0 0, .subs .r1 .r1 (.imm 1)]

def trialDigitHigh : List Instr :=
  [.dp .sub .r0 .r0 (.imm 1), .ldrb .r7 .r0 0,
    .dp .orr .r5 .r5 (.shifted .r7 .lsl 8), .dp .sub .r1 .r1 (.imm 1)]

def trialDigit : Prog isa := .seq (.block trialDigitHead)
  (.ite .eq (.block []) (.block trialDigitHigh))

/-- Trial division by the odd prime in r7 using RSA's radix-2^16 reducer.
Read octet pairs backwards, with a zero high octet for an odd byte length.
The final accumulator is below twice the prime, so zero or the prime
means divisibility. Z reports that result; r10/r11 remain the sieve cursor. -/
def trialSmall : Prog isa := seqs [
  .block ([.mov .r3 (.reg .r7), .mov .r4 (.reg .r3)] ++
    TrialDivision16.newton ++ TrialDivision16.newton ++ TrialDivision16.newton ++
    [.mov .r5 (.imm 0), .dp .sub .r4 .r5 (.reg .r4),
      .mov .r4 (.shifted .r4 .lsl 16), .mov .r4 (.shifted .r4 .lsr 16),
      .ldrSp .r0 4, .ldrSp .r1 12, .dp .add .r0 .r0 (.reg .r1), .mov .r2 (.imm 0)]),
  .loop (seqs [trialDigit, .block (TrialDivision16.redc ++ [.cmp .r1 (.imm 0)])]) .ne,
  .block [.cmp .r2 (.imm 0)],
  .ite .eq (.block []) (.block [.cmp .r2 (.reg .r3)])]

def sieve : Prog isa := seqs [
  .block (tablePointer ++ [.mov .r10 (.reg .r11), .mov .r11 (.imm 53), .mov .r1 (.imm 0)] ++ save .r1 64),
  .loop (seqs [.block [.ldr .r7 .r10 0, .dp .add .r10 .r10 (.imm 4)], trialSmall,
    .ite .eq (.block ([.mov .r1 (.imm 1)] ++ save .r1 64)) (.block []),
    .block [.subs .r11 .r11 (.imm 1)]]) .ne,
  .block [.ldrSp .r1 64, .cmp .r1 (.imm 0)]]

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

def montPrep : Prog isa := seqs [
  .block [.ldrSp .r0 0, .ldrSp .r6 12], VG.Impl.Ffdh.Arm.prepare,
  smallConst 1 1, montOp 1 1 4,
  .block (keyContext ++ [.str .r7 .r0 224, .mov .r1 (.imm 0), .str .r1 .r0 228] ++
    Rsa.Arm.Recover.clrTop 0 ++ Rsa.Arm.Recover.clrTop 1),
  Rsa.Arm.Keys.copy 9 1, Rsa.Arm.Keys.sub3 10 0 9]

def phaseHead (q : Bool) : List Instr :=
  [.ldrSp .r3 24] ++ (if q then [.dp .sub .r3 .r3 (.imm 1)] else []) ++ save .r3 44 ++
  [.dp .add .r4 .r3 (.imm 7), .mov .r4 (.shifted .r4 .lsr 3)] ++ save .r4 48 ++
  [.dp .sub .r3 .r3 (.imm 1), .subs .r3 .r3 (.imm 2048), .mov .r5 (.imm 0),
    .adc .r5 .r5 (.imm 0), .mov .r5 (.shifted .r5 .lsl 6), .dp .add .r5 .r5 (.imm 64)] ++
  save .r5 52 ++ [.mov .r1 (.imm 0)] ++ save .r1 56

def halfCountStep : Prog isa := seqs [
  .block [.mov .r11 (.imm 0)], Rsa.Arm.Keys.half 29,
  .block ([.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] ++ save .r1 60 ++
    Rsa.Arm.Keys.ptr .r0 29 ++ [.ldr .r1 .r0 0, .dp .and .r1 .r1 (.imm 1), .cmp .r1 (.imm 0)])]

def exponentHalf : Prog isa := seqs [
  .block [.mov .r11 (.imm 0)], Rsa.Arm.Keys.half 27,
  .block ([.ldrSp .r1 64, .subs .r1 .r1 (.imm 1)] ++ save .r1 64)]

def powerBitStep : List Instr :=
  [.mov .r2 (.shifted .r4 .lsr 31), .mov .r5 (.shifted .r5 .lsl 1),
    .dp .orr .r5 .r5 (.reg .r2), .mov .r4 (.shifted .r4 .lsl 1), .subs .r6 .r6 (.imm 1)]

/-- The compact round's exponent and its complete u64 decomposition word. -/
def expSetup : Prog isa := seqs [
  .block keyContext, Rsa.Arm.Keys.copy 29 0,
  .block (Rsa.Arm.Keys.clrLow 29 ++ [.mov .r1 (.imm 0)] ++ save .r1 60),
  .loop halfCountStep .eq,
  .block [.ldrSp .r1 60, .dp .and .r1 .r1 (.imm 3), .cmp .r1 (.imm 0)],
  .ite .eq (.block [.mov .r1 (.imm 4)]) (.block []),
  .block (save .r1 64), Rsa.Arm.Keys.copy 27 0, .loop exponentHalf .ne,
  .block [.ldrSp .r6 60, .dp .and .r6 .r6 (.imm 63),
    .mov .r4 (.imm 1), .mov .r5 (.imm 0), .cmp .r6 (.imm 0)],
  .ite .eq (.block []) (.loop (.block powerBitStep) .ne),
  .block (Rsa.Arm.Keys.ptr .r0 27 ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2),
    .dp .sub .r0 .r0 (.imm 8), .str .r4 .r0 0, .str .r5 .r0 4])]

/-- Mask the highest native word occupied by a witness, including at a
32- or 64-bit width boundary. Import has already cleared the higher words. -/
def witnessMask : Prog isa := seqs [
  .block [.ldrSp .r6 44, .dp .sub .r6 .r6 (.imm 1), .mov .r5 (.shifted .r6 .lsr 5),
    .dp .and .r6 .r6 (.imm 31), .dp .add .r6 .r6 (.imm 1), .mov .r7 (.imm 0)],
  .loop (.block maskStep) .ne,
  .block [.ldrSp .r0 0, .ldr .r4 .r0 72, .dp .add .r4 .r4 (.shifted .r5 .lsl 2),
    .ldr .r3 .r4 0, .dp .and .r3 .r3 (.reg .r7), .str .r3 .r4 0]]

def onPass : Prog isa := seqs [
  .block [.ldrSp .r1 56, .dp .add .r1 .r1 (.imm 1), .ldrSp .r2 52,
    .cmp .r1 (.reg .r2)],
  .ite .eq (.block [.mov .r3 (.imm 1)]) (.block [.mov .r3 (.imm 4)]),
  .block (save .r1 56 ++ [.cmp .r3 (.imm 4)])]

def round (name : String) (body : Prog isa) : Prog isa := seqs [
  montOp 5 1 4, .block [.ldrSp .r0 0, .ldrSp .r1 36], .call name body,
  .block [.cmp .r0 (.imm 0)],
  .ite .eq (.block [.mov .r3 (.imm 2), .cmp .r3 (.imm 4)]) onPass]

def draw (name : String) (body : Prog isa) : Prog isa := seqs [
  .block [.ldrSp .r0 0, .ldrSp .r4 16, .ldrSp .r1 40, .ldrSp .r6 48,
    .dp .add .r4 .r4 (.reg .r1), .dp .add .r1 .r1 (.reg .r6)] ,
  .block (save .r1 40), importOperand 1, witnessMask, VG.Impl.Ffdh.Arm.inRange 1,
  .block [.cmp .r11 (.imm 0)],
  .ite .eq (.block [.mov .r3 (.imm 4), .cmp .r3 (.imm 4)]) (round name body)]

def millerRabin (name : String) (body : Prog isa) : Prog isa :=
  .loop (seqs [.block witnessRoom,
    .ite .eq (.block [.mov .r3 (.imm 0), .cmp .r3 (.imm 4)]) (draw name body)]) .eq

def test (q : Bool) (name : String) (body : Prog isa) : Prog isa :=
  seqs [.block (phaseHead q), montPrep, expSetup, millerRabin name body]

def result : Prog isa := seqs [
  .block [.cmp .r3 (.imm 0)], .ite .eq finNone
    (seqs [.block [.cmp .r3 (.imm 1)], .ite .eq finAccepted finRejected])]

def tests (name : String) (body : Prog isa) : Prog isa := seqs [
  test true name body, .block [.cmp .r3 (.imm 1)],
  .ite .eq (seqs [shapeP, test false name body, result]) result]

def main (name : String) (body : Prog isa) : Prog isa := seqs [
  .block ([.ldrSp .r1 12] ++ save .r1 40), shapeP, residue,
  .ite .eq (seqs [.block tableWrite, sieve,
    .ite .eq (seqs [halveQ,
      .ite .eq finRejected (seqs [sieve, .ite .eq (tests name body) finRejected])]) finRejected]) finRejected]

def code (name : String) (body : Prog isa) : Prog isa := VG.Impl.Ffdh.Arm.framed
  (seqs [.block entry, .block initialRoom, .ite .eq finNone (main name body)])

end VG.Impl.Ffdh.Arm.ParameterCandidate
