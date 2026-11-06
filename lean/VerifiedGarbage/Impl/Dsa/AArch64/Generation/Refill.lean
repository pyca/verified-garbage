module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop

/-! # DSA parameter generation over refillable random tapes on AArch64

`vg_dsa_parameter_search` for one modulus width (`Spec/Dsa/ParameterSearch.lean`).
The seeds, the witnesses of their tests and the generator's `h` candidates
are all read from one tape, `rand`: the witness tape of the seed attempts
(frame words 14, 15 and 16: its base, length and the octets consumed). Each
seed is a seed attempt whose generator stage reads its `h` candidates from
the window of `rand` after the seed's witnesses, at most
`generatorAttempts` candidates (words 11 and 13), and whose octets of them
it read (`Proof.Dsa.GeneratorStage.result`) then count as consumed; a
window cut short by the tape's end, without a generator, ran out of
entropy (status 0).

The controller keeps the pointers to `used` and `state`, the seeds it may
still reject and the current seed's start in words above the attempts'
frame and the saved registers (`ctl`), which the attempts never write. Its
loop runs seeds while they are rejected (status 3), stopping with no seeds
left (status 2), with a tape too short for the next seed or a seed that ran
out (status 0), or with parameters (status 1); `finish` then writes `used`,
`state` and `out` and returns the protocol's status
(`Entropy.Outcome.status`).
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- The function's frame: the attempts' words, the saved registers and the
controller's words. -/
def frameBytes : Nat := 480

/-- The controller's words: the pointer to `used` (0), the pointer to
`state` (1), the seeds it may still reject (2) and the current seed's start
in `rand` (3). -/
def ctl (k : Nat) : Nat := 448 + 8 * k

/-- The h candidates a seed may draw (`Spec.Dsa.generatorAttempts`), in octets. -/
def windowBytes (pLen : Nat) : Nat := 128 * pLen

/-- The `h` tape: `rand` after the octets the seed has consumed (word 11),
at most `windowBytes` of them (word 13). -/
def window (pLen : Nat) : List Instr :=
  [.ldrSp .x3 112, .ldrSp .x4 128, .ldrSp .x6 120, .add .x .x5 .x3 .x4, .strSp .x5 88,
   .sub .x .x3 .x6 .x4, movi .x5 (windowBytes pLen), .subs .x .x6 .x3 .x5, .csel .x .x3 .x5 .x3,
   .strSp .x3 104]

/-- The stage's octets of candidates (`x0 / 4`) count as consumed; its end
(`x0 % 4`) in `x3`, and `x4` zero exactly when it found no generator. -/
def consumed : List Instr :=
  [.lsr .x .x4 .x0 2, .ldrSp .x5 128, .add .x .x5 .x5 .x4, .strSp .x5 128,
   .lsl .x .x4 .x4 2, .sub .x .x3 .x0 .x4, .subImm .x .x4 .x3 3]

/-- Without a generator: rejected (3), or ran out (0) if the window was
shorter than `windowBytes`. -/
def shortStatus (pLen : Nat) : List Instr :=
  [.ldrSp .x4 104, movi .x5 (windowBytes pLen), .subs .x .x4 .x4 .x5, movi .x4 3, movi .x5 0,
   .csel .x .x3 .x4 .x5, .strSp .x3 152]

/-- With a generator: 1 for parameters, 3 for an invalid domain (`2 x3 - 1`). -/
def foundStatus : List Instr := [.add .x .x3 .x3 .x3, .subImm .x .x3 .x3 1, .strSp .x3 152]

/-- The stage's result as the seed's status. -/
def stageStatus (pLen : Nat) : Prog isa :=
  .seq (.block consumed) (.ite (.zero .x .x4) (.block (shortStatus pLen)) (.block foundStatus))

/-- The generator stage over the window. -/
def refillGenerator (gen : Nat → Prog isa) (pLen : Nat) : Prog isa :=
  seqs [.block (window pLen), .block (generatorCallArgs pLen), gen pLen, stageStatus pLen]

/-- One seed, at `W 1`, with its witnesses and its generator's candidates
read from `rand` from `W 16` on. -/
def refillAttempt (G1 G256 : Hash) (gen : Nat → Prog isa) (prime : Nat → Prog isa) (pLen qLen : Nat) :
    Prog isa :=
  .seq (.seq (.block (seedArguments qLen)) (subgroup G1 G256 prime qLen))
    (onSuccess (.seq (primeSearch G1 G256 prime pLen qLen) (onSuccess (refillGenerator gen pLen))))

/-- The start of an iteration: the seed's start, `W 16`, in `x0` and
`ctl 3`, and the seeds left in `x3`. -/
def iterStart : List Instr := [.ldrSp .x0 128, .ldrSp .x3 (ctl 2), .strSp .x0 (ctl 3)]

/-- `x3 := 1` exactly when fewer than `qLen` octets are left from `x0`. -/
def roomCheck (qLen : Nat) : List Instr :=
  [.ldrSp .x3 120, .sub .x .x3 .x3 .x0, movi .x4 qLen, .subs .x .x3 .x3 .x4, movi .x4 1, movi .x5 0,
   .csel .x .x3 .x5 .x4]

/-- The seed's octets at `W 1 = rand + start`, and its witnesses after them. -/
def seedStart (qLen : Nat) : List Instr :=
  [.ldrSp .x3 112, .add .x .x3 .x3 .x0, .strSp .x3 8, movi .x4 qLen, .add .x .x0 .x0 .x4, .strSp .x0 128]

/-- A rejected seed counts against the seeds left. -/
def rejected : List Instr := [.ldrSp .x3 (ctl 2), .subImm .x .x3 .x3 1, .strSp .x3 (ctl 2)]

/-- One step of the controller, ending with `x0 = W 19 - 3`. -/
def iteration (attempt : Prog isa) (qLen : Nat) : Prog isa := seqs [
  .block iterStart,
  .ite (.zero .x .x3) (.block (stackStatus 2))
    (.seq (.block (roomCheck qLen))
      (.ite (.nonzero .x .x3) (.block (stackStatus 0))
        (seqs [.block (seedStart qLen), attempt, .block tapeStatus,
          .ite (.zero .x .x0) (.block rejected) (.block [])]))),
  .block tapeStatus]

/-- The controller: seeds until one is not rejected. -/
def controller (G1 G256 : Hash) (gen : Nat → Prog isa) (prime : Nat → Prog isa) (pLen qLen : Nat) :
    Prog isa :=
  .loop (iteration (refillAttempt G1 G256 gen prime pLen qLen) qLen) (.zero .x .x0)

/-- A seed that ran out: the octets left from its start in `x10`, the
budget (`Spec.Dsa.parameterEntropy`) in `x11`, and `x12` zero exactly when
they are fewer. -/
def ranOutCheck (pLen : Nat) : List Instr :=
  [.ldrSp .x10 120, .ldrSp .x9 (ctl 3), .sub .x .x10 .x10 .x9, movi .x9 pLen, .lsl .x .x11 .x9 15,
   .add .x .x11 .x11 .x9, .subs .x .x12 .x10 .x11, movi .x12 0, movi .x13 1, .csel .x .x12 .x13 .x12]

/-- The next tape's length (`VG.Proof.Dsa.Generation.parameterRequest`)
into `x10`: twice the larger of the octets left and `256 pLen`, at most the
budget. -/
def request : List Instr :=
  [.lsl .x .x12 .x9 8, .subs .x .x13 .x10 .x12, .csel .x .x10 .x10 .x12,
   .add .x .x10 .x10 .x10, .subs .x .x13 .x10 .x11, .csel .x .x10 .x11 .x10]

/-- `state[0]`, `state[3]` and `used[0]` from `x11`, `x10` and `x12`. -/
def stores : List Instr :=
  [.ldrSp .x9 (ctl 1), .ldrSp .x13 (ctl 0), st .x11 .x9 0, st .x10 .x9 24, st .x12 .x13 0]

/-- The status the search returns, kept in `ctl 3` while the output is written. -/
def statusWord (status : Nat) : List Instr := [movi .x9 status, .strSp .x9 (ctl 3)]

/-- Ran out: the seeds left, the request and the seed's start; status 0. -/
def entropyWords : List Instr := [.ldrSp .x11 (ctl 2), .ldrSp .x12 (ctl 3)] ++ stores ++ statusWord 0

/-- Exhausted: no seeds left, no request, and the seed's start; status 3. -/
def exhaustedWords : List Instr := [movi .x11 0, movi .x10 0, .ldrSp .x12 (ctl 3)] ++ stores ++ statusWord 3

/-- Parameters: no seeds left, no request, and the octets consumed; status 1. -/
def acceptedWords : List Instr := [movi .x11 0, movi .x10 0, .ldrSp .x12 128] ++ stores ++ statusWord 1

/-- The words written and the status for each way the controller ended
(`W 19`: 0 ran out, 1 parameters, 2 no seeds left), a seed that ran out
with its whole budget exhausting the search. -/
def results (pLen : Nat) : Prog isa :=
  .seq (.block [.ldrSp .x3 152])
    (.ite (.zero .x .x3)
      (.seq (.block (ranOutCheck pLen))
        (.ite (.zero .x .x12) (.block (request ++ entropyWords)) (.block exhaustedWords)))
      (.seq (.block [.subImm .x .x3 .x3 1])
        (.ite (.zero .x .x3) (.block acceptedWords) (.block exhaustedWords))))

/-- The search's words, status and output, then its status in `x0`. -/
def finish (pLen : Nat) : Prog isa := seqs [results pLen, finishOutput, .block [.ldrSp .x0 (ctl 3)]]

/-- The modulus's widths: `W 18` and `W 26` hold `qLen`. -/
def widthHeader (qLen : Nat) : List Instr := [movi .x3 qLen, .strSp .x3 144, .strSp .x3 208]

/-- The search for one width, from the entry's words. -/
def search (G1 G256 : Hash) (gen : Nat → Prog isa) (prime : Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  seqs [.block (widthHeader qLen), controller G1 G256 gen prime pLen qLen, finish pLen]

end VG.Impl.Dsa.AArch64.Generation.Refill
