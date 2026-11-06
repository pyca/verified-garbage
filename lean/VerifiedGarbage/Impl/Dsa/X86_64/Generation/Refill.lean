module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry

/-! # DSA parameter generation over refillable random tapes on x86-64

`vg_dsa_parameter_search` for one modulus width (`Spec/Dsa/ParameterSearch.lean`).
The seeds, the witnesses of their tests and the generator's `h` candidates
are all read from one tape, `rand`: the witness tape of the finite search's
seed attempts (frame words 13, 15 and 16: its base, length and the octets
consumed). Each seed is the finite search's attempt (`refillAttempt`) with
two changes: its `h` tape (words 11 and 12) is the window of `rand` after
the seed's witnesses, at most `generatorAttempts` candidates, whose octets
the generator's then count as consumed; and a window cut short by the
tape's end, without a generator, ran out of entropy (status 0).

The controller keeps the pointers to `used` and `state`, the seeds it may
still reject and the current seed's start in a frame above the attempts'
(`ctl`), which they never write. Its loop runs seeds while they are
rejected (status 3), stopping with no seeds left (status 2), with a tape
too short for the next seed or a seed that ran out (status 0), or with
parameters (status 1); `finish` then writes `used`, `state` and `out` and
returns the protocol's status (`Entropy.Outcome.status`).
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

variable {checkName : String}

/-- The attempts' frame. -/
def frameBytes : Nat := 296

/-- The controller's words, above the attempts' frame: the pointer to
`used` (0), the pointer to `state` (1), the seeds it may still reject (2)
and the current seed's start in `rand` (3). -/
def ctl (k : Nat) : MemOp := sp (frameBytes + 8 * k)

/-- The h candidates a seed may draw (`Spec.Dsa.generatorAttempts`), in octets. -/
def windowBytes (pLen : Nat) : Nat := 128 * pLen

/-- The `h` tape: `rand` after the octets the seed has consumed, at most
`windowBytes`. -/
def window (pLen : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)), .store (sp 88) .rax,
      .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 (windowBytes pLen)))])
    (.ite .b (.block [.store (sp 96) .rcx])
      (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (windowBytes pLen))), .store (sp 96) .rax]))

/-- The generator's candidates count as consumed octets of `rand`. -/
def windowConsumed : List Instr :=
  [.mov .rax (.mem (sp 128)), .alu .add .rax (.mem (sp 160)), .store (sp 128) .rax]

/-- Without a generator, a window shorter than `windowBytes` ran out. -/
def windowShort (pLen : Nat) : Prog isa :=
  .seq (.block successStatus)
    (.ite .e (.block [])
      (.seq (.block [.mov .rax (.mem (sp 96)), .alu .cmp .rax (.imm (BitVec.ofNat 32 (windowBytes pLen)))])
        (.ite .b (.block (stackStatus 0)) (.block []))))

/-- One seed, at `W 1`, with its witnesses and its generator's candidates
read from `rand` from `W 16` on. -/
def refillAttempt (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (prime : Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (.seq (.block (seedArguments qLen)) (subgroup G1 G256 prime qLen))
    (onSuccess (.seq (primeSearch G1 G256 prime pLen qLen)
      (onSuccess (seqs [window pLen, generatorSearch sq mul pLen, .block windowConsumed, windowShort pLen,
        onSuccess (finishDomain (checkName := checkName) sq mul pLen qLen)]))))

/-- The next seed: its start, `W 16`, saved; the seed's octets at
`W 1 = rand + start`; and its witnesses after them. -/
def seedStart (qLen : Nat) : List Instr :=
  [.mov .rcx (.mem (sp 104)), .alu .add .rcx (.reg .rax), .store (sp 8) .rcx,
   .alu .add .rax (.imm (BitVec.ofNat 32 qLen)), .store (sp 128) .rax]

/-- A rejected seed counts against the seeds left. -/
def rejected : List Instr :=
  [.mov .rax (.mem (ctl 2)), .alu .sub .rax (.imm 1), .store (ctl 2) .rax]

/-- One step of the controller, ending with `W 19` compared with 3. -/
def iteration (attempt : Prog isa) (qLen : Nat) : Prog isa := seqs [
  .block [.mov .rax (.mem (sp 128)), .store (ctl 3) .rax, .mov .rcx (.mem (ctl 2)),
    .alu .test .rcx (.reg .rcx)],
  .ite .e (.block (stackStatus 2))
    (.seq (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))])
      (.ite .b (.block (stackStatus 0))
        (seqs [.block (seedStart qLen), attempt, .block tapeStatus,
          .ite .e (.block rejected) (.block [])]))),
  .block tapeStatus]

/-- The entropy budget (`Spec.Dsa.parameterEntropy`). -/
def budget (pLen : Nat) : Nat := 32769 * pLen

/-- A seed that ran out: the octets left from its start, in `rcx`, exhaust
the search if they reach the budget (status 2); otherwise the next tape's
length (`VG.Proof.Dsa.Generation.parameterRequest`) goes in `ctl 3`'s place in `state`,
computed into `rdx`. -/
def ranOut (pLen : Nat) : Prog isa :=
  .seq (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (ctl 3)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 (budget pLen))), .alu .cmp .rcx (.reg .rdx)])
    (.ite .b
      (.seq (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (256 * pLen))), .alu .cmp .rcx (.reg .rax)])
        (.seq (.ite .b (.block []) (.block [.mov .rax (.reg .rcx)]))
          (.seq (.block [.alu .add .rax (.reg .rax), .alu .cmp .rax (.reg .rdx)])
            (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block [])))))
      (.block (stackStatus 2)))

/-- The words written for each status: `used`, the seeds left and the next
tape's length (in `rdx` for status 0). -/
def results (pLen : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp 152)), .alu .test .rax (.reg .rax)])
    (.ite .e
      (.seq (ranOut pLen) (.seq (.block [.mov .rax (.mem (sp 152)), .alu .test .rax (.reg .rax)])
        (.ite .e
          (.block [.mov .rcx (.mem (ctl 1)), .mov .rax (.mem (ctl 2)), .store (at0 .rcx) .rax,
            .store { base := .rcx, disp := 24 } .rdx,
            .mov .rax (.mem (ctl 3)), .mov .rcx (.mem (ctl 0)), .store (at0 .rcx) .rax])
          (.block [.mov .rcx (.mem (ctl 1)), .mov32 .rax (.imm 0), .store (at0 .rcx) .rax,
            .store { base := .rcx, disp := 24 } .rax,
            .mov .rax (.mem (ctl 3)), .mov .rcx (.mem (ctl 0)), .store (at0 .rcx) .rax]))))
      (.seq (.block [.mov .rcx (.mem (ctl 1)), .mov32 .rax (.imm 0), .store (at0 .rcx) .rax,
          .store { base := .rcx, disp := 24 } .rax, .mov .rax (.mem (sp 152)), .alu .cmp .rax (.imm 1)])
        (.ite .e (.block [.mov .rax (.mem (sp 128)), .mov .rcx (.mem (ctl 0)), .store (at0 .rcx) .rax])
          (.block [.mov .rax (.mem (ctl 3)), .mov .rcx (.mem (ctl 0)), .store (at0 .rcx) .rax]))))

/-- The protocol's status from `W 19`: 0 and 1 as they are, 2 (exhausted) as 3. -/
def returnStatus : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp 152)), .alu .cmp .rax (.imm 2)])
    (.ite .e (.block [.mov32 .rax (.imm 3)]) (.block []))

/-- The search's words and output, then its status in `rax`. -/
def finish (pLen : Nat) : Prog isa := seqs [results pLen, finishOutput, returnStatus]

/-- The controller: seeds until one is not rejected. -/
def controller (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (prime : Prog isa) (pLen qLen : Nat) : Prog isa :=
  .loop (iteration (refillAttempt (checkName := checkName) G1 G256 sq mul prime pLen qLen) qLen) .e

/-- `vg_dsa_parameter_search(out, out_len, used, rand, rand_len, scratch,
scratch_len, state)` for one width, all frames allocated: the attempts'
words as the finite search's entry sets them, with `rand` as every tape
(the seeds', the witnesses' and, empty, the generator's), and the
controller's words. `state` is the second stack argument. -/
def entryHeader (pLen qLen : Nat) : List Instr :=
  [.store (sp 48) .rdi, .store (sp 56) .rsi, .store (ctl 0) .rdx,
   .store (sp 64) .rcx, .store (sp 72) .r8, .store (sp 104) .rcx, .store (sp 120) .r8,
   .store (sp 88) .rcx, .mov32 .rax (.imm 0), .store (sp 96) .rax, .store (sp 80) .rax,
   .store (sp 40) .r9,
   .mov32 .rax (.imm (BitVec.ofNat 32 pLen)), .store (sp 136) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 qLen)), .store (sp 144) .rax, .store (sp 224) .rax,
   .mov .rax (.mem (sp (frameBytes + 32 + 48 + 16))), .store (ctl 1) .rax,
   .mov .rax (.mem (at0 .rax)), .store (ctl 2) .rax]

def body (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (prime : Prog isa) (pLen qLen : Nat) : Prog isa := seqs [
  .block (entryHeader pLen qLen ++ entryDerived),
  controller (checkName := checkName) G1 G256 sq mul prime pLen qLen,
  finish pLen]

/-- The function for one width: the callee-saved registers, the
controller's frame and the attempts'. -/
def code (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (prime : Prog isa) (pLen qLen : Nat) : Prog isa :=
  .frame (.alloc 48)
    (.seq (.block saveRegisters)
      (.seq (.frame (.alloc 32) (.frame (.alloc frameBytes)
          (body (checkName := checkName) G1 G256 sq mul prime pLen qLen) (.free frameBytes)) (.free 32))
        (.block restoreRegisters))) (.free 48)

end VG.Impl.Dsa.X86_64.Generation.Refill
