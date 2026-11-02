module

public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-!
# FFDH on i686: the parameter-generation controller

`vg_ffdh_generate_parameters_sieved` repeats `vg_ffdh_parameter_candidate_sieved`
on the random tape until it accepts a p, the attempts run out, or the tape
does: rejected candidates never return to the host.

The first four state words are the attempts (64 bits: 64 bits² is above
2³² for 8192 bits), the width, the entropy cap and the next request (their
low halves; the high halves of the last three stay zero). The controller
keeps its own words in the rest, at `esi`: the caller's `esi`, the arguments
it passes on, the tape's current pointer and length, the octets consumed,
the status, and the candidate's `used`.
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86.ParamSearch
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The state's words, by their byte offsets. -/
def attemptsOff : Nat := 0
def widthOff : Nat := 8
def capOff : Nat := 16
def requestOff : Nat := 24
def savedOff : Nat := 32
def outOff : Nat := 36
def upOff : Nat := 40
def bitsOff : Nat := 44
def genOff : Nat := 48
def randOff : Nat := 52
def leftOff : Nat := 56
def scratchOff : Nat := 60
def slenOff : Nat := 64
def statusOff : Nat := 68
def usedOff : Nat := 72
def candOff : Nat := 80

/-- A word of the state, at `esi`. -/
def st (d : Nat) : MemOp := at_ .esi d

/-- Argument `i` (`out, out_len, used, bits, generator, rand, rand_len, scratch, scratch_len,
state`) to the state's word at `d`. -/
def keep (i d : Nat) : List Instr := [.mov .eax (.mem (argAt 0 i)), .store (st d) .eax]

/-- `esi` the state, the caller's `esi` saved in it; the arguments kept; nothing consumed; the
high halves of the width, the cap and the request zero. -/
def entry : List Instr :=
  [.mov .eax (.mem (argAt 0 9)), .store (at_ .eax savedOff) .esi, .mov .esi (.reg .eax)] ++
  keep 0 outOff ++ keep 2 upOff ++ keep 3 bitsOff ++ keep 4 genOff ++ keep 5 randOff ++ keep 6 leftOff ++
  keep 7 scratchOff ++ keep 8 slenOff ++
  [.mov .eax (.imm 0), .store (st usedOff) .eax, .store (st (widthOff + 4)) .eax, .store (st (capOff + 4)) .eax,
    .store (st (requestOff + 4)) .eax]

/-- Zeros at `out`, the width's octets. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .edx (.mem (st outOff)), .mov .ecx (.mem (st widthOff)), .mov .eax (.imm 0)])
    (.loop (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

/-- The attempts and the request zero, and `status`. -/
def terminal (status : Nat) : List Instr :=
  [.mov .eax (.imm 0), .store (st attemptsOff) .eax, .store (st (attemptsOff + 4)) .eax,
    .store (st requestOff) .eax, .mov .eax (.imm (BitVec.ofNat 32 status)), .store (st statusOff) .eax]

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The request `min (2 max(left, 256 L)) cap`, and the status 0. -/
def requestWords : List Instr :=
  [.mov .eax (.mem (st leftOff)), .mov .ecx (.mem (st widthOff))] ++
  -- `ecx := 256 L`, eight doublings.
  List.replicate 8 (.alu .add .ecx (.reg .ecx)) ++
  [
    .alu .cmp .eax (.reg .ecx), .alu .sbb .edx (.reg .edx),
    -- `eax := max(eax, ecx)`: `edx` all ones when `eax < ecx`.
    .alu .xor .ecx (.reg .eax), .alu .and .ecx (.reg .edx), .alu .xor .eax (.reg .ecx),
    .alu .add .eax (.reg .eax), .mov .ecx (.mem (st capOff)),
    .alu .cmp .ecx (.reg .eax), .alu .sbb .edx (.reg .edx),
    -- `eax := min(eax, ecx)`: `edx` all ones when `ecx < eax`.
    .alu .xor .ecx (.reg .eax), .alu .and .ecx (.reg .edx), .alu .xor .eax (.reg .ecx),
    .store (st requestOff) .eax, .mov .eax (.imm 0), .store (st statusOff) .eax]

/-- Ask for more of the tape, with `out` zero. -/
def request : Prog isa := .seq (.block requestWords) zeroOut

/-- The state's word at `d` to the callee's argument `j`. -/
def pass (d j : Nat) : List Instr := [.mov .eax (.mem (st d)), .store (at_ .esp (4 * j)) .eax]

/-- `vg_ffdh_parameter_candidate_sieved`'s arguments `(out, L, &cand, bits, generator, rand, left,
scratch, scratch_len)`, for the tape at its pointer. -/
def arguments : List Instr :=
  pass outOff 0 ++ pass widthOff 1 ++
  [.mov .eax (.reg .esi), .alu .add .eax (.imm (BitVec.ofNat 32 candOff)), .store (at_ .esp 8) .eax] ++
  pass bitsOff 3 ++ pass genOff 4 ++ pass randOff 5 ++ pass leftOff 6 ++ pass scratchOff 7 ++ pass slenOff 8

/-- The bytes of the attempt's frame of arguments. -/
def argsBytes : Nat := 36

/-- The attempt, a call of `vg_ffdh_parameter_candidate_sieved`, in a frame of its arguments. -/
def attempt : Prog isa :=
  .frame (.alloc argsBytes)
    (.seq (.block arguments) (.call "vg_ffdh_parameter_candidate_sieved" Candidate.code))
    (.free argsBytes)

/-- The status to `edx`, and the candidate's octets consumed. -/
def advance : List Instr :=
  [.mov .edx (.reg .eax), .mov .ecx (.mem (st candOff)),
    .mov .eax (.mem (st randOff)), .alu .add .eax (.reg .ecx), .store (st randOff) .eax,
    .mov .eax (.mem (st leftOff)), .alu .sub .eax (.reg .ecx), .store (st leftOff) .eax,
    .mov .eax (.mem (st usedOff)), .alu .add .eax (.reg .ecx), .store (st usedOff) .eax]

/-- A rejected candidate: one fewer attempt left (64 bits). -/
def rejected : List Instr :=
  [.mov .eax (.mem (st attemptsOff)), .alu .sub .eax (.imm 1), .store (st attemptsOff) .eax,
    .mov .eax (.mem (st (attemptsOff + 4))), .alu .sbb .eax (.imm 0), .store (st (attemptsOff + 4)) .eax,
    .mov .eax (.imm 4), .store (st statusOff) .eax]

/-- A shortage: exhausted once the tape holds the entropy cap, else a request. -/
def shortage : Prog isa :=
  .seq (.block [.mov .eax (.mem (st leftOff)), .mov .ecx (.mem (st capOff)), .alu .cmp .eax (.reg .ecx)])
    (.ite .b request exhausted)

def classify : Prog isa := .seq (.block (advance ++ [.alu .cmp .edx (.imm 1)]))
  (.ite .e (.block (terminal 1))
    (.seq (.block [.alu .cmp .edx (.imm 2)]) (.ite .e (.block rejected) shortage)))

/-- The borrow set when the tape holds less than a candidate's octets. -/
def room : List Instr :=
  [.mov .eax (.mem (st leftOff)), .mov .ecx (.mem (st widthOff)), .alu .cmp .eax (.reg .ecx)]

def attemptOrRequest : Prog isa := .seq (.block room) (.ite .b request (.seq attempt classify))

def branch : Prog isa :=
  .seq (.block [.mov .eax (.mem (st attemptsOff)), .alu .or .eax (.mem (st (attemptsOff + 4))),
      .alu .test .eax (.reg .eax)])
    (.ite .e exhausted attemptOrRequest)

/-- The loop goes on while the status is 4, a rejection. -/
def iteration : Prog isa :=
  .seq branch (.block [.mov .eax (.mem (st statusOff)), .alu .cmp .eax (.imm 4)])

/-- `used` written (64 bits), the status returned and the caller's `esi` restored. -/
def finish : List Instr :=
  [.mov .ecx (.mem (st upOff)), .mov .eax (.mem (st usedOff)), .store (at_ .ecx 0) .eax,
    .mov .eax (.imm 0), .store (at_ .ecx 4) .eax, .mov .eax (.mem (st statusOff)),
    .mov .esi (.mem (st savedOff))]

def code : Prog isa := .seq (.block entry) (.seq (.loop iteration .e) (.block finish))

end VG.Impl.Ffdh.X86.ParamSearch
