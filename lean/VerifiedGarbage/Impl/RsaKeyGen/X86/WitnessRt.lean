module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # Miller–Rabin's witness loop at the run-time width

The width comes from the prepared header (byte 48) and every array through
its header pointer, so one copy serves every width. A witness is the
candidate's full width (`8 w` octets, `2 w` native words); the number of
uniform tests required is computed from the width without a branch.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.MillerRabin.X86 (ptr)

/-- `edx := 8 w`, a witness's octets. -/
def draw : List Instr :=
  [.mov .edx (.mem (sc 48)), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx)]

/-- One term of the required tests: `ecx += m` when `w < c`. -/
def term (c m : Nat) : List Instr :=
  [.mov .eax (.mem (sc 48)), .alu .cmp .eax (.imm (BitVec.ofNat 32 c)), .alu .sbb .eax (.reg .eax),
    .alu .and .eax (.imm (BitVec.ofNat 32 m)), .alu .add .ecx (.reg .eax)]

/-- The counters cleared and `WitnessChecks.checks w` uniform tests required. -/
def checks : List Instr :=
  [.mov .eax (.imm 0), .store (sc 176) .eax, .store (sc 192) .eax, .mov .ecx (.imm 3)] ++
    term 59 1 ++ term 22 1 ++ term 8 1 ++ term 7 1 ++ term 6 1 ++ term 5 19 ++ [.store (sc 200) .ecx]

/-- The carry flag set when fewer than `8 w` octets of entropy remain. -/
def available : List Instr :=
  draw ++ [.mov .eax (.mem (sc 32)), .alu .sub .eax (.mem (sc 152)), .alu .cmp .eax (.reg .edx)]

/-- `esi` at the next `8 w` octets, which are counted used. -/
def advance : List Instr :=
  draw ++ [.mov .esi (.mem (sc 28)), .mov .eax (.mem (sc 152)), .alu .add .esi (.reg .eax),
    .alu .add .eax (.reg .edx), .store (sc 152) .eax]

/-- `Import.code`'s arguments for array 6: `ebx` at its top word and `ecx`
its `2 w` words. -/
def importArgs : List Instr :=
  draw ++ ptr .ebx 6 ++ [.alu .add .ebx (.reg .edx), .alu .sub .ebx (.imm 4),
    .mov .ecx (.mem (sc 48)), .alu .add .ecx (.reg .ecx)]

/-- The witness drawn into array 6. -/
def load : Prog isa := .seq (.block importArgs) Import.code

/-- The witness's low bit set, its low word saved in `ebx`. -/
def markAt : List Instr :=
  [.mov .ebx (.mem (at_ .ebp 0)), .mov .eax (.reg .ebx), .alu .or .eax (.imm 1), .store (at_ .ebp 0) .eax]

def mark : List Instr := ptr .ebp 6 ++ markAt

/-- The loop of a comparison `[esi] < [ebp]`, `edx` octets, its borrow a
mask in `ecx` (`PublicRt.compareAt`'s). -/
def lessLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .alu .add .ecx (.reg .ecx),
    .alu .sbb .eax (.mem (at_ .ebp 0)), .alu .sbb .ecx (.reg .ecx), .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne

/-- `lessLoop`'s pointers at the witness and the candidate, `edx` their octets. -/
def lessArgs : List Instr := ptr .esi 6 ++ ptr .ebp 0 ++ draw ++ [.mov .ecx (.imm 0)]

/-- `ecx` all ones when the marked witness is below the candidate. -/
def less : Prog isa := .seq (.block lessArgs) lessLoop

/-- The witness's low word restored, the comparison's mask kept in `esi`. -/
def restoreAt : List Instr := [.store (at_ .ebp 0) .ebx, .mov .esi (.reg .ecx)]

def restore : List Instr := ptr .ebp 6 ++ restoreAt

/-- The loop of an OR scan of `ecx` words at `ebp` into `ebx`. -/
def orLoop : Prog isa :=
  .loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne

/-- `ebx` the OR of the witness's words but its lowest. -/
def scanArgs : List Instr :=
  [.mov .ebx (.imm 0)] ++ ptr .ebp 6 ++
    [.alu .add .ebp (.imm 4), .mov .ecx (.mem (sc 48)), .alu .add .ecx (.reg .ecx), .alu .sub .ecx (.imm 1)]

def scan : Prog isa := .seq (.block scanArgs) orLoop

/-- `eax` all ones when the witness is at least two and below `c − 1`. -/
def lowerAt : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .or .eax (.imm 1), .alu .xor .eax (.imm 1),
    .alu .or .ebx (.reg .eax), .alu .cmp .ebx (.imm 1), .alu .sbb .ebx (.reg .ebx),
    .alu .xor .ebx (.imm (BitVec.allOnes 32)), .mov .eax (.reg .esi), .alu .and .eax (.reg .ebx)]

def lower : List Instr := ptr .ebp 6 ++ lowerAt

/-- Unless `eax` is all ones, bit one of the word at `ebp` set. -/
def fallbackLow : List Instr :=
  [.mov .ecx (.reg .eax), .alu .xor .ecx (.imm (BitVec.allOnes 32)), .alu .and .ecx (.imm 2),
    .alu .or .ecx (.mem (at_ .ebp 0)), .store (at_ .ebp 0) .ecx]

/-- Unless `eax` is all ones, the top bit of the word at `ebx` cleared. -/
def fallbackHigh : List Instr :=
  [.mov .ecx (.reg .eax), .alu .xor .ecx (.imm (BitVec.allOnes 32)), .alu .and .ecx (.imm 0x80000000),
    .alu .xor .ecx (.imm (BitVec.allOnes 32)), .alu .and .ecx (.mem (at_ .ebx 0)), .store (at_ .ebx 0) .ecx]

/-- `ebx` at the witness's top word. -/
def fallbackTop : List Instr :=
  draw ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (.reg .edx), .alu .sub .ebx (.imm 4)]

/-- Where the witness is not uniform: its bit one set and its top bit
cleared; `eax`, the mask, is kept. -/
def fallback : List Instr := ptr .ebp 6 ++ fallbackLow ++ fallbackTop ++ fallbackHigh

/-- The witness sampled in array 6, and its uniformity mask in `eax`. -/
def sample : Prog isa :=
  .seq (.block mark) (.seq less (.seq (.block restore) (.seq scan (.block (lower ++ fallback)))))

/-- A witness drawn and sampled. -/
def drawn : Prog isa := .seq load sample

def round (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq drawn (.seq (.block [.store (sc WitnessRound.uniformOffset) .eax])
    (.seq (WitnessMont.code montName montCode) (RoundCall.code roundName roundCode)))

def body (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block advance) (.seq (round montName montCode roundName roundCode) WitnessCount.code)

def step (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block available)
    (.seq (.ite .b (.block MillerRabinLoop.exhausted) (body montName montCode roundName roundCode))
      (.block MillerRabinLoop.again))

def code (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block checks) (.loop (step montName montCode roundName roundCode) .e)

end VG.Impl.RsaKeyGen.X86.WitnessRt
