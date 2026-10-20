module

public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Impl.Mont.X86.Mac

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit x86

The word count and workspace offsets are public code parameters. Unlike
fixed-curve arithmetic, the negative inverse is loaded from the workspace,
so the same code handles independently supplied DSA domain parameters.
-/

@[expose] public section

namespace VG.Impl.Mont.X86.Dynamic

open VG VG.X86 VG.Impl.Mont.X86

/-- The reduction digit, from the low accumulator word and the runtime
negative inverse at `inv`, to the multiplier word `[mult]`. Neither value
affects control flow. -/
def redDigit (acc inv mult : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp acc)), .mov .edx (.mem (sc inv)),
   .mul .edx, .store (sc mult) .eax]

/-- `[ebp + acc + d] += [mult] · [ecx + b + d]`, with the carry word in
`ebx`. The accumulator's word is added before the carry, so that the carry
from one word to the next passes through one addition (`add`, `adc`) rather
than two. -/
def macW (acc b mult d : Nat) : List Instr :=
  macWord (acc + d) (b + d) mult

/-- The words `j` and `j + 1` that `ecx` points to, then both pointers move
up two words: the loop's own instructions run once for two words. -/
def mulStepW (N acc b mult : Nat) : List Instr :=
  macW acc b mult 0 ++ macW acc b mult 4 ++
    [.alu .add .ecx (.imm 8), .alu .add .ebp (.imm 8),
      .mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 (4 * N))), .alu .cmp .ecx (.reg .eax)]

/-- The window `+= [mult] · [b]`, `N` words (an even number), with its
carry, through `ecx`. -/
def mulRowW (acc b N mult : Nat) : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0), .mov .ecx (.reg .edi)]) <|
  .seq (.loop (.block (mulStepW N acc b mult)) .ne)
    (.block (.alu .sub .ebp (.imm (BitVec.ofNat 32 (4 * N))) :: carryUp acc N))

/-- A CIOS row once its multiplier `a_i` is in `[mult]`. -/
def rowTail (N acc b mo inv mult : Nat) : Prog isa :=
  .seq (mulRowW acc b N mult) <|
  .seq (.block (redDigit acc inv mult)) <|
  .seq (mulRowW acc mo N mult)
    (.block [.alu .add .ebp (.imm 4), .mov .edx (.reg .edi),
      .alu .add .edx (.imm (BitVec.ofNat 32 (4 * N))), .alu .cmp .ebp (.reg .edx)])

/-- One CIOS row with the runtime inverse at `[inv]`, its multipliers in
`[mult]`. -/
def row (N acc a b mo inv mult : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .ebp a)), .store (sc mult) .eax]) (rowTail N acc b mo inv mult)

/-- `[o] = [a] [b] R⁻¹ mod m`, with the runtime inverse at `[inv]`. The
rows keep their multiplier in the first word of `[M.tmp]`, and leave `esi`
alone. -/
def mul (M : Mod) (inv acc o a b : Nat) : Prog isa :=
  .seq (zerosW acc (2 * words M + 1)) <|
  .seq (.block [.mov .ebp (.reg .edi)]) <|
  .seq (.loop (row (words M) acc a b M.mo inv M.tmp) .ne)
    (csubW M (acc + 4 * words M) o)

end VG.Impl.Mont.X86.Dynamic
