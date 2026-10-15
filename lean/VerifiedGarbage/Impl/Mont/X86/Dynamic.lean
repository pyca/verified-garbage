module

public import VerifiedGarbage.Impl.Mont.X86

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit x86

The word count and workspace offsets are public code parameters. Unlike
fixed-curve arithmetic, the negative inverse is loaded from the workspace,
so the same code handles independently supplied DSA domain parameters.
-/

@[expose] public section

namespace VG.Impl.Mont.X86.Dynamic

open VG VG.X86 VG.Impl.Mont.X86

/-- Load the reduction digit from the low accumulator word and the runtime
negative inverse at `inv`. Neither value affects control flow. -/
def redDigit (acc inv : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp acc)), .mov .ecx (.mem (sc inv)),
   .mul .ecx, .mov .ecx (.reg .eax)]

/-- One CIOS row, with a general runtime modulus at `mo`. -/
def row (N acc a b mo inv : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .ebp a))] ++ mulRow acc b N ++
  redDigit acc inv ++ mulRow acc mo N ++
  [.alu .add .ebp (.imm 4), .mov .edx (.reg .edi),
   .alu .add .edx (.imm (BitVec.ofNat 32 (4 * N))), .alu .cmp .ebp (.reg .edx)]

/-- Montgomery multiplication with a runtime inverse. `M` supplies only
workspace geometry (`n`, `mo`, `tmp`); its fixed-modulus optimizations and
embedded inverse are not used. The result may alias either input. -/
def mul (M : VG.Impl.Mont.Mod) (inv acc o a b : Nat) : Prog isa :=
  .seq (.block (zeros acc (2 * words M + 1) ++ [.mov .ebp (.reg .edi)]))
    (.seq (.loop (.block (row (words M) acc a b M.mo inv)) .ne)
      (.block (csub M (acc + 4 * words M) o)))

end VG.Impl.Mont.X86.Dynamic
