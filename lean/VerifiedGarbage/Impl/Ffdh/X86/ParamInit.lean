module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-!
# FFDH on i686: initialization of parameter generation

`vg_ffdh_parameter_generation_init(state, bits, generator)`: unless
`512 ≤ bits ≤ 8192` and the generator is 2 or 5, the controller's four
public words cleared and 0 returned; otherwise its attempt limit
`64 bits²` (above 2³² for 8192 bits, the one word with a high half), the
width `L = ⌈bits / 8⌉`, the entropy cap `32769 L` and the first request
`512 L`, and 1 returned. The products come from `mul`, which the baseline
ISA has; every branch is on the public arguments.
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86.ParamInit
open VG VG.X86 VG.Impl.Bignum.X86
open VG.Impl.Mont.X86 (at_)

/-- `[ecx + 4 j] := eax`: word `j` of the state, 32 bits of it. -/
def st (j : Nat) : Instr := .store (at_ .ecx (4 * j)) .eax

/-- The four words zero, and 0 returned. -/
def clear : List Instr :=
  [.mov .ecx (.mem (PublicFn.argument 0)), .mov .eax (.imm 0), st 0, st 1, st 2, st 3, st 4, st 5, st 6, st 7]

/-- `eax := L = (bits + 7) / 8`. -/
def width : List Instr := [.mov .eax (.mem (PublicFn.argument 1)), .alu .add .eax (.imm 7), .shift .shr .eax 3]

/-- The four words, and 1 returned. -/
def setup : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 1)), .mul .eax, .mov .edx (.imm 64), .mul .edx,
    .mov .ecx (.mem (PublicFn.argument 0)), st 0, .store (at_ .ecx (4 * 1)) .edx] ++
  width ++ [st 2, .mov .edx (.imm 32769), .mul .edx, st 4] ++
  width ++ [.mov .edx (.imm 512), .mul .edx, st 6,
    .mov .eax (.imm 0), st 3, st 5, st 7, .mov .eax (.imm 1)]

def code : Prog isa :=
  .seq (.block [.mov .edx (.mem (PublicFn.argument 1)), .alu .cmp .edx (.imm 512)]) <|
  .ite .b (.block clear) <|
  .seq (.block [.alu .cmp .edx (.imm 8193)]) <|
  .ite .ae (.block clear) <|
  .seq (.block [.mov .eax (.mem (PublicFn.argument 2)), .alu .cmp .eax (.imm 2)]) <|
  .ite .e (.block setup) <|
  .seq (.block [.alu .cmp .eax (.imm 5)]) (.ite .e (.block setup) (.block clear))

end VG.Impl.Ffdh.X86.ParamInit
