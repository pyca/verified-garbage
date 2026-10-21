module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Whole-word Montgomery trial division on 32-bit x86

The small-prime sieve follows x86-64's Montgomery-remainder filter. IA-32's
`mul` supplies a full 64-bit product, so each step consumes an entire 32-bit
candidate word. The carry of the input sum is kept explicitly; it must not
be lost when `h + acc` overflows a word.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Trial
open VG VG.X86

/-- `EBP := (X + q s) / 2^32`, where `X = EAX + EBP` and
`q = X (-s⁻¹) mod 2^32`. The prime is in EBX and its negative inverse in
ESI. ECX holds X's low word; EBP temporarily holds its carry. No memory or
control flow depends on the candidate word. -/
def redc32 : List Instr :=
  [.alu .add .eax (.reg .ebp), .mov .ebp (.imm 0), .alu .adc .ebp (.imm 0),
    .mov .ecx (.reg .eax), .mul .esi, .mul .ebx,
    .alu .add .eax (.reg .ecx), .alu .adc .edx (.reg .ebp), .mov .ebp (.reg .edx)]

/-- Consume one whole candidate word, advance its public pointer, and compare
it with the public end pointer held in a stack slot. -/
def wordStep (endOffset : Nat) : List Instr :=
  [.mov .eax (.mem ⟨.edi, 0⟩)] ++ redc32 ++
    [.alu .add .edi (.imm 4), .alu .cmp .edi (.mem ⟨.esp, endOffset⟩)]

/-- The positive-width word loop, from the candidate's first word to its end. -/
def words (endOffset : Nat) : Prog isa := .loop (.block (wordStep endOffset)) .ne

/-- Convert the two possible zero residues into a bit. The accumulator is
below twice the positive divisor, so the two tests are mutually exclusive. -/
def finish : List Instr :=
  [.mov .eax (.imm 0), .mov .edx (.reg .ebp), .alu .sub .edx (.imm 1),
    .alu .adc .eax (.imm 0), .alu .sub .ebp (.reg .ebx), .alu .sub .ebp (.imm 1),
    .alu .adc .eax (.imm 0)]

/-- The complete fixed-width test for one public small-prime divisor. -/
def divisor (endOffset : Nat) : Prog isa := .seq (words endOffset) (.block finish)

end VG.Impl.RsaKeyGen.X86.Trial
