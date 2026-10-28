module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
public import VerifiedGarbage.Impl.Mont.X86

/-! # The shared header and the inverse at the run-time width

`Header.code w` for the width that header byte 4 gives (the candidate's
`8 w` octets): the width, the stride `8 w + 16` and the first eight arrays'
pointers, each stride above the last. The inverse reads only the
candidate's low words, at 256 for every width.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.HeaderRt
open VG VG.X86 VG.Impl.Mont.X86

/-- Pointer `i` stored as a pair, `eax` moved up a stride (`ecx`). -/
def pointer (i : Nat) : List Instr :=
  [.store (sc (64 + 8 * i)) .eax, .store (sc (64 + 8 * i + 4)) .edx, .alu .add .eax (.reg .ecx)]

def code : List Instr :=
  [.mov .ecx (.mem (sc 4)), .mov .eax (.reg .ecx), .shift .shr .eax 3, .mov .edx (.imm 0),
    .store (sc 48) .eax, .store (sc (48 + 4)) .edx, .alu .add .ecx (.imm 16), .mov .eax (.reg .ecx),
    .store (sc 224) .eax, .store (sc (224 + 4)) .edx, .mov .eax (.reg .edi), .alu .add .eax (.imm 256)] ++
    (List.range 8).flatMap pointer

/-- `PrepareHeader.code` at the run-time width. -/
def prepare : Prog isa := .seq (.block code) (MontInverse.code 256 56)

end VG.Impl.RsaKeyGen.X86.HeaderRt
