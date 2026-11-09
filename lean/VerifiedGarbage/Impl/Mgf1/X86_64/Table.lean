module

public import VerifiedGarbage.Impl.Mgf1.X86_64
public import VerifiedGarbage.Impl.ICall

/-!
# MGF1 on x86-64 with the hash function of a table

`mgfXor` of `Impl/Mgf1/X86_64.lean` for the hash function of a table of the
interface `Hash` (`Spec/HashTable.lean`) rather than a fixed one: the
table's address is the word at `[rsp + sArg]` (the caller's argument),
which MGF1 copies to the slot `sTab`, and the table's digest length (its
word 4) to the slot `sD`. The hash function's `init`, `update` and
`finalize` are the table's functions 0, 1 and 2, which it calls indirectly
(`tcall`: their address, the table's word `j`, into `r11`, then `call r11`,
of whichever of the functions `Fns` lists is at that address); the digest
length is read from `sD` rather than being an immediate. Everything else is
`Impl/Mgf1/X86_64.lean`'s.
-/

@[expose] public section

namespace VG.Impl.Mgf1.X86_64.Table

open VG.X86_64

/-- The functions an indirect call of each of a table's functions may
reach: for each of `init`, `update` and `finalize`, that function of every
table of the interface, by name. -/
structure Fns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)

variable (L : Layout) (sArg sTab sD : Nat) (f : Fns)

/-- The call of the table's function `j`, among `ts`: its address (the
table's word `j`) into `r11`, then `call r11`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (sp sTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))])
    (Code.icalls (.callr .r11) ts)

/-- `xorHead`, with the digest length read from `sD`. -/
def xorHead : List Instr :=
  scr L .rcx L.oDig ++ [.mov .rdx (.mem (sp L.sDone)), .mov .rdi (.mem (sp L.sDst)),
    .alu .add .rdi (.reg .rdx), .mov .rax (.mem (sp L.sDstLen)), .alu .sub .rax (.reg .rdx),
    .mov .r10 (.mem (sp sD)), .alu .cmp .rax (.reg .r10)]

/-- `xorOut`, with the digest length read from `sD`. -/
def xorOut : Prog isa :=
  seqs [.block (xorHead L sD), .ite .b (.block [.mov .r10 (.reg .rax)]) (.block []), .block [.mov32 .r8 (.imm 0)],
    byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdx (ix .rdi .r8), .alu .xor .rdx (.reg .rax),
      .store8 (ix .rdi .r8) .rdx] (.reg .r10)]

/-- `nextCtr`, with the digest length read from `sD`. -/
def nextCtr : List Instr :=
  [.mov .rax (.mem (sp L.sCtr)), .alu .add .rax (.imm 1), .store (sp L.sCtr) .rax, .mov .rax (.mem (sp L.sDone)),
    .alu .add .rax (.mem (sp sD)), .store (sp L.sDone) .rax, .alu .cmp .rax (.mem (sp L.sDstLen))]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`. -/
def round : Prog isa :=
  seqs [.block (initArgs L), tcall sTab 0 f.init, .block (updSrcArgs L), tcall sTab 1 f.upd,
    .block (updCtrArgs L), tcall sTab 1 f.upd, .block (finArgs L), tcall sTab 2 f.fin, xorOut L sD,
    .block (nextCtr L sD)]

/-- The table's address to `sTab`. -/
def tabArg : List Instr := [.mov .rax (.mem (sp sArg)), .store (sp sTab) .rax]

/-- The table's digest length to `sD`, and the counter and `done` set to 0. -/
def tabHead : List Instr :=
  [.mov .rax (.mem (sp sTab)), .mov .rax (.mem (at_ .rax 32)), .store (sp sD) .rax,
    .mov32 .rax (.imm 0), .store (sp L.sCtr) .rax, .store (sp L.sDone) .rax]

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`, with the hash function of
the table at `[rsp + sArg]`. -/
def mgfXor : Prog isa :=
  seqs [.block (tabArg sArg sTab), .block (tabHead L sTab sD), .loop (round L sTab sD f) .b]

end VG.Impl.Mgf1.X86_64.Table
