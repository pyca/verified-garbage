module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateBits
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Near

/-! # The candidate drawn, compared with `p` and sieved at the run-time width

The candidate's length `8 w` is at header byte 4, before any array pointer is
in the header: each loop computes its arrays' addresses (`256 + j (len + 16)`
above the workspace) and its count from the length. The subtractions and the
select of the distance to `p` use `edi` as a pointer or a count, the
workspace pointer saved in their frame.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.MillerRabin.X86 (scaleIndex)

/-- `r := edi + 256 + j (len + 16)`, array `j`, for `len` at header byte 4;
`t` is clobbered. -/
def lenPtr (r t : Reg) (j : Nat) : List Instr :=
  [.mov t (.mem (sc 4)), .alu .add t (.imm 16), .mov r (.imm 0)] ++ scaleIndex r t j ++
    [.alu .add r (.reg .edi), .alu .add r (.imm 256)]

/-- `Import.code`'s arguments for array `j`: `ebx` at its top word and `ecx`
its `len / 4` words. -/
def importArgs (j : Nat) : List Instr :=
  lenPtr .ebx .edx j ++ [.mov .ecx (.mem (sc 4)), .alu .add .ebx (.reg .ecx), .alu .sub .ebx (.imm 4),
    .shift .shr .ecx 2]

/-- Array `j` from the big-endian octets at `esi`. -/
def importAt (j : Nat) : Prog isa := .seq (.block (importArgs j)) Import.code

/-- The candidate's two top bits and its low bit set. -/
def bits : List Instr :=
  CandidateBits.forceWord 256 1 ++ [.mov .ebx (.mem (sc 4)), .alu .add .ebx (.reg .edi),
    .mov .eax (.mem (at_ .ebx 252)), .alu .or .eax (.imm 0xc0000000), .store (at_ .ebx 252) .eax]

/-- The octets used: the candidate's `len`. -/
def count : List Instr :=
  [.mov .eax (.mem (sc 4)), .store (sc 152) .eax, .mov .eax (.imm 0), .store (sc 156) .eax]

/-- The candidate drawn into array 0. -/
def load : Prog isa :=
  .seq (.block [.mov .esi (.mem (sc 28))]) (.seq (importAt 0) (.block (bits ++ count)))

/-- The loop of a subtraction `[edi] := [ebp] − [ebx]`, `edx` bytes, its borrow a
mask in `ecx`. -/
def subLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx),
    .alu .sbb .eax (.mem (at_ .ebx 0)), .store (at_ .edi 0) .eax, .alu .sbb .ecx (.reg .ecx),
    .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .edi (.imm 4),
    .alu .sub .edx (.imm 4)]) .ne

/-- `[out] := [a] − [b]`, its borrow a mask in `ecx`; `edi` set back. -/
def sub (out a b : Nat) : Prog isa :=
  .seq (.block (lenPtr .ebp .edx a ++ lenPtr .ebx .edx b ++ lenPtr .eax .edx out ++
    [.mov .edx (.mem (sc 4)), .mov .edi (.reg .eax), .mov .ecx (.imm 0)]))
    (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))]))

/-- The loop of a select `[ebx] := [ebp]` where the mask `ecx` is all ones,
`edi` bytes. -/
def selectLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebp 0)),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
    .store (at_ .ebx 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4),
    .alu .sub .edi (.imm 4)]) .ne

/-- `|c − p|` into array 2, through array 3: `c − p`, `p − c`, and the second
where the first borrowed. -/
def difference : Prog isa :=
  .seq (sub 2 0 4) (.seq (.block [.mov .esi (.reg .ecx)]) (.seq (sub 3 4 0)
    (.seq (.block (lenPtr .ebp .edx 3 ++ lenPtr .ebx .edx 2 ++ [.mov .edi (.mem (sc 4)), .mov .ecx (.reg .esi)]))
      (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))])))))

/-- `ebx` the OR of array 2's words but its top four, `ebp` past them. -/
def orScan : Prog isa :=
  .seq (.block ([.mov .ebx (.imm 0)] ++ lenPtr .ebp .edx 2 ++
    [.mov .ecx (.mem (sc 4)), .shift .shr .ecx 2, .alu .sub .ecx (.imm 4)]))
    (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)

/-- `Near.top` at `ebp`, the top four words. -/
def top : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .mov .ecx (.reg .eax), .shift .shr .ecx 28,
    .alu .and .eax (.imm 0x0fffffff), .alu .or .ebx (.reg .eax),
    .mov .edx (.mem (at_ .ebp 4)), .alu .or .edx (.mem (at_ .ebp 8)), .alu .or .edx (.mem (at_ .ebp 12))]

/-- `eax = 1` when `|c − p|` is at most the threshold. -/
def near : Prog isa := .seq orScan (.block (top ++ Near.finish))

/-- `p` into array 4, then the distance check. -/
def other : Prog isa :=
  .seq (.block [.mov .esi (.mem (sc 20))]) (.seq (importAt 4)
    (.frame (.alloc 20) (.seq (.block [.store (at_ .esp 0) .edi]) (.seq difference near)) (.free 20)))

def close : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc 24)), .alu .cmp .eax (.imm 0)])
    (.ite .e (.block [.mov .eax (.imm 0)]) other)

/-- The trial frame: the candidate's end from the length, read before `edi`
moves to the candidate. -/
def candidateSlots : List Instr :=
  [.store (Sieve.slot 0) .edi, .mov .eax (.reg .edi), .alu .add .eax (.reg .edx), .store (Sieve.slot 4) .eax]

/-- The table's 512 entries for a candidate of at most 128 octets, else 1024. -/
def tableSlots : List Instr :=
  [.store (Sieve.slot 8) .eax, .mov .eax (.reg .edx), .alu .cmp .eax (.imm 129), .alu .sbb .eax (.reg .eax),
    .alu .and .eax (.imm (BitVec.ofInt 32 (-512))), .alu .add .eax (.imm 1024), .store (Sieve.slot 12) .eax,
    .mov .eax (.imm 0), .store (Sieve.slot 16) .eax]

def sieveBody : Prog isa :=
  .seq (.block candidateSlots) (.seq Sieve.tableAddress (.seq (.block tableSlots) (Sieve.loop Sieve.stackSlots)))

def sieve : Prog isa :=
  .frame (.alloc 20) (.seq (.block [.mov .edx (.mem (sc 4)), .alu .add .edi (.imm 256)])
    (.seq sieveBody (.block CandidateSieve.restore))) (.free 20)

/-- The candidate drawn and compared with `p`, and trial division: the result
2 or 3 written, or `eax = 4` to go on. -/
def code : Prog isa :=
  .seq load (.seq close (.seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .ne (CandidateFinish.used 2) (.seq sieve (.seq (.block [.alu .cmp .eax (.imm 0)])
      (.ite .ne (CandidateFinish.used 3) (.block [.mov .eax (.imm 4)])))))))

end VG.Impl.RsaKeyGen.X86.FrontRt
