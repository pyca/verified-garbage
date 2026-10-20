module

public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # Runtime-width copies, comparisons, and masked table scans for i686 -/

@[expose] public section
namespace VG.Impl.MillerRabin.X86
open VG VG.X86

def copy (dst src : Nat) : Prog isa :=
  .seq (.block (ptr .ebp dst ++ ptr .ebx src ++ words))
    (.loop (.block [.mov .eax (.mem (at_ .ebx 0)), .store (at_ .ebp 0) .eax,
      .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 1)]) .ne)

/-- Compare the low 2w words, storing a bit. Spare array words do not enter
this comparison. The final subtraction exposes accumulator=0 as a carry bit. -/
def equal (result a b : Nat) : Prog isa :=
  .seq (.block (ptr .ebp a ++ ptr .ecx b ++ words ++ [.mov .ebx (.imm 0)]))
    (.seq (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.mem (at_ .ecx 0)),
      .alu .or .ebx (.reg .eax), .alu .add .ebp (.imm 4), .alu .add .ecx (.imm 4),
      .alu .sub .esi (.imm 1)]) .ne)
      (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1),
        .alu .adc .eax (.imm 0), .store (slot result) .eax]))

/-- Select a table entry into the witness array under the mask at sEq1.
The destination aliases one input; each word is read before it is replaced. -/
def selectEntry (j : Nat) : Prog isa :=
  .seq (.block (ptr .ebp (aTable + j) ++ ptr .ebx aX ++ words ++
    [.mov .ecx (.mem (slot sEq1))]))
    (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.mem (at_ .ebx 0)),
      .alu .and .eax (.reg .ecx), .alu .xor .eax (.mem (at_ .ebx 0)), .store (at_ .ebx 0) .eax,
      .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .sub .esi (.imm 1)]) .ne)

/-- Mask of the secret four-bit window being the compile-time table index. -/
def maskIndex (j : Nat) : List Instr :=
  [.mov .eax (.mem (slot sValue)), .shift .shr .eax 28,
    .alu .xor .eax (.imm (BitVec.ofNat 32 j)), .alu .sub .eax (.imm 1), .shift .shr .eax 31,
    .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax), .store (slot sEq1) .ecx]

def scanFrom : Nat → Nat → Prog isa
  | _, 0 => .block []
  | j, n + 1 => .seq (.block (maskIndex j)) (.seq (selectEntry j) (scanFrom (j + 1) n))

/-- Every entry is read at fixed addresses for every secret digit. -/
def scan : Prog isa := .seq (copy aX aTable) (scanFrom 1 15)

end VG.Impl.MillerRabin.X86
