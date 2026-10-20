module

public import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
public import VerifiedGarbage.Impl.Bignum.Arm.CombScan

/-! A fixed public five-column schedule uses one square and one product per row. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.CombExp
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Big-endian source, byte count, row index, spacing and maximum bit width. -/
def digitArgs : List Instr :=
  [.ldr .r4 .r0 128, .ldr .r5 .r0 132, .ldr .r6 .r0 192, .dp .sub .r6 .r6 (.imm 1),
   .ldr .r7 .r0 204, .ldr .r8 .r0 136]

def choose : Prog isa :=
  .seq (.block digitArgs) (.seq CombDigit.code (.seq (.block [.str .r11 .r0 196]) CombScan.code))

def next : List Instr :=
  [.ldr .r1 .r0 192, .subs .r1 .r1 (.imm 1), .str .r1 .r0 192]

def step (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (op 6 6 6) (.seq choose (op 6 6 1))

def round (op : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (step op) (.block next)

def rows (op : Nat → Nat → Nat → Prog isa) : Prog isa := .loop (round op) .ne

/-- R-squared times ordinary one gives Montgomery one. -/
def initial (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (smallConst 7 1) (.seq (op 6 4 7)
    (.block [.ldr .r1 .r0 204, .str .r1 .r0 192]))

/-- Process all public rows, including zero digits, then decode to ordinary form. -/
def phase (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (initial op) (.seq (rows op) (op 6 6 7))

end VG.Impl.Bignum.Arm.CombExp
