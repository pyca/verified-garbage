module

public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Impl.Bignum.Arm.ImportArray
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut

/-! Public five-tooth table construction through one shared Montgomery helper.
The four bases and their subsets use runtime loops and canonical context storage. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.CombPrecompute
open VG VG.Arm VG.Impl.Bignum.Arm

def entryArgs : List Instr :=
  [.addSp .r12 0, Domain.st .r0 4, Domain.st .r2 24, Domain.st .r3 28,
    .ldrSp .r3 128, Domain.st .r3 32, .ldrSp .r0 132, Domain.st .r0 0]

def entry : List Instr := entryArgs ++ Domain.prepareArgs 24 ++ Domain.domainPointers

/-- The policy's saved width and low-byte mask determine its exact maximum bits. -/
def bitCountStep : List Instr :=
  [.dp .add .r1 .r1 (.imm 1), .mov .r3 (.shifted .r3 .lsr 1), .cmp .r3 (.imm 0)]

def bitCount : Prog isa :=
  .seq (.block [.ldrSp .r3 68, .mov .r1 (.imm 0)]) (.loop (.block bitCountStep) .ne)

def bitsSave : List Instr :=
  [.ldrSp .r6 20, .dp .sub .r6 .r6 (.imm 1), .mov .r6 (.shifted .r6 .lsl 3),
    .dp .add .r1 .r1 (.reg .r6), .addSp .r12 0, Domain.st .r1 16]

/-- Public repeated division by five, with carry materialized before its branch. -/
def rowsStep : List Instr :=
  [.dp .sub .r3 .r3 (.imm 5), .dp .add .r6 .r6 (.imm 1), .cmp .r3 (.imm 5),
    .adc .r7 .r2 (.imm 0), .cmp .r7 (.imm 0)]

def rowsCount : Prog isa :=
  .seq (.block [.dp .add .r3 .r1 (.imm 4), .mov .r6 (.imm 0), .mov .r2 (.imm 0)])
    (.seq (.loop (.block rowsStep) .ne) (.block [.addSp .r12 0, Domain.st .r6 44]))

def header : List Instr :=
  [.ldrSp .r4 4, .mov .r2 (.imm 0), .ldrSp .r1 16,
    .str .r1 .r4 0, .str .r2 .r4 4, .ldrSp .r1 20,
    .str .r1 .r4 8, .str .r2 .r4 12, .ldrSp .r1 44,
    .str .r1 .r4 16, .str .r2 .r4 20]

def metadata : Prog isa := .seq bitCount (.seq (.block bitsSave) (.seq rowsCount (.block header)))

/-- r3 is the public digit; r4 becomes its canonical context entry address. -/
def tableArgs : List Instr :=
  [.ldrSp .r4 4, .ldr .r1 .r0 48, .mov .r1 (.shifted .r1 .lsl 3),
    .dp .add .r3 .r3 (.imm 2), .mul .r3 .r3 .r1,
    .dp .add .r4 .r4 (.reg .r3), .dp .add .r4 .r4 (.imm 24)]

def store (array : Nat) : Prog isa :=
  .seq (.block (tableArgs ++ [.mov .r2 (.imm (BitVec.ofNat 32 array))])) exportArray

def montgomeryOut : Prog isa :=
  .seq (.block [.ldrSp .r4 4, .dp .add .r4 .r4 (.imm 24)])
    (.seq precomputeOut (.block [.ldrSp .r0 0]))

def initial (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (Domain.importAt 1 56 32) (.seq (SharedWindow.init op)
    (.seq (.block [.mov .r3 (.imm 0)]) (.seq (store 6)
      (.seq (.block [.mov .r3 (.imm 1)]) (store 5)))))

def squaresInit : List Instr := [.ldrSp .r3 44, .addSp .r12 0, Domain.st .r3 68]
def squaresNext : List Instr :=
  [.ldrSp .r3 68, .subs .r3 .r3 (.imm 1), .addSp .r12 0, Domain.st .r3 68]
def squares (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block squaresInit) (.loop (.seq (op 5 5 5) (.block squaresNext)) .ne)

def productLoad : Prog isa :=
  .seq (.block ([.ldrSp .r3 40] ++ tableArgs ++ [.mov .r2 (.imm 1)])) importArray

def productStore : Prog isa :=
  .seq (.block [.ldrSp .r3 36, .ldrSp .r2 40, .dp .add .r3 .r3 (.reg .r2)]) (store 6)

def productNext : List Instr :=
  [.ldrSp .r3 40, .dp .add .r3 .r3 (.imm 1), .addSp .r12 0, Domain.st .r3 40,
    .ldrSp .r2 36, .cmp .r3 (.reg .r2)]

def products (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block [.mov .r3 (.imm 1), .addSp .r12 0, Domain.st .r3 40])
    (.loop (.seq productLoad (.seq (op 6 1 5) (.seq productStore (.block productNext)))) .ne)

def basisNext : List Instr :=
  [.ldrSp .r3 36, .dp .add .r3 .r3 (.reg .r3), .addSp .r12 0, Domain.st .r3 36,
    .cmp .r3 (.imm 32)]

def basis (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (squares op) (.seq (.block [.ldrSp .r3 36])
    (.seq (store 5) (.seq (products op) (.block basisNext))))

def table (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (initial op) (.seq (.block [.mov .r3 (.imm 2), .addSp .r12 0, Domain.st .r3 36])
    (.loop (basis op) .ne))

def main (op : Nat → Nat → Nat → Prog isa) (bound : Prog isa) : Prog isa :=
  .seq (NormalizedPrepare.prepareAt op 24)
    (.seq bound (.seq metadata (.seq montgomeryOut (.seq (table op) (Domain.ret 1)))))

def code (op : Nat → Nat → Nat → Prog isa) (bound : Prog isa) : Prog isa :=
  framed (.seq (.block entry) (main op bound))

end VG.Impl.Ffdh.Arm.CombPrecompute
