module

public import VerifiedGarbage.Impl.Bignum.Arm.Round

/-! A UMAAL product row and its Montgomery cancellation share one accumulator scan. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.Fios
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Enter with the existing Montgomery temporary in `r0`. -/
def args : List Instr :=
  [.ldr .r1 .r0 16, .ldr .r1 .r1 0, .ldr .lr .r0 0,
   .ldr .r12 .r0 4, .ldr .r4 .r0 8, .ldr .r2 .r0 12,
   .ldr .r0 .r0 28, .mov .r7 (.imm 0), .mov .r8 (.imm 0)]

def product : Prog isa := .block [.umaal .r6 .r7 .r3 .r1]
def cancel : Prog isa := .block [.umaal .r6 .r8 .r5 .r2]

def firstLoads : List Instr := [.ldr .r3 .r12 0, .ldr .r5 .r4 0, .ldr .r6 .r0 0]
def firstNext : List Instr :=
  [.dp .add .r12 .r12 (.imm 4), .dp .add .r4 .r4 (.imm 4), .subs .lr .lr (.imm 1)]

/-- The first product determines the cancellation scalar; its cancelled low word is discarded. -/
def first : Prog isa :=
  .seq (.block firstLoads) (.seq product (.seq (.block [.mul .r2 .r2 .r6])
    (.seq cancel (.block firstNext))))

def loads : List Instr := [.ldr .r3 .r12 0, .ldr .r5 .r4 0, .ldr .r6 .r0 4]
def store : Prog isa := .block [.str .r6 .r0 0]

def step : Prog isa := .seq (.block loads) (.seq product (.seq cancel store))
def advance : List Instr :=
  [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 4),
   .dp .add .r4 .r4 (.imm 4), .subs .lr .lr (.imm 1)]
def body : Prog isa := .seq step (.block advance)
def pairLoadsA0 : List Instr := [.ldr .r3 .r12 0, .ldr .r6 .r0 4]
def pairLoadsA1 : List Instr := [.ldr .r3 .r12 4, .ldr .r10 .r0 8]
def product1 : Prog isa := .block [.umaal .r10 .r7 .r3 .r1]
def cancel1 : Prog isa := .block [.umaal .r10 .r8 .r5 .r2]

/-- Product and reduction each retain their own carry chain across two words. -/
def pairStep : Prog isa :=
  .seq (.block pairLoadsA0) (.seq product
    (.seq (.block pairLoadsA1) (.seq product1
      (.seq (.block [.ldr .r5 .r4 0]) (.seq cancel (.seq store
        (.seq (.block [.ldr .r5 .r4 4]) (.seq cancel1 (.block [.str .r10 .r0 4])))))))))

def pairAdvance : List Instr :=
  [.dp .add .r0 .r0 (.imm 8), .dp .add .r12 .r12 (.imm 8),
   .dp .add .r4 .r4 (.imm 8), .subs .lr .lr (.imm 2)]
def pairBody : Prog isa := .seq pairStep (.block pairAdvance)
def loop : Prog isa := .loop pairBody .ne

/-- Both independent carries are added before the high quotient words are stored. -/
def top : Prog isa :=
  .seq (.block [.ldr .r3 .r0 4, .ldr .r4 .r0 8])
    (.seq (.block (addWord .r7)) (.seq (.block (addWord .r8))
      (.block [.str .r3 .r0 0, .str .r4 .r0 4, .dp .add .r0 .r0 (.imm 8)])))

def code : Prog isa := .seq first (.seq body (.seq loop top))
def round : Prog isa := .seq (.block args) (.seq code (.block roundFinish))

end VG.Impl.Bignum.Arm.Fios
