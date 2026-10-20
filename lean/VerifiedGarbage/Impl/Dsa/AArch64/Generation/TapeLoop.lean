module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random

/-! # Complete-chunk iteration over DSA seed and generator tapes

Compare total minus used before advancing a cursor. Status 3 retries;
accepted and fatal statuses stop. Exhaustion sets status 3 but clears
continuation independently, so an exhausted tape cannot retry forever.
-/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Random (store)

structure TapeSlots where
  base : Nat
  total : Nat
  used : Nat
  pointer : Nat

def seedTape : TapeSlots := ⟨8, 9, 10, 1⟩
def generatorTape : TapeSlots := ⟨11, 13, 20, 21⟩

def tapeReset (slots : TapeSlots) : List Instr :=
  [movi .x0 0] ++ store (8 * slots.used) .x0

/-- x0 is one exactly when there is no complete next chunk. -/
def chunkCheck (slots : TapeSlots) (width : Nat) : List Instr :=
  [.ldrSp .x3 (8 * slots.total), .ldrSp .x4 (8 * slots.used),
   .sub .x .x3 .x3 .x4, movi .x5 width, .subs .x .x3 .x3 .x5,
   movi .x4 1, movi .x5 0, .csel .x .x0 .x5 .x4]

def tapeTake (slots : TapeSlots) (width : Nat) : List Instr :=
  [.ldrSp .x3 (8 * slots.base), .ldrSp .x4 (8 * slots.used),
   .add .x .x3 .x3 .x4, movi .x5 width, .add .x .x4 .x4 .x5] ++
  store (8 * slots.pointer) .x3 ++ store (8 * slots.used) .x4

def tapeStatus : List Instr := [.ldrSp .x0 152, .subImm .x .x0 .x0 3]

def tapeIteration (slots : TapeSlots) (width : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block (chunkCheck slots width))
    (.ite (.nonzero .x .x0)
      (.block ([movi .x0 3] ++ store 152 .x0 ++ [movi .x0 1]))
      (.seq (.block (tapeTake slots width)) (.seq body (.block tapeStatus))))

def tapeLoop (slots : TapeSlots) (width : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block (tapeReset slots)) (.loop (tapeIteration slots width body) (.zero .x .x0))

end VG.Impl.Dsa.AArch64.Generation
