module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Impl.Bignum.CrtLayout
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive


/-! The measured full-scan SIMD selectors. Widths that are a multiple of 16
limbs make one pass over the table per 128-byte column block, selecting with
eight vector accumulators and a mask from a scalar comparison (`wide`); other
multiples of 8 limbs use four accumulators and a vector comparison per 64-byte
block (`blocked`). Widths without a complete block use the scalar selector. -/

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowSelectVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Bignum.Public hiding sI sBit sV
open VG.Impl.Rsa.AArch64
def accs : List VReg := [.v16,.v17,.v18,.v19]
/-- One full-table row, with a secret comparison mask and public addresses. -/
def inner : List Instr :=
 [.vop (.cmeq .d2 .v20 .v23 .v22)] ++
 (accs.zipIdx.flatMap fun (r,i) =>
  [.ldrq .v21 .x16 (16*i), .vop (.bsel .bit r .v21 .v20)]) ++
 [.add .x .x16 .x16 .x6, .vop (.add .d2 .v23 .v23 .v24)]
def blocked (entries : Nat) : Prog isa :=
 .seq (.block [ldh .x12 sW, .addImm .x .x6 .x12 2, .lsl .x .x6 .x6 3,
  .lsr .x .x13 .x12 3, ldh .x5 sNib, .vop (.dup .d2 .v22 .x5), movi .x2 1, .vop (.dup .d2 .v24 .x2), ldh .x17 (sArr aT)])
 (.seq (.loop
  (.seq (.block ([ldh .x16 (sArr aT), .sub .x .x16 .x17 .x16,
    ldh .x3 sTab, .add .x .x16 .x16 .x3,  .vop (.movi0 .v23), movi .x14 entries] ++
    accs.map fun r => .vop (.movi0 r)))
   (.seq (countLoop .x14 inner)
    (.block ((accs.zipIdx.map fun (r,i) => .strq r .x17 (16*i)) ++
     [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1])))) (.nonzero .x .x13))
 (.block [ldh .x3 sTab, .lsl .x .x4 .x6 (if entries == 64 then 6 else if entries == 32 then 5 else 4), .add .x .x3 .x3 .x4,
   sth .x3 sEnt, movi .x3 entries, sth .x3 sJ]))
/-- The eight accumulators of a 128-byte column block. -/
def accsWide : List VReg := accs ++ [.v22,.v23,.v24,.v25]
/-- One full-table row of a 128-byte block. `x14` counts the rows down from
`entries`, and `x5` is `entries` minus the secret digit: the comparison's flags
choose the mask (`x7`, all ones, or `x8`, zero) and never an address. -/
def innerWide : List Instr :=
 [.subs .x .x9 .x14 .x5, .cselc .x .x9 .x7 .x8 .eq, .vop (.dup .d2 .v20 .x9)] ++
 (accsWide.zipIdx.flatMap fun (r,i) =>
  [.ldrq .v21 .x16 (16*i), .vop (.bsel .bit r .v21 .v20)]) ++
 [.add .x .x16 .x16 .x6]
def wide (entries : Nat) : Prog isa :=
 .seq (.block [ldh .x12 sW, .addImm .x .x6 .x12 2, .lsl .x .x6 .x6 3, .lsr .x .x13 .x12 4,
  ldh .x5 sNib, movi .x2 entries, .sub .x .x5 .x2 .x5, movi .x8 0, .subImm .x .x7 .x8 1,
  ldh .x17 (sArr aT)])
 (.seq (.loop
  (.seq (.block ([ldh .x16 (sArr aT), .sub .x .x16 .x17 .x16,
    ldh .x3 sTab, .add .x .x16 .x16 .x3, movi .x14 entries] ++
    accsWide.map fun r => .vop (.movi0 r)))
   (.seq (countLoop .x14 innerWide)
    (.block ((accsWide.zipIdx.map fun (r,i) => .strq r .x17 (16*i)) ++
     [.addImm .x .x17 .x17 128, .subImm .x .x13 .x13 1])))) (.nonzero .x .x13))
 (.block [ldh .x3 sTab, .lsl .x .x4 .x6 (if entries == 64 then 6 else if entries == 32 then 5 else 4), .add .x .x3 .x3 .x4,
   sth .x3 sEnt, movi .x3 entries, sth .x3 sJ]))
/-- The vector selector for a width that is a multiple of 8 limbs. -/
def vector (entries : Nat) : Prog isa :=
 .seq (.block [ldh .x12 sW, movi .x4 15, .logic .and .x .x4 .x12 .x4])
 (.ite (.zero .x .x4) (wide entries) (blocked entries))
def select (entries : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 3, movi .x4 7, .logic .and .x .x4 .x12 .x4])
 (.ite (.nonzero .x .x3) (.ite (.zero .x .x4) (vector entries) fallback) fallback)

end VG.Impl.Rsa.AArch64.WindowSelectVector
