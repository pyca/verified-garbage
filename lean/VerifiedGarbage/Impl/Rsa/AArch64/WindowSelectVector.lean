module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Impl.Bignum.CrtLayout
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive


/-! The measured full-scan SIMD selector: four vector accumulators select
64 bytes per pass. Widths without a complete block use the scalar selector. -/

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
def select (entries : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 3, movi .x4 7, .logic .and .x .x4 .x12 .x4])
 (.ite (.nonzero .x .x3) (.ite (.zero .x .x4) (blocked entries) fallback) fallback)

end VG.Impl.Rsa.AArch64.WindowSelectVector
