module

public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc

/-! Montgomery cancellation with the known-zero low word omitted.
The carry into the second limb is obtained by comparing the old low word
with one. This is valid under the existing inverse condition. -/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.BlockedRedcFast
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
-- The cancelled low word is zero; its addition carries iff it was nonzero.
def lowChain : List Instr :=
 [movi .x13 1, .subs .x .x13 .x19 .x13] ++
 (List.range 4).flatMap (fun j => BlockedRedc.product false (j+1) BlockedRedc.tt[(j+1)%4]!) ++
 (List.range 7).flatMap (fun k =>
  let j := k+1
  [.adcs .x BlockedRedc.aa[j]! BlockedRedc.aa[j]! BlockedRedc.tt[j%4]!] ++
  (if j < 4 then BlockedRedc.product false (j+4) BlockedRedc.tt[j%4]!
   else BlockedRedc.product true (j-4) BlockedRedc.tt[j%4]!))

def cancel (i : Nat) : List Instr :=
 [.mul .x .x27 .x19 .x15, st .x27 .x8 (8*i), movi .x1 0] ++
 lowChain ++ [.adc .x .x1 .x1 .x7] ++ BlockedRedc.highChain
open BlockedRedc
def redc : Prog isa :=
  .seq (.block [.lsr .x .x12 .x12 3, movi .x10 0])
  (.seq (.loop
    (.seq (.block (BlockedRedc.asLoad ++ [ldh .x17 (sArr Public.aN), ldh .x15 sMinv] ++ BlockedRedc.nsLoad ++
       (List.range 8).flatMap cancel ++
       [.addImm .x .x16 .x8 64, .addImm .x .x17 .x17 64,
        ldh .x15 sW, .lsr .x .x15 .x15 3, .subImm .x .x15 .x15 1]))
     (.seq (countLoop .x15 (BlockedRedc.addMemory false ++ BlockedRedc.nsLoad ++
        (List.range 8).flatMap BlockedRedc.tail ++ [.addImm .x .x17 .x17 64]))
      (.block (BlockedRedc.addMemory true ++ [.adc .x .x10 .x7 .x7] ++ BlockedRedc.asStore ++
        [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))))
    (.nonzero .x .x12))
    (.block [ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16,
      st .x10 .x16, st .x7 .x16 8, ldh .x10 (sArr Public.aN)]))

end VG.Impl.Bignum.AArch64.BlockedRedcFast
