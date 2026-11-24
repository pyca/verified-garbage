module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium

/-! Seal one bounded record directly from the caller’s source and destination registers. -/
@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect

open VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.DirectGather

def streamFor (n : Nat) : Prog isa :=
  .seq (.block [mov .x27 .x6,mov .x28 .x7]) (CounterBatch.kernel n Medium.keyO)

def stream : Prog isa := Medium.chooseGroup 129 (streamFor 9) (Medium.chooseGroup 161 (streamFor 11) (streamFor 15))

def zeroAuth : List Instr :=
  .vop (.movi0 .v0) :: (List.range 17).map fun i => .strq .v0 .x19 (Medium.authO+16*i)

def cursors : List Instr :=
  [ptr .x1 .x19 (Medium.keyO+16), mov .x2 .x28] ++ Stitch.atP .x3 (Medium.authO+128) 1

def body : Prog isa :=
  .seq (.block (shortSetupAt Medium.work)) <| .seq (.block zeroAuth) <| .seq (Medium.aadWith true) <| .seq stream <|
  .seq (.block cursors) <| .seq (shortPieceWith [mov .x0 .x27, mov .x12 .x26]) <|
  .seq (.block [.ldrSp .x5 (Medium.work+16)]) <| Medium.finishCached (Medium.work+8)

def frame : Prog isa := .frame (.alloc Medium.work) body (.free Medium.work)

end VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect
