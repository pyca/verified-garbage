module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium

/-! Seal one bounded record directly from the caller’s source and destination registers. -/
@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect

open VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.DirectGather

def cursors : List Instr :=
  [ptr .x1 .x19 (Medium.keyO+16), mov .x2 .x28] ++ Stitch.atP .x3 (Medium.authO+128) 1

def body (c : Callees) : Prog isa :=
  .seq (.block (shortSetupAt Medium.work)) <| .seq (.block Medium.zero) <| .seq (Medium.aadWith true) <| .seq (Medium.keys c) <|
  .seq (.block cursors) <| .seq (shortPieceWith [mov .x0 .x27, mov .x12 .x26]) <|
  .seq (.block [.ldrSp .x5 (Medium.work+16)]) <| Medium.finishCached (Medium.work+8)

def frame (c : Callees) : Prog isa := .frame (.alloc Medium.work) (body c) (.free Medium.work)

end VG.Impl.AesGcm.AArch64.Contiguous.MediumDirect
