module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.General

/-! The bounded specialization for a 12-byte nonce and at most one block of AAD. -/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous

open VG.AArch64
/-- Supply the register pointers directly to the fragment that also processes a
gather descriptor. The public contiguous ABI already supplies its length. -/
def directPointers : List Instr := [ptr .x1 .x19 (DirectGather.streamO+16),mov .x2 .x7] ++
    Stitch.atP .x3 DirectGather.authO 1

def shortRecordBody : Prog isa :=
  let k := DirectGather.shortWork
  .seq (.block (DirectGather.shortSetupAt k)) <| .seq (.block DirectGather.shortZero) <|
    .seq DirectGather.shortAad <| .seq (VG.Impl.Gcm.AArch64.Stitch.byRounds (DirectGather.shortKeys 0)) <|
    .seq (.block directPointers) <| .seq (DirectGather.shortPieceWith [mov .x0 .x6,mov .x12 .x26]) <|
    .seq (.block [.ldrSp .x5 (k+16)]) <|
    .block (DirectGather.shortLengths ++ DirectGather.shortHashWith DirectGather.authO DirectGather.hashEightWith ++
      DirectGather.shortTagAt (k+8) ++ restore)

def shortFrame : Prog isa :=
  .frame (.alloc DirectGather.shortWork) shortRecordBody (.free DirectGather.shortWork)

def standardGuard : List Instr :=
  [.subImm .x .x10 .x3 12,imm .x9 17,.subs .x .x11 .x5 .x9,.csel .x .x10 .x9 .x10]

end VG.Impl.AesGcm.AArch64.Contiguous
