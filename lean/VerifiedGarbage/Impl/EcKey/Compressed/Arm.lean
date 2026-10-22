module

public import VerifiedGarbage.Impl.Ecdh.Arm

/-! # SEC 1 point compression with the existing ARMv7 field backend -/

@[expose] public section
namespace VG.Impl.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Ecdsa.Arm

/-- All setup reads are within the encoding; peer parsing replaces E and QY. -/
def args : Args := ⟨.r1, .r1, .r1, some .r2, none⟩

def compressTag (c : Cfg) : List Instr :=
  [.ldr .r4 wb (c.sl Ecdh.Arm.QY), .dp .and .r4 .r4 (.imm 1),
    .dp .orr .r4 .r4 (.imm 2), .dp .and .r4 .r4 (.reg .r10), .strb .r4 .lr 0]

def compressFinish (c : Cfg) : List Instr :=
  [.ldr .r10 wb (c.sl FLAG)] ++ compressTag c ++
  storeBytes c.C.len c.n .lr 1 (c.sl E) ++
  [.dp .and .r0 .r10 (.imm 1)] ++ Cfg.restore

def compress (c : Cfg) : Prog isa :=
  .seq (.block (c.setupWith args)) <|
  .seq (.block (Ecdh.Arm.Cfg.peerAt c .r1)) <|
  .seq (Ecdh.Arm.Cfg.validate c) (.block (compressFinish c))

end VG.Impl.EcKey.Compressed.Arm
