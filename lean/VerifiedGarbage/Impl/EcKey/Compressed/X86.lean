module

public import VerifiedGarbage.Impl.Ecdh.X86

/-! # SEC 1 conversion with the existing 32-bit x86 field backend -/

@[expose] public section
namespace VG.Impl.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86

def args : Args := ⟨2, 1, 1, 1, none⟩

def compressTag (c : Cfg) : List Instr :=
  [.mov .eax (.mem (sc (c.sl Ecdh.X86.QY))), .alu .and .eax (.imm 1),
    .alu .or .eax (.imm 2), .alu .and .eax (.reg .ecx), .store8 (at_ .ebx 0) .al]

def compressFinish (c : Cfg) : List Instr :=
  [.mov .ecx (.mem (sc (c.sl FLAG))), .mov .ebx (.mem (Cfg.argOp 0))] ++ compressTag c ++
  storeBytes c.C.len c.n .ebx 1 (c.sl E) ++
  [.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] ++ Cfg.restore

def compress (c : Cfg) : Prog isa :=
  .seq (.block (c.setupWith args)) <|
  .seq (.block (Ecdh.X86.Cfg.peerAt c 1)) <|
  .seq (Ecdh.X86.Cfg.validate c) (.block (compressFinish c))

end VG.Impl.EcKey.Compressed.X86
