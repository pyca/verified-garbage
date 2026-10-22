module

public import VerifiedGarbage.Impl.Ecdh.AArch64

/-! # Shared SEC 1 point compression on AArch64

Curve parameters and field operations come from the existing EC configuration.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.AArch64

open VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64

/-- Point all three setup inputs at x, retaining the encoding's address. -/
def args : List Instr :=
  [.addImm .x .x4 .x2 0, .addImm .x .x6 .x1 0,
    .addImm .x .x3 .x1 1, .addImm .x .x1 .x3 0,
    .addImm .x .x2 .x3 0]

/-- Write the parity tag, masked by validity in x3. -/
def compressTag (c : Cfg) : List Instr :=
  [ld .x1 (c.sl Ecdh.AArch64.QY), .movz .x .x2 1 0,
    .logic .and .x .x1 .x1 .x2, .addImm .x .x1 .x1 2,
    .logic .and .x .x1 .x1 .x3, .strb .x1 .x20 0]

def compressFinish (c : Cfg) : List Instr :=
  [ld .x3 (c.sl FLAG)] ++ compressTag c ++
  storeBytes c.C.len c.n .x20 1 (c.sl E) ++
  Cfg.saved.map (fun (r, d) => ld r d) ++
  [.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1]

/-- Validate the input point before emitting its SEC 1 compressed encoding. -/
def compress (c : Cfg) : Prog isa :=
  .seq (.block args) <|
  .seq (.block (c.setupWith none)) <|
  .seq (.block (Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Ecdh.AArch64.Cfg.validate c) (.block (compressFinish c))

end VG.Impl.EcKey.Compressed.AArch64
