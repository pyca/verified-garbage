module
public import VerifiedGarbage.Impl.Ecdh.X86_64


/-! # Compressed public-point conversion on x86-64

The converters use the existing ECDSA field configuration and ECDH point
check. Constants and arithmetic therefore follow the same Lean sources
and baseline/ADX selection as the other EC operations.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64

/-- Keep `out` in `rdi` for the shared setup; pass the public key in `r9`
and read its `x` into the setup's three input slots. -/
def args : List Instr :=
  [.mov .r8 (.reg .rdx), .mov .r9 (.reg .rsi),
    .mov .rcx (.reg .rsi), .alu .add .rcx (.imm 1),
    .mov .rsi (.reg .rcx), .mov .rdx (.reg .rcx)]

/-- Write the parity tag and canonical `x`, both masked by validity, and
restore the shared setup's saved registers. `QY` and `E` retain the input
coordinates throughout the point check. -/
def compressTag (c : Cfg) : List Instr :=
  [.mov .rdx (.mem (sc (c.sl Ecdh.X86_64.QY))),
    .alu .and .rdx (.imm 1), .alu .add .rdx (.imm 2),
    .alu .and .rdx (.reg .rcx), .store8 { base := .rsi } .rdx]

def compressFinish (c : Cfg) : List Instr :=
  [.mov .rcx (.mem (sc (c.sl FLAG)))] ++ compressTag c ++
  storeBytes c.C.len c.n .rsi 1 (c.sl E) ++
  [.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] ++
  Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- Validate the original uncompressed point before writing its compressed
encoding. The existing point checker supplies all field arithmetic. -/
def compress (c : Cfg) : Prog isa :=
  .seq (.block args) <|
  .seq (.block (c.setupWith none)) <|
  .seq (.block (Ecdh.X86_64.Cfg.peer c)) <|
  .seq (Ecdh.X86_64.Cfg.check c) (.block (compressFinish c))

end VG.Impl.EcKey.Compressed.X86_64
