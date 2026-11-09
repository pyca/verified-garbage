module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Call

/-! # Fixed-size copies for prepared ML-DSA keys

The loop uses only caller-saved registers. All supported encoded key lengths
and polynomial lengths are multiples of 16, so no padding is read or written.
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call

def copyBody : List Instr :=
  [.ldrq .v0 .x1 0, .strq .v0 .x0 0,
    .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 16, .subImm .x .x2 .x2 1]

def copy (dst src : Ptr) (bytes : Nat) : Prog isa :=
  if bytes = 0 then .block [] else
    .seq (.block (lea .x0 dst.1 dst.2 ++ lea .x1 src.1 src.2 ++ movV .x2 (bytes / 16)))
      (.loop (.block copyBody) (.nonzero .x .x2))

end VG.Impl.MlDsa.AArch64.PreparedKey
