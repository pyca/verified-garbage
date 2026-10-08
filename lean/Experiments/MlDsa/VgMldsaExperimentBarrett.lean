import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlDsa.AArch64.Arith.Neon

def vectorMul (acc : Bool) : Prog isa :=
 .seq (.block (Neon.consts ++ movW .x9 2149582593 ++ [.vop (.dup .s4 .v18 .x9), .movz .x .x12 64 0]))
  (.loop (.block (
   [.ldrq .v0 .x1 0, .ldrq .v1 .x2 0] ++
   [.vop (.umull false .v2 .v1 .v18), .vop (.umull true .v3 .v1 .v18),
    .vop (.shift .ushr .d2 .v2 .v2 23), .vop (.shift .ushr .d2 .v3 .v3 23),
    .vop (.perm .uzp1 .s4 .v4 .v2 .v3), .vop (.sqdmulh .v4 .v0 .v4),
    .vop (.mul .v0 .v0 .v1), .vop (.mls .v0 .v4 .v16)] ++ Neon.csub .v0 .v4 ++
   (if acc then [.ldrq .v1 .x0 0,.vop (.add .s4 .v0 .v0 .v1)] ++ Neon.csub .v0 .v4 else []) ++
   [.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1])) (.nonzero .x .x12))

def vectorAcc (sub : Bool) : Prog isa :=
 .seq (.block (Neon.consts ++ [.movz .x .x12 64 0]))
  (.loop (.block ([.ldrq .v0 .x0 0,.ldrq .v1 .x1 0] ++
  (if sub then [.vop (.add .s4 .v0 .v0 .v16), .vop (.sub .s4 .v0 .v0 .v1)] else [.vop (.add .s4 .v0 .v0 .v1)]) ++
  Neon.csub .v0 .v4 ++ [.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.subImm .x .x12 .x12 1])) (.nonzero .x .x12))

def main : IO Unit := do
 for (name,code) in [("vg_mldsa_multiply_ntt",vectorMul false),("vg_mldsa_multiply_add_ntt",vectorMul true),("vg_mldsa_add",vectorAcc false),("vg_mldsa_sub",vectorAcc true)] do
  IO.FS.writeFile ("/tmp/"++name++".body") (String.join ((printer.function code).map (Rust.line printer.call)))
