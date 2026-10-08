import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Frag
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust
open VG VG.AArch64
namespace CombDot
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call

def product (j : Nat) : List Instr :=
 [.ldrq .v0 .x1 (1024*j),.ldrq .v1 .x2 (1024*j)] ++
 (if j=0 then [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1)]
 else [.vop (.umlal false .v2 .v0 .v1),.vop (.umlal true .v3 .v0 .v1)])
def dot (n : Nat) : Prog isa :=
 .seq (.block (consts ++ [.movz .x .x12 64 0])) <|
 .loop (.block ((List.range n).flatMap product ++
 [.vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
 .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
 .vop (.perm .uzp2 .s4 .v0 .v2 .v3)] ++ csub .v0 .v4 ++
 [.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
 .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1])) (.nonzero .x .x12)
def dotAt (n : Nat) (h f g : Ptr) : Prog isa :=
 callAt ("vg_mldsa_dot" ++ toString n) (dot n) [(.x0,.ptr h),(.x1,.ptr f),(.x2,.ptr g)]
end CombDot

def main : IO Unit := do
 for n in [4,5,7] do
  let code := printer.function (CombDot.dot n)
  IO.FS.writeFile ("/tmp/comb-dot"++toString n++".body") (String.join (code.map (Rust.line printer.call)))
  IO.println s!"dot{n}: {code.length}"
