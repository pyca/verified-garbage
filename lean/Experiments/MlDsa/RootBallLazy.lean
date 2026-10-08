import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace RootBallLazy
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
def zeroWide : Prog isa := .block <| [.vop (.movi0 .v0)] ++
 (List.range 64).map (fun i => .strq .v0 .x26 (16*i))
def earlyBody : Prog isa := .seq bTry <| .seq
 (.block [.addImm .x .x2 .x2 1,.subImm .x .x5 .x5 1])
 (.ite (.zero .x .x11) (.block [.movz .x .x5 0 0]) (.block []))
def loop : Prog isa := .ite (.zero .x .x11) (.block []) (.loop earlyBody (.nonzero .x .x5))
def first : Prog isa := .seq (.block (bSetup ++ [.movz .x .x5 128 0])) loop
def second : Prog isa := .seq
 (.block [.str .x .x9 .x25 1800,.str .x .x10 .x25 1808,.str .x .x11 .x25 1816,
 mov .x2 .x0,mov .x0 .x25,.movz .x .x1 136 0,.addImm .x .x3 .x25 840,
 .movz .x .x4 136 0,.addImm .x .x5 .x25 200]) <|
 .seq (.call "vg_keccak_squeeze_scratch_sha3"
 (Impl.Sha3.AArch64.Stream.squeezeWith VG.Variants.Keccak.AArch64.Sha3.variant.callee)) <|
 .seq (.block ([.ldr .x .x9 .x25 1800,.ldr .x .x10 .x25 1808,.ldr .x .x11 .x25 1816,
 .addImm .x .x2 .x25 840,.movz .x .x5 136 0] ++ movQ .x12 ++
 [.subImm .x .x12 .x12 2,.movz .x .x15 1 0])) loop
def code : Prog isa :=
 .seq (.block (pro .x4 .x3 (.addImm .w .x27 .x2 0) (mov .x4 .x1))) <|
 .seq (spongeWith VG.Variants.Keccak.AArch64.Sha3.variant.callee 136 136) <|
 .seq zeroWide <| .seq first <|
 .seq (.ite (.zero .x .x11) (.block []) second)
 (.block (.lsr .x .x0 .x10 8 :: epi))
end RootBallLazy
def main : IO Unit := do
 IO.FS.writeFile "/tmp/root-ball-lazy.body" (String.join ((printer.function RootBallLazy.code).map (Rust.line printer.call)))
