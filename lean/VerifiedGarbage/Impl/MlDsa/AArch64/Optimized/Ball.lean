module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball

/-! Demand-driven SampleInBall: parse the first SHAKE block, stop once all
coefficients are assigned, and squeeze a second block only when needed.
The total byte budget remains 272 and only the public challenge affects
branches and addresses. Scratch offsets 1800..1824 save parser registers. -/

@[expose] public section

open VG VG.AArch64
namespace VG.Impl.MlDsa.AArch64.Optimized.Ball
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
def zeroWide : Prog isa := .block <| ([.vop (.movi0 .v0)] : List Instr) ++
 (List.range 64).map (fun i => .strq .v0 .x26 (16*i))
def earlyBody : Prog isa := .seq bTry <| .seq
 (.block [.addImm .x .x2 .x2 1,.subImm .x .x5 .x5 1])
 (.ite (.zero .x .x11) (.block [.movz .x .x5 0 0]) (.block []))
def loop : Prog isa := .ite (.zero .x .x11) (.block []) (.loop earlyBody (.nonzero .x .x5))
def first : Prog isa := .seq (.block (bSetup ++ ([.movz .x .x5 128 0] : List Instr))) loop
def second (c : Impl.Sha3.AArch64.Callee) : Prog isa := .seq
 (.block [.str .x .x9 .x25 1800,.str .x .x10 .x25 1808,.str .x .x11 .x25 1816,
 mov .x2 .x0,mov .x0 .x25,.movz .x .x1 136 0,.addImm .x .x3 .x25 840,
 .movz .x .x4 136 0,.addImm .x .x5 .x25 200]) <|
 .seq (.call ("vg_keccak_squeeze_scratch" ++ c.suffix)
 (Impl.Sha3.AArch64.Stream.squeezeWith c)) <|
 .seq (.block (([.ldr .x .x9 .x25 1800,.ldr .x .x10 .x25 1808,.ldr .x .x11 .x25 1816,
 .addImm .x .x2 .x25 840,.movz .x .x5 136 0] : List Instr) ++ movQ .x12 ++
 ([.subImm .x .x12 .x12 2,.movz .x .x15 1 0] : List Instr))) loop
def codeWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
 .seq (.block (pro .x4 .x3 (.addImm .w .x27 .x2 0) (mov .x4 .x1))) <|
 .seq (spongeWith c 136 136) <|
 .seq zeroWide <| .seq first <|
 .seq (.ite (.zero .x .x11) (.block []) (second c))
 (.block (.lsr .x .x0 .x10 8 :: epi))
end VG.Impl.MlDsa.AArch64.Optimized.Ball
