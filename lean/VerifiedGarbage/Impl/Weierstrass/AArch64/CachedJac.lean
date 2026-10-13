module

public import VerifiedGarbage.Impl.Weierstrass.CachedJac
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.CachedJac
open VG VG.AArch64 VG.Impl.Mont.AArch64
open VG.Impl.Weierstrass
open Jacobian

def cacheOps (K : WinCfg) : List FOp :=
  (List.range 8).flatMap fun i =>
    let p := tablePt K (i+1)
    [.mul (Weierstrass.CachedJac.tableZ2 i) p.z p.z,
     .mul (Weierstrass.CachedJac.tableZ3 i) (Weierstrass.CachedJac.tableZ2 i) p.z]

def cache (K : WinCfg) : Prog isa := fprogB K.M (cacheOps K)

/-- The arithmetic blocks can use their independently checked forwarding certificates. -/
structure Ops where
  head : Prog isa
  tail : Prog isa
  double : Prog isa

def add (K : WinCfg) (ops : Ops) : Prog isa :=
  .seq (.block (zeroMask 4 K.R.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt 4 K.D K.E)) <|
  .seq (.block (zeroMask 4 K.E.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt 4 K.D K.R)) <|
  .seq ops.head <|
  .seq (.block (zeroMask 4 K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask 4 K.S.t5)) <|
      .ite (.nonzero .x .x2) ops.double (.block (infinity K K.D)))
    ops.tail

def load : List Instr :=
  [.subImm .x .x17 .x2 1,.lsl .x .x17 .x17 6,
   .movz .x .x16 6000 0,.add .x .x16 .x0 .x16,.add .x .x16 .x16 .x17] ++
  (List.range 8).flatMap (fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (5400+8*i)])

def entry (K : WinCfg) : Prog isa :=
  .seq (.block (Naf.digitIndex ++ load ++ publicEntry K)) <|
  .seq (.block (Naf.signRead K)) <|
  .ite (.nonzero .x .x3) (.block (Mont.AArch64.sub K.M K.E.y K.zero K.E.y)) (.block [])

def digit (K : WinCfg) (ops : Ops) : Prog isa :=
  .seq (.block (Naf.digitRead K)) <|
  .ite (.nonzero .x .x2)
    (.seq (entry K) <| .seq (add K ops) (.block (copyPt 4 K.R K.D))) (.block [])

end VG.Impl.Weierstrass.AArch64.CachedJac
