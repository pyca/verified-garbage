module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PackedNaf
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.P521Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open Jacobian

def K : WinCfg := Cfg.packedNafQ p521
def KG : WinCfg := {K with bits := slot 9 45}
def prep7 : Prog isa := PubNafWide.prep KG (p521.sl U) 7

def fixedLoad : List Instr :=
 Naf.digitIndex ++ [.lsl .x .x2 .x2 1,.subImm .x .x2 .x2 2,.movz .x .x3 144 0,
 .mul .x .x2 .x2 .x3,.adrSym .x16 "VG_P521_COMB",.add .x .x16 .x16 .x2] ++
 (List.range 18).flatMap (fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (K.E.x+8*i)]) ++
 copy 9 K.E.z (p521.sl ONEP)
def fixedEntry : Prog isa := .seq (.block fixedLoad) <|
 .seq (.block (Naf.signRead KG)) <|
 .ite (.nonzero .x .x3) (.block (VG.Impl.Mont.AArch64.sub K.M K.E.y K.zero K.E.y)) (.block [])
def fixedDigit : Prog isa := .seq (.block (Naf.digitRead KG)) <|
 .ite (.nonzero .x .x2)
  (.seq fixedEntry <| .seq (jacMixedAdd K K.R K.E K.D) (.block (copyPt 9 K.R K.D))) (.block [])
def digits : Prog isa := .seq (PubNaf.digit K) fixedDigit
def step : Prog isa := .seq (.block [decCounter]) <|
 .seq (fprogB K.M (dblJ K.S K.R K.D)) digits
def window : Prog isa :=
 .seq (PubNaf.table K) <| .seq (PubNaf.cache K) <|
 .seq (.block (infinity K K.D ++ [.movz .x .x19 576 0])) <|
 .seq digits <| .seq (.loop step (.nonzero .x .x19)) (PubNaf.finish K)
def points : Prog isa := .seq prep7 <| .seq (PubNaf.prep K (p521.sl V)) window

def verify : Prog isa :=
 let c := p521
 .seq (.block (Cfg.args c)) <| .seq (VG.Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
 .seq (.block (Cfg.loadS c)) <| .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer c)) <|
 .seq (VG.Impl.Ecdh.AArch64.Cfg.validate c) <|
 .seq (Cfg.scalars c) <| .seq c.nPow <| .seq (Cfg.uv c) <| .seq points (Cfg.tail c)
end VG.Impl.Ecdsa.Verify.AArch64.P521Joint
