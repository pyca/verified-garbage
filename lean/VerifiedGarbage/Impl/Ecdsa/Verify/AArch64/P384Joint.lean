module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PubNaf
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.P384.EcdhAllocatedCode
public import VerifiedGarbage.Impl.P384.GTable9
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint

/-! # ECDSA verification over P-384 on AArch64: one loop for `[u]G + [v]Q`

The public width-five NAF of `v` (`PubNaf`) and the width-nine NAF of `u`, as sixteen-bit words
(`PubNafWide.prep9`), share their doublings (the register-allocated ones of ECDH's window); each
digit of `u` other than 0 adds `[m]G` by a mixed addition, from the static `VG_P384_GTAB` of
`[m]G` for `m = 1 … 256`, read directly at the digit. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.P384Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open Jacobian

/-- P-384 as verification has it: its table is `[m]G`, `m = 1 … 256`, a comb of one window of nine
bits, in the static `VG_P384_GTAB` (`combConsts`). -/
def p384v : Cfg :=
  { p384 with tbl := Impl.P384.p384G9, start := Impl.P384.p384G9Start, tsym := "VG_P384_GTAB" }

def K : WinCfg := Cfg.winCfg p384 PX PY
/-- The generator's 385 digits of width nine, as words, past the area of `v`'s and below `TMP`. -/
def KG : WinCfg := {K with bits := 3152}
def cfg : Joint.Cfg := ⟨K,KG.bits,p384.sl ONEP,p384v.tsym,9⟩

def prep9 : Prog isa := PubNafWide.prep9 KG (p384.sl U)

/-- The odd multiple `2 a - 1` of `G` is at `96 (2 a - 2)`. -/
def fixedAddress : List Instr :=
  [.subImm .x .x2 .x2 1,.movz .x .x3 192 0,.mul .x .x2 .x2 .x3,.adrSym .x16 p384v.tsym,
   .add .x .x16 .x16 .x2]
def fixedLoad : List Instr :=
  Joint.fixedIndex cfg ++ fixedAddress ++ Joint.loadWords K.E.x 12 ++ copy 6 K.E.z (p384.sl ONEP)
def fixedEntry : Prog isa := .seq (.block fixedLoad) (Joint.signEntry cfg)
def fixedDigit : Prog isa := .seq (.block (Joint.fixedRead cfg)) <|
 .ite (.nonzero .x .x2)
  (.seq fixedEntry <| .seq (jacMixedAdd K K.R K.E K.D) (.block (copyPt 6 K.R K.D))) (.block [])
def digits : Prog isa := .seq (PubNaf.digit K) fixedDigit
def double : Prog isa := .block Impl.P384.EcdhAllocatedCode.doubleRD
def step : Prog isa := .seq (.block [decCounter]) <| .seq double digits
def window : Prog isa :=
 .seq (PubNaf.table K) <| .seq (PubNaf.cache K) <|
 .seq (.block (infinity K K.D ++ [.movz .x .x19 384 0])) <|
 .seq digits <| .seq (.loop step (.nonzero .x .x19)) (PubNaf.finish K)
def points : Prog isa := .seq prep9 <| .seq (PubNaf.prep K (p384.sl V)) window

def verify : Prog isa :=
 let c := p384
 .seq (.block (Cfg.args c)) <| .seq (VG.Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
 .seq (.block (Cfg.loadS c)) <| .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer c)) <|
 .seq (VG.Impl.Ecdh.AArch64.Cfg.validate c) <|
 .seq (Cfg.scalars c) <| .seq c.nPow <| .seq (Cfg.uv c) <| .seq points (Cfg.tail c)
end VG.Impl.Ecdsa.Verify.AArch64.P384Joint
