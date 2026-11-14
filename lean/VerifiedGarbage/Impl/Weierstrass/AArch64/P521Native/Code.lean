module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Representation
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64

/-! Native ordinary-field P-521 ECDH: existing validation/inversion, a sixteen-entry
affine table, signed five-bit windows, and fused point operations. This definition
is not registered for emission until its complete public contract is proved. -/

@[expose] public section
namespace VG.Impl.Weierstrass.AArch64.P521Native
open VG VG.AArch64
open VG.Impl.Mont.AArch64.P521Field

abbrev config := VG.Impl.Ecdsa.AArch64.p521

def sequence (cs : List (Prog isa)) : Prog isa := cs.foldr .seq (.block [])

def callNormalMul : Prog isa := .call "vg_p521_normal_mul" mulFn
def callNormalSqr : Prog isa := .call "vg_p521_normal_sqr" square
def callNormalDouble : Prog isa := .call "vg_p521_normal_double" doubleFn
def callNormalMadd : Prog isa := .call "vg_p521_normal_madd" mixedFn
def callInvModP : Prog isa := .call "vg_p521_inv_mod_p" (config.invFn config.pPowI)
def callCheckPoint : Prog isa := .call "vg_p521_check_point" (VG.Impl.Ecdh.AArch64.Cfg.checkFn config)

def loop20 : Prog isa := .loop (sequence [
  .block outerBlock002
]) (.nonzero .x .x19)

def loop21 : Prog isa := .loop (sequence [
  .block outerBlock006
]) (.nonzero .x .x19)

def loop22 : Prog isa := .loop (sequence [
  .block outerBlock016,
  callNormalSqr,
  .block outerBlock017,
  callNormalMul,
  .block outerBlock018,
  callNormalMul,
  .block outerBlock019,
  callNormalMul,
  .block outerBlock020,
  callNormalSqr,
  .block outerBlock021,
  callNormalMul,
  .block outerBlock022,
  callNormalMul,
  .block outerBlock023,
  callNormalSqr,
  .block outerBlock024,
  callNormalMul,
  .block outerBlock025,
  callNormalMul,
  .block outerBlock026,
  callNormalMul,
  .block outerBlock027
]) (.nonzero .x .x19)

def loop24 : Prog isa := .loop (sequence [
  .block outerBlock138,
  callNormalDouble,
  .block outerBlock139,
  callNormalDouble,
  .block outerBlock140
]) (.nonzero .x .x2)

def loop23 : Prog isa := .loop (sequence [
  .block outerBlock137,
  loop24,
  .block outerBlock141,
  callNormalDouble,
  .block outerBlock142,
  callNormalMadd,
  .block outerBlock143
]) (.nonzero .x .x4)

def loop25 : Prog isa := .loop (sequence [
  .block outerBlock145,
  callNormalDouble,
  .block outerBlock146,
  callNormalDouble,
  .block outerBlock147
]) (.nonzero .x .x2)

def validateAndPrepare : Prog isa := sequence [
  .block outerBlock001,
  loop20,
  .block outerBlock003,
  callCheckPoint,
  .block outerBlock004,
  .block (representationMemoryCode representationFromCode 2800),
  .block (representationMemoryCode representationFromCode 3160),
  .block (representationMemoryCode representationFromCode 424),
  .block (representationMemoryCode representationFromCode 496),
  .block (representationMemoryCode representationFromCode 568),
  .block outerBlock005
]

def recodeScalar : Prog isa := sequence [
  loop21
]

def buildTable : Prog isa := sequence [
  .block outerBlock007,
  callNormalSqr,
  .block outerBlock008,
  callNormalSqr,
  .block outerBlock009,
  callNormalMul,
  .block outerBlock010,
  callNormalSqr,
  .block outerBlock011,
  callNormalMul,
  .block outerBlock012,
  callNormalSqr,
  .block outerBlock013,
  callNormalSqr,
  .block outerBlock014,
  callNormalMul,
  .block outerBlock015,
  loop22
]

def normalizeCodePrefix : Prog isa := sequence [
  .block outerBlock028,callNormalMul,
  .block outerBlock029,callNormalMul,
  .block outerBlock030,callNormalMul,
  .block outerBlock031,callNormalMul,
  .block outerBlock032,callNormalMul,
  .block outerBlock033,callNormalMul,
  .block outerBlock034,callNormalMul,
  .block outerBlock035,callNormalMul,
  .block outerBlock036,callNormalMul,
  .block outerBlock037,callNormalMul,
  .block outerBlock038,callNormalMul,
  .block outerBlock039,callNormalMul,
  .block outerBlock040,callNormalMul,
  .block outerBlock041,callNormalMul,
  .block outerBlock042,callNormalMul,
  .block outerBlock043]

def normalizeCodeInverse : Prog isa := sequence [
  .block (representationMemoryCode representationToCode 1216),
  .block outerBlock044,callInvModP,.block outerBlock045,
  .block (representationMemoryCode representationFromCode 2152)]

def normalizeCodeBack0 : Prog isa := sequence [
  .block outerBlock046,callNormalMul,
  .block outerBlock047,callNormalMul,
  .block outerBlock048,callNormalSqr,
  .block outerBlock049,callNormalMul,
  .block outerBlock050,callNormalMul,
  .block outerBlock051,callNormalMul,
  .block outerBlock052,callNormalMul,
  .block outerBlock053,callNormalMul,
  .block outerBlock054,callNormalSqr,
  .block outerBlock055,callNormalMul,
  .block outerBlock056,callNormalMul,
  .block outerBlock057,callNormalMul,
  .block outerBlock058,callNormalMul,
  .block outerBlock059,callNormalMul,
  .block outerBlock060,callNormalSqr,
  .block outerBlock061,callNormalMul,
  .block outerBlock062,callNormalMul,
  .block outerBlock063,callNormalMul,
  .block outerBlock064,callNormalMul,
  .block outerBlock065,callNormalMul,
  .block outerBlock066,callNormalSqr,
  .block outerBlock067,callNormalMul,
  .block outerBlock068,callNormalMul,
  .block outerBlock069,callNormalMul,
  .block outerBlock070,callNormalMul,
  .block outerBlock071,callNormalMul,
  .block outerBlock072,callNormalSqr,
  .block outerBlock073,callNormalMul,
  .block outerBlock074,callNormalMul,
  .block outerBlock075,callNormalMul,
  .block (outerBlock076.take 19)]

def normalizeCodeBack1 : Prog isa := sequence [
  .block (outerBlock076.drop 19),callNormalMul,
  .block outerBlock077,callNormalMul,
  .block outerBlock078,callNormalSqr,
  .block outerBlock079,callNormalMul,
  .block outerBlock080,callNormalMul,
  .block outerBlock081,callNormalMul,
  .block outerBlock082,callNormalMul,
  .block outerBlock083,callNormalMul,
  .block outerBlock084,callNormalSqr,
  .block outerBlock085,callNormalMul,
  .block outerBlock086,callNormalMul,
  .block outerBlock087,callNormalMul,
  .block outerBlock088,callNormalMul,
  .block outerBlock089,callNormalMul,
  .block outerBlock090,callNormalSqr,
  .block outerBlock091,callNormalMul,
  .block outerBlock092,callNormalMul,
  .block outerBlock093,callNormalMul,
  .block outerBlock094,callNormalMul,
  .block outerBlock095,callNormalMul,
  .block outerBlock096,callNormalSqr,
  .block outerBlock097,callNormalMul,
  .block outerBlock098,callNormalMul,
  .block outerBlock099,callNormalMul,
  .block outerBlock100,callNormalMul,
  .block outerBlock101,callNormalMul,
  .block outerBlock102,callNormalSqr,
  .block outerBlock103,callNormalMul,
  .block outerBlock104,callNormalMul,
  .block outerBlock105,callNormalMul,
  .block (outerBlock106.take 19)]

def normalizeCodeBack2 : Prog isa := sequence [
  .block (outerBlock106.drop 19),callNormalMul,
  .block outerBlock107,callNormalMul,
  .block outerBlock108,callNormalSqr,
  .block outerBlock109,callNormalMul,
  .block outerBlock110,callNormalMul,
  .block outerBlock111,callNormalMul,
  .block outerBlock112,callNormalMul,
  .block outerBlock113,callNormalMul,
  .block outerBlock114,callNormalSqr,
  .block outerBlock115,callNormalMul,
  .block outerBlock116,callNormalMul,
  .block outerBlock117,callNormalMul,
  .block outerBlock118,callNormalMul,
  .block outerBlock119,callNormalMul,
  .block outerBlock120,callNormalSqr,
  .block outerBlock121,callNormalMul,
  .block outerBlock122,callNormalMul,
  .block outerBlock123,callNormalMul,
  .block outerBlock124,callNormalMul,
  .block outerBlock125,callNormalMul,
  .block outerBlock126,callNormalSqr,
  .block outerBlock127,callNormalMul,
  .block outerBlock128,callNormalMul,
  .block outerBlock129,callNormalMul,
  .block outerBlock130,callNormalMul,
  .block outerBlock131,callNormalMul,
  .block outerBlock132,callNormalSqr,
  .block outerBlock133,callNormalMul,
  .block outerBlock134,callNormalMul,
  .block outerBlock135,callNormalMul,
  .block (outerBlock136.take 19)]

def normalizeAndInit : Prog isa :=
  .seq normalizeCodePrefix <| .seq normalizeCodeInverse <|
    .seq (.seq normalizeCodeBack0 (.seq normalizeCodeBack1 normalizeCodeBack2))
      (.block (outerBlock136.drop 19))

def windowLoop : Prog isa := sequence [
  loop23
]

def finishAndWrite : Prog isa := sequence [
  .block outerBlock144,
  loop25,
  .block outerBlock148,
  callNormalDouble,
  .block outerBlock149,
  callNormalMul,
  .block outerBlock150,
  callNormalSqr,
  .block outerBlock151,
  callNormalMul,
  .block outerBlock152,
  callNormalMul,
  .block outerBlock153,
  callNormalMul,
  .block outerBlock154,
  callNormalMul,
  .block outerBlock155,
  callNormalMul,
  .block outerBlock156,
  callNormalMul,
  .block outerBlock157,
  callNormalMul,
  .block outerBlock158,
  callNormalMul,
  .block outerBlock159,
  callNormalMul,
  .block outerBlock160,
  callNormalMul,
  .block outerBlock161,
  callNormalMul,
  .block outerBlock162,
  callNormalMul,
  .block outerBlock163,
  callNormalMul,
  .block outerBlock164,
  callNormalMul,
  .block outerBlock165,
  callNormalMul,
  .block outerBlock166,
  .block (representationMemoryCode representationToCode 1216),
  .block outerBlock167,
  callInvModP,
  .block outerBlock168,
  .block (representationMemoryCode representationFromCode 2152),
  .block outerBlock169,
  callNormalMul,
  .block outerBlock170,
  callNormalMul,
  .block outerBlock171
]

def body : Prog isa := sequence [validateAndPrepare, recodeScalar, buildTable, normalizeAndInit, windowLoop, finishAndWrite]

def exchange : Prog isa := sequence [
  .block outerBlock000,
  .frame (.alloc 3456) body (.free 3456),
  .block outerBlock172
]

end VG.Impl.Weierstrass.AArch64.P521Native
