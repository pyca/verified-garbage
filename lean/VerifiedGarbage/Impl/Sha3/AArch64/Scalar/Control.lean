import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

namespace VG.Impl.Sha3.AArch64.Scalar.Control
open VG VG.AArch64

/-- Public FIPS202 constants, with zero high halfwords omitted. -/
def constant (v : BitVec 64) : List Instr :=
  [.movz .x .x26 (v.extractLsb' 0 16) 0] ++
  (if v.extractLsb' 16 16 = 0 then [] else [.movk .x .x26 (v.extractLsb' 16 16) 1]) ++
  (if v.extractLsb' 32 16 = 0 then [] else [.movk .x .x26 (v.extractLsb' 32 16) 2]) ++
  (if v.extractLsb' 48 16 = 0 then [] else [.movk .x .x26 (v.extractLsb' 48 16) 3])

end VG.Impl.Sha3.AArch64.Scalar.Control
