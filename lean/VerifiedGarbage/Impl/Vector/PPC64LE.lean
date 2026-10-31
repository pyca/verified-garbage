module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # PPC64LE vector setup helpers -/

@[expose] public section
namespace VG.Impl.Vector.PPC64LE
open VG.PPC64LE

def const64 (d : Reg) (x : BitVec 64) : List Instr :=
  [.lis d (x.extractLsb' 48 16), .ori d d (x.extractLsb' 32 16), .lsl d d 32,
   .oris d d (x.extractLsb' 16 16), .ori d d (x.extractLsb' 0 16)]

/-- With `zero = 0`, form both halves without retaining either undefined
half produced by `mtvsrd`. The three vector registers must be distinct. -/
def pair (d tmp zero : VReg) (hi lo : Reg) : List Instr :=
  [.mtvsrd d hi, .mtvsrd tmp lo, .vop (.sldoi d zero d 8), .vop (.sldoi d d tmp 8)]


/-- A vector load followed by a byte permutation. `r0` must contain zero. -/
def loadPerm (d : VReg) (p : Reg) (control : VReg) : List Instr :=
  [.lxvd2x d p .r0, .vop (.perm d d d control)]

/-- A SHA sigma in the architectural high doubleword. SHA-256 uses its
low word (architectural word one); the undefined low doubleword is unused. -/
def shaSigma (wide upper one : Bool) (d n : Reg) : List Instr :=
  let v := if upper then (if one then VReg.v2 else VReg.v3) else (if one then VReg.v0 else VReg.v1)
  [.mtvsrd v n,
   .vop (if wide then .sha512 v v upper (if one then 8 else 0)
     else .sha256 v v upper (if one then 4 else 0)),
   .mfvsrd d v]

end VG.Impl.Vector.PPC64LE
