module

public import VerifiedGarbage.Impl.Mont.X86.Power

/-! A reduced high-bit seed for a publicly full-width modulus. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86

/-- The high bit of an n-word integer, with every other bit cleared. -/
def highOne (n out : Nat) : Prog isa :=
  .seq (zerosW out (2*n)) (.block [.mov .eax (.imm 2147483648),
    .store (sc (out + 4*(2*n-1))) .eax])

/-- Double the high-bit seed a positive public number of times. Callers
establish that the initial seed is reduced for their public modulus. -/
def highPower (M : VG.Impl.Mont.Mod) (acc out bits : Nat) : Prog isa :=
  .seq (highOne M.n out) (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 bits))])
    (doubleLoop M acc out))

end VG.Impl.Mont.X86.Dynamic
