module
public import VerifiedGarbage.Impl.Mont.X86.Words


/-! # Runtime-modulus exponentiation building blocks on x86 -/

@[expose] public section

namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- Initialize an n-word integer to one. -/
def one (n out : Nat) : Prog isa :=
  .seq (zerosW out (2 * n)) (.block [.mov .eax (.imm 1), .store (sc out) .eax])

/-- Double the reduced integer at `out` and decrement the public count. -/
def doubleStep (M : Mod) (acc out : Nat) : Prog isa :=
  .seq (addW M acc out out out) (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- A positive number of modular doublings, initially in `esi`. -/
def doubleLoop (M : Mod) (acc out : Nat) : Prog isa :=
  .loop (doubleStep M acc out) .ne

/-- Compute `2^bits mod m`, for public positive `bits` and `m > 1`. -/
def powerTwo (M : Mod) (acc out bits : Nat) : Prog isa :=
  .seq (one M.n out) (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 bits))]) (doubleLoop M acc out))

end VG.Impl.Mont.X86.Dynamic
