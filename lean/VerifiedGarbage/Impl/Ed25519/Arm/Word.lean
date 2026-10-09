import VerifiedGarbage.Impl.X25519.Arm

/-! Ed25519 field arithmetic on ARMv7 uses sixteen 16-bit limbs and only
32-bit `mul`. The multiplication accumulator follows the 22 field slots, and
the registers that the functions of point arithmetic save follow it; packed
point tables let the complete implementation fit the reviewed 8 KiB scratch
contract. No long-multiply instructions are used. -/
namespace VG.Impl.Ed25519.Arm
open VG VG.Arm

abbrev carryStep := Impl.X25519.Arm.carryStep
abbrev pass := Impl.X25519.Arm.pass
abbrev ldSrc := Impl.X25519.Arm.ldSrc
abbrev tail := Impl.X25519.Arm.tail
abbrev prologue := Impl.X25519.Arm.prologue
abbrev addSrc := Impl.X25519.Arm.addSrc
abbrev add := Impl.X25519.Arm.add
abbrev subHi := Impl.X25519.Arm.subHi
abbrev subLo := Impl.X25519.Arm.subLo
abbrev subSrc := Impl.X25519.Arm.subSrc
abbrev sub := Impl.X25519.Arm.sub
abbrev storeN := Impl.X25519.Arm.storeN
abbrev cswapStep := Impl.X25519.Arm.cswapStep
abbrev cswap := Impl.X25519.Arm.cswap

def ACC : Nat := 1472

abbrev zeroAcc := Impl.X25519.Arm.zeroAcc ACC
abbrev row := Impl.X25519.Arm.row ACC

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`), with the product in `ACC`. -/
abbrev mul (o a b : Nat) : Prog isa := Impl.X25519.Arm.mulAt ACC o a b

/-- Where the functions of point arithmetic save the registers they change:
the 32 bytes after `ACC`'s 128. -/
def SAVE : Nat := ACC + 128

/-- Where the functions that call the functions of point arithmetic save
`lr`, which a call overwrites: the word after verification's headers. -/
def LRS : Nat := 8172

end VG.Impl.Ed25519.Arm
