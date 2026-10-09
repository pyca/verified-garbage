import VerifiedGarbage.Impl.X25519.Arm.Field16

/-! Ed25519 field arithmetic on ARMv7 uses sixteen 16-bit limbs and only
32-bit `mul`. A product is a call of `vg_gf25519_r16_mul`, whose own working
space (its accumulator and the registers it saves) follows the 22 field
slots; packed point tables let the complete implementation fit the reviewed
8 KiB scratch contract. No long-multiply instructions are used. -/
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

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`), by a call of `vg_gf25519_r16_mul`,
whose own working space is `ACC` and the 32 bytes after it. -/
abbrev mul (o a b : Nat) : Prog isa := Impl.X25519.Arm.Field16.mulCall o a b

/-- Where the functions that call `vg_gf25519_r16_mul` save `lr`, which a call
overwrites: the word after verification's headers. -/
def LRS : Nat := 8172

end VG.Impl.Ed25519.Arm
