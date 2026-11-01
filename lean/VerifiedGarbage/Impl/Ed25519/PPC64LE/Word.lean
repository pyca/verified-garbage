module

public import VerifiedGarbage.Impl.X25519.PPC64LE

/-!
# Ed25519 on PPC64LE: X25519's field code, with its product at `ACC`

The field arithmetic of X25519's PPC64LE code (`Impl/X25519/PPC64LE.lean`:
eight 32-bit limbs, one to a word, with the working space in `r6`), with the
product's limbs at `ACC`, inside the own working space of the functions on
points (`Proof/Ed25519/Point32Contract.lean`, bytes 864 to 1023).
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE

open VG VG.PPC64LE

abbrev pass := Impl.X25519.PPC64LE.pass
abbrev ldSrc := Impl.X25519.PPC64LE.ldSrc
abbrev add := Impl.X25519.PPC64LE.add
abbrev sub := Impl.X25519.PPC64LE.sub
abbrev storeN := Impl.X25519.PPC64LE.storeN
abbrev cswap := Impl.X25519.PPC64LE.cswap

def ACC : Nat := 864

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`), with the product at `ACC`. -/
abbrev mul (o a b : Nat) : Prog isa := Impl.X25519.PPC64LE.mulAt ACC o a b

end VG.Impl.Ed25519.PPC64LE
