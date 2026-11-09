module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Mont
public import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Calls of the Montgomery functions, and field programs, on PPC64LE

`callOp f body o a b`: `[o] = f([a], [b])` by a call of the function `f`
(whose code is `body`, a function of `Impl/Weierstrass/PPC64LE/Mont.lean`)
on the working space in `r3`, with the offsets loaded into `r4`–`r6` (`li`:
every offset is below `2¹⁵`). The functions write only `r0` and `r4`–`r12`
and leave `r3`, so a caller keeps its own values in `r14`–`r31` (the
callee-saved registers, which it saves itself) and the working space in
`r3`; a call changes the link register, which a caller saves once.

The multiplication saves `r15`–`r(15 + n)` (for at most four words,
`r15`–`r(15 + 2n)`), all of them in `r15`–`r24`, in its own working space
and restores them (`Impl/Mont/PPC64LE.lean`, `rmul` and `rmul4`). Their values are the
caller's again, but loaded from memory, which the constant-time analysis
(`Proof/Framework/PPC64LE/Taint.lean`) takes as secret: a value that must be
public after a call of the multiplication (a pointer, a counter) is kept in
`r14` or `r25`–`r31`.

`fprog S ops`: the field operations `ops` on slots of the working space, one
after the other, by calls of the functions of the modulus `S`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

open VG.PPC64LE VG.Impl.Weierstrass

/-- `[o] = f([a], [b])` by a call of `f`, whose code is `body`, on the
working space in `r3`. -/
def callOp (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.li .r4 o, .li .r5 a, .li .r6 b]) (.call f body)

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
def mulCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "mul") (Mont.mulFn S.k S.m) o a b

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
def addCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "add") (Mont.addFn S.k S.m) o a b

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
def subCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "sub") (Mont.subFn S.k S.m) o a b

/-- The code of a field operation modulo `S`: a call of its function. -/
def opCode (S : Impl.Weierstrass.Mont.Modulus) : FOp → Prog isa
  | .mul o a b => mulCall S o a b
  | .add o a b => addCall S o a b
  | .sub o a b => subCall S o a b

/-- Programs one after the other. -/
def progs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (progs ps)

/-- A straight-line sequence of field operations. -/
def fprog (S : Impl.Weierstrass.Mont.Modulus) (ops : List FOp) : Prog isa := progs (ops.map (opCode S))

end VG.Impl.Weierstrass.PPC64LE
