module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! The field operations of P-256's code without BMI2 and ADX, modulo `p` and
`n`, as templates (`materialize_template`): every product, sum and difference
of that code reads its template rather than being built again. Only the
literals of that code import it: the code with BMI2 and ADX has its own
products, and looking for these templates in it costs more than it saves. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P256Templates
open VG VG.Impl.Ecdsa.X86_64 VG.Impl.Mont.X86_64

materialize_template mulPT := mulG p256.MP'
materialize_template addPT := addR p256.MP'
materialize_template subPT := subR p256.MP'
materialize_template mulNT := mulG p256.MN'
materialize_template addNT := addR p256.MN'
materialize_template subNT := subR p256.MN'

end VG.Proof.Weierstrass.X86_64.P256Templates
