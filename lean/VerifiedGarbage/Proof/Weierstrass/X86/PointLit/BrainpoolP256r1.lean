module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Weierstrass.X86.Point
meta import VerifiedGarbage.Impl.Weierstrass.X86.Point
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Literals of brainpoolP256r1's x86 point addition and doubling

The code of `vg_<curve>_point_add` and `vg_<curve>_point_double`, checked
once here, so that the taint analysis and `spSafe` read it rather than
building it again; its calls refer to the Montgomery functions' literals.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.PointLit.BrainpoolP256r1

open VG VG.Impl.Weierstrass.X86.Point

materialize_code add := fn (modP Spec.Weierstrass.Point.brainpoolp256r1) false
materialize_code double := fn (modP Spec.Weierstrass.Point.brainpoolp256r1) true

end VG.Proof.Weierstrass.X86.PointLit.BrainpoolP256r1
