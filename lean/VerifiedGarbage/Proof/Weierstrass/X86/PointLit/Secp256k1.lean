module

public import VerifiedGarbage.Impl.Weierstrass.X86.Point
meta import VerifiedGarbage.Impl.Weierstrass.X86.Point
public import VerifiedGarbage.Impl.Secp256k1.Point
meta import VerifiedGarbage.Impl.Secp256k1.Point
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# Literals of secp256k1's x86 point addition and doubling

The code of `vg_<curve>_point_add` and `vg_<curve>_point_double`, checked
once here, so that the taint analysis and `spSafe` read it rather than
building it again; its calls refer to the Montgomery functions' literals.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.PointLit.Secp256k1

open VG VG.Impl.Weierstrass.X86.Point

materialize_code add := fn (modP Impl.Secp256k1.point) false
materialize_code double := fn (modP Impl.Secp256k1.point) true

end VG.Proof.Weierstrass.X86.PointLit.Secp256k1
