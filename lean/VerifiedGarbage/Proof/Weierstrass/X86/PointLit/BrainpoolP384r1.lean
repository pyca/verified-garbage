module

public import VerifiedGarbage.Impl.Weierstrass.X86.Point
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP384r1
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Weierstrass.X86.Point
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Literals of brainpoolP384r1's x86 point addition and doubling

The code of `vg_<curve>_point_add` and `vg_<curve>_point_double`, checked
once here, so that the taint analysis and `spSafe` read it rather than
building it again; its calls refer to the Montgomery functions' literals.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.PointLit.BrainpoolP384r1

open VG VG.Impl.Weierstrass.X86.Point

materialize_code add := fn (modP Impl.Weierstrass.Point.brainpoolp384r1) false
materialize_code double := fn (modP Impl.Weierstrass.Point.brainpoolp384r1) true

end VG.Proof.Weierstrass.X86.PointLit.BrainpoolP384r1
