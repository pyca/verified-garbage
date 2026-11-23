module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac

/-! Public mixed Jacobian addition with register forwarding between field operations. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Jacobian
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- `o = p + q` for an affine `q`, the double of `p` by `dbl` if they are
equal (`dblJMul` for `a = -3`): `p`'s `X`, `Y` and `Z` copied to `t2`, `t4`
and `o.z` (`U1`, `S1` and `Z`), the header, then `fin`, the end of the
additions (`CachedJac.addEnd`, or a call of it). -/
def jacMixedForward (K : WinCfg) (p q o : Pt) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul)
    (fin : Prog isa := CachedJac.addEnd K p q o dbl) : Prog isa :=
  .seq (.block (zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y ++ copy K.M.n o.z p.z)) <|
  .seq (ForwardField.programB K.M (jacMixedHead K.S p q)) fin


end VG.Impl.Weierstrass.X86_64.Jacobian
