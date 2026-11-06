module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! Fixed-base public comb with a Jacobian accumulator. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The result of one mixed Jacobian addition and accumulator copy. -/
structure JacCombSumPost (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat)
    (P Q : Point C) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base (combW K.toComb) s.mem s'.mem
  lt : ∀ x ∈ [K.A.x,K.A.y,K.A.z], wordsVal s'.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y)
    (tmv C K.M.n base s' K.A.z) (Spec.Weierstrass.add P Q)

/-- The field-program proof is independent of the scalar recoding and tables. -/
def JacCombSumCorrect (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat) : Prop :=
  ∀ (s : State) (P Q : Point C), Scr s base size → ModOkA K.M size C.p s.mem base →
    (∀ x ∈ rcbR K.S K.A K.E, wordsVal s.mem base x K.M.n < C.p) →
    tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b →
    onCurve C P = true → onCurve C Q = true →
    InvJ C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z) P →
    Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) Q →
    tmv C K.M.n base s K.E.z = 1 →
    WP isa (Jacobian.jacCombSum K) s (JacCombSumPost K C base size P Q s)

end VG.Proof.Weierstrass.AArch64
