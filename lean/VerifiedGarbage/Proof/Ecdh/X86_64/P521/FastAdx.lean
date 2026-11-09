module

public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.MulF
import VerifiedGarbage.Proof.P521.Curve
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P521.MulF
meta import VerifiedGarbage.Proof.P521.Curve
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase

/-!
# ECDH over P-521 on x86-64 with BMI2 and ADX: the fast window method's facts

`fastCfg_p521x`: `FastCfg` for `p521x`'s window, its slots checked by
evaluation, and its doubling and addition keeping `rbx` and `rsi`
(`KeepReg.keeps`, on their code as literals).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P521

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64

materialize_code dblXI := (Impl.Weierstrass.X86_64.P521F.dbl (winQ p521x).S (winQ p521x).R).inline
materialize_code maddXI := (Impl.Weierstrass.X86_64.P521F.madd (winQ p521x).S (winQ p521x).R (winQ p521x).E
  (winQ p521x).D).inline

theorem p_succ : p521x.C.p + 1 = 512 * (2 ^ 64) ^ 8 := by
  have h : p521x.C.p =
      6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 :=
    Proof.P521.curve_p
  omega

theorem fastCfg_p521x (hc : BaseCfgOk p521x) : P521F.FastCfg (winQ p521x) p521x.C size where
  ctx := ⟨(winLayQ hc (by decide)).lay, rfl, rfl, p_succ,
    unitMod_pow_two hc.p_odd _, by decide⟩
  dnd := by decide
  dsl := by decide
  dW := by decide
  dlow := by decide
  dv0 := by decide
  dkb := by lit_decide
  dks := by lit_decide
  msl := by decide
  mkb := by lit_decide
  mks := by lit_decide

end VG.Proof.Ecdh.X86_64.P521
