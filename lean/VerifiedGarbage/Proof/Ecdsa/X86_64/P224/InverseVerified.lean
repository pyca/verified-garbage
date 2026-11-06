module

import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
public import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb

/-!
# `vg_p224_inv_mod_p` and `_n` on x86-64: the configuration

`cfg`, the configuration of the functions (which have no `_adx` forms,
whatever the flag), which the code supports (`cfg_ok`), and its curve
(`cfg_C`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P224.Inverse

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64

/-- The configuration of the functions, which have no `_adx` forms. -/
abbrev cfg (_ : Bool) : Cfg := p224

theorem cfg_ok (hI : InvSounds) (adx : Bool) : BaseCfgOk (cfg adx) := p224_ok hI |>.toBaseCfgOk

theorem cfg_C (adx : Bool) : (cfg adx).C = Spec.P224.curve := rfl

end VG.Proof.Ecdsa.X86_64.P224.Inverse
