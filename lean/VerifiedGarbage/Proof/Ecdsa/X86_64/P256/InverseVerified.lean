module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Ecdsa.X86_64.P256.InverseLit
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P256.InverseLit
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Framework.LitShare

/-!
# `vg_p256_inv_mod_p` and `_n` on x86-64: the configuration

`cfg adx`, the configuration of the functions (`adx` false) or of their
`_adx` forms, which the code supports (`cfg_ok`), and its curve (`cfg_C`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P256.Inverse

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64

/-- The configuration of the functions (`adx` false) or their `_adx` forms. -/
abbrev cfg (adx : Bool) : Cfg := if adx then p256x else p256

theorem cfg_ok (hI : InvSounds) (adx : Bool) : CfgOk (cfg adx) := by
  cases adx
  · exact p256_ok hI
  · exact p256x_ok hI

theorem cfg_C (adx : Bool) : (cfg adx).C = Spec.P256.curve := by cases adx <;> rfl

end VG.Proof.Ecdsa.X86_64.P256.Inverse
