module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.InverseLit
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.InverseLit
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare

/-!
# `vg_secp256k1_inv_mod_p` and `_n` on x86-64: the configuration

`cfg`, the configuration of the functions (which have no `_adx` forms,
whatever the flag), which the code supports (`cfg_ok`), and its curve
(`cfg_C`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.Secp256k1.Inverse

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64

/-- The configuration of the functions, which have no `_adx` forms. -/
abbrev cfg (_ : Bool) : Cfg := secp256k1

theorem cfg_ok (hI : InvSounds) (adx : Bool) : BaseCfgOk (cfg adx) := secp256k1_ok hI

theorem cfg_C (adx : Bool) : (cfg adx).C = Spec.Secp256k1.curve := rfl

end VG.Proof.Ecdsa.X86_64.Secp256k1.Inverse
