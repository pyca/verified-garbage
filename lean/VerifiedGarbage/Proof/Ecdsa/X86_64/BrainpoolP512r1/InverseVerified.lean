module

import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseLit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseLit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare

/-!
# `vg_brainpoolp512r1_inv_mod_p` and `_n` on x86-64: the configuration

`cfg`, the configuration of the functions, which the code supports
(`cfg_ok`), and its curve (`cfg_C`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP512r1.Inverse

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP512r1

/-- The configuration of the functions. -/
abbrev cfg : Cfg := brainpoolp512r1

theorem cfg_ok (hI : InvSounds) : BaseCfgOk cfg := brainpoolp512r1_ok hI

theorem cfg_C : cfg.C = Spec.BrainpoolP512r1.curve := rfl

end VG.Proof.Ecdsa.X86_64.BrainpoolP512r1.Inverse
