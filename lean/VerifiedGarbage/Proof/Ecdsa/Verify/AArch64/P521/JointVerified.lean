module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Hash
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Contract

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521

theorem verify_ct (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pre
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pub verifyP521 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact Joint.verify_public_ct (p521_ok hI) hL hO (by decide) hT _ _ _ _ _ _
    (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (jacPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    Verified AArch64.target verifyP521
      (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hO hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hO hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩


/-- `vg_ecdsa_p521_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    Verified AArch64.target
      (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true verifyP521)
      (Spec.Ecdsa.P521.inst.verifyHashContract (AArch64.abi.withConsts p521.combConsts) 80) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.p521_len (by decide) (verify_verified hL hO hI hT)
    (by taint_decide) (Hash.hashSat_cons (by decide) sat_spec (by decide) fun r hr => by
      simp only [satState, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.Verify.AArch64.P521
