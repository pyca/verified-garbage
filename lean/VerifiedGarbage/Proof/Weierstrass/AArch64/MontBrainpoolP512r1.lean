module

import VerifiedGarbage.Proof.Weierstrass.AArch64.MontVerified
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontContract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Shared BrainpoolP512r1 Montgomery multiplication on AArch64 -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.Mont
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont Impl.Weierstrass.Mont

theorem brainpoolp512r1p_ok : ModOk brainpoolp512r1p.k brainpoolp512r1p.m := .inr {
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  g := by decide +kernel
  novec := by decide +kernel }

theorem brainpoolp512r1p_mul_ct : ConstantTime isa (mulA brainpoolp512r1p).pre (mulA brainpoolp512r1p).pub (mulFn brainpoolp512r1p.k brainpoolp512r1p.m) := by
  exact ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1p_mul_verified : Verified AArch64.target (mulFn brainpoolp512r1p.k brainpoolp512r1p.m) (brainpoolp512r1p.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a brainpoolp512r1p_ok) brainpoolp512r1p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat brainpoolp512r1p (by decide) (m_pos_of_inv brainpoolp512r1p_ok.inv)⟩ }

theorem brainpoolp512r1n_ok : ModOk brainpoolp512r1n.k brainpoolp512r1n.m := .inr {
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  g := by decide +kernel
  novec := by decide +kernel }

theorem brainpoolp512r1n_mul_ct : ConstantTime isa (mulA brainpoolp512r1n).pre (mulA brainpoolp512r1n).pub (mulFn brainpoolp512r1n.k brainpoolp512r1n.m) := by
  exact ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem brainpoolp512r1n_mul_verified : Verified AArch64.target (mulFn brainpoolp512r1n.k brainpoolp512r1n.m) (brainpoolp512r1n.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a brainpoolp512r1n_ok) brainpoolp512r1n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat brainpoolp512r1n (by decide) (m_pos_of_inv brainpoolp512r1n_ok.inv)⟩ }

end VG.Proof.Weierstrass.AArch64.Mont
