module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1
meta import VerifiedGarbage.Proof.BrainpoolP512r1.Point
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! # brainpoolP512r1's configuration for public keys and ECDH on Arm -/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp512r1_nBits : 64 * brainpoolp512r1.n ≤ Spec.Ecdsa.nBits brainpoolp512r1.C := by
  show 512 ≤ Spec.BrainpoolP512r1.curve.n.log2 + 1
  have : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega_using [this]

/-- No bit of a hash of `64` bytes is dropped. -/
theorem brainpoolp512r1_sh : brainpoolp512r1.sh = 0 := by
  have h : 64 * 8 ≤ Spec.Ecdsa.nBits brainpoolp512r1.C := brainpoolp512r1_nBits
  exact Nat.sub_eq_zero_of_le h

theorem brainpoolp512r1_ok : CfgOk brainpoolp512r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP512r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  n_enc := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [brainpoolp512r1_sh]; decide
  fp := ⟨rfl, rfl, Mont.brainpoolp512r1p_ok, rfl⟩
  fn := ⟨rfl, rfl, Mont.brainpoolp512r1n_ok, rfl⟩
  mulNf := fun _ h => nomatch h


/-- brainpoolp512r1 with its field multiplications by `vg_brainpoolp512r1_mul_mod_<p|n>_umaal`:
what `brainpoolp512r1_ok` states. -/
theorem brainpoolp512r1u_ok : CfgOk (brainpoolp512r1With true) where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP512r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  n_enc := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by
    have h : 64 * 8 ≤ Spec.Ecdsa.nBits (brainpoolp512r1With true).C := brainpoolp512r1_nBits
    rw [show (brainpoolp512r1With true).sh = 0 from Nat.sub_eq_zero_of_le h]; decide
  fp := ⟨rfl, rfl, Mont.brainpoolp512r1p_ok, rfl⟩
  fn := ⟨rfl, rfl, Mont.brainpoolp512r1n_ok, rfl⟩
  mulNf := fun _ h => nomatch h

/-- Either configuration. -/
theorem brainpoolp512r1With_ok (u : Bool) : CfgOk (brainpoolp512r1With u) := by
  cases u
  · exact brainpoolp512r1_ok
  · exact brainpoolp512r1u_ok

/-! The functions modulo `p` as literals, for their summaries (the kernel would otherwise build
their instructions once for the analysis and once for the frame). -/
materialize_code mulModP := Mont.mulFnWith false brainpoolp512r1.SP.k brainpoolp512r1.SP.m
materialize_code addModP := Mont.addFn brainpoolp512r1.SP.k brainpoolp512r1.SP.m
materialize_code subModP := Mont.subFn brainpoolp512r1.SP.k brainpoolp512r1.SP.m

/-! The constant-time analyses of the calls of the functions modulo `p`, from their arguments,
each done once for every check of code that calls them (`taint_decide_sum`: signing, ECDH, the
public key and its compression). They keep what is public of `r10` (which the callers keep `lr`
in) and of the loops' counter `r11`: the functions write neither. The analysis is `taintS`'s,
which has summaries (`Proof/Framework/Arm/TaintMono.lean`); the `_umaal` variants' checks are
`taintU`'s, which has none. -/
taint_summary mulPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (Mont.mulName false brainpoolp512r1.SP)
    (Mont.mulFnWith false brainpoolp512r1.SP.k brainpoolp512r1.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])
taint_summary addPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (brainpoolp512r1.SP.fn "add") (Mont.addFn brainpoolp512r1.SP.k brainpoolp512r1.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])
taint_summary subPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (brainpoolp512r1.SP.fn "sub") (Mont.subFn brainpoolp512r1.SP.k brainpoolp512r1.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])

end VG.Proof.Ecdsa.Arm.BrainpoolP512r1
