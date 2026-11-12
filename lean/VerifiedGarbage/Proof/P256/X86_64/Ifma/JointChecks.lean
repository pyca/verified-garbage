module

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Timing
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Config
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
import VerifiedGarbage.Proof.P256.X86_64.JointTiming
import VerifiedGarbage.Proof.P256.X86_64.JointWindowTiming
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublicTiming
import VerifiedGarbage.Proof.P256.X86_64.NafTableTiming
import VerifiedGarbage.Proof.P256.X86_64.NafCacheTiming
import VerifiedGarbage.Proof.P256.X86_64.FastNafTiming
import VerifiedGarbage.Proof.P256.X86_64.JointLoop
meta import VerifiedGarbage.Proof.P256.X86_64.Ifma.Timing
meta import VerifiedGarbage.Proof.P256.X86_64.Ifma.Config
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
meta import VerifiedGarbage.Proof.P256.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JointWindowTiming
meta import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublicTiming
meta import VerifiedGarbage.Proof.P256.X86_64.NafTableTiming
meta import VerifiedGarbage.Proof.P256.X86_64.NafCacheTiming
meta import VerifiedGarbage.Proof.P256.X86_64.FastNafTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JointLoop

/-!
# P-256 on x86-64 with AVX512_IFMA: the joint multiplication's taint checks

Those of `publicJointAdx` where the code is its, and those of the generator's
digits, at `5480` (`publicJointIfma`), and of the loop in vectors (`VChecks`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.P256.X86_64.Ifma VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.P256.X86_64 VG.Proof.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Mont.X86_64 (sc)

theorem joint_ifma_cached_checks : JointCachedChecks publicJointIfma :=
  ⟨joint_adx_cached_checks.read, joint_adx_cached_checks.entry, joint_adx_cached_checks.add,
    joint_adx_cached_checks.copy⟩

theorem joint_ifma_fixed_checks : JointFixedChecks publicJointIfma :=
  ⟨VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ _ _ h => h) (by taint_decide),
    joint_adx_fixed_checks.entry, joint_adx_fixed_checks.add, joint_adx_fixed_checks.copy⟩

theorem fastGeneratorIfma_checks : FastPrepChecks16 4 (p256x.sl U) 5480 := by
  constructor
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs (nafPrepPublicN 4)) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_ifma_mul_checks : JointMulChecks p256vx publicJointIfma :=
  ⟨joint_ifma_cached_checks, joint_ifma_fixed_checks, nafTableCoZ_adx_checks, nafCacheTable_adx_ct,
    joint_adx_infinity_ct, joint_adx_counter_ct, fastGeneratorIfma_checks, fastPeer_adx_checks⟩

theorem joint_ifma_doubler (hc : CfgOk p256vx) (hC : Weierstrass.Law p256vx.C) :
    JointDoubler publicJointIfma p256vx.C size (jointDouble publicJointIfma.K) :=
  p256_doubler joint_ifma_layout rfl (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3 joint_ifma_double_nodup
    doubleHalfPublic_adx_ct

theorem joint_ifma_zero_ct : ScratchCT (.block (Jacobian.zeroTest publicJointIfma.K.M.n publicJointIfma.K.R.z)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The taint checks of the loop in vectors. -/
theorem joint_ifma_vchecks : VChecks publicJointIfma where
  head := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .r10, .r11, .rbx]) (fun _ _ _ _ h => h)
    (by taint_decide)
  qRead := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ _ _ h => h) (by taint_decide)
  qBody := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .r10, .r8, .r11]) (fun _ _ _ _ h => h)
    (by taint_decide)
  gRead := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ _ _ h => h) (by taint_decide)
  gBody := VG.Taint.constantTime (A := taintSym ["VG_P256_GTAB"]) (Taint.ofRegs [.rdi, .r10, .r8, .r11])
    (fun _ _ _ _ h => h) (by taint_decide)
  init := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  out := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .r10, .r11]) (fun _ _ _ _ h => h) (by taint_decide)
  mov := VG.Taint.constantTime (A := taint) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)
  mx1 := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  mx2 := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  lf := VG.Taint.constantTime (A := taint) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)
  mx4 := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  pack := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ _ _ h => h) (by taint_decide)
  ctr0 := VG.Taint.constantTime (A := taint) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64.Ifma
