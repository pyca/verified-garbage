module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.P256.X86_64.JointLoop
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Impl.P256.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JointLoop
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Impl.P256.X86_64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
meta import VerifiedGarbage.Proof.P256.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
public import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
meta import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Weierstrass.CombLay
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Impl.Ecdh.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfForward
meta import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfForward
public import VerifiedGarbage.Proof.Framework.TaintMap
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZTiming
meta import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64

/-! ### `P256.X86_64.FastNafTiming`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG.Impl.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Weierstrass.X86_64

theorem fastPeer_checks : FastPrepChecks 4 (p256.sl V) p256.winBits 5 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastGenerator16_checks : FastPrepChecks16 4 (p256.sl U) 6000 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

/-- With BMI2 and ADX the recoders have no branches on the scalars' bits (`Joint.Cfg.recodeB`). -/
theorem fastPeer_adx_checks : FastPrepChecksB 4 (p256x.sl V) p256x.winBits := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastGenerator16_adx_checks : FastPrepChecksB16 4 (p256x.sl U) 6000 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64

end

end

/-! ### `P256.X86_64.NafTableTiming`, which this module and modules that import it used -/

section

/-! Baseline and ADX taint checks for the verifier's odd-multiple table. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass.X86_64

theorem nafTableCoZ_checks : NafTableCoZChecks nafJacWin := by
  have hT : p256T.Ok nafJacWin.M := p256T_ok
  constructor
  iterate 2 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 2 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafTableCoZ_adx_checks : NafTableCoZChecks nafJacWinAdx := by
  have hT : p256XT.Ok nafJacWinAdx.M := p256XT_ok
  constructor
  iterate 2 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 2 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64

end

end

/-! ### `P256.X86_64.DoubleHalfPublicTiming`, which this module and modules that import it used -/

section

/-! ### `P256.X86_64.DoubleHalfTiming`, which only this module used -/

section

/-! The forwarded point doubler's addresses depend only on the scratch pointer. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Ecdsa.X86_64

theorem doubleHalfForward_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (doubleHalfForward p256x.MP' p256x.rcbSlots (p256x.pt RX RY RZ)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64

end

end

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Ecdsa.X86_64

theorem doubleHalfPublic_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (doubleHalfPublic p256.MP' p256.rcbSlots (p256.pt RX RY RZ)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem doubleHalfPublic_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (doubleHalfPublic p256x.MP' p256x.rcbSlots (p256x.pt RX RY RZ)) := doubleHalfForward_adx_ct

end VG.Proof.P256.X86_64

end

end

/-! ### `P256.X86_64.JointWindowTiming`, which this module and modules that import it used -/

section

/-! Taint checks of the joint loop's seed and counter. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem joint_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJoint.K publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top publicJoint)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top publicJointAdx)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJointAdx.K publicJointAdx.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64

end

end

/-! ### `P256.X86_64.JointTiming`, which this module and modules that import it used -/

section

/-! ### `P256.X86_64.NafCacheTiming`, which this module and modules that import it used -/

section

/-! Building the cache uses fixed addresses; lookup depends only on the public digit. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

def cacheWin := p256.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP
def cacheWinAdx := p256x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP

theorem nafSignedCachedEntry_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.r8]))
      (Naf.signedCachedEntry cacheWin 4000 5408) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafSignedCachedEntry_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.r8]))
      (Naf.signedCachedEntry cacheWinAdx 4000 5408) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (Naf.cacheTable cacheWin.M cacheWin.tbl 4000 cacheWin.E.x).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (Naf.cacheTable cacheWinAdx.M cacheWinAdx.tbl 4000 cacheWinAdx.E.x).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64

end

end

/-! ### `P256.X86_64.JointFixedTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Proof.Weierstrass.X86_64

theorem jointFixedEntryW_ct : FixedEntryCTW nafJacWin "VG_P256_GTAB" :=
  VG.Taint.constantTime (A:=taintSym ["VG_P256_GTAB"]) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem jointFixedEntryW_adx_ct : FixedEntryCTW nafJacWinAdx "VG_P256_GTAB" :=
  VG.Taint.constantTime (A:=taintSym ["VG_P256_GTAB"]) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64

end

end

/-! Taint checks of P-256's baseline and ADX digit additions in the joint loop. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem joint_cached_checks : JointCachedChecks publicJoint := by
  refine ⟨?_,nafSignedCachedEntry_ct,nafCachedJac_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_cached_checks : JointCachedChecks publicJointAdx := by
  refine ⟨?_,nafSignedCachedEntry_adx_ct,nafCachedJac_adx_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_fixed_checks : JointFixedChecks publicJoint := by
  refine ⟨?_,jointFixedEntryW_ct,nafMixedJac_checks,joint_cached_checks.copy⟩
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_fixed_checks : JointFixedChecks publicJointAdx := by
  refine ⟨?_,jointFixedEntryW_adx_ct,nafMixedJac_adx_checks,joint_adx_cached_checks.copy⟩
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64

end

end

/-! Concrete timing checks for baseline and ADX public joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P256.X86_64
open VG.Proof.P256.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p256v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTableCoZ_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator16_checks,fastPeer_checks⟩

theorem joint_adx_mul_checks : JointMulChecks p256vx publicJointAdx :=
  ⟨joint_adx_cached_checks,joint_adx_fixed_checks,nafTableCoZ_adx_checks,
    nafCacheTable_adx_ct,joint_adx_infinity_ct,joint_adx_counter_ct,fastGenerator16_adx_checks,
    fastPeer_adx_checks⟩

theorem joint_doubler (hc : CfgOk p256v) (hC : Weierstrass.Law p256.C) :
    JointDoubler publicJoint p256.C size (jointDouble publicJoint.K) :=
  p256_doubler joint_layout rfl (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3 joint_double_nodup
    doubleHalfPublic_ct

theorem joint_adx_doubler (hc : CfgOk p256vx) (hC : Weierstrass.Law p256vx.C) :
    JointDoubler publicJointAdx p256vx.C size (jointDouble publicJointAdx.K) :=
  p256_doubler joint_adx_layout rfl (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3 joint_adx_double_nodup
    doubleHalfPublic_adx_ct

/-- `jointPrefix p256v` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixErased : Prog isa := Code.erase (jointPrefix p256v)

materialize_shared jointPrefixErased

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p256v) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `jointPrefix p256vx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixAdxErased : Prog isa := Code.erase (jointPrefix p256vx)

materialize_shared jointPrefixAdxErased

theorem joint_adx_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p256vx) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixAdxErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p256v).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256v).inline

materialize_shared jointTailErased

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256v).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p256vx).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailAdxErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256vx).inline

materialize_shared jointTailAdxErased

theorem joint_adx_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256vx).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailAdxErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64
