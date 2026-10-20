module

public import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
import VerifiedGarbage.Proof.X25519.X86.Field32.Pow250Sum
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Pow250Sum
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.Set
meta import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.Power
import VerifiedGarbage.Proof.Ed25519.X86.RecoverPoint
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.X25519.X86.Freeze
import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Impl.Ed25519.X86.PointMul
meta import VerifiedGarbage.Impl.Mont.Mod
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
meta import VerifiedGarbage.Proof.Ed25519.X86.Power
meta import VerifiedGarbage.Proof.Ed25519.X86.RecoverPoint
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.X25519.X86.Freeze
meta import VerifiedGarbage.Spec.Rc2

/-! Fixed-trace arithmetic blocks used in point recovery. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem edi_agree {base : BitVec 32} {s t : State} (hs : s.gpr .edi = base) (ht : t.gpr .edi = base) :
    VG.X86.Taint.Agree (regsTaint [.edi]) s t := regsTaint_agree (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : BitVec 32) :
    RelCT isa (CallCTPre base) recoverCandidate (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check callTaint₀ recoverCandidate h).isSome = true := by
    native_taint_decide_sum [VG.Proof.X25519.X86.pow250Sum]
  exact VG.RelCT.taint (A := taint) callTaint₀ (fun _ _ h => callTaint₀_agree h) hc

theorem parityBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem zeroBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem negateBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem successBlock_ct (base : BitVec 32) :
    RelCT isa (fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
  exact fun _ _ h => edi_agree h.1 h.2

theorem recoverInvalid_ct : RelCT isa (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by native_taint_decide)
  exact fun _ _ _ => regsTaint_agree (by simp)

end VG.Proof.Ed25519.X86
