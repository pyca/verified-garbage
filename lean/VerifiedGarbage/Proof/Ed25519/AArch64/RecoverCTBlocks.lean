module

public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
public import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Function.Basic
meta import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Ed25519.AArch64.Point64
import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint
import VerifiedGarbage.Proof.Ed25519.Field64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Impl.Ed25519.AArch64.Point64
meta import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop
meta import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
meta import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint
meta import VerifiedGarbage.Proof.Ed25519.Field64
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.Csub
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds

/-! Fixed-trace arithmetic blocks used in point recovery. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem x0_agree {base : Addr} {s t : State} (hs : s.gpr .x0 = base) (ht : t.gpr .x0 = base) :
    ∀ r ∈ Taint.ofRegs [.x0], s.gpr r = t.gpr r := agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) recoverCandidate (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem parityBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (freeze (offset 0) ++ recoverParity)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem zeroBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem negateBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem successBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem recoverInvalid_ct : CT (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
  exact fun _ _ _ => agree_ofRegs (by simp)

end VG.Proof.Ed25519.AArch64
