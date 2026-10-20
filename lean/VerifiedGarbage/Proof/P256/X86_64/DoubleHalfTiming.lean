module

public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfForward
meta import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfForward
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! The forwarded point doubler's addresses depend only on the scratch pointer. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Ecdsa.X86_64

theorem doubleHalfForward_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (doubleHalfForward p256.MP' p256.rcbSlots (p256.pt RX RY RZ)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem doubleHalfForward_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (doubleHalfForward p256x.MP' p256x.rcbSlots (p256x.pt RX RY RZ)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64
