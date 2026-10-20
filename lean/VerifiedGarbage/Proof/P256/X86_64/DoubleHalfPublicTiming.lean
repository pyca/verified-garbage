module

public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfTiming
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfTiming
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
