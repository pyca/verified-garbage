import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfTiming

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
