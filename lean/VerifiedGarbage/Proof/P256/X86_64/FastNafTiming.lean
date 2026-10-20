module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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

theorem fastGenerator_checks : FastPrepChecks 4 (p256.sl U) 6000 7 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastPeer_adx_checks : FastPrepChecks 4 (p256x.sl V) p256x.winBits 5 := fastPeer_checks

theorem fastGenerator_adx_checks : FastPrepChecks 4 (p256x.sl U) 6000 7 := fastGenerator_checks

end VG.Proof.P256.X86_64
