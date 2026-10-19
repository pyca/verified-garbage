module

public import VerifiedGarbage.Proof.P256.X86_64.JacTiming
public import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
meta import VerifiedGarbage.Proof.P256.X86_64.JacTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Weierstrass.CombLay
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Proof.Weierstrass.X86_64

theorem jointFixedEntry_ct : FixedEntryCT nafJacWin "VG_P256_COMB" :=
  VG.Taint.constantTime (A:=taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem jointFixedEntry_adx_ct : FixedEntryCT nafJacWinAdx "VG_P256_COMB" :=
  VG.Taint.constantTime (A:=taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64
