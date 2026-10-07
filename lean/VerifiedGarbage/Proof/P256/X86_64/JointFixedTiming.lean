import VerifiedGarbage.Proof.P256.X86_64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Proof.Weierstrass.X86_64

theorem jointFixedEntry_ct : FixedEntryCT nafJacWin "VG_P256_COMB" :=
  VG.Taint.constantTime (A:=taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem jointFixedEntry_adx_ct : FixedEntryCT nafJacWinAdx "VG_P256_COMB" :=
  VG.Taint.constantTime (A:=taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64
