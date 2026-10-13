module

public import VerifiedGarbage.Proof.P256.X86_64.JacTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JacTiming
public import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
meta import VerifiedGarbage.Proof.P256.X86_64.JacTimingAdx
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
