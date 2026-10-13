module

public import VerifiedGarbage.Proof.P224.X86_64.JacTiming
meta import VerifiedGarbage.Proof.P224.X86_64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Taint checks for P-224's verifier's odd-multiple table. -/

@[expose] public section

namespace VG.Proof.P224.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass.X86_64

theorem nafTable_checks : NafTableChecks nafJacWin := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · decide +kernel
  · exact instrs_noClobber (by decide +kernel)

end VG.Proof.P224.X86_64
