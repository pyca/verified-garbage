module

public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # The taints of prime recovery's timing at a run-time width

Every operation reads the modulus's length and the working space from the
arguments on the stack, so the taint analysis takes them public: `τA`, the
arguments above `esp`, `edi` and `esp`, and `τF`, the same inside the frame
of 36 bytes of a call of `vg_rsa_mont_mul_at`.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86

/-- The arguments, `edi` and `esp`. -/
def τA : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 52 }

/-- `τA` in the frame of a call of `vg_rsa_mont_mul_at`. -/
def τF : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 52, stk := [some 36] }

end VG.Proof.Rsa.X86.Recover
