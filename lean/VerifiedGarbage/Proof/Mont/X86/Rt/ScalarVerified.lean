module

import VerifiedGarbage.Proof.Mont.X86.Rt.Body
meta import VerifiedGarbage.Proof.Mont.X86.Rt.Body
import VerifiedGarbage.Proof.Dsa.X86.PowABI
meta import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.Basic
meta import Init.Data.BitVec.Basic
public import Init.Data.List.BasicAux
meta import Init.Data.List.BasicAux
public import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import Init.Data.BitVec.BasicAux
meta import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.Isa

/-! # `vg_rsa_mont_mul_at` on x86 against its contract

Its correctness, from `body_ok`; its timing, from one taint
check of its code: every public value is in a register
or computed from the read-only arguments.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)

theorem numAt_val32 (m : Mem) (ws : Addr) (d n : Nat) : numAt m ws d (8 * n) = val32 m ws d (2 * n) := by
  unfold numAt
  rw [show 8 * n = 4 * (2 * n) by omega]
  exact VG.Proof.Dsa.X86.Pow.read_eq_val32 m ws (2 * n) d

theorem numAt_w32 (m : Mem) (ws : Addr) (d : Nat) : numAt m ws d 4 = w32 m ws d := by
  unfold numAt
  rw [show 4 = 4 * 1 from rfl, VG.Proof.Dsa.X86.Pow.read_eq_val32 m ws 1 d]
  simp [val32]

/-! ## Timing -/

/-! ## A state meeting the precondition

At width 1: the working space of 15 words at `0x1000`, its inverse word `1`
at 0 and its modulus `2^64 - 1`, all bytes `0xFF`, at 8, whose inverse
modulo `2^32` is `-1`; the function's range at 16, the result at 96 and the
operands, zero, at 104 and 112. The arguments are above `esp = 0xf0000000`. -/

end VG.Proof.Mont.X86.Rt
