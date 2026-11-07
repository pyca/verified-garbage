module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame

import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract
import Init.Data.BitVec.Basic
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.X86.Isa

/-! # Prepared metadata and numbers survive the callee's register save -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.Mont

theorem layout_pointer_low {m : Mem} {W : Addr} {wsLen j : Nat}
    (layout : Layout m W wsLen) (index : j < 8) :
    w32 m W (64 + 8 * j) = (W.toNat + arrAt (wOf m W) j) % 2 ^ 32 := by
  rw [show 64 + 8 * j = 8 * arrWord j by unfold arrWord; omega, header_low,
    layout.2.2.2 j index, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.Mont.X86.Compact
