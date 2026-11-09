module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract
import Init.Data.BitVec.Basic
import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.X86.Isa

/-! # The register-saving frame retains cdecl arguments and workspace access -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86

theorem argument_address (s : State) (i : Nat) :
    (entered s).ea (Compact.arg i) = argAddr s i := by
  change (((entered s).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) = _
  rw [entered, pushed_esp, show 4 * savedRegisters.length = 16 from rfl,
    show 20 + 4 * i = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

end VG.Proof.Mont.X86.Compact
