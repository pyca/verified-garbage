module

public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
meta import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.Isa

/-! # Public cached geometry controls every symmetric-square column

The column loop writes only the prepared workspace. Its cached parameters
can therefore be treated as read-only for this proof, then execution can
be widened back to the caller's permissions. The first cached word is not
read by the loop; the following words hold the modulus pointer, input
pointer and width.
-/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86

def columnTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .edi], flags := false, argLen := 16 }

theorem columns_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree columnTaint)
      VG.Impl.Mont.X86.PreparedSquare.columns :=
  VG.Taint.constantTime (A := sseTaint) columnTaint (fun _ _ _ _ H => H) (by taint_decide)

end VG.Proof.Mont.X86.PreparedSquare
