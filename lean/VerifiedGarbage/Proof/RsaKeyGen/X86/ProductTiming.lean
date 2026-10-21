module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Native multiplication keeps both operands secret

Offsets and public loop bounds erase to a single checked program. ESI
can remain public for an enclosing fixed arithmetic schedule.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Product

def productEndTaint (counter : Bool) : VG.X86.Taint.T :=
  { regs := .ofList ([.edi, .ebp, .ecx, .edx] ++ if counter then [.esi] else []), flags := true }

def productHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (code 1 2 0 0 0 0))

theorem product_check (counter : Bool) (left right out a b mult : Nat) :
    VG.Taint.check taint (workspaceTaint counter) (code left right out a b mult) (productHint counter) =
      some (productEndTaint counter) := by
  exact (check_of_erase_eq (code left right out a b mult) (code 1 2 0 0 0 0)
    (workspaceTaint counter) (productHint counter) rfl
    (by cases counter <;> rfl) (by cases counter <;> rfl)).trans (by cases counter <;> rfl)

theorem code_trace (counter : Bool) (left right out a b mult : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint counter)) (code left right out a b mult)
      (VG.X86.Taint.Agree (productEndTaint counter)) := by
  intro s t u v s' t' agree first second
  exact VG.Taint.check_sound (product_check counter left right out a b mult) agree first second

end VG.Proof.RsaKeyGen.X86.Product
