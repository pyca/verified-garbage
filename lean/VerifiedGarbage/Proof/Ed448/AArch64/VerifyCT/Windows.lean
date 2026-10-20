module
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Erase
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# Ed448 verification's equation on AArch64: constant time of the windows and the comparison

Untrusted: everything here is checked by Lean. As `VerifyCT/Front.lean`, for
the last two phases: the windows over the challenge, and the comparison with
the result. The field operations of the functions called, erased
(`Proof/X448/AArch64/Fast/Erase.lean`), are each a block of their own: the
kernel analyses each once, not once for every slot they work on.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.X448.AArch64.Fast (codeOf)

theorem kWindows_ct : ∃ h, ((taintS [Impl.X448.AArch64.Base.combSym]).check (Taint.ofRegs [.x3]) kWindows h).map
    ((taintS [Impl.X448.AArch64.Base.combSym]).le (Taint.ofRegs [.x3])) = some true := by
  apply exists_map_le_of_eraseT
  simp only [Code.eraseT, kWindows, nibbles, kNib, window, dbl4Loop, Point56.doubleCall, Point56.addCall, fnCall,
    Point56.doubleFn, Point56.addFn, asFn, ops_eraseT, List.map_append]
  refine ⟨?h, ?g⟩
  case g => taint_decide

theorem tail_ct :
    ∃ h, ((taintS [Impl.X448.AArch64.Base.combSym]).check (Taint.ofRegs [.x3])
      (.seq wcross wfinish) h).isSome = true := by
  apply exists_isSome_of_eraseT
  simp only [Code.eraseT, wcross, wfinish, wcmp, wresult, Point56.doubleCall, Point56.addCall, fnCall, Point56.doubleFn,
    Point56.addFn, asFn, ops_eraseT, List.map_append, eqSlots_eraseT]
  refine ⟨?h, ?g⟩
  case g => taint_decide

end VG.Proof.Ed448.AArch64
