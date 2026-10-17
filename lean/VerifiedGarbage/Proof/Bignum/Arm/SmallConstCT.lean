module

public import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Impl.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Constant-time initialization of an RSA workspace array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem smallConst_ct {base : BitVec 32} {len w o : Nat} (value : BitVec 32)
    (ho : o < 8) (encO : encodable (BitVec.ofNat 32 o) = true)
    (encV : encodable value = true) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (smallConst (BitVec.ofNat 32 o) value) (fun _ _ => True) := by
  let P := fun (s t : State) => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp
  have args : RelCT isa P (.block (smallConstArgs (BitVec.ofNat 32 o) value)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block (smallConstArgs (BitVec.ofNat 32 o) value)) s (SmallFnReady base len w o) := by
    refine WP.mono (smallConstArgs_ok s _ value encO encV) ?_
    rintro u ⟨index, _, mem, rest⟩
    have ready := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
    exact ⟨ready.workspace, ready.layout, ready.width, ready.ptr, index⟩
  have setup := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact (setup.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq (setSmallFn_ct ho)

end VG.Proof.Bignum.Arm
