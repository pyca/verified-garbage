module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
public import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Impl.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # Constant-time initialization of an RSA workspace array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem smallConstLayout_ct {base : BitVec 32} {len w o : Nat} (value : BitVec 32)
    (ho : o < 8) (encO : encodable (BitVec.ofNat 32 o) = true)
    (encV : encodable value = true) :
    RelCT isa (fun s t => SelectArrayReady base len w s ∧ SelectArrayReady base len w t ∧ s.sp = t.sp)
      (smallConst (BitVec.ofNat 32 o) value) (fun _ _ => True) := by
  let P := fun (s t : State) => SelectArrayReady base len w s ∧ SelectArrayReady base len w t ∧ s.sp = t.sp
  have args : RelCT isa P (.block (smallConstArgs (BitVec.ofNat 32 o) value)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : SelectArrayReady base len w s) :
      WP isa (.block (smallConstArgs (BitVec.ofNat 32 o) value)) s (SmallFnReady base len w o) := by
    refine WP.mono (smallConstArgs_ok s _ value encO encV) ?_
    rintro u ⟨index, _, mem, rest⟩
    exact ⟨h.workspace.congr rest.wr, by rw [mem]; exact h.layout,
      by rw [mem]; exact h.width, (rest.gpr .r0 (by simp)).trans h.ptr, index⟩
  have setup := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact (setup.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq (setSmallFn_ct ho)

end VG.Proof.Bignum.Arm
