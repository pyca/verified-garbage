module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Ops
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # The four-lane operations with SVE2: `op_ok` for `Op.codeFor` -/

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

/-- `op_ok` for the code with SVE2: an XAR in place of an `xorRol` whose
destination is its first source. -/
theorem op_ok_for (sve : Bool) (op : Op) {vs : Nat → CState} {s : State} (h : Holds vs s)
    (ht : s.v .v30 = rol8Table) :
    WP isa (.block (op.codeFor sve)) s fun s' => Holds (fun j => step (vs j) op) s' ∧ RoundSame s s' := by
  cases sve with
  | false => exact op_ok op h ht
  | true =>
    cases op with
    | add d a b =>
      rw [show Op.codeFor true (.add d a b) = (Op.add d a b).code from rfl]; exact op_ok _ h ht
    | xorRol d a b n =>
      by_cases hda : d = a ∧ 0 < n.val
      · obtain ⟨rfl, h0⟩ := hda
        have hn : n.val < 32 := n.isLt
        have hr : 1 ≤ 32 - n.val ∧ 32 - n.val ≤ 32 := ⟨by omega, by omega⟩
        rw [show Op.codeFor true (.xorRol d d b n) = [.vop (.xarS (vreg d) (vreg b) (32 - n.val))]
          from ite_eq_left ⟨rfl, h0⟩]
        apply WP.of_runBlock
        simp only [runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some, hr, and_self,
          ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
        refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
          by simp only [↓reduceIte, RegUpd.v_setV, Ne.symm (vreg_ne30 d)]⟩⟩
        simp only [RegUpd.v_setV, step, get_set, vreg_inj]
        split
        · rw [vword_map2 _ _ _ hj, h d j hj, h b j hj, Rows6.ror_sub _ h0 hn]
        · exact h k j hj
      · rw [show Op.codeFor true (.xorRol d a b n) = (Op.xorRol d a b n).code from ite_eq_right hda]
        exact op_ok _ h ht

end VG.Proof.ChaCha20.AArch64.Neon4
