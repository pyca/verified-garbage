module
public import VerifiedGarbage.Impl.Dsa.Arm.Shape
public import VerifiedGarbage.Proof.Dsa.Arm.CoreTrace

import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# DSA on 32-bit ARM: the shape check's trace

The shape check loads p and q through their pointers, the same in both
runs, and computes its masks without branching on them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest)

theorem optionalWidth_relCT (n a tmp bits : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (optionalWidth n a tmp bits) (VG.Arm.Taint.Agree T0) := by
  unfold optionalWidth
  split
  · unfold widthMask
    refine RelCT.seq (lessThanConstant_relCT _ _ _ _) (RelCT.seq (block_relCT_T0 _ rfl) ?_)
    split
    · exact RelCT.seq (lessThanConstant_relCT _ _ _ _) (block_relCT_T0 _ rfl)
    · exact block_relCT_T0 _ rfl
  · exact block_relCT_T0 _ rfl

theorem saveWidth_relCT (n bits offset : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (Shape.saveWidth n bits offset) (VG.Arm.Taint.Agree T0) :=
  RelCT.seq (optionalWidth_relCT _ _ _ _)
    (erased_relCT (c₀ := .block [.str .r2 .r12 0]) (VG.Taint.hintOf taint T0 (.block [.str .r2 .r12 0])) rfl
      (wsT_noBase _ _) rfl)

theorem threeWidths_relCT (n a b c output : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (Shape.threeWidths n a b c output) (VG.Arm.Taint.Agree T0) :=
  RelCT.seq (saveWidth_relCT _ _ _) (RelCT.seq (saveWidth_relCT _ _ _) (saveWidth_relCT _ _ _))

theorem inspectP_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (pLen : Nat) (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : 4960 ≤ size₁) (hz₂ : 4960 ≤ size₂) (he : PtrEq base s₁ s₂ (.input .p)) :
    SameTrace isa (Shape.inspectP pLen) s₁ s₂ := by
  unfold Shape.inspectP Shape.loadWidths
  dsimp only
  refine SameTrace.assoc_left (loadThen_trace (p := .input _) (Q := fun _ _ => True) hs₁ hs₂ (by omega) (by omega)
    (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) he (relCT_T10 ?_))
  refine (RelCT.seq (threeWidths_relCT _ _ _ _ _)
    (erased_relCT (c := .block (Shape.saveParity ((pLen + 7) / 8))) (σ := T0) (c₀ := .block (Shape.saveParity 0)) (VG.Taint.hintOf taint T0 (.block (Shape.saveParity 0))) rfl
      (wsT_noBase _ _) rfl)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem inspectQ_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (qLen : Nat) (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : 4960 ≤ size₁) (hz₂ : 4960 ≤ size₂) (he : PtrEq base s₁ s₂ (.input .q)) :
    SameTrace isa (Shape.inspectQ qLen) s₁ s₂ := by
  unfold Shape.inspectQ Shape.loadWidths
  dsimp only
  refine SameTrace.assoc_left (loadThen_trace (p := .input _) (Q := fun _ _ => True) hs₁ hs₂ (by omega) (by omega)
    (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) he (relCT_T10 ?_))
  refine (RelCT.seq (threeWidths_relCT _ _ _ _ _)
    (erased_relCT (c := .block (Shape.parity ((qLen + 7) / 8) ++ Shape.combine)) (σ := T0)
      (c₀ := .block (Shape.parity 0 ++ Shape.combine))
      (VG.Taint.hintOf taint T0 (.block (Shape.parity 0 ++ Shape.combine))) rfl
      (wsT_noBase _ _) rfl)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem check_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat} (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : 4960 ≤ size₁) (hz₂ : 4960 ≤ size₂) (wp : Width pLen nP) (wq : Width qLen nQ)
    (Rp₁ : Ready s₁ base (.input .p) pLen) (Rp₂ : Ready s₂ base (.input .p) pLen)
    (Rq₁ : Ready s₁ base (.input .q) qLen) (Rq₂ : Ready s₂ base (.input .q) qLen)
    (hep : PtrEq base s₁ s₂ (.input .p)) (heq : PtrEq base s₁ s₂ (.input .q)) :
    SameTrace isa (Shape.check pLen qLen) s₁ s₂ := by
  simp only [Shape.check, Core.sequence, List.foldr]
  refine SameTrace.seq (inspectP_trace pLen hs₁ hs₂ hz₁ hz₂ hep) (inspectP_ok hs₁ hz₁ wp Rp₁ rfl)
    (inspectP_ok hs₂ hz₂ wp Rp₂ rfl) fun u₁ u₂ ⟨E₁, E₂, E₃, E₄, R₁, O₁⟩ ⟨F₁, F₂, F₃, F₄, R₂, O₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  have pq : PtrEq base u₁ u₂ (.input .q) := by
    unfold PtrEq
    rw [pointerValue_keep (R₁.gpr .r12 (by decide)) O₁ (by decide) Rq₁.ok,
      pointerValue_keep (R₂.gpr .r12 (by decide)) O₂ (by decide) Rq₁.ok]
    exact heq
  refine SameTrace.seq (inspectQ_trace qLen w₁ w₂ hz₁ hz₂ pq)
    (inspectQ_ok w₁ hz₁ wq (Rq₁.keep_rest R₁ (O := O₁) (hO := by decide)) rfl E₁ E₂ E₃ E₄)
    (inspectQ_ok w₂ hz₂ wq (Rq₂.keep_rest R₂ (O := O₂) (hO := by decide)) rfl F₁ F₂ F₃ F₄)
    fun v₁ v₂ ⟨_, _, _, _, S₁, _⟩ ⟨_, _, _, _, S₂, _⟩ => ?_
  exact SameTrace.of_relCT (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.seq (block_relCT_T0 _ rfl)
    (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial)))
    (agree0 (w₁.of_rest S₁ (by decide)) (w₂.of_rest S₂ (by decide)))

end VG.Proof.Dsa.Arm
