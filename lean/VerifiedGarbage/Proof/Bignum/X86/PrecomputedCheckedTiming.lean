module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedKeyTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedApplyTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedFailureTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedChecks
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckExponent

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedDataTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedKey

/-! # Packed-key rejection branches only on public key values -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86

theorem precomputedChecked_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PackedPair base bytes len args s t ∧
        val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (.seq (PublicContext.precomputedChecks (Spec.Rsa.modulusWords len))
        (.ite .e PublicFn.failure (PrecomputedFn.applyInput (Spec.Rsa.modulusWords len)))) (fun _ _ => True) := by
  let R := fun s t => PrecomputedPair base bytes len args s t ∧
    val32 s.mem base 128 2 = val32 t.mem base 128 2 ∧ ∃ b : Bool, s.zf = some (!b) ∧ t.zf = some (!b) ∧
      (b = true → PackedAccepted base (Spec.Rsa.modulusWords len) s ∧ PackedAccepted base (Spec.Rsa.modulusWords len) t)
  have Checks : RelCT isa (fun s t => PackedPair base bytes len args s t ∧
        val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (PublicContext.precomputedChecks (Spec.Rsa.modulusWords len)) R := by
    intro s t tr ur sf tf ⟨H, Ex⟩ E F
    have A : VG.X86.Taint.Agree (workspaceTaint false) s t :=
      agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.1.agree.rf.1 _ (by decide))
    have Trace := (precomputedChecks_relCT _ _ _ _ _ _ _ A E F).1
    obtain ⟨_, Zs, Os, Ks⟩ := wp_result (PublicContext.precomputedChecks_ok H.1.left.scratch H.1.left.dimensions.1 H.1.left.space) E
    obtain ⟨_, Zt, Ot, Kt⟩ := wp_result (PublicContext.precomputedChecks_ok H.1.right.scratch H.1.right.dimensions.1 H.1.right.space) F
    have sz := H.1.left.space
    have size := PublicContext.size_eq (Spec.Rsa.modulusWords len)
    have nw := H.1.left.scratch.nowrap
    have nw' := H.1.right.scratch.nowrap
    have Ps := PublicContext.precomputedCheck_saved Os sz
    have Pt := PublicContext.precomputedCheck_saved Ot sz
    refine ⟨Trace, H.1.keep Ks Kt (by decide) (by decide) (Ps.mono (by omega) (by omega))
      (Pt.mono (by omega) (by omega)), ?_, _, Zs, ?_, ?_⟩
    · rw [PublicContext.precomputedCheck_exponent Os, PublicContext.precomputedCheck_exponent Ot, Ex]
    · rw [H.2.1, H.2.2]; exact Zt
    · intro B
      constructor
      · unfold PackedAccepted
        rw [PublicContext.precomputedCheck_value Os (by decide : 0 < 8) (by decide) (by decide) (by omega),
          PublicContext.precomputedCheck_value Os (by decide : 5 < 8) (by decide) (by decide) (by omega)]
        exact B
      · unfold PackedAccepted
        rw [PublicContext.precomputedCheck_value Ot (by decide : 0 < 8) (by decide) (by decide) (by omega),
          PublicContext.precomputedCheck_value Ot (by decide : 5 < 8) (by decide) (by decide) (by omega),
          ← H.2.1, ← H.2.2]
        exact B
  refine VG.RelCT.seq Checks (VG.RelCT.ite (M := isa) (c := .e) ?_ ?_ ?_)
  · intro s t H
    obtain ⟨_, _, Zs, Zt, _⟩ := H.2
    exact Zs.trans Zt.symm
  · exact (precomputedFailure_relCT base bytes len args).mono (fun _ _ H => H.1.1) (fun _ _ h => h)
  · intro s t tr ur sf tf ⟨H, Z⟩ E F
    obtain ⟨Ex, b, Zs, _, Ready⟩ := H.2
    have B : b = true := by
      change s.zf = some false at Z
      have := Option.some.inj (Zs.symm.trans Z)
      simpa using this
    exact precomputedApply_relCT base bytes len args _ _ _ _ _ _ ⟨H.1, (Ready B).1, (Ready B).2, Ex⟩ E F

theorem precomputedSized_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PrecomputedPair base bytes len args s t ∧
      Spec.Rsa.wordsAt s.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len) =
        Spec.Rsa.wordsAt t.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len) ∧
      val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (PrecomputedFn.sized (Spec.Rsa.modulusWords len)) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨H, Key, Ex⟩ E F
  cases E with | seq E₁ E₂ => cases F with | seq F₁ F₂ =>
  have T₁ := precomputedKey_relCT base bytes len args _ _ _ _ _ _ ⟨H, Key⟩ E₁ F₁
  have keep {σ u : State} {tr : List Leak} (I : PrecomputedInputs base bytes len args σ)
      (E : Exec isa (PrecomputedFn.importKey (Spec.Rsa.modulusWords len)) σ tr u) :
      val32 u.mem base 128 2 = val32 σ.mem base 128 2 := by
    obtain ⟨-, -, O, -⟩ := wp_result (PublicContext.precomputedKey_ok I) E
    exact VG.Proof.Mont.Outside.val32 O (.inl (by decide)) (by decide)
  have T₂ := precomputedChecked_relCT base bytes len args _ _ _ _ _ _
    ⟨T₁.2, by rw [keep H.left E₁, keep H.right F₁, Ex]⟩ E₂ F₂
  rw [T₁.1, T₂.1]
  exact ⟨rfl, trivial⟩

end VG.Proof.Bignum.X86
