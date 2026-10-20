module

public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
public import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! Scalar upper-bound comparison uses only the public domain-shape branch. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem scalarUpper_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    RelCT isa (fun s t => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.withQ
        (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 6 60 32) (VG.Impl.Bignum.Arm.arrayCompare 1 6))
        (VG.Impl.Ffdh.Arm.belowP 1)) (fun _ _ => True) := by
  let P := ImportAtInput p slots
  let Q := fun s : State => P s ∧ s.z = !p.hasQ
  have tests := qTest_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.qTest s Q := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    have ptr := (rest.gpr .r0 (by simp)).trans h.context.ptr
    exact ⟨⟨h.context.of_mem mem rest ptr, h.ready.of_mem mem rest ptr⟩, zero⟩
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 6 60 32) (VG.Impl.Bignum.Arm.arrayCompare 1 6))
        (VG.Impl.Ffdh.Arm.belowP 1)) (fun _ _ => True) := by
    apply iteKnown_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      have wpImport (s : State) (h : P s) :
          WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 6 60 32) s (ArithmeticReady p.base p.len p.w) :=
        WP.mono (importAt_ok s 6 60 32 h.context stable h60 h32 h.ready (by decide) (by decide)
          (h.context.qBytes hasQ) (by rw [p.qLength hasQ]; have := p.minLength; omega)
          (by rw [p.qLength hasQ]; exact p.width.2.2.2.1)
          (by change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ])) fun _ j => j.2.1
      exact (relCT_chain (importAt_ct (p := p) (a := 6) (k := p.k) stable h60 h32 rfl (by decide))
        wpImport wpImport (compare_ct (by decide : 1 < 8) (by decide : 6 < 8))).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (belowP_ct (base := p.base) (len := p.len) (w := p.w) (by decide : 1 < 8)).mono
        (fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain tests wp wp branches

end VG.Proof.Ffdh.Arm
