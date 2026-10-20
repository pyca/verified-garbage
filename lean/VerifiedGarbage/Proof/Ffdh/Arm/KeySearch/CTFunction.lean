module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFinish
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Native entry, bounded key search, result stores, and saved-register
frame compose without timing dependence beyond the disclosed search policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm

private theorem loop_ready (backend : VG.Proof.Ffdh.Arm.Backend) (a : KeyPublic × List Nat) (s : State)
    (h : Entered a s) :
    WP isa (.loop (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) .eq)
      s (KeyCTDone a.1) := by
  obtain ⟨original, live, _⟩ := h
  refine WP.mono (loop backend (attemptRun_ok backend)
    (expected := a.1.tail (keyRand a.1 original) 0 a.1.keys a.1.scalars)
    (n := 128 * a.1.keys + a.1.scalars + 1) ?_) (fun _ result => ⟨original, _, result⟩)
  exact ⟨0, a.1.keys, a.1.scalars, rfl, live, rfl, rfl⟩

theorem body_ct (backend : VG.Proof.Ffdh.Arm.Backend) : RelCT isa (Two PushedStart)
    (.seq (.block VG.Impl.Ffdh.Arm.KeySearch.entry)
      (.seq (.loop (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) .eq)
        (.block VG.Impl.Ffdh.Arm.KeySearch.finish))) (fun _ _ => True) := by
  refine RelCT.seq (two_post entry_ct entry_ready) ?_
  have loopCT : RelCT isa (Two Entered)
      (.loop (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) .eq) (fun _ _ => True) :=
    (loop_ct backend).mono (fun _ _ ⟨a, h₁, h₂, sp⟩ => ⟨initialPoint a, h₁, h₂, sp⟩) (fun _ _ h => h)
  refine RelCT.seq (two_post loopCT (loop_ready backend)) ?_
  exact finish_ct.mono (fun _ _ ⟨a, h₁, h₂, sp⟩ => ⟨a.1, h₁, h₂, sp⟩) (fun _ _ h => h)

private theorem push_search_eq {s t : State}
    (h : isa.push (.push [.r4, .r9, .r10, .r11, .r12, .lr]) s = some t) : t = searchPushed s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem function_ct (backend : VG.Proof.Ffdh.Arm.Backend) : RelCT isa (Two KeyStart)
    (VG.Impl.Ffdh.Arm.KeySearch.code (.call backend.keyName backend.generateKey)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.code
  refine RelCT.frame (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (body_ct backend).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨q, h₁, h₂, sp⟩, push₁, push₂⟩
  have first := push_search_eq push₁
  have second := push_search_eq push₂
  subst first second
  refine ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, ?_⟩
  change s.sp - 24#32 = t.sp - 24#32
  rw [sp]

end VG.Proof.Ffdh.Arm.KeySearch
