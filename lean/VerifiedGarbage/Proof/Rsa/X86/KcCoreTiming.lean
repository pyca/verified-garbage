module

public import VerifiedGarbage.Proof.Rsa.X86.KcTiming

/-! # Key checks are constant time without requiring a public initial counter -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem crt_check (w : Nat) : ∃ hint out,
    VG.Taint.check taint (workspaceTaint false) (crtBody w) hint = some out ∧
    taint.le (workspaceTaint true) out = true := by
  let startHint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase (start 1))
  let startOut : VG.X86.Taint.T := { regs := .ofList [.edi, .ebp, .edx, .ecx], flags := true }
  have started : VG.Taint.check taint (workspaceTaint false) (start w) startHint = some startOut := by
    exact (check_of_erase_eq (start w) (start 1) (workspaceTaint false) startHint
      (by rfl) (by rfl) (by decide +kernel)).trans (by rfl)
  let divHint := VG.Proof.Rsa.X86.Div.divisionHint
  let divOut : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebp, .edx], flags := true }
  have divided : VG.Taint.check taint (workspaceTaint false) (division w) divHint = some divOut := by
    exact (check_of_erase_eq (division w) (VG.Impl.Rsa.X86.Div.code 1 0 0 0 0)
      (workspaceTaint false) divHint (by rfl) (by rfl) (by decide +kernel)).trans (by rfl)
  obtain ⟨restHint, restOut, checked, le⟩ := crtChecks_public w
  refine ⟨.seq (workspaceTaint false) startHint (.seq (workspaceTaint true) divHint restHint), restOut, ?_, le⟩
  exact exponent_check_seq taint started (by decide +kernel)
    (exponent_check_seq taint divided (by decide +kernel) checked)

theorem key_check (w : Nat) : ∃ hint out,
    VG.Taint.check taint (workspaceTaint false) (keyBody w) hint = some out ∧
    taint.le (workspaceTaint true) out = true := by
  obtain ⟨firstHint, firstOut, checked, le⟩ := crt_check w
  obtain ⟨restHint, restOut, rest, last⟩ := (dChecks1_public w).seq
    ((division_public w _ _ _ _).seq ((dChecks2_public w).seq
      ((division_public w _ _ _ _).seq (dChecks3_public w))))
  refine ⟨.seq (workspaceTaint true) firstHint restHint, restOut, ?_, last⟩
  exact exponent_check_seq taint checked le rest

theorem core_constantTime (full : Bool) (w : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false))
      (if full then keyBody w else crtBody w) := by
  have checked : ∃ hint out, VG.Taint.check taint (workspaceTaint false)
      (if full then keyBody w else crtBody w) hint = some out := by
    cases full
    · obtain ⟨hint, out, eq, _⟩ := crt_check w; exact ⟨hint, out, eq⟩
    · obtain ⟨hint, out, eq, _⟩ := key_check w; exact ⟨hint, out, eq⟩
  obtain ⟨hint, out, eq⟩ := checked
  exact VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := hint) (by rw [eq]; rfl)
end VG.Proof.Rsa.X86.KeyCheck
