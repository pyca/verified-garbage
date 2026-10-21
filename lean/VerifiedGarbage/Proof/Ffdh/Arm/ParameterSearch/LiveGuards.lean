module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Guard
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FieldGuard

/-! Every native decision reads only proven public counters and lengths. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

theorem SearchLive.budget_guard {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4] ++
      VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard)) s fun t =>
      (SearchLive p used remaining t ∧ t.z = decide (remaining = 0) ∧ t.mem = s.mem) ∧ Rest [.r9, .r10] s t := by
  refine WP.mono (guard_ok s h.buffers.controller h.remaining_bound h.counter) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.after_read (by decide) mem rest, flag, mem⟩, rest⟩

theorem SearchLive.length_guard {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 1] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s fun t =>
      (SearchLive p used remaining t ∧ t.z = decide (p.c.bytes.length - used < p.c.length) ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10, .r11] s t := by
  have tape := h.saved 10 (by simp [searchSlots])
  have width := h.saved 1 (by simp [searchSlots])
  simp only [searchValues] at tape width
  refine WP.mono (fieldGuard_ok s h.buffers.controller (by decide : 10 < 16) (by decide : 1 < 16)
    (by have := p.c.tapeCount; omega) (by have := p.width_bounds; omega) tape width) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.after_read (by decide) mem rest, flag, mem⟩, rest⟩

theorem SearchLive.entropy_guard {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 2] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s fun t =>
      (SearchLive p used remaining t ∧
        t.z = decide (p.c.bytes.length - used < Spec.Ffdh.parameterEntropy p.c.bits) ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10, .r11] s t := by
  have tape := h.saved 10 (by simp [searchSlots])
  have cap := h.saved 2 (by simp [searchSlots])
  simp only [searchValues] at tape cap
  refine WP.mono (fieldGuard_ok s h.buffers.controller (by decide : 10 < 16) (by decide : 2 < 16)
    (by have := p.c.tapeCount; omega) p.entropy_fits tape cap) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.after_read (by decide) mem rest, flag, mem⟩, rest⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
