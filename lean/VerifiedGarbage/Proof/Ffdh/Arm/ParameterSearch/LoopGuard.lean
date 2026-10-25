module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Memory
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The native search continues only after a complete rejected candidate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

theorem statusGuard_ok (s : State) {base : BitVec 32} {status : Nat}
    (h : Controller base s) (small : status < 5)
    (value : lowWord s.mem base 13 = BitVec.ofNat 32 status) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 13, .cmp .r9 (.imm 4)]) s fun t =>
      (t.z = decide (status = 4) ∧ t.mem = s.mem) ∧ Rest [.r9] s t := by
  refine withRest_all [.r9] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord at *
  ffrun [h.addr (by decide : 13 < 16), h.read (by decide : 13 < 16), value]
  have casesStatus : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 ∨ status = 4 := by omega
  rcases casesStatus with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem SearchDone.after_read {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s t : State} {rs : List Reg} (h : SearchDone p result s) (kept : .r4 ∉ rs)
    (mem : t.mem = s.mem) (rest : Rest rs s t) : SearchDone p result t := by
  have frame : Frame (searchRegions p s.sp) s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.buffers.after_frame kept frame rest, h.usedBound, by rw [mem]; exact h.usedPtr,
    by rw [mem]; exact h.used, by rw [mem]; exact h.status,
    by rw [mem]; exact h.policy, by rw [mem]; exact h.output⟩

theorem SearchDone.loop_guard {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} (h : SearchDone p result s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 13, .cmp .r9 (.imm 4)]) s fun t =>
      (isa.eval .eq t = some false ∧ SearchDone p result t) ∧ Rest [.r9] s t := by
  have small : result.status < 5 := by cases result <;> simp only [Spec.Ffdh.ParameterSearchResult.status] <;> decide
  refine WP.mono (statusGuard_ok s h.buffers.controller small h.status) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  refine ⟨⟨?_, h.after_read (by decide) mem rest⟩, rest⟩
  change some t.z = some false
  rw [flag]
  cases result <;> rfl

theorem SearchLive.loop_guard {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (status : lowWord s.mem p.control 13 = 4#32) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 13, .cmp .r9 (.imm 4)]) s fun t =>
      (isa.eval .eq t = some true ∧ SearchLive p used remaining t) ∧ Rest [.r9] s t := by
  refine WP.mono (statusGuard_ok s h.buffers.controller (by decide : 4 < 5) status) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨by change some t.z = some true; rw [flag]; rfl, h.after_read (by decide) mem rest⟩, rest⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
