module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentContext
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Copy each public controller argument into the candidate's AAPCS stack frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem argumentCopy_ok (s : State) {p : SearchParams} {used j d : Nat}
    (h : ArgumentContext p used s) (member : j ∈ searchSlots) (fit : d + 4 ≤ 24) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 j, .str .r9 .r12 d]) s fun t =>
      (ArgumentContext p used t ∧
        t.mem = s.mem.writeW (off (State.addr s.sp) d) (searchValues p used j)) ∧ Rest [.r9] s t := by
  have bound : j < 16 := by
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have address : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = off (State.addr s.sp) d := by
    rw [h.pointer]
    exact VG.Arm.addr_add (by have := h.stack.nowrap; omega)
  have value := h.headers j member
  unfold VG.Proof.Ffdh.Arm.KeySearch.lowWord at value
  have raw : WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 j, .str .r9 .r12 d]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) d) (searchValues p used j) ∧ Rest [.r9] s t := by
    refine withRest_all [.r9] ?_ (by rfl) (by rfl)
    unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf
    ffrun [controllerAddr h.controller (8 * j) (by omega), h.controller.space.read (off := 8 * j) (by omega),
      address, h.stack.write fit, value, show 8 * j < 4096 by omega, show d < 4096 by omega]
  refine WP.mono raw ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr s.sp, 24⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ fit (by omega))
  exact ⟨⟨h.after_frame (by decide) frame rest, mem⟩, rest⟩

theorem wp_argumentCopy {s : State} {p : SearchParams} {used j d : Nat}
    {tail : List Instr} {Q : State → Prop} (h : ArgumentContext p used s)
    (member : j ∈ searchSlots) (fit : d + 4 ≤ 24)
    (next : ∀ t, ArgumentContext p used t →
      t.mem = s.mem.writeW (off (State.addr s.sp) d) (searchValues p used j) →
      Rest [.r9] s t → WP isa (.block tail) t Q) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 j, .str .r9 .r12 d] ++ tail)) s Q := by
  rw [WP.block_append_iff]
  exact WP.mono (argumentCopy_ok s h member fit) (fun _ post => next _ post.1.1 post.1.2 post.2)

end VG.Proof.Ffdh.Arm.ParameterSearch
