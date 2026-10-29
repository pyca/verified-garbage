module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentContext
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentHead
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
import VerifiedGarbage.Proof.Framework.Omega
/-! The complete native candidate argument block writes precisely its five stack arguments. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/ArgumentCopy.lean`, which only this module imported.
section

/-! Copy each public controller argument into the candidate's AAPCS stack frame. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)
open VG.Proof.X25519.Arm (Rest)

def callMem (p : SearchParams) (used : Nat) (m : Mem) (sp : BitVec 32) : Mem :=
  ((((m.writeW (off (State.addr sp) 0) (BitVec.ofNat 32 p.c.generator)).writeW
    (off (State.addr sp) 4) (p.c.tape + BitVec.ofNat 32 used)).writeW
    (off (State.addr sp) 8) (BitVec.ofNat 32 (p.c.bytes.length - used))).writeW
    (off (State.addr sp) 12) p.c.base).writeW
    (off (State.addr sp) 16) (BitVec.ofNat 32 p.c.capacity)

theorem arguments_ok (s : State) {p : SearchParams} {used : Nat}
    (h : Controller p.control s) (stack : Workspace s s.sp 24)
    (separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, 24⟩)
    (headers : ∀ j ∈ searchSlots, lowWord s.mem p.control j = searchValues p used j) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.arguments) s fun t =>
      (ArgumentContext p used t ∧ t.mem = callMem p used s.mem s.sp) ∧
      Rest [.r0, .r1, .r2, .r3, .r9, .r12] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3, .r9, .r12] ?_ (by rfl) (by rfl)
  change WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 5, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 1,
    .dp .add .r2 .r4 (.imm 112), VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r3 7, .addSp .r12 0] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (argumentHead_ok s h stack separate headers) ?_
  rintro u ⟨⟨context, mem⟩, rest⟩
  refine wp_argumentCopy (j := 8) (d := 0) context (by simp [searchSlots]) (by decide) fun s1 c1 m1 r1 => ?_
  have sp1 := r1.sp.trans rest.sp
  refine wp_argumentCopy (j := 9) (d := 4) c1 (by simp [searchSlots]) (by decide) fun s2 c2 m2 r2 => ?_
  have sp2 := r2.sp.trans sp1
  refine wp_argumentCopy (j := 10) (d := 8) c2 (by simp [searchSlots]) (by decide) fun s3 c3 m3 r3 => ?_
  have sp3 := r3.sp.trans sp2
  refine wp_argumentCopy (j := 11) (d := 12) c3 (by simp [searchSlots]) (by decide) fun s4 c4 m4 r4 => ?_
  have sp4 := r4.sp.trans sp3
  refine wp_argumentCopy (j := 12) (d := 16) c4 (by simp [searchSlots]) (by decide) fun _ c5 m5 _ => WP.block_nil ?_
  refine ⟨c5, ?_⟩
  rw [m5, m4, m3, m2, m1, mem, sp4, sp3, sp2, sp1, rest.sp]
  rfl

theorem callMem_frame (p : SearchParams) (used : Nat) (m : Mem) (sp : BitVec 32) :
    Frame [⟨State.addr sp, 24⟩] m (callMem p used m sp) := by
  unfold callMem
  exact (((((Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ (by decide : 0 + 4 ≤ 24) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 4 + 4 ≤ 24) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 8 + 4 ≤ 24) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 12 + 4 ≤ 24) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 16 + 4 ≤ 24) (by decide))

end VG.Proof.Ffdh.Arm.ParameterSearch
