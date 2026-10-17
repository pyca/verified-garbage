module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Selecting a CRT workspace preserves all shared inputs and initializes its saved base -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem acceptance_after_base_save {s t : State} {rs : List Reg}
    (frame : Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem) (rest : Rest rs s t) :
    t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
  rw [rest.sp]
  apply frame.readW (r := ⟨off (State.addr s.sp) 48, 4⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact Offset.disjoint_base _ (by decide) (by decide)

theorem CrtShared.workspace_eq_after_base {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    (h : CrtShared g bs s) (ws : Workspace s child (8 * workspaceWords g.words))
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (frame : Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem) :
    WorkspaceEq (State.addr child) (8 * workspaceWords g.words) s.mem t.mem :=
  WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (h.stack.separate.symm.sub_right (Region.sub_prefix (by decide))).sub_left
      (crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member))

theorem crt_selected_ready {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    (h : CrtShared g bs s) (ws : Workspace s child (8 * workspaceWords g.words))
    (layout : CrtLayoutState child (workspaceWords g.words) g.words s.mem)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (ptr : t.gpr .r0 = child) (mem : t.mem = s.mem.writeW (State.addr s.sp) child)
    (frame : Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem) (rest : Rest [.r0, .r12] s t) :
    CrtShared g bs t ∧ LayoutFrameReady child (workspaceWords g.words) g.words t := by
  have sep : Region.Disjoint ⟨State.addr g.base, g.size⟩ ⟨State.addr s.sp, 4⟩ :=
    h.stack.separate.symm.sub_right (Region.sub_prefix (by decide))
  have shared := h.after_external frame rest (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [crtLiveMutable])
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep)
  have childSub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  have eq : WorkspaceEq (State.addr child) (8 * workspaceWords g.words) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep.sub_left childSub)
  have childLayout := layout.congr eq
  refine ⟨shared, ⟨⟨ws.congr rest.wr, childLayout.layout, childLayout.width, ptr⟩, ?_, ?_, ?_⟩⟩
  · simpa only [off, BitVec.add_zero] using shared.stack.read (d := 0) (by decide)
  · rw [rest.sp]; exact sep.symm.sub_right childSub
  · rw [rest.sp, mem, Mem.readW_writeW_self32]

theorem crt_selectLinked_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (ws : Workspace s child (8 * workspaceWords g.words))
    (layout : CrtLayoutState child (workspaceWords g.words) g.words s.mem)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (slotFit : slot + 4 ≤ 8 * workspaceWords g.words) (hs : slot < 4096)
    (ptr : s.gpr .r0 = g.base) (link : s.mem.readW (off (State.addr g.base) slot) 32 = child) :
    WP isa (selectChild slot) s fun t => CrtShared g bs t ∧ LayoutFrameReady child (workspaceWords g.words) g.words t ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  refine WP.mono (crt_selectChild_ok s h.buffers.context.main slotFit hs ptr link
    (by simpa only [off, BitVec.add_zero] using h.stack.write (d := 0) (by decide))) ?_
  rintro t ⟨ptrT, mem, frame, rest⟩
  obtain ⟨shared, ready⟩ := crt_selected_ready h ws layout member ptrT mem frame rest
  exact ⟨shared, ready, frame, rest⟩

theorem crt_selectMain_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa selectMain s fun t => CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  refine WP.mono (crt_selectMain_ok s (by have := h.stack.nowrap; omega)
    (h.stack.read (by decide)) h.savedMain
    (by simpa only [off, BitVec.add_zero] using h.stack.write (d := 0) (by decide))) ?_
  rintro t ⟨ptr, mem, frame, rest⟩
  obtain ⟨shared, ready⟩ := crt_selected_ready h h.buffers.context.main h.main.toCrtLayoutState
    (by simp [crtRegions]) ptr mem frame rest
  exact ⟨shared, ready, frame, rest⟩

end VG.Proof.Bignum.Arm
