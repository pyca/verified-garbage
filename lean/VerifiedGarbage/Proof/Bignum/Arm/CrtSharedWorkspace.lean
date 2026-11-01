module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Offset

/-! # An operation in one CRT workspace preserves the other two -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_workspace_frame {s : State} {g : CrtGeometry} {child : BitVec 32} {m m' : Mem}
    (ws : Workspace s g.base g.size) (fits : totalBytes g.words ≤ g.size)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] m m') :
    Frame (crtLiveMutable g s.sp) m m' := by
  apply frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp [crtLiveMutable], crt_region_sub_workspace ws fits member⟩
  · exact ⟨⟨off (State.addr s.sp) 48, 4⟩, by simp [crtLiveMutable], fun _ h => h⟩

theorem CrtShared.acceptance_after_workspace {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {child : BitVec 32} {rs : List Reg} (h : CrtShared g bs s)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩] s.mem t.mem) (rest : Rest rs s t) :
    t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
  have eq : WorkspaceEq (State.addr s.sp) 112 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.stack.separate.sub_right (crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member))
  rw [rest.sp]
  exact eq.word (d := 48) (bits := 32) (by decide)

theorem CrtShared.workspace_eq_after {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child other : BitVec 32}
    (h : CrtShared g bs s) (ws : Workspace s other (8 * workspaceWords g.words))
    (member : (⟨State.addr other, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (separate : Region.Disjoint ⟨State.addr other, 8 * workspaceWords g.words⟩ ⟨State.addr child, 8 * workspaceWords g.words⟩)
    (frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem) :
    WorkspaceEq (State.addr other) (8 * workspaceWords g.words) s.mem t.mem := by
  apply WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact separate
  · exact (h.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))).sub_left
      (crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member)

theorem CrtShared.after_main {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s)
    (frame : Frame [⟨State.addr g.base, 8 * workspaceWords g.words⟩,
      ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem) (rest : Rest rs s t)
    (main : CrtMainState g.base (workspaceWords g.words) g.words t.mem)
    (modulus : Proof.Rsa.Mont.numAt t.mem (State.addr g.base) g.words 0 = Proof.Rsa.Mont.numAt s.mem (State.addr g.base) g.words 0) :
    CrtShared g bs t := by
  have pEq := h.workspace_eq_after h.buffers.context.p (by simp [crtRegions]) h.buffers.context.sepMP.symm frame
  have qEq := h.workspace_eq_after h.buffers.context.q (by simp [crtRegions]) h.buffers.context.sepMQ.symm frame
  exact h.after_frame (crt_workspace_frame h.buffers.workspace h.buffers.storageFits (by simp [crtRegions]) frame) rest
    main (h.p.congr pEq) (h.q.congr qEq) modulus

theorem CrtShared.after_p {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s)
    (frame : Frame [⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩,
      ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem) (rest : Rest rs s t)
    (layout : CrtLayoutState (crtP g.base g.words) (workspaceWords g.words) g.words t.mem) :
    CrtShared g bs t := by
  have mainEq := h.workspace_eq_after h.buffers.context.main (by simp [crtRegions]) h.buffers.context.sepMP frame
  have qEq := h.workspace_eq_after h.buffers.context.q (by simp [crtRegions]) h.buffers.context.sepPQ.symm frame
  exact h.after_frame (crt_workspace_frame h.buffers.workspace h.buffers.storageFits (by simp [crtRegions]) frame) rest
    (h.main.congr mainEq) layout (h.q.congr qEq) (mainEq.number h.buffers.context.arraysFit (by decide))

theorem CrtShared.after_q {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s)
    (frame : Frame [⟨State.addr (crtQ g.base g.words), 8 * workspaceWords g.words⟩,
      ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem) (rest : Rest rs s t)
    (layout : CrtLayoutState (crtQ g.base g.words) (workspaceWords g.words) g.words t.mem) :
    CrtShared g bs t := by
  have mainEq := h.workspace_eq_after h.buffers.context.main (by simp [crtRegions]) h.buffers.context.sepMQ frame
  have pEq := h.workspace_eq_after h.buffers.context.p (by simp [crtRegions]) h.buffers.context.sepPQ frame
  exact h.after_frame (crt_workspace_frame h.buffers.workspace h.buffers.storageFits (by simp [crtRegions]) frame) rest
    (h.main.congr mainEq) (h.p.congr pEq) layout (mainEq.number h.buffers.context.arraysFit (by decide))

end VG.Proof.Bignum.Arm
