module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Offset

/-! # Shared CRT inputs survive arithmetic and mutable stack-slot updates -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtLiveMutable (g : CrtGeometry) (sp : BitVec 32) : List Region :=
  [⟨State.addr g.base, g.size⟩, ⟨State.addr sp, 4⟩, ⟨off (State.addr sp) 48, 4⟩]

theorem CrtShared.after_frame {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s) (frame : Frame (crtLiveMutable g s.sp) s.mem t.mem) (rest : Rest rs s t)
    (main : CrtMainState g.base (workspaceWords g.words) g.words t.mem)
    (p : CrtLayoutState (crtP g.base g.words) (workspaceWords g.words) g.words t.mem)
    (q : CrtLayoutState (crtQ g.base g.words) (workspaceWords g.words) g.words t.mem)
    (modulus : numAt t.mem (State.addr g.base) g.words 0 = numAt s.mem (State.addr g.base) g.words 0) :
    CrtShared g bs t := by
  have wider : Frame (crtMutable g s.sp) s.mem t.mem := frame.mono (by
    intro r hr
    simp only [crtLiveMutable, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [crtMutable])
  refine ⟨h.buffers.after_mutable wider rest, h.stack.after_frame wider rest,
    main, p, q, modulus.trans h.modulus, h.valid, ?_⟩
  rw [rest.sp]
  have word : t.mem.readW (off (State.addr s.sp) 8) 32 = s.mem.readW (off (State.addr s.sp) 8) 32 := by
    apply frame.readW (r := ⟨off (State.addr s.sp) 8, 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [crtLiveMutable, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.stack.separate.sub_left (Offset.sub_base _ (by decide))
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  exact word.trans h.savedMain

theorem CrtShared.after_external {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {rs : List Reg} {regions : List Region} (h : CrtShared g bs s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (subset : ∀ r ∈ regions, r ∈ crtLiveMutable g s.sp)
    (separate : ∀ r ∈ regions, (⟨State.addr g.base, g.size⟩ : Region).Disjoint r) :
    CrtShared g bs t := by
  have eq (base : BitVec 32) (ws : Workspace s base (8 * workspaceWords g.words))
      (member : (⟨State.addr base, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
      WorkspaceEq (State.addr base) (8 * workspaceWords g.words) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
      (fun r hr => (separate r hr).sub_left (crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member))
  have mainEq := eq g.base h.buffers.context.main (by simp [crtRegions])
  exact h.after_frame (frame.mono subset) rest (h.main.congr mainEq)
    (h.p.congr (eq _ h.buffers.context.p (by simp [crtRegions])))
    (h.q.congr (eq _ h.buffers.context.q (by simp [crtRegions])))
    (mainEq.number h.buffers.context.arraysFit (by decide))

end VG.Proof.Bignum.Arm
