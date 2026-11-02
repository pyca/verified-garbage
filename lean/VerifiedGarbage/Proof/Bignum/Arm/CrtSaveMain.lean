module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtImportModulus
public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCall
import VerifiedGarbage.Proof.Bignum.Arm.LayoutExternal
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Offset

/-! # Reuse the imported modulus pointer's stack slot for the main workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_saveMain_ready (s : State) {base : BitVec 32} {size w : Nat}
    (h : CrtLoaded base size w s) :
    WP isa (.block saveMain) s fun t => CrtLoaded base size w t ∧
      t.mem.readW (off (State.addr t.sp) 8) 32 = base ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨off (State.addr s.sp) 8, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  refine WP.mono (crt_saveMain_ok s h.stackFits h.stackWrite) ?_
  rintro t ⟨mem, frame, rest⟩
  have sep (r : Region) (hr : r ∈ crtRegions base (workspaceWords w) w) :
      r.Disjoint ⟨off (State.addr s.sp) 8, 4⟩ :=
    (h.stackSeparate.sub_left (Offset.sub_base _ (by decide))).symm.sub_left
      (crt_region_sub_workspace h.workspace h.storageFits hr)
  have mainSep := sep ⟨State.addr base, 8 * workspaceWords w⟩ (by simp [crtRegions])
  obtain ⟨ready, eq⟩ := h.ready.after_external frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact mainSep)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact (Offset.disjoint_base (State.addr s.sp) (d := 8) (n := 4) (k := 4) (by decide) (by decide)).symm)
    rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  have eqP : WorkspaceEq (State.addr (crtP base w)) (8 * workspaceWords w) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := h.context.p.nowrap; omega) frame
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep _ (by simp [crtRegions]))
  have eqQ : WorkspaceEq (State.addr (crtQ base w)) (8 * workspaceWords w) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := h.context.q.nowrap; omega) frame
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep _ (by simp [crtRegions]))
  refine ⟨⟨h.workspace.congr rest.wr, h.context.congr rest.wr, ready, h.main.congr eq,
    h.p.congr eqP, h.q.congr eqQ, by rw [rest.sp]; exact h.stackFits,
    by rw [rest.wr, rest.sp]; exact h.stackWrite,
    by rw [rest.sp]; exact h.stackSeparate, h.storageFits⟩, ?_, eq.number h.context.arraysFit (by decide : 0 < 8), frame, rest⟩
  rw [rest.sp, mem, Mem.readW_writeW_self32, h.ready.ptr]

end VG.Proof.Bignum.Arm
