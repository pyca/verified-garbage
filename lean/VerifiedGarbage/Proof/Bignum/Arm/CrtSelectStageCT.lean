module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Workspace selection preserves independent secret state in paired executions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_selectP_stage (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs g.base s) : WP isa (selectChild 224) s (CrtSelected g bs (crtP g.base g.words)) :=
  (crt_selectLinked_ready s h.1 h.1.buffers.context.p h.1.p (by simp [crtRegions])
    (by have := h.1.buffers.context.size; omega : 224 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) h.2.ptr h.1.main.p).mono (fun _ j => ⟨j.1, j.2.1⟩)

theorem crt_selectQ_stage (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs g.base s) : WP isa (selectChild 228) s (CrtSelected g bs (crtQ g.base g.words)) :=
  (crt_selectLinked_ready s h.1 h.1.buffers.context.q h.1.q (by simp [crtRegions])
    (by have := h.1.buffers.context.size; omega : 228 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) h.2.ptr h.1.main.q).mono (fun _ j => ⟨j.1, j.2.1⟩)

theorem crt_select_stage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (slot : Nat) :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      (selectChild slot) (fun _ _ => True) :=
  (crt_selectChild_ct slot).mono (fun _ _ h => ⟨h.1.2.ptr.trans h.2.1.2.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
