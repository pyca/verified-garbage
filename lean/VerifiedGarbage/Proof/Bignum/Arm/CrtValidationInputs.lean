module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptStage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPStage
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Recover validation inputs from the selected workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem CrtSelected.accept_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs g.base s) : CrtAcceptInput g.base g.input (workspaceWords g.words) g.words g.length (bs 1) s := by
  have mainSub := crt_region_sub_workspace h.1.buffers.workspace h.1.buffers.storageFits
    (r := ⟨State.addr g.base, 8 * workspaceWords g.words⟩) (by simp [crtRegions])
  exact ⟨h.2, h.1.main, h.1.inputSaved (by simp [crtRegions]),
    by have := h.1.buffers.lengthValid.1; omega, (crt_width_valid h.1.buffers.lengthValid).2.2,
    by have := h.1.stack.nowrap; omega, h.1.stack.write (by decide),
    (h.1.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))).sub_left mainSub⟩

theorem CrtSelected.loadP_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs (crtP g.base g.words) s) :
    CrtLoadPInput (crtP g.base g.words) g.p g.qi (workspaceWords g.words) g.words g.pLength (bs 2) (bs 6) s :=
  ⟨h.2, h.1.savedOperand 1 (by simp [crtRegions]), h.1.savedOperand 5 (by simp [crtRegions]),
    h.1.buffers.pPositive,
    by have := h.1.buffers.pShort; have := (crt_width_valid h.1.buffers.lengthValid).2.2
       change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega,
    h.1.stack.write (by decide)⟩

end VG.Proof.Bignum.Arm
