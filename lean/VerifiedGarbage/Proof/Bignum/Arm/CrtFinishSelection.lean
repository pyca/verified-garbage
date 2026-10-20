module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishStage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtOutputArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMasked
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.CrtExportGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Retain the secret acceptance bit and result bound until masked export -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

def CrtFinishSelection (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop :=
  CrtSelected g bs g.base s ∧ ∃ accepted : Bool,
    s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat ∧
    (accepted = true → crtReconstruction g s.mem < 2 ^ (8 * g.length))

def CrtExportSelection (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop :=
  CrtSelected g bs g.base s ∧ ∃ accepted : Bool,
    s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat ∧
    (accepted = true → val32 s.mem (State.addr g.base) (productOffset g.words) (4 * g.words + 2) < 2 ^ (8 * g.length))

theorem crt_recombineExport_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtFinishSelection g bs s) :
    WP isa (.seq (.seq (.block CrtFn.qSource) (transferArray 1 6)) recombine) s (CrtExportSelection g bs) := by
  refine WP.mono (crt_recombineStage_ok s h.1.1 h.1.2) ?_
  rintro t ⟨sharedT, readyT, value, frame, rest⟩
  obtain ⟨accepted, flag, bound⟩ := h.2
  have stackEq : WorkspaceEq (State.addr s.sp) 112 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.1.stack.separate)
  exact ⟨⟨sharedT, readyT⟩, accepted,
    by rw [rest.sp, stackEq.word (d := 48) (bits := 32) (by decide)]; exact flag,
    by rw [value]; exact bound⟩

theorem crt_exportArgs_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtExportSelection g bs s) : WP isa (.block CrtFn.outputArgs) s
      (fun t => ∃ accepted, ExportBufferInput (crtProduct g.base g.words) g.output (4 * (4 * g.words + 2)) g.length accepted t) := by
  refine WP.mono (crt_outputArgs_ok s h.1.1 h.1.2.ptr) ?_
  rintro t ⟨source, output, count, mem, rest⟩
  obtain ⟨accepted, flag, bound⟩ := h.2
  exact ⟨accepted, (h.1.1.of_mem mem rest).export_input source output count
    (by rw [mem, rest.sp]; exact flag) (by rw [mem]; exact bound)⟩

end VG.Proof.Bignum.Arm
