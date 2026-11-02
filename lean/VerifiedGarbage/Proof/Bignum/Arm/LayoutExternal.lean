module

public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

/-! # Writes outside the arithmetic workspace and saved base preserve readiness -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem LayoutFrameReady.after_external {s t : State} {base : BitVec 32} {len w : Nat}
    {regions : List Region} {rs : List Reg}
    (h : LayoutFrameReady base len w s) (frame : Frame regions s.mem t.mem)
    (workspaceSep : ∀ r ∈ regions, (⟨State.addr base, 8 * len⟩ : Region).Disjoint r)
    (baseSep : ∀ r ∈ regions, (⟨State.addr s.sp, 4⟩ : Region).Disjoint r)
    (rest : Rest rs s t) (ptr : t.gpr .r0 = base) :
    LayoutFrameReady base len w t ∧ WorkspaceEq (State.addr base) (8 * len) s.mem t.mem := by
  have fit : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega
  have eq := WorkspaceEq.of_frame (by have := h.workspace.nowrap; omega : 8 * len < 2 ^ 64) frame workspaceSep
  have saved := WorkspaceEq.of_frame (by decide : 4 < 2 ^ 64) frame baseSep
  refine ⟨⟨⟨h.workspace.congr rest.wr, eq.layout h.layout, (eq.width (by omega)).trans h.width, ptr⟩,
    ?_, ?_, ?_⟩, eq⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [rest.sp]
    have word := saved.word (d := 0) (bits := 32) (by decide)
    simp only [off, BitVec.add_zero] at word
    exact word.trans h.saved

end VG.Proof.Bignum.Arm
