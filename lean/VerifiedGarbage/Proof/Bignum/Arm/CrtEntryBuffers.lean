module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPush
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBodyScope
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Stack entry preserves all source bytes and provides the three scratch subworkspaces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crtExpanded_read {s : State} {base : BitVec 32} {w n : Nat} {a : Addr}
    (h : InRegions (s.rd ++ s.wr) a n) : InRegions ((crtExpanded s base w).rd ++ (crtExpanded s base w).wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, ?_, hc⟩
  simp only [crtExpanded, State.withRegions, List.mem_append] at hr ⊢
  rcases hr with hr | hr
  · exact Or.inl hr
  · exact Or.inr (Or.inr hr)

theorem crtExpanded_write {s : State} {base : BitVec 32} {w n : Nat} {a : Addr}
    (h : InRegions s.wr a n) : InRegions (crtExpanded s base w).wr a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem crt_entry_buffers {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtFnInput g bs s) (frame : Frame [FrameStack.belowA s.sp 56] s.mem t.mem)
    (rest : Rest rs (pcPushed s) t) : CrtBuffers g bs (crtExpanded t g.base g.words) := by
  have ws : Workspace t g.base g.size :=
    ⟨h.workspace.nowrap, by rw [rest.wr]; exact List.mem_cons_of_mem _ h.workspace.writable⟩
  have width := crt_width_valid h.lengthValid
  have source (i : Fin 7) : PublicBytes (g.source i) (g.sourceLength i) (bs i) (crtExpanded t g.base g.words) := by
    refine ⟨(h.source i).fits, crtExpanded_read ?_, ?_⟩
    · rw [rest.rd, rest.wr]
      exact InRegions_append_cons.mpr (Or.inr (h.source i).read)
    · exact (rsa_bytes_frame frame (by have := (h.source i).fits; omega)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact (h.stackSource i).symm)).trans (h.source i).bytes
  refine ⟨⟨ws.nowrap, List.mem_append_right _ ws.writable⟩,
    crt_expanded_context ws h.storageFits width.1 (by have := width.2.1; change Spec.Rsa.modulusWords g.length < _; omega), h.lengthValid,
    h.storageFits, h.pPositive, h.pShort, h.qPositive, h.qShort, source, h.sourceSeparate,
    ?_, h.outputFits, crtExpanded_write ?_, h.outputSeparate, ?_⟩
  · intro i
    change Region.Disjoint _ ⟨State.addr t.sp, 56⟩
    rw [rest.sp]; exact (h.stackSource i).symm
  · rw [rest.wr]
    obtain ⟨r, hr, hc⟩ := h.write
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · change Region.Disjoint _ ⟨State.addr t.sp, 56⟩
    rw [rest.sp]; exact h.stackOutput.symm

end VG.Proof.Bignum.Arm
