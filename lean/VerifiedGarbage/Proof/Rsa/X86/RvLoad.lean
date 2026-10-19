module

public import VerifiedGarbage.Proof.Rsa.X86.RvInputs
public import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Importing one recovery input into its fixed workspace array -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem load_ok {g : CallGeometry} {s : State} (h : Inputs g s) (i : Fin 3) {j : Nat} (hj : j < nArr) :
    WP isa (load g.n (4 + 2 * i.val) j) s fun t =>
      Inputs g t ∧ Keep g.B g.toGeo.w [j] [] s.mem t.mem ∧
      val32 t.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.buffer (4 + 2 * i.val)).base (g.buffer (4 + 2 * i.val)).len) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have positive := h.inputPositive i
  have bound := h.inputBound i
  have sourceFit := h.inputFit i
  have sourceRead := h.inputRead i
  have apart := h.inputApart i ⟨g.B, g.Z⟩ (by simp [CallGeometry.writes])
  have fits := h.ws.arr_fit hj
  have width : 8 * (g.n + 2) = S g.toGeo.w := by simp only [S, Geo.w, width]; omega
  have nwidth : g.toGeo.w = 2 * g.n + 2 := rfl
  simp only [S] at fits
  unfold load VG.Impl.Rsa.X86.CrtValues.inputArgs
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    ((h.arguments _ (by omega)).readSrc) ((h.arguments _ (by omega)).readSrc)) ?_)
  rintro u ⟨P, C, M, K⟩
  have hu := h.ws.workspace.of_keeps K (by decide)
  change WP isa (VG.Impl.Bignum.X86.loadBE (g.n + 2) (arr g.toGeo.w j)) u _
  refine WP.mono (loadBE_ok hu (by have := h.lower; omega) (by omega)
    positive (by omega) (by rw [P]; exact sourceFit) (by rw [C]; simp [CallGeometry.buffer])
    (by rw [K.2.1, K.2.2, P]; exact sourceRead)
    (by rw [P]; exact apart.sub_right (Offset.sub_base g.B (by omega)))) ?_
  rintro t ⟨value, frame, rest⟩
  rw [M] at value frame
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := (K.mono (by decide)).trans rest
  have full : Outside g.B 16 (g.Z - 16) s.mem t.mem := frame.mono (by have : hdr ≤ arr g.toGeo.w j := Nat.le_add_right _ _; unfold hdr at this; omega) (by omega)
  refine ⟨h.after all (by decide) (by decide) (h.scratchFrame full), ?_, ?_, all⟩
  · exact Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega) (by simp)
  · rw [wordsVal_eq_val32, P] at value
    have width : 2 * (g.n + 2) = g.toGeo.w + 2 := by simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
    rw [width] at value
    exact value
end VG.Proof.Rsa.X86.Recover
