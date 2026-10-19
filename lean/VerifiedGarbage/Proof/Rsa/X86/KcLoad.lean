module

public import VerifiedGarbage.Proof.Rsa.X86.KcInputs
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! # Importing one CRT input into its fixed workspace array -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Rsa.X86.CrtValues (load inputArgs)
open VG.Proof.Rsa.X86.Keys

theorem Inputs.scratchFrame {g : CallGeometry} {s : State} {m : Mem} (h : Inputs g s)
    (frame : Outside g.base 0 g.size s.mem m) : Frame g.writes s.mem m := by
  have fit := h.ws.workspace.nowrap
  have f := outside_frame frame (by omega)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    f.mono (rs' := g.writes) (by simp [CallGeometry.writes, off])

theorem load_ok {g : CallGeometry} {s : State} (h : Inputs g s) (i : Nat) (hi : 2 * i < scratchArg g.full) {j : Nat} (hj : j < nArr) :
    WP isa (load g.n (2 * i) j) s fun t =>
      Inputs g t ∧ Keep g.base (2 * g.n) [j] [] s.mem t.mem ∧
      num t.mem g.base (2 * g.n) j =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.buffer (2 * i)).base (g.buffer (2 * i)).len) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have positive := h.inputPositive i hi
  have bound := h.inputBound i hi
  have sourceFit := h.inputFit i hi
  have sourceRead := h.inputRead i hi
  have apart := h.inputApart i hi ⟨g.base, g.size⟩ (by simp [CallGeometry.writes])
  have fits := h.ws.arr_fit hj
  simp only [S] at fits
  unfold load inputArgs
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    ((h.arguments _ (by omega)).readSrc) ((h.arguments _ (by omega)).readSrc)) ?_)
  rintro u ⟨P, C, M, K⟩
  have hu := h.ws.workspace.of_keeps K (by decide)
  change WP isa (VG.Impl.Bignum.X86.loadBE g.n (arr (2 * g.n) j)) u _
  refine WP.mono (loadBE_ok hu (by have := h.lower; omega) (by omega)
    positive bound (by rw [P]; exact sourceFit) (by rw [C]; simp [CallGeometry.buffer])
    (by rw [K.2.1, K.2.2, P]; exact sourceRead)
    (by rw [P]; exact apart.sub_right (Offset.sub_base g.base (by omega)))) ?_
  rintro t ⟨value, frame, rest⟩
  rw [M] at value frame
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := (K.mono (by decide)).trans rest
  have full : Outside g.base 0 g.size s.mem t.mem := frame.mono (by omega) (by omega)
  refine ⟨h.after all (by decide) (by decide) (h.scratchFrame full), ?_, ?_, all⟩
  · exact Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega) (by simp)
  · rw [wordsVal_eq_val32, P] at value
    exact value
end VG.Proof.Rsa.X86.KeyCheck
