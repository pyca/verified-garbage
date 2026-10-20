module

public import VerifiedGarbage.Proof.Bignum.X86.CrtImportFrame
public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
import VerifiedGarbage.Proof.Bignum.X86.CrtImportStep
import VerifiedGarbage.Proof.Bignum.X86.CrtSlotFrame
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout

/-! # All private CRT byte slices are imported without changing the call header -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

theorem importComponents_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s) :
    WP isa (importComponents (Spec.Rsa.modulusWords len)) s fun t =>
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) 9) (2 * Spec.Rsa.modulusWords len) = componentValue s.mem args 2 ∧
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) 15) (Spec.Rsa.modulusWords len) = componentValue s.mem args 4 ∧
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) 10) (Spec.Rsa.modulusWords len) = componentValue s.mem args 6 ∧
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) 11) (Spec.Rsa.modulusWords len) = componentValue s.mem args 8 ∧
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) 12) (Spec.Rsa.modulusWords len) = componentValue s.mem args 10 ∧
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) 13) (Spec.Rsa.modulusWords len) = componentValue s.mem args 12 ∧
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) 14) (Spec.Rsa.modulusWords len) = componentValue s.mem args 14 ∧
      Outside base 64 (bytes - 64) s.mem t.mem ∧ Inputs base bytes len args t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let n := Spec.Rsa.modulusWords len
  have fit : size n ≤ 2 ^ 64 := by have := h.scratch.nowrap; have H : size n ≤ bytes := h.space; omega
  have space : size n ≤ bytes := h.space
  have head : 64 ≤ bytes := by have := size_eq n; omega
  unfold importComponents
  refine WP.seq (WP.mono (importStep_ok h (i := 2) (dst := 9) (k := 2 * n) (by decide) (by decide) (by omega) (by omega))
    fun s0 ⟨V0, O0, H0, K0⟩ => ?_)
  have F0 := import_frame O0 (by decide) (by omega) space
  have B0 := h.component_keep (F0.mono (by omega) (by omega))
  refine WP.seq (WP.mono (importStep_ok H0 (i := 4) (dst := 15) (k := n) (by decide) (by decide) (by omega) (by omega))
    fun s1 ⟨V1, O1, H1, K1⟩ => ?_)
  have F1 := import_frame O1 (by decide) (by omega) space
  have B1 := H0.component_keep (F1.mono (by omega) (by omega))
  refine WP.seq (WP.mono (importStep_ok H1 (i := 6) (dst := 10) (k := n) (by decide) (by decide) (by omega) (by omega))
    fun s2 ⟨V2, O2, H2, K2⟩ => ?_)
  have F2 := import_frame O2 (by decide) (by omega) space
  have B2 := H1.component_keep (F2.mono (by omega) (by omega))
  refine WP.seq (WP.mono (importStep_ok H2 (i := 8) (dst := 11) (k := n) (by decide) (by decide) (by omega) (by omega))
    fun s3 ⟨V3, O3, H3, K3⟩ => ?_)
  have F3 := import_frame O3 (by decide) (by omega) space
  have B3 := H2.component_keep (F3.mono (by omega) (by omega))
  refine WP.seq (WP.mono (importStep_ok H3 (i := 10) (dst := 12) (k := n) (by decide) (by decide) (by omega) (by omega))
    fun s4 ⟨V4, O4, H4, K4⟩ => ?_)
  have F4 := import_frame O4 (by decide) (by omega) space
  have B4 := H3.component_keep (F4.mono (by omega) (by omega))
  refine WP.seq (WP.mono (importStep_ok H4 (i := 12) (dst := 13) (k := n) (by decide) (by decide) (by omega) (by omega))
    fun s5 ⟨V5, O5, H5, K5⟩ => ?_)
  have F5 := import_frame O5 (by decide) (by omega) space
  have B5 := H4.component_keep (F5.mono (by omega) (by omega))
  refine WP.mono (importStep_ok H5 (i := 14) (dst := 14) (k := n) (by decide) (by decide) (by omega) (by omega))
    fun s6 ⟨V6, O6, H6, K6⟩ => ?_
  have F6 := import_frame O6 (by decide) (by omega) space
  have B6 := H5.component_keep (F6.mono (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H6, K0.trans (K1.trans (K2.trans (K3.trans (K4.trans (K5.trans K6)))))⟩
  · rw [slot_value O6 (i := 9) (k := 2 * n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O5 (i := 9) (k := 2 * n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O4 (i := 9) (k := 2 * n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O3 (i := 9) (k := 2 * n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O2 (i := 9) (k := 2 * n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O1 (i := 9) (k := 2 * n) (by decide) (by decide) (by omega) (by omega) fit, V0]
    change componentValue s.mem args 2 = _
    rfl
  · rw [slot_value O6 (i := 15) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O5 (i := 15) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O4 (i := 15) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O3 (i := 15) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O2 (i := 15) (k := n) (by decide) (by decide) (by omega) (by omega) fit, V1]
    change componentValue s0.mem args 4 = _
    rw [B0 4 (by decide)]
  · rw [slot_value O6 (i := 10) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O5 (i := 10) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O4 (i := 10) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O3 (i := 10) (k := n) (by decide) (by decide) (by omega) (by omega) fit, V2]
    change componentValue s1.mem args 6 = _
    rw [B1 6 (by decide), B0 6 (by decide)]
  · rw [slot_value O6 (i := 11) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O5 (i := 11) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O4 (i := 11) (k := n) (by decide) (by decide) (by omega) (by omega) fit, V3]
    change componentValue s2.mem args 8 = _
    rw [B2 8 (by decide), B1 8 (by decide), B0 8 (by decide)]
  · rw [slot_value O6 (i := 12) (k := n) (by decide) (by decide) (by omega) (by omega) fit, slot_value O5 (i := 12) (k := n) (by decide) (by decide) (by omega) (by omega) fit, V4]
    change componentValue s3.mem args 10 = _
    rw [B3 10 (by decide), B2 10 (by decide), B1 10 (by decide), B0 10 (by decide)]
  · rw [slot_value O6 (i := 13) (k := n) (by decide) (by decide) (by omega) (by omega) fit, V5]
    change componentValue s4.mem args 12 = _
    rw [B4 12 (by decide), B3 12 (by decide), B2 12 (by decide), B1 12 (by decide), B0 12 (by decide)]
  · rw [V6]
    change componentValue s5.mem args 14 = _
    rw [B5 14 (by decide), B4 14 (by decide), B3 14 (by decide), B2 14 (by decide), B1 14 (by decide), B0 14 (by decide)]
  · exact F0.trans (F1.trans (F2.trans (F3.trans (F4.trans (F5.trans F6)))))

end VG.Proof.Bignum.X86.Crt
