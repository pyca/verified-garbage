module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
import VerifiedGarbage.Proof.Framework.Offset

/-! # Append a power at the public table cursor using the shared byte copy -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem table_transfer {σ s : State} {base : Addr} {bytes w j : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (hj : 13 ≤ j ∧ j < 27)
    (initial : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (cursor : s.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w j)) :
    WP isa tabTransfer s fun t => Stage base bytes w σ t ∧
      TransferResult s (ptr32 base (arrAt w 6)) (ptr32 base (arrAt w j)) (8 * w) t := by
  have fa := array_fits_bytes hf (show 6 < 28 by decide)
  have fo := array_fits_bytes hf (show j < 28 by omega)
  have nw := h.context.ws.nowrap
  have aa := ptr32_addr (base := base) (d := arrAt w 6) (by omega)
  have ao := ptr32_addr (base := base) (d := arrAt w j) (by omega)
  have h52 : 52 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  unfold tabTransfer
  refine WP.mono (transfer_ok (s := s) (src := ptr32 base (arrAt w 6))
    (dst := ptr32 base (arrAt w j)) (n := 8 * w)
    (setup := arrayPointer .esi aY .edx ++ [.mov .ebx (.mem (sp tableCursor))] ++ width .ecx)
    (by omega) (by omega)
    (by rw [ptr32_toNat (by omega)]; omega) (by rw [ptr32_toNat (by omega)]; omega)
    (by rw [aa]; exact h.context.ws.read (by omega))
    (by rw [ao]; exact h.context.ws.write (by omega))
    (by rw [aa, ao]; exact Offset.disjoint _ (arrays_apart w (by omega : 6 ≠ j)) (by omega) (by omega))
    ?_) ?_
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine arrayPointer_ok (by decide) (by decide) (by decide)
      (by rw [readSrc_sc h.context.ws h52, h.width hf initial]) hu h.context.ws.edi_toNat
      fun s₁ K₁ m₁ p₁ => ?_
    have h₁ := h.of_registers K₁ m₁
    refine wp_movS (by rw [h₁.context.read_sp (by decide), h₁.stack, m₁, cursor]) fun s₂ U₂ _ => ?_
    have h₂ := h₁.of_registers U₂.keeps U₂.mem
    refine width_ok (by rw [readSrc_sc h₂.context.ws h52, h₂.width hf initial]) fun t K₃ m₃ v₃ =>
      WP.block_nil ?_
    refine ⟨((K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (K₃.mono (by decide)),
      by rw [m₃, U₂.mem, m₁], ?_, ?_, v₃⟩
    · rw [K₃.1 .esi (by decide), U₂.other .esi (by decide)]
      exact ptrAt_eq p₁
    · rw [K₃.1 .ebx (by decide), U₂.gpr]
  · intro t result
    have F := result.frame
    rw [ao] at F
    exact ⟨h.after_array result.keeps F (.inr (.inr (.inr ⟨by omega, hj.2⟩))), result⟩

end VG.Proof.MillerRabin.X86
