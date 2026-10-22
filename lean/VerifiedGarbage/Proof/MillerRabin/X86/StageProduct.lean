module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Product
public import VerifiedGarbage.Proof.MillerRabin.Math

/-! # The shared Montgomery call preserves the round invariant -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt)

namespace Stage

theorem product_frame {σ s : State} {base : Addr} {bytes w o : Nat} {m' : Mem}
    (h : Stage base bytes w σ s)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27))
    (F : Frame [⟨off base (arrAt w o), 8 * w⟩,
      ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
      below (s.gpr .esp) 40] s.mem m') : Frame (stageAreas base w (σ.gpr .esp)) s.mem m' := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · obtain ⟨p, hp, sub⟩ := mutable_array mutable base
    exact ⟨_, workspace_member hp, sub⟩
  · exact ⟨⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
      workspace_member (p := (scratch w, Spec.Rsa.MontMul.scratchBytes w))
        (by simp only [workingRanges, List.mem_cons, true_or]), fun _ hc => hc⟩
  · refine ⟨below (σ.gpr .esp) 40, List.mem_append_right _ (by simp), ?_⟩
    rw [h.stack]
    exact fun _ hc => hc

theorem product {σ s : State} {base : Addr} {bytes w o a b : Nat} {len : BitVec 32}
    (h : Stage base bytes w σ s) (size : bytes = len.toNat * 8)
    (hw : 4 ≤ w) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27))
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (length : σ.mem.readW (off (byteAddr (σ.gpr .esp)) VG.Impl.MillerRabin.X86.savedLength) 32 = len)
    (inverse : (val32 σ.mem base 256 (2 * w) * w32 σ.mem base 56 + 1) % 2 ^ 32 = 0)
    (bLt : val32 s.mem base (arrAt w b) (2 * w) < val32 σ.mem base 256 (2 * w)) :
    WP isa (VG.Impl.MillerRabin.X86.product o a b) s fun t =>
      Stage base bytes w σ t ∧
      val32 t.mem base (arrAt w o) (2 * w) < val32 σ.mem base 256 (2 * w) ∧
      val32 t.mem base (arrAt w o) (2 * w) * 2 ^ (64 * w) % val32 σ.mem base 256 (2 * w) =
        val32 s.mem base (arrAt w a) (2 * w) * val32 s.mem base (arrAt w b) (2 * w) %
          val32 σ.mem base 256 (2 * w) ∧
      Keeps [.eax, .ecx, .edx] s t ∧
      Frame [⟨off base (arrAt w o), 8 * w⟩, ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
        below (s.gpr .esp) 40] s.mem t.mem := by
  have modulus := h.modulus_constant hw hf
  have inv : (val32 s.mem base 256 (2 * w) * w32 s.mem base 56 + 1) % 2 ^ 32 = 0 := by
    rw [modulus, h.inverse_constant hf]
    exact inverse
  refine WP.mono (product_ok h.context.ws size h.room h.context.stackFit hw hu hf ho ha hb
    (h.width hf width) (h.length hf length) inv (by rw [modulus]; exact bLt)) ?_
  rintro t ⟨saved, rd, wr, frame, bound, value⟩
  have K : Keeps [.eax, .ecx, .edx] s t := ⟨by
    intro r hr
    apply saved
    cases r <;> simp_all [calleeSaved], rd, wr⟩
  rw [modulus] at bound value
  exact ⟨h.after K (h.product_frame mutable frame), bound, value, K, frame⟩

/-- Reuse the target-independent Montgomery arithmetic from the ARM round. -/
theorem product_value {σ s : State} {base : Addr} {bytes w o a b : Nat} {len : BitVec 32}
    (h : Stage base bytes w σ s) (size : bytes = len.toNat * 8)
    (hw : 4 ≤ w) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27))
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (length : σ.mem.readW (off (byteAddr (σ.gpr .esp)) VG.Impl.MillerRabin.X86.savedLength) 32 = len)
    (inverse : (val32 σ.mem base 256 (2 * w) * w32 σ.mem base 56 + 1) % 2 ^ 32 = 0)
    (odd : val32 σ.mem base 256 (2 * w) % 2 = 1)
    (bLt : val32 s.mem base (arrAt w b) (2 * w) < val32 σ.mem base 256 (2 * w)) :
    WP isa (VG.Impl.MillerRabin.X86.product o a b) s fun t =>
      val32 t.mem base (arrAt w o) (2 * w) =
        VG.Proof.MillerRabin.Math.mm (val32 σ.mem base 256 (2 * w)) w
          (val32 s.mem base (arrAt w a) (2 * w)) (val32 s.mem base (arrAt w b) (2 * w)) ∧
      Stage base bytes w σ t ∧ Keeps [.eax, .ecx, .edx] s t ∧
      Frame [⟨off base (arrAt w o), 8 * w⟩, ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
        below (s.gpr .esp) 40] s.mem t.mem := by
  refine WP.mono (h.product size hw hu hf ho ha hb mutable width length inverse bLt) ?_
  rintro t ⟨stage, bound, congruence, keeps, frame⟩
  exact ⟨VG.Proof.MillerRabin.Math.mm_eq odd bound congruence, stage, keeps, frame⟩

end Stage
end VG.Proof.MillerRabin.X86
