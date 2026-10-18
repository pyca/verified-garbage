module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputPlan
public import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Framework.Omega

/-! # Normalize every search outcome to the public output and status convention -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem finishOutput_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (expected : Option Spec.Dsa.Params)
    (result : (((W 19 = 0 ∨ W 19 = 3) ∧ expected = none) ∨
      (W 19 = 1 ∧ ∃ a, expected = some a ∧
        Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a))) :
    WP isa Impl.Dsa.AArch64.Generation.finishOutput s fun t =>
      t.gpr .x0 = (if expected.isSome then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        (expected.map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen)).getD
          (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame [⟨p.geo.F, frameBytes⟩, ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧
      Keep (.x0 :: mmRegs) s t := by
  have pn : 0 < p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.AArch64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok h.layout R) fun u ⟨hz, hm, ku⟩ => ?_)
  have mu := h.congr hm ku
  have hwu : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ u.wr := by rw [ku.wr]; exact hw
  rcases result with ⟨h19, he⟩ | ⟨h19, a, he, bytes⟩
  · have hn : W 19 ≠ 1 := by rcases h19 with hh | hh <;> rw [hh] <;> decide
    refine WP.ite false (by exact hz.trans (congrArg some (beq_eq_false_iff_ne.mpr hn)))
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    obtain ⟨Vu, Ru⟩ := mu.rep
    have h6 := mu.slots 6 (by simp [generationSlots])
    have h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    have call := outputZero_ok mu.layout Ru h7 ⟨by omega, by omega⟩
    rw [h6] at call
    refine WP.mono (call hwu o.bound o.apart) fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    exact ⟨hr, bt, by simpa only [hm] using ft, (ku.trans kt).mono (by decide)⟩
  · refine WP.ite true (by apply hz.trans; rw [h19]; rfl)
      (fun _ => ?_) (fun impossible => Bool.noConfusion impossible)
    have bytesu : Spec.Rsa.bytesAt u.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := hm ▸ bytes
    refine WP.mono (output_copy_context mu o hwu _ (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytesu)
      fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    refine ⟨hr, bt, ?_, (ku.trans kt).mono (by decide)⟩
    rw [hm] at ft
    exact ft.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)

end VG.Proof.Dsa.AArch64.Generation
