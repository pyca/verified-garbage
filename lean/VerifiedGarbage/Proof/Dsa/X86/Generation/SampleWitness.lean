module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadWitness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessRange
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ForceStoredWitness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleGeometry
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Compose the shared loader, interval check, and forced witness transformation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86

private theorem stored_witness_valid {m : Mem} {base : Addr} {len candidate : Nat}
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (valid : 2 ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off base Layout.witness) len) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off base Layout.witness) len) < candidate - 1) :
    Spec.RsaKeyGen.witness (candidate - 1)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off base Layout.witness) len)) =
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off base Layout.witness) len), true) := by
  have size : (Spec.Rsa.bytesAt m (off base Layout.witness) len).length = len := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have bound := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (off base Layout.witness) len)
  rw [size, VG.Proof.Bignum.pow256_eq] at bound
  simp only [Spec.RsaKeyGen.witness, bits, Nat.mod_eq_of_lt bound, ite_eq_left valid]

theorem sample_witness {s : State} {base : Addr} {bytes n len candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (C : WitnessContext base n candidate s)
    (positive : 0 < n) (upper : n ≤ 48) (lower : 4 ≤ len)
    (length : len ≤ 8 * n) (aligned : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len) :
    WP isa (sampleWitness n len) s fun t =>
      WitnessContext base n candidate t ∧
      wordsVal t.mem base (slot n 5) n =
        (Spec.RsaKeyGen.witness (candidate - 1)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len))).1 ∧
      w32 t.mem base witnessUniform =
        (if (Spec.RsaKeyGen.witness (candidate - 1)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len))).2 then 1 else 0) ∧
      SampleFrame base s t ∧ SamplingFrame base n len s t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have lenBound : len ≤ 384 := by omega
  have loadFit : slot n 5 + 8 * n ≤ Layout.witness := by
    simp only [slot, stride, Layout.witness]; omega
  have slotFrame : slot n 5 + 8 * n ≤ Layout.arithmetic := by
    simp only [slot, stride, Layout.arithmetic]; omega
  have flagFrame : witnessUniform + 4 ≤ Layout.arithmetic := by decide
  have afterBuffer : Layout.witness + len ≤ witnessUniform := by
    unfold Layout.witness witnessUniform Layout.control; omega
  have bufferFit : Layout.witness + len ≤ bytes := by
    have : Layout.witness + len ≤ 40960 := by unfold Layout.witness; omega
    omega
  unfold sampleWitness
  refine WP.seq (WP.mono (load_witness scr capacity C upper lower length aligned)
    fun a ⟨Ca, valueA, Fa, Ka⟩ => ?_)
  have Sa := scr.of_keeps Ka (by decide)
  have bufferA := sample_buffer Fa lenBound (.inl loadFit)
  have frameA := sample_outside Fa slotFrame
  have fineA : SamplingFrame base n len s a :=
    (Fa.frameAt (by simp only [slot, stride]; omega)).mono (by simp)
  refine WP.seq (WP.mono (witness_range Sa capacity Ca positive upper valueA)
    fun b ⟨Cb, _, flagB, zfB, Fb, Kb⟩ => ?_)
  have Kpre : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s b :=
    (Ka.mono (by decide)).trans (Kb.mono (by decide))
  have Sb := scr.of_keeps Kpre (by decide)
  have bufferB := (sample_buffer Fb lenBound (.inr afterBuffer)).trans bufferA
  have frameB := frameA.trans (sample_outside Fb flagFrame)
  have fineB : SamplingFrame base n len s b :=
    fineA.trans ((Fb.frameAt (by decide)).mono (by simp))
  by_cases valid : 2 ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len) < candidate - 1
  · have spec := stored_witness_valid bits valid
    refine WP.ite false (by simpa [eval, valid] using zfB)
      (by intro h; cases h) ?_
    intro _
    apply WP.block_nil
    refine ⟨Cb, ?_, ?_, frameB, fineB, Kpre⟩
    · rw [spec]
      exact (by rw [wordsVal_eq_val32] at valueA ⊢
                exact (Fb.val32 (.inl (by omega)) (by simp only [slot, stride]; omega)).trans valueA)
    · simpa [spec, valid] using flagB
  · refine WP.ite true (by simpa [eval, valid] using zfB) ?_
      (by intro h; cases h)
    intro _
    refine WP.seq (WP.mono (force_stored_witness Sb (by omega) bufferFit bits (by
      rw [bufferB]; exact valid)) fun c ⟨spec, Fc, Kc⟩ => ?_)
    rw [bufferB] at spec
    have Cc := forced_context Cb lenBound Fc Kc
    have Sc := Sb.of_keeps Kc (by decide)
    refine WP.mono (load_witness Sc capacity Cc upper lower length aligned)
      fun t ⟨Ct, valueT, Ft, Kt⟩ => ?_
    refine ⟨Ct, ?_, ?_, frameB.trans ((forced_frame lenBound Fc).trans
      (sample_outside Ft slotFrame)), ?_, Kpre.trans ((Kc.mono (by decide)).trans (Kt.mono (by decide)))⟩
    · rw [spec]
      exact valueT
    · rw [spec]
      have loadFlag := Ft.w32 (d := witnessUniform) (.inr (by
        have : Layout.witness ≤ witnessUniform := by decide
        omega)) (by decide)
      rw [loadFlag, forced_flag lenBound Fc]
      simpa [valid] using flagB
    · exact fineB.trans ((Fc.mono (by simp)).trans
        ((Ft.frameAt (by simp only [slot, stride]; omega)).mono (by simp)))

end VG.Proof.Dsa.X86.Generation
