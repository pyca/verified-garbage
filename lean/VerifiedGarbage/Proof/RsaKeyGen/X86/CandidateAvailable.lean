module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedResult

/-! # Every supported public output length selects its verified native width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Outputs.keepFlags {E : Environment} {status count : Nat} {bytes : List Byte} {s t : State}
    (O : Outputs E status count bytes s) (F : Fupd s t) : Outputs E status count bytes t := by
  unfold Outputs at O ⊢
  rw [F.gpr, F.mem]
  exact O

theorem available_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round) s fun t =>
      FilteredOutputs E (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have bounds := v.width_bounds
  have lengthBound : E.length < 2 ^ 32 := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  have space : 256 ≤ E.size := v.geometry.headerFit
  unfold VG.Impl.RsaKeyGen.X86.Candidate.available VG.Impl.RsaKeyGen.X86.Candidate.width
  refine WP.seq (wp_movS (readSrc_sc I.scratch (d := 4) (by omega)) fun a A _ =>
    wp_shr (by decide) fun b B _ => WP.block_nil ?_)
  have M : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have width : b.gpr .eax = BitVec.ofNat 32 E.width := by
    rw [B.gpr, A.gpr, I.header 1 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    change (E.length % 2 ^ 32) / 8 = E.width % 2 ^ 32
    rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt (by omega : E.width < 2 ^ 32)]
    rfl
  refine WP.seq (WP.mono (dispatch_ok (Q := fun t => FrontOutputs E eBytes pBytes entropy t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t) width (by omega)
    VG.Impl.RsaKeyGen.X86.Candidate.widths ?_ ?_ fun c C => ?_) fun d ⟨front, Fd, Kd⟩ => ?_)
  · exact List.mem_map.mpr ⟨E.width - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro w mem
    obtain ⟨i, index, rfl⟩ := List.mem_map.mp mem
    have bound := List.mem_range.mp index
    omega
  · have Mc : c.mem = s.mem := C.mem.trans M
    have Kc : Keeps [.eax] s c := K.widen (C.keeps [])
    refine WP.mono (sized_front_ok v (I.keepMem v Mc Kc (by decide) (by decide) (C.syms.trans (B.syms.trans A.syms)))
      (by rw [Mc]; exact zeros) enough) fun t ⟨output, F, Kt⟩ => ?_
    rw [Mc] at F
    exact ⟨output, F, (Kc.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  refine WP.seq (wp_cmpS rfl fun e Ee Z => WP.block_nil ?_)
  have Fe : MutableFrame E s.mem e.mem := by rw [Ee.mem]; exact Fd
  have Ke : Keeps WitnessStep.clob s e := Kd.widen (Ee.keeps [])
  unfold FrontOutputs at front
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)
  · rw [close] at front
    simp only [Bool.false_eq_true, ↓reduceIte] at front
    cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
    · rw [composite] at front
      simp only [Bool.false_eq_true, ↓reduceIte] at front
      obtain ⟨De, four⟩ := front
      refine WP.ite true (by change e.zf = _; rw [Z, four]; rfl) (fun _ => ?_) (fun bad => nomatch bad)
      have Dd := De.keepMem v Ee.mem (Ee.keeps []) (by decide) (by decide) Ee.syms
      refine WP.mono (exponent_result_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Dd enough)
        fun t ⟨output, Ft, Kt⟩ => ?_
      exact ⟨by simpa only [FilteredOutputs, SieveOutputs, close, composite, Bool.false_eq_true, ↓reduceIte]
        using output, Fe.trans Ft, Ke.trans Kt⟩
    · rw [composite] at front
      simp only [↓reduceIte] at front
      refine WP.ite false (by change e.zf = _; rw [Z, front.1]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.block_nil ⟨?_, Fe, Ke⟩
      simpa only [FilteredOutputs, SieveOutputs, close, composite, Bool.false_eq_true, ↓reduceIte] using
        front.keepFlags Ee
  · rw [close] at front
    simp only [↓reduceIte] at front
    refine WP.ite false (by change e.zf = _; rw [Z, front.1]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.block_nil ⟨?_, Fe, Ke⟩
    simpa only [FilteredOutputs, close, ↓reduceIte] using front.keepFlags Ee

end VG.Proof.RsaKeyGen.X86.Candidate
