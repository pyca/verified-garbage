module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedResult

/-! # Every supported public output length selects its verified native width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem available_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
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
  unfold VG.Impl.RsaKeyGen.X86.Candidate.available
  refine WP.seq (wp_movS (readSrc_sc I.scratch (d := 4) (by omega)) fun a A _ =>
    wp_shr (by decide) fun b B _ => WP.block_nil ?_)
  have M : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Ib := I.keepMem v M K (by decide) (by decide) (B.syms.trans A.syms)
  have width : b.gpr .eax = BitVec.ofNat 32 E.width := by
    rw [B.gpr, A.gpr, I.header 1 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    change (E.length % 2 ^ 32) / 8 = E.width % 2 ^ 32
    rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt (by omega : E.width < 2 ^ 32)]
    rfl
  refine WP.mono (dispatch_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Ib
    (by rw [M]; exact zeros) enough width VG.Impl.RsaKeyGen.X86.Candidate.widths ?_ ?_)
    fun t ⟨output, F, Kt⟩ => ?_
  · exact List.mem_map.mpr ⟨E.width - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro w mem
    obtain ⟨i, index, rfl⟩ := List.mem_map.mp mem
    have bound := List.mem_range.mp index
    omega
  · rw [M] at F
    exact ⟨output, F, (K.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
