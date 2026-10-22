module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFilter
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTable
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset

/-! Initialize the existing packed table and filter one full-width DSA candidate. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.RsaKeyGen

theorem candidate_trial {s : State} {base : Addr} {bytes n candidate bits : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (positive : 0 < n) (upper : n ≤ 48)
    (modulus : wordsVal s.mem base (slot n 0) n = candidate) (large : 8161 < candidate)
    (policy : 1024 < bits ↔ 16 < n) :
    WP isa (candidateTrial n) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite bits candidate).toNat ∧
      Frame [⟨off base trialTableOffset, 2048⟩, below (s.gpr .esp) 40] s.mem t.mem ∧
      Keeps trialCallerClob s t := by
  have countBound : trialWordCount n ≤ 512 := by unfold trialWordCount; split <;> decide
  have tableFits : trialTableOffset + 4 * trialWordCount n ≤ bytes := by unfold trialTableOffset; omega
  unfold candidateTrial
  refine WP.seq (WP.mono (trial_table (offset := trialTableOffset) scr (trialWordCount n) countBound tableFits)
    fun a ⟨values, F, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  have Ra : CallRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact room
  have candidateA : wordsVal a.mem base (slot n 0) n = candidate := by
    rw [wordsVal_eq_val32, F.val32 (.inl (by simp only [slot, stride, trialTableOffset]; omega))
      (by simp only [slot, stride]; omega), ← wordsVal_eq_val32]
    exact modulus
  have table : ∀ i < trialWordCount n, a.mem.readW (off base (trialTableOffset + 4 * i)) 32 =
      BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabWord32 i) := by
    intro i hi
    apply BitVec.eq_of_toNat_eq
    change w32 a.mem base (trialTableOffset + 4 * i) = _
    rw [values i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (tabWord32_lt (Nat.lt_of_lt_of_le hi countBound))]
  refine WP.mono (trial_filter Sa capacity Ra positive upper candidateA large policy table)
    fun t ⟨value, Ft, Kt⟩ => ?_
  have first : Frame [⟨off base trialTableOffset, 2048⟩, below (s.gpr .esp) 40] s.mem a.mem := by
    apply (F.frameAt (by unfold trialTableOffset; omega)).sub
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact ⟨⟨off base trialTableOffset, 2048⟩, by simp, Region.sub_prefix (by omega)⟩
  have last : Frame [⟨off base trialTableOffset, 2048⟩, below (s.gpr .esp) 40] a.mem t.mem := by
    rw [K.1 .esp (by decide)] at Ft
    exact Ft.mono (by simp)
  exact ⟨value, first.trans last, (K.mono (by decide)).trans Kt⟩

end VG.Proof.Dsa.X86.Generation
