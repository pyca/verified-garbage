module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Code
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! # Exponent filtering retains all live candidate inputs and the consumed entropy count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem exponent_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.ExponentRt.code s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) = 1)).toNat ∧
      val32 t.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1 ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have fit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega
  have stack : (s.gpr .esp).toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 40 ≤ (s.gpr .esp).toNat := by
    rw [D.input.stack]
    rcases v.workspaceStack with h | h <;> omega
  have outLen : s.mem.readW (off E.base 4) 32 = BitVec.ofNat 32 (8 * E.width) := by
    rw [D.input.header 1 (by decide), v.length_eq]; rfl
  refine WP.mono_syms (ExponentRt.code_ok D.input.scratch v.width_bounds.1 v.width_bounds.2
    (v.slotFit (by decide : 5 < 28)) D.candidate (by have := candidate_large v entropy; omega) (candidate_odd v entropy)
    D.input.exponent_eq (D.input.exponentLength_eq v) (by have := v.exponentLength; omega) v.exponentLength.2
    v.exponentFit D.input.memory.exponentRead (v.readWorkspace List.mem_cons_self) fit stack outLen)
    fun t ⟨result, value, saved, W, F, K⟩ syms => ?_
  rw [D.input.memory.exponentBytes] at result
  rw [D.input.stack] at F
  have frame : WorkFrame E s.mem t.mem := VG.X86.Frame.below_mono (wr := [E.workspaceRegion]) (a := 20) F (by decide) v.low
  have low : ∀ r ∈ ExponentRt.ranges E.width, 48 ≤ r.1 := by
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact Nat.le_trans (by decide) (E.slotHeader 5)
      · decide
    · rcases List.mem_append.mp mem with mem | mem
      · have := ExponentFilter.gcd_ranges_class mem; omega
      · obtain rfl := List.mem_singleton.mp mem
        exact Nat.le_trans (by decide) (E.slotHeader 0)
  have I := D.input.keepWorkspace v K (by decide) (by decide) frame W low (by rw [syms])
  have used : t.mem.readW (off E.geometry.W 152) 32 = s.mem.readW (off E.geometry.W 152) 32 :=
    W.read32 (by change 152 + 4 ≤ E.size; omega) (by
      intro r mem
      rcases List.mem_append.mp mem with mem | mem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact Or.inl (by have := E.slotHeader 5; omega)
        · exact Or.inr (by decide)
      · exact ExponentFilter.ranges_apart (by right; constructor <;> decide) mem)
  exact ⟨⟨I, value, (congrArg BitVec.toNat used).trans D.used, (frame.output v).trans D.zeros⟩,
    result, saved, frame, K⟩

end VG.Proof.RsaKeyGen.X86.Candidate
