module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSaved
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpCode
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBody
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # The complete candidate restores the native calling convention after every result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem StepOutputs.keep {E : Environment} {entropy : List Byte}
    {result : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand)} {s t : State}
    (R : StepOutputs E entropy result s) (eax : t.gpr .eax = s.gpr .eax) (mem : t.mem = s.mem) :
    StepOutputs E entropy result t := by
  cases result with
  | none => simpa only [StepOutputs, Outputs, eax, mem] using R
  | some pr =>
    obtain ⟨candidate, rest⟩ := pr
    cases candidate <;> simpa only [StepOutputs, Outputs, eax, mem] using R

theorem framed_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : EntryInput E eBytes pBytes entropy (Compact.entered s))
    (fit : 112 ≤ (s.gpr .esp).toNat)
    (returnFar : ∀ r ∈ E.writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) s fun t =>
      abiPreserved s t ∧ StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) t := by
  have savedFit : 16 ≤ (s.gpr .esp).toNat := by omega
  have entrySp := I.arguments.sp
  have inner : NoSp (.seq (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (.block Compact.restoreRegs)) :=
    CandidateNoSp.sequence (CandidateNoSp.body montNoSp roundNoSp montName roundName) (NoSp.of_all (by rfl))
  unfold VG.Impl.RsaKeyGen.X86.Candidate.code
  refine WP.frame (rs := VG.Proof.Mont.X86.Compact.savedRegisters) (by decide) (by decide) (by decide) savedFit inner ?_
  refine WP.seq (WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v I)
    fun t ⟨R, F, K⟩ => ?_)
  have sp : t.gpr .esp = E.p := (K.1 .esp (by unfold bodyClob; decide)).trans entrySp
  have pFit : E.p.toNat + 16 ≤ 2 ^ 32 := by
    rw [← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat savedFit]
    have := (s.gpr .esp).isLt
    omega
  have read (i : Nat) (index : i < 4) : readSrc t (.mem (at_ .esp (4 * i))) = some
      (s.gpr (VG.Proof.Mont.X86.Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (addr E.p (4 * i)) 4
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      have region : below (s.gpr .esp) 16 = ⟨E.p.setWidth 64, 16⟩ := by
        rw [← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
        rfl
      rw [region, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, saved_read v savedFit entrySp F index]
  refine WP.mono (VG.Proof.Mont.X86.Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  have sp' : u.gpr .esp = E.p := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show VG.Proof.Mont.X86.Compact.savedRegisters.length = 4 from rfl,
        VG.Proof.Mont.X86.Compact.popped_four_value, sp', mem]
      exact saved_read v savedFit entrySp F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', ← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact return_read v fit entrySp returnFar F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]

end VG.Proof.RsaKeyGen.X86.Candidate
