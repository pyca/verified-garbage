module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Finish
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.MillerRabin.Contract

import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.NoSp
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Test
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Load
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Memory
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
/-! # The four saved registers and the return address survive the test -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ProbablePrime/Body.lean`, which only this module imported.
section

/-! # Trial division, then the blinded loop -/

section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86
open VG.Impl.Dsa.X86.ProbablePrime

theorem used_tail {E : Environment} (v : E.Valid) {m m' : Mem} (F : Frame [E.usedRegion] m m') :
    Tail E m m' := by
  intro i _ hi
  apply F
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  intro contains
  have fit := v.workspaceFit
  exact v.usedWorkspace _ contains (Offset.contains_base E.base (by omega) (by omega))

theorem sieved_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (sieved E.bits montName mont roundName round) s fun t =>
      Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ MutableFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps WitnessStep.clob s t := by
  have shape := candidate_shape odd length (by have := v.bits.low; omega)
  have big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega)
  unfold sieved
  refine WP.seq (WP.mono (sieve_ok v L (by omega)) fun a ⟨La, flag, Wa, Ta, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Candidate.cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  obtain ⟨Lb, Wb, Tb⟩ := La.keepStack v (by rw [B.mem]; exact Frame.refl _ _) (B.keeps []) (by decide) (by decide)
    (by rw [B.syms])
  have Kb : Keeps WitnessStep.clob s b := (Ka.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  have Mb : MutableFrame E s.mem b.mem := (Wa.trans Wb).mutable
  have Tsb : Tail E s.mem b.mem := Ta.trans Tb
  have same : Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c = Spec.RsaKeyGen.obviouslyComposite E.bits c :=
    obviouslyComposite_eq v.bits c
  rw [same] at cond
  cases composite : Spec.RsaKeyGen.obviouslyComposite E.bits c
  · refine WP.ite false (by rw [cond, composite]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Lb odd length)
      fun t ⟨out, Mt, Tt, Kt⟩ => ?_
    rw [← probablePrime_eq v entropy odd length composite] at out
    exact ⟨out, Mb.trans Mt, Tsb.trans Tt, Kb.trans Kt⟩
  · refine WP.ite true (by rw [cond, composite]) (fun _ => ?_) (fun bad => nomatch bad)
    have result : Spec.Dsa.probablePrime c entropy = some (false, entropy) := by
      have three : (c == 3) = false := by rw [beq_eq_false_iff_ne]; omega
      unfold Spec.Dsa.probablePrime
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by rw [three]; decide), length,
        composite]
      rfl
    refine WP.mono (CandidateFinish.used_ok (status := 2) Lb.input.scratch (by have := v.header; omega)
      Lb.input.memory.usedWrite Lb.input.usedPtr rfl) fun t ⟨eax, mem, O, Kt⟩ => ?_
    have F := used_frame O
    refine ⟨⟨?_, ?_⟩, Mb.trans (MutableFrame.of_used F), Tsb.trans (used_tail v F),
      Kb.trans (Kt.mono (by decide))⟩
    · rw [eax, result]; rfl
    · rw [mem]
      refine used_outputs (fun _ rest same => ?_)
      rw [result] at same
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      rw [L.input.memory.entropyLength, Nat.sub_self]
      change w32 b.mem E.base 152 = 0
      exact Lb.count

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : EntryInput E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (body E.bits montName mont roundName round) s fun t =>
      Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ MutableFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps bodyClob s t := by
  unfold body
  refine WP.seq (WP.mono (enter_ok v I) fun a ⟨Ia, count, O, Ka⟩ => ?_)
  have Wa := v.work_of_outside O (by have := v.header; omega)
  have Ta := v.tail_of_outside O (by have := v.scratchLow; omega)
  refine WP.seq (WP.mono (load_ok v Ia count odd) fun b ⟨Lb, Wb, Tb, Kb⟩ => ?_)
  refine WP.mono (sieved_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Lb odd length)
    fun t ⟨out, Mt, Tt, Kt⟩ => ?_
  exact ⟨out, (Wa.trans Wb).mutable.trans Mt, (Ta.trans Tb).trans Tt,
    ((Ka.mono (by unfold bodyClob; decide)).trans (Kb.mono (by unfold bodyClob; decide))).trans
      (Kt.mono (by unfold WitnessStep.clob bodyClob; decide))⟩

end VG.Proof.Dsa.X86.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem saved_stack_far {E : Environment} (v : E.Valid) :
    (⟨E.p.setWidth 64, 16⟩ : Region).Disjoint (below E.p 136) := by
  unfold below
  rw [Taint.sub_setWidth v.low]
  exact Offset.base_disjoint_below _ (by decide)

theorem pFit {E : Environment} {s : State} (fit : 16 ≤ (s.gpr .esp).toNat)
    (sp : (Compact.entered s).gpr .esp = E.p) : E.p.toNat + 16 ≤ 2 ^ 32 := by
  rw [← sp, Compact.entered, pushed_esp]
  change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
  rw [sub_toNat fit]
  have := (s.gpr .esp).isLt
  omega

theorem saved_read {E : Environment} (v : E.Valid) {s t : State}
    (fit : 16 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (F : MutableFrame E (Compact.entered s).mem t.mem) {i : Nat} (index : i < 4) :
    t.mem.readW (addr E.p (4 * i)) 32 = s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have fitP := pFit fit sp
  have same := F.readW (r := (⟨E.p.setWidth 64, 16⟩ : Region)) (a := addr E.p (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega)) (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact (v.savedFar _ List.mem_cons_self).symm
      · exact saved_stack_far v
      · exact (v.savedFar _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).symm)
    (by decide)
  have word := pushed_word (rs := Compact.savedRegisters) (by decide) fit index
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [sp] at word
  exact same.trans word

theorem return_read {E : Environment} (_ : E.Valid) {s t : State}
    (fit : 152 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (returnFar : ∀ r ∈ [E.workspaceRegion, E.usedRegion], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (F : MutableFrame E (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have outside : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 152) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  have inner : (below E.p 136).Sub (below (s.gpr .esp) 152) := by
    rw [← sp, Compact.entered, pushed_esp]
    exact below_inner (by decide) fit
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4) (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact returnFar _ List.mem_cons_self
    · exact outside.sub_right inner
    · exact returnFar _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by decide)
  have pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) (by change 16 ≤ _; omega)
  exact same.trans (pushed.readW (Region.contains_self _ _) (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem
    exact outside.sub_right (below_sub (by decide) fit)) (by decide))

theorem Outputs.keep {E : Environment} {res : Option (Bool × Spec.RsaKeyGen.Rand)} {s t : State}
    (R : Outputs E res s) (eax : t.gpr .eax = s.gpr .eax) (mem : t.mem = s.mem) : Outputs E res t := by
  unfold Outputs at *
  rw [eax, mem]
  exact R

theorem framed_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : EntryInput E c entropy (Compact.entered s)) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits)
    (fit : 152 ≤ (s.gpr .esp).toNat)
    (returnFar : ∀ r ∈ [E.workspaceRegion, E.usedRegion], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r) :
    WP isa (VG.Impl.Dsa.X86.ProbablePrime.code E.bits montName mont roundName round) s fun t =>
      abiPreserved s t ∧ Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ Tail E s.mem t.mem := by
  have savedFit : 16 ≤ (s.gpr .esp).toNat := by omega
  have entrySp := I.sp
  have inner : NoSp (.seq (VG.Impl.Dsa.X86.ProbablePrime.body E.bits montName mont roundName round)
      (.block Compact.restoreRegs)) :=
    VG.Proof.RsaKeyGen.X86.CandidateNoSp.sequence (body_noSp montNoSp roundNoSp E.bits montName roundName)
      (NoSp.of_all (by rfl))
  have pushedTail : Tail E s.mem (Compact.entered s).mem := by
    have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) savedFit
    intro i _ hi
    apply F
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    have region : below (s.gpr .esp) (4 * Compact.savedRegisters.length) = ⟨E.p.setWidth 64, 16⟩ := by
      rw [← entrySp, Compact.entered, pushed_esp]
      rfl
    rw [region]
    intro contains
    have fitW := v.workspaceFit
    exact v.savedFar _ List.mem_cons_self _ (Offset.contains_base E.base (by omega) (by omega)) contains
  unfold VG.Impl.Dsa.X86.ProbablePrime.code
  refine WP.frame (rs := Compact.savedRegisters) (by decide) (by decide) (by decide) savedFit inner ?_
  refine WP.seq (WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v I odd length)
    fun t ⟨R, F, T, K⟩ => ?_)
  have sp : t.gpr .esp = E.p := (K.1 .esp (by unfold bodyClob; decide)).trans entrySp
  have fitP := pFit savedFit entrySp
  have read (i : Nat) (index : i < 4) : readSrc t (.mem (at_ .esp (4 * i))) = some
      (s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (addr E.p (4 * i)) 4
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      have region : below (s.gpr .esp) 16 = ⟨E.p.setWidth 64, 16⟩ := by
        rw [← entrySp, Compact.entered, pushed_esp]
        rfl
      rw [region, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, saved_read v savedFit entrySp F index]
  refine WP.mono (Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  have sp' : u.gpr .esp = E.p := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show Compact.savedRegisters.length = 4 from rfl, Compact.popped_four_value, sp', mem]
      exact saved_read v savedFit entrySp F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', ← entrySp, Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact return_read v fit entrySp returnFar F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]
  · rw [popped_mem, mem]
    exact pushedTail.trans T

end VG.Proof.Dsa.X86.ProbablePrime
