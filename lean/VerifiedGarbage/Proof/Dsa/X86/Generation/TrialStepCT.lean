module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialReduce
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialArgsCT

/-! # Early trial rejection depends only on the public candidate's remainder -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen

theorem trialArgs_phase_ct (len entries : Nat) :
    RelCT isa (Two fun p s => p.index < entries ∧ TrialAt len entries p s)
      (.block (trialCheckArgs len)) (Two fun p s => p.index < entries ∧ TrialArgsAt len entries p s) := by
  refine two_post (two_map (fun p : TrialPublic => (⟨p.base, p.table, p.index⟩ : TrialAddressPublic)) ?_
    (trialCheckArgs_ct len)) ?_
  · rintro p t ⟨_, s, _, _, I⟩
    exact ⟨I.context.frame, I.table, I.index⟩
  · rintro p t ⟨hi, s, R, value, I⟩
    refine WP.mono (trialCheckArgs_ok R I.context hi I.source I.table I.index)
      fun u ⟨C, _, si, di, bp, cx⟩ => ?_
    exact ⟨hi, s, R, value, C, si, di, bp, cx⟩

theorem trialReduce_phase_ct (len entries : Nat) :
    RelCT isa (Two fun p s => p.index < entries ∧ TrialArgsAt len entries p s)
      trialReduce (Two TrialReducedAt) := by
  refine two_post ((trialReduce_ct).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨p, ⟨_, a, _, _, _, _, _, bp, cx⟩, ⟨_, b, _, _, _, _, _, bp', cx'⟩⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [bp.trans bp'.symm, cx.trans cx'.symm]
  · rintro p t ⟨hi, s, R, value, C, si, di, bp, cx⟩
    have pf := VG.Proof.RsaKeyGen.tabEntry_facts (by have := R.entriesBound; omega : p.index < 1024)
    have half : 2 * (len / 2) = len := by have := R.lenEven; omega
    refine WP.mono (trialReduce_ok (by omega) (by omega) (by have := R.lenPos; omega)
      (by rw [half]; exact R.lenBound) bp cx si di (by rw [half]; exact R.inputFit)
      (fun i hi => by rw [C.keeps.2.1, C.keeps.2.2]; exact R.inputRead i (by omega)))
      fun u ⟨bx, _, K⟩ => ?_
    refine ⟨C.frame.keeps K (by decide), ?_⟩
    rw [bx, half, C.inputBytes R]
    change BitVec.ofNat 32 (trialValue s p.input len % tabEntry p.index) = _
    rw [value]

theorem trialCheckStep_ct (len entries : Nat) :
    RelCT isa (Two fun p s => p.index < entries ∧ TrialAt len entries p s)
      (trialCheckStep len entries) (fun _ _ => True) := by
  unfold trialCheckStep
  refine RelCT.seq (trialArgs_phase_ct len entries) (RelCT.seq (trialReduce_phase_ct len entries) ?_)
  refine two_taint [.esp, .ebx] ?_ (hc := .seq { regs := .ofList [.esp, .ebx], flags := true } (.block []) (.ite (.block []) (.block []))) (by rfl)
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact BitVec.eq_of_toNat_eq (hs.1.espNat.trans ht.1.espNat.symm)
  · exact hs.2.trans ht.2.symm
end VG.Proof.Dsa.X86.Generation
