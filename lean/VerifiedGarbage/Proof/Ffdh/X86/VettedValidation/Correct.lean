module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Recognize
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Fallback
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Exact certificate success and complete general validation share the unchanged API contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem test_result {s u : State} (h : Result s u) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) u fun t =>
      Result s t ∧ t.zf = some (recognized s == 0) := by
  refine wp_test fun t T zero => WP.block_nil ⟨?_, ?_⟩
  · exact ⟨h.tracking.after T.mem (T.keeps []) (by decide),
      by rw [T.gpr]; exact h.value, fun r hr => by rw [T.gpr]; exact h.regs r hr⟩
  · simpa only [BitVec.and_self, h.value] using zero

private theorem abi_trans {s t u : State} (a : abiPreserved s t) (b : abiPreserved t u) :
    abiPreserved s u := by
  have ret := b.2
  rw [a.1 .esp (by decide)] at ret
  exact ⟨fun r hr => (b.1 r hr).trans (a.1 r hr), ret.trans a.2⟩

theorem correct (s : State) (h : contract.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ contract.post s t := by
  rw [code, WP.seq_iff]
  refine WP.mono (recognize_ok h) ?_
  intro t result
  rw [WP.seq_iff]
  refine WP.mono (test_result result) ?_
  rintro u ⟨tested, zero⟩
  refine WP.ite (!(recognized s == 0)) (by simp only [eval, zero, Option.map_some]) ?_ ?_
  · intro hit
    have nonzero : recognized s ≠ 0 := by simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using hit
    have raw : recognizeList groups (arg s 2).toNat (domain s) ≠ 0 := by
      intro bad
      exact nonzero (by unfold recognized; rw [bad]; rfl)
    have len : (domain s).length = (arg s 1).toNat := by
      simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    have shape : (domain s).length = 2 * (arg s 2).toNat ∨ (domain s).length = 3 * (arg s 2).toNat := by
      rw [len]; exact (geometry h).dLen
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups (fun _ hg => hg) shape raw
    refine wp_movi fun w W => WP.block_nil ⟨?_, ?_⟩
    · have kept := tested.abi h
      exact ⟨fun r hr => (W.other r (by revert r; decide)).trans (kept.1 r hr),
        by rw [W.mem]; exact kept.2⟩
    · change (Spec.Ffdh.checkDomainContract abi 172).post s w
      sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes]
      rw [BitVec.setWidth_append_eq_right, W.gpr]
      change 1 = if Spec.Ffdh.domainValid (arg s 2).toNat (domain s) then 1 else 0
      rw [valid]; rfl
  · intro _
    obtain ⟨tr, w, run, kept, post⟩ := fallback_run (tested.tracking.pre h)
    refine ⟨tr, w, run, abi_trans (tested.abi h) kept, ?_⟩
    change (Spec.Ffdh.checkDomainContract abi 172).post s w
    sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes] at post ⊢
    rw [BitVec.setWidth_append_eq_right] at post ⊢
    change (w.gpr .eax).toNat = if Spec.Ffdh.domainValid (arg u 2).toNat (domain u) then 1 else 0 at post
    change (w.gpr .eax).toNat = if Spec.Ffdh.domainValid (arg s 2).toNat (domain s) then 1 else 0
    rw [tested.tracking.args h 2 (by decide), tested.tracking.domain_eq h] at post
    exact post

end VG.Proof.Ffdh.X86.VettedValidation
