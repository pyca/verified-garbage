module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Fallback
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Restore
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.State
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Recognize

/-! Recognition success is certified; every miss retains the complete selected validator. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

def emittedCode (v : RoundImpl) : Prog isa := code (CheckDomain.domainCode v)
def recognized (s : State) : BitVec 64 :=
  BitVec.ofNat 64 (recognizeList groups (s.gpr .rdx).toNat (CheckDomain.cdDom s))

theorem test_result {s t : State} (h : Result s t) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) t fun u =>
      Result s u ∧ u.zf = some (recognized s == 0) := by
  refine WP.mono_mx (by decide +kernel)
    (WP.keep [.rax] (Q := fun u => u.gpr .rax = t.gpr .rax ∧
      u.zf = some (t.gpr .rax == 0) ∧ u.mem = t.mem)
      (by xrun [BitVec.and_self]) rfl) ?_
  rintro u ⟨⟨value, zero, mem⟩, rest⟩ mxcsr
  have total : Keep allClobbers s u := (h.keep.trans rest).mono (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · have same : r = .rax := by simpa using hr
      subst r
      decide)
  refine ⟨⟨value.trans h.value, h.context.after mem (rest.mono (by decide)),
    mem.trans h.mem, total, mxcsr.trans h.mxcsr⟩, ?_⟩
  rw [zero, h.value]
  rfl

private theorem post_shared {s t : State} (h : CheckDomain.cdPost s t) : contract.post s t := by
  change (Spec.Ffdh.checkDomainContract abi 8).post s t
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq]
  exact h

private theorem post_native {s t : State} (h : (Spec.Ffdh.checkDomainContract abi 8).post s t) :
    CheckDomain.cdPost s t := by
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, List.append_eq] at h
  exact h

private theorem abi_trans {s t u : State} (a : abiPreserved s t) (b : abiPreserved t u) :
    abiPreserved s u := by
  have ret := b.2.1
  rw [a.1 .rsp (by decide)] at ret
  exact ⟨fun r hr => (b.1 r hr).trans (a.1 r hr), ret.trans a.2.1, b.2.2.trans a.2.2⟩

theorem correct (v : RoundImpl) (s : State) (hs : contract.pre s) :
    WP isa (emittedCode v) s fun t => abiPreserved s t ∧ contract.post s t := by
  have g := geometry hs
  rw [emittedCode, code, WP.seq_iff]
  refine WP.mono (recognize_ok g) ?_
  intro t result
  rw [WP.seq_iff]
  refine WP.mono (test_result result) ?_
  rintro u ⟨tested, zero⟩
  refine WP.ite (!(recognized s == 0)) (by simp only [eval, zero, Option.map_some]) ?_ ?_
  · intro hit
    have nonzero : recognized s ≠ 0 := by simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using hit
    have raw : recognizeList groups (s.gpr .rdx).toNat (CheckDomain.cdDom s) ≠ 0 := by
      intro bad
      exact nonzero (by unfold recognized; rw [bad]; rfl)
    have shape : (CheckDomain.cdDom s).length = 2 * (s.gpr .rdx).toNat ∨
        (CheckDomain.cdDom s).length = 3 * (s.gpr .rdx).toNat := by
      simpa only [CheckDomain.cdDom, Spec.Rsa.bytesAt, List.length_map, List.length_range] using g.shape
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups (fun _ hg => hg) shape raw
    refine WP.mono_mx (by decide +kernel) (return_ok u 1 (by decide)) ?_
    rintro w ⟨value, mem, rest⟩ mxcsr
    have total : Keep allClobbers s w := (tested.keep.trans rest).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · exact List.mem_cons_of_mem _ hr)
    refine ⟨⟨fun r hr => total.gpr (by revert r; decide), ?_, ?_⟩, post_shared ?_⟩
    · rw [mem, tested.mem]
      exact (entryMem_frame g).readW (Region.contains_self _ _)
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact g.returnSeparate) (by decide)
    · rw [mxcsr, tested.mxcsr]
    · unfold CheckDomain.cdPost
      rw [value, valid]
      rfl
  · intro _
    rw [WP.seq_iff]
    refine WP.mono (restore_ok tested) ?_
    intro w restored
    obtain ⟨trace, x, run, preserved, post⟩ := fallback_run v (restored.pre hs)
    have native := post_native post
    unfold CheckDomain.cdPost at native
    rw [restored.args.2.2.1, restored.domain g] at native
    exact ⟨trace, x, run, abi_trans (restored.abi g) preserved, post_shared native⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
