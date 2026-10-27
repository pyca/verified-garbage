module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe

/-!
# RSASSA-PSS signing on x86-64, around the encoding: the calling convention

`signC_correct`: `signC` meets `signK` and keeps the callee-saved registers,
its return address (which only its frame and calls are below) and MXCSR's
control bits (no instruction loads MXCSR).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (chkContract)

variable {G : Spec.Mgf1.Hash} {encN : String} {encC : Prog isa} {privN : String} {privC : Prog isa}

theorem spAll_of {c : Prog isa} (hC : SpSafe c) : c.allInstrs (fun i => !isa.writesSp i) = true := by
  rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by rw [hC i hi]; rfl

theorem signC_spAll (hE : SpSafe encC) (hC : SpSafe privC) :
    (signC encN encC privN privC).allInstrs (fun i => !isa.writesSp i) = true := by
  simp only [signC, signCBody, seqs, Code.allInstrs, spAll_of hE, spAll_of hC, rec_all, List.all_append,
    signFail, Bool.and_true, Bool.true_and]
  rfl

theorem signC_sp (hE : SpSafe encC) (hC : SpSafe privC) : SpSafe (signC encN encC privN privC) := by
  have h := signC_spAll (encN := encN) (privN := privN) hE hC
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem signC_xd (hdE : encC.x86_64Depth ≤ encStack) (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    (signC encN encC privN privC).x86_64Depth ≤ signStack := by
  simp only [signC, signCBody, seqs, Code.x86_64Depth, signFail, byteLoop, X86_64.Instr.frameBytes, Nat.zero_max,
    Nat.max_zero]
  unfold signStack Rsa.X86_64.stackBytes frameBytes encStack at *
  exact Nat.add_le_add_right (Nat.max_le.mpr ⟨(by omega : _ ≤ 3264), by omega⟩) 392

theorem signC_correct
    (hvE : ∀ s, (encK G).pre s → ∃ t s', Exec isa encC s t s' ∧ abiPreserved s s' ∧ (encK G).post s s')
    (hE : SpSafe encC) (hdE : encC.x86_64Depth ≤ encStack)
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
    (s : State) (h : (signK G).pre s) :
    ∃ t s', Exec isa (signC encN encC privN privC) s t s' ∧ abiPreserved s s' ∧ (signK G).post s s' := by
  have hp := SPre.of G h
  have hd := signC_xd (encN := encN) (privN := privN) hdE hdC
  have hW := X86_64.WP.stackFrame (signC_sp hE hC)
    (by unfold signStack Rsa.X86_64.stackBytes at hd; omega)
    (signC_ok (encN := encN) (privN := privN) hvE hE hdE hv hC hdC h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega) (by omega)) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (signC encN encC privN privC).x86_64Depth) (k := 8)
      (by unfold signStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64
