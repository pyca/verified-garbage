module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

import VerifiedGarbage.Proof.RsaPss.X86_64.PcCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: the calling convention

`codeC_correct`: `verifyC` meets `verifyK` when the cache matches, and keeps
the callee-saved registers, its return address (which only its frame and
calls are below) and MXCSR's control bits.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)

variable {G : Spec.Mgf1.Hash} {chkN : String} {chkC : Prog isa}

theorem codeC_spAll (hK : SpSafe chkC) (v : PublicImpl) :
    (verifyC chkN chkC v.name v.code).allInstrs (fun i => !isa.writesSp i) = true := by
  simp only [verifyC, verifyCBody, seqs, Code.allInstrs, spAll_of hK, spAll_of (SpSafe.of_all v.spSafe),
    verifyFail, Bool.and_true, Bool.true_and]
  rfl

theorem codeC_sp (hK : SpSafe chkC) (v : PublicImpl) : SpSafe (verifyC chkN chkC v.name v.code) := by
  have h := codeC_spAll (chkN := chkN) hK v
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem codeC_xd (hdK : chkC.x86_64Depth ≤ chkStack) (v : PublicImpl) :
    (verifyC chkN chkC v.name v.code).x86_64Depth ≤ verifyStack := by
  simp only [verifyC, verifyCBody, seqs, Code.x86_64Depth, x86_64Depth_zero v.nosp v.depth, verifyFail,
    X86_64.Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  unfold verifyStack frameBytes chkStack at *
  exact Nat.add_le_add_right (Nat.max_le.mpr ⟨(by omega : _ ≤ 408), by omega⟩) 392

theorem codeC_correct
    (hvK : ∀ s, (chkK G).pre s → ∃ t s', Exec isa chkC s t s' ∧ abiPreserved s s' ∧ (chkK G).post s s')
    (hK : SpSafe chkC) (hdK : chkC.x86_64Depth ≤ chkStack) (v : PublicImpl)
    (s : State) (h : (Spec.RsaPss.verifyPrecomputedContract G G abi verifyStack).pre s) :
    ∃ t s', Exec isa (verifyC chkN chkC v.name v.code) s t s' ∧ abiPreserved s s' ∧
      (validCache s → (verifyK G).post s s') := by
  have hp := pre_of G h
  have hd := codeC_xd (chkN := chkN) hdK v
  have hW := X86_64.WP.stackFrame (codeC_sp hK v) (by unfold verifyStack at hd; omega)
    (codeC_ok (chkN := chkN) hvK hK hdK v h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (verifyC chkN chkC v.name v.code).x86_64Depth) (k := 8)
      (by unfold verifyStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64.Pc
