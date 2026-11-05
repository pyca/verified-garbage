module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

public import VerifiedGarbage.Proof.RsaPss.X86_64.PcCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.ByIdx
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

variable {tsH tsG : List FnTable} {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns}

theorem chk_calls (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) :
    (byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs).allInstrs
        (fun i => !isa.writesSp i) = true ∧
      (byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs).x86_64Depth ≤ chkStack + 8 :=
  byIdx_calls fun i hi => ⟨by simp only [Code.allInstrs]; exact spAll_of (hK i hi),
    by simp only [Code.x86_64Depth]; exact Nat.add_le_add_right (hdK i hi) 8⟩

theorem codeC_spAll (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl) :
    (Impl.RsaPss.X86_64.verifyC f g v.name v.code).allInstrs (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPss.X86_64.verifyC, verifyCBody, seqs, Code.allInstrs, (chk_calls hK hdK).1,
    spAll_of (SpSafe.of_all v.spSafe), verifyFail, Bool.and_true, Bool.true_and]
  rfl

theorem codeC_sp (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl) :
    SpSafe (Impl.RsaPss.X86_64.verifyC f g v.name v.code) := by
  have h := codeC_spAll hK hdK v
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem codeC_xd (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl) :
    (Impl.RsaPss.X86_64.verifyC f g v.name v.code).x86_64Depth ≤ verifyStack := by
  have := (chk_calls hK hdK).2
  simp only [Impl.RsaPss.X86_64.verifyC, verifyCBody, seqs, Code.x86_64Depth, x86_64Depth_zero v.nosp v.depth,
    verifyFail, X86_64.Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.max_le.mpr ⟨(by decide : 0 + 8 ≤ chkStack + 8), this⟩) frameBytes)
    (by decide)

theorem codeC_correct (hsel : ∀ s, (verifyK tsH tsG).pre s → ∃ i T Hs Gs, KSel f g s i T Hs Gs)
    (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl)
    (s : State) (h : (verifyK tsH tsG).pre s) :
    ∃ t s', Exec isa (Impl.RsaPss.X86_64.verifyC f g v.name v.code) s t s' ∧ abiPreserved s s' ∧
      (verifyK tsH tsG).post s s' := by
  have hp := pre_of h
  have hd := codeC_xd hK hdK v
  obtain ⟨i, T, Hs, Gs, E⟩ := hsel s h
  have hW := X86_64.WP.stackFrame (codeC_sp hK hdK v) (by unfold verifyStack chkStack at hd; omega)
    (codeC_ok hK hdK v h E)
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
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (Impl.RsaPss.X86_64.verifyC f g v.name v.code).x86_64Depth)
      (k := 8) (by unfold verifyStack chkStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64.Pc
