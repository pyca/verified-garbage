module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Precomputed
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall

import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedBody
import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)

theorem public_sp (v : PublicImpl) : v.code.allInstrs (fun i => !isa.writesSp i) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [(SpSafe.of_all v.spSafe) i hi]
  rfl

theorem sp_of_safe {c : Prog isa} (h : c.allInstrs safeI = true) : c.allInstrs (fun i => !isa.writesSp i) = true := by
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at h
  exact h.1

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem code_sp (v : PublicImpl) :
    (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code).allInstrs (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPss.X86_64.Precomputed.pubArgs, Impl.RsaPss.X86_64.Precomputed.code, Impl.RsaPss.X86_64.Precomputed.body, seqs,
    Impl.RsaPss.X86_64.Precomputed.main, Code.allInstrs, sp_of_safe (mgfXor_safe hH K), sp_of_safe (saltBack_safe hH K),
    public_sp v, rec_all,
    List.all_append, verifyFail, emLen, anyArgs, posScan, posCheck, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem code_xd (v : PublicImpl) :
    (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code).x86_64Depth ≤ verifyStack := by
  simp only [Impl.RsaPss.X86_64.Precomputed.pubArgs, Impl.RsaPss.X86_64.Precomputed.code, Impl.RsaPss.X86_64.Precomputed.body, seqs,
    Impl.RsaPss.X86_64.Precomputed.main, Code.x86_64Depth, mgfXor_xd K, saltBack_xd K, x86_64Depth_zero v.nosp v.depth, verifyFail, emLen,
    anyArgs, posScan, posCheck, byteLoop,
    X86_64.Instr.frameBytes]
  unfold verifyStack frameBytes
  decide

include hH K in
theorem code_correct (lk : Pbkdf2.Md.X86_64.MgfLink H hH) (v : PublicImpl)
    (s : State) (h : (Spec.RsaPss.verifyPrecomputedContract lk.G lk.G abi verifyStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code) s t s' ∧ abiPreserved s s' ∧ (validCache s → (verifyK lk.G).post s s') := by
  have hp := pre_of lk.G h
  have hW := X86_64.WP.stackFrame (SpSafe.of_all (Code.all_of_allInstrs (code_sp hH K v)))
    (by have := code_xd K v; unfold verifyStack at this; omega) (code_ok hH K lk v h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  have hd := code_xd K v
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code).x86_64Depth) (k := 8)
      (by unfold verifyStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64.Pc
