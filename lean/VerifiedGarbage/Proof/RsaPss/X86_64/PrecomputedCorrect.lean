import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedBody

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)

theorem public_safe (v : PublicImpl) : v.code.allInstrs safeI = true := by
  rw [safeI_eq, allInstrs_and, v.mxSafe, Bool.and_true, Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [(SpSafe.of_all v.spSafe) i hi]
  rfl

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem code_safe (v : PublicImpl) :
    (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code).allInstrs safeI = true := by
  simp only [Impl.RsaPss.X86_64.Precomputed.pubArgs, Impl.RsaPss.X86_64.Precomputed.code, Impl.RsaPss.X86_64.Precomputed.body, seqs,
    Impl.RsaPss.X86_64.Precomputed.main, Code.allInstrs, mgfXor_safe hH K, ctHash_safe hH K, public_safe v, rec_all,
    List.all_append, verifyFail, emLen, anyArgs, posScan, posCheck, clearY, copyDigest, copyDb, shift, shiftPass,
    cmpH, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem code_xd (v : PublicImpl) :
    (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code).x86_64Depth ≤ verifyStack := by
  simp only [Impl.RsaPss.X86_64.Precomputed.pubArgs, Impl.RsaPss.X86_64.Precomputed.code, Impl.RsaPss.X86_64.Precomputed.body, seqs,
    Impl.RsaPss.X86_64.Precomputed.main, Code.x86_64Depth, mgfXor_xd K, ctHash_xd K, x86_64Depth_zero v.nosp v.depth, verifyFail, emLen,
    anyArgs, posScan, posCheck, clearY, copyDigest, copyDb, shift, shiftPass, cmpH, byteLoop,
    X86_64.Instr.frameBytes]
  unfold verifyStack frameBytes
  decide

include hH K in
theorem code_correct (lk : Pbkdf2.Md.X86_64.MgfLink H hH) (v : PublicImpl)
    (s : State) (h : (Spec.RsaPss.verifyPrecomputedContract lk.G lk.G abi verifyStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPss.X86_64.Precomputed.code H v.name v.code) s t s' ∧ abiPreserved s s' ∧ (validCache s → (verifyK lk.G).post s s') := by
  have hp := pre_of lk.G h
  have hsf := code_safe hH K v
  have hW := X86_64.WP.stackFrame (safe_sp hsf) (by have := code_xd K v; unfold verifyStack at this; omega)
    (code_ok hH K lk v h)
  obtain ⟨t, s', he, hq⟩ := WP.mono_mx (safe_mx hsf) hW fun s' q hmx => (⟨q, hmx⟩ : _ ∧ _)
  obtain ⟨⟨⟨hcs, hpost⟩, hf⟩, hmx⟩ := hq
  refine ⟨t, s', he, ⟨hcs, ?_, by rw [hmx]⟩, hpost⟩
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
