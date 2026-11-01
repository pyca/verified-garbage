module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared8
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: `_prepared`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_prepared`
is `vg_aes_gcm_seal_gather` calling an implementation of
`vg_aes_gcm_seal_prepared`, with the key context `CtxSpec.prepared`: its
384 bytes, holding the prepared powers (`PreparedPowersRepr`). The call
finds them where the shared contract of `vg_aes_gcm_seal_gather_prepared`
gives them (`Proof.Gcm.sealGatherPrepared8Contract`), since the code writes
only its frame and `dst` before it (`inv_gMem`); the call's shared contract
(`Proof.Gcm.sealPrepared8Contract`) then holds (`sealPreparedSpec_pre`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.SealGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

/-- The key context of `vg_aes_gcm_seal_prepared`: its 384 bytes, holding
the prepared powers. -/
abbrev CtxSpec.prepared : CtxSpec :=
  ⟨384, by decide, Proof.Gcm.PreparedPowers8Repr, fun h hr => Proof.AesGcm.preparedPowers8Repr_congr h hr⟩

/-! ## The call -/

theorem sealPreparedSpec_pre {s : State} (h : callPre .prepared s)
    (hr : Proof.Gcm.PreparedPowers8Repr s.mem (s.gpr .x0)) :
    (Proof.Gcm.sealPrepared8Contract AArch64.abi 2576).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄
  have a₂₅ := h
  clear h
  sig_pre [Proof.Gcm.sealPrepared8Contract, Proof.Gcm.sealPrepared8Sig,
    Proof.Gcm.sealPrepared8Pre, AArch64.abi, AArch64.argRegs, stackArgs_one, List.append_eq]
  sig_reduce [Proof.Gcm.sealPrepared8Contract, Proof.Gcm.sealPrepared8Sig, AArch64.abi,
    AArch64.argRegs, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealPreparedSpec_post {s s' : State} (h : (Proof.Gcm.sealPrepared8Contract AArch64.abi 2576).post s s')
    (hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) :
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Proof.Gcm.sealPrepared8Contract, Proof.Gcm.sealPrepared8Sig, Spec.Gcm.sealPost,
    AArch64.abi, AArch64.argRegs, stackArgs_one, List.append_eq] at h
  exact h hR

theorem sealPreparedSpec_pub {s₁ s₂ : State} (h : s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0) : (Proof.Gcm.sealPrepared8Contract AArch64.abi 2576).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Proof.Gcm.sealPrepared8Contract, Proof.Gcm.sealPrepared8Sig, AArch64.abi,
    AArch64.argRegs, stackArgs_one, List.append_eq]
  sig_reduce [Proof.Gcm.sealPrepared8Contract, Proof.Gcm.sealPrepared8Sig, AArch64.abi,
    AArch64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- An implementation of `vg_aes_gcm_seal_prepared`, by its shared contract
(`Proof.Gcm.sealPrepared8Contract`, with 2576 bytes of stack). -/
def SealFn.prepared (fn : Impl.AesGcm.AArch64.Fn)
    (verified : Verified AArch64.target fn.code (Proof.Gcm.sealPrepared8Contract AArch64.abi 2576))
    (depth : 16 * fn.code.aarch64Depth ≤ 2576) : SealFn .prepared where
  fn := fn
  k := Proof.Gcm.sealPrepared8Contract AArch64.abi 2576
  verified := verified
  depth := depth
  pre _ h hr := sealPreparedSpec_pre h hr
  post _ _ h hR := sealPreparedSpec_post h hR
  pub _ _ h := sealPreparedSpec_pub h

/-! ## The shared contract -/

theorem gatherPre_of_specP {s : State} (h : (Proof.Gcm.sealGatherPrepared8Contract AArch64.abi 2592).pre s) :
    (gatherAArch64 .prepared).pre s := by
  sig_pre [Proof.Gcm.sealGatherPrepared8Contract, Proof.Gcm.sealGatherPrepared8Sig,
    Proof.Gcm.sealGatherPrepared8Pre, AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, tl, ta⟩,
    bk, bn, ba, bd, bt, ⟨bds, bl, barg⟩, ok, on, oa, od, ot, ⟨ods, ol⟩, hr, hg, hp⟩ := h
  exact ⟨⟨rd, wr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩,
    dt, da, ta, bk, bn, ba, bds, bl, barg, bd, bt, ok, on, oa, ods, ol, od, ot, w₁, w₂, hr, hg⟩, hp⟩

theorem gatherPost_ofP {s s' : State} (h : gatherPost s s') :
    (Proof.Gcm.sealGatherPrepared8Contract AArch64.abi 2592).post s s' := by
  sig_post [Proof.Gcm.sealGatherPrepared8Contract, Proof.Gcm.sealGatherPrepared8Sig,
    Spec.Gcm.sealGatherPost, AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_ofP {s₁ s₂ : State} (hp : (Proof.Gcm.sealGatherPrepared8Contract AArch64.abi 2592).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Proof.Gcm.sealGatherPrepared8Contract, Proof.Gcm.sealGatherPrepared8Sig,
    Proof.Gcm.sealGatherPrepared8Pre, AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, q6, q7, a0, a1, a2, hd⟩ := hp
  exact ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, a0, a1, a2, hd⟩

/-- `gatherSat` with the context's 384 bytes, all zero. -/
def gatherSatP : State :=
  { gatherSat with rd := [⟨0x1000, 384⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9000, 24⟩] }

theorem gatherSatP_pre : ∃ s, (Proof.Gcm.sealGatherPrepared8Contract AArch64.abi 2592).pre s := by
  refine ⟨gatherSatP, ?_⟩
  sig_pre [Proof.Gcm.sealGatherPrepared8Contract, Proof.Gcm.sealGatherPrepared8Sig,
    Proof.Gcm.sealGatherPrepared8Pre, AArch64.abi, AArch64.argRegs, stackArgs_three, List.append_eq, gatherSatP,
    gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Proof.AesGcm.preparedPowers8Repr_of_zeroMem fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

theorem gather_impliesP :
    (gatherAArch64 .prepared).Implies (Proof.Gcm.sealGatherPrepared8Contract AArch64.abi 2592) :=
  ⟨fun _ h => gatherPre_of_specP h, fun _ _ _ h => gatherPost_ofP h, fun _ _ _ _ h => gatherPub_ofP h,
    gatherSatP_pre⟩

theorem sealGatherPrepared_verified (F : SealFn .prepared) :
    Verified AArch64.target (sealGather F.fn) (Proof.Gcm.sealGatherPrepared8Contract AArch64.abi 2592) :=
  Verified.of_correct (k := gatherAArch64 .prepared) (sealGather_correct F) (sealGather_ct F) gather_impliesP

end VG.Proof.AesGcm.AArch64.Gather
