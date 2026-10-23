module

public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8

/-!
# AES-GCM out of place from a list of slices, with the powers, AArch64: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather_with_powers`, with the 2624 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.Gcm.sealGatherWithPowersContract`), implies the one the proof is
written against (`gatherAArch64`, `gather_implies`), and so the code, calling
an implementation of `vg_aes_gcm_seal_with_powers` by its shared contract, is
`Verified` against it (`sealGatherPw_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.GatherPw

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.SealGather
open VG.Proof.AesGcm.AArch64.Gather (pairFacts_ro filter_true' filter_false' filterMap_some' filterMap_none')

theorem sealGatherPw_correct (F : SealPwFn) (s : State) (hs : gatherAArch64.pre s) :
    ∃ t s', Exec isa (sealGatherPw F.fn) s t s' ∧ abiPreserved s s' ∧ gatherAArch64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGatherPw_wp F hs.1 hs.2
  exact ⟨t, s', he, ha, hp⟩

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem gatherPre_of_spec {s : State} (h : (Spec.Gcm.sealGatherWithPowersContract AArch64.abi 2624).pre s) :
    gatherAArch64.pre s := by
  sig_pre [Spec.Gcm.sealGatherWithPowersContract, Spec.Gcm.sealGatherWithPowersSig,
    Spec.Gcm.sealGatherWithPowersPre, Spec.Gcm.sealGatherPre, Spec.Gcm.sealGatherSig, Spec.Gcm.withPowersParam,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dpw, dds, ⟨dls, darg⟩, tpw, tds, tls, targ⟩, sk, sn, sa, sd,
    st, spw, ⟨sds, sls, sarg⟩, ok, on, oa, od, ot, opw, ⟨ods, ols⟩, hR, hgl, hp⟩ := h
  exact ⟨⟨rd, wr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr => ⟨(dls r hr).symm, (tls r hr).symm⟩,
    dpw.symm, tpw.symm, dt, darg, targ, sk, sn, sa, sds, sls, spw, sarg, sd, st, ok, on, oa, ods, ols, opw, od, ot,
    w₁, w₂, hR, hgl⟩, hp⟩

theorem gatherPost_of {s s' : State} (h : Gather.gatherPost s s') :
    (Spec.Gcm.sealGatherWithPowersContract AArch64.abi 2624).post s s' := by
  sig_post [Spec.Gcm.sealGatherWithPowersContract, Spec.Gcm.sealGatherWithPowersSig,
    Spec.Gcm.sealGatherWithPowersPost, Spec.Gcm.sealGatherPost, Spec.Gcm.sealGatherSig, Spec.Gcm.withPowersParam,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State}
    (hp : (Spec.Gcm.sealGatherWithPowersContract AArch64.abi 2624).pub s₁ s₂) : gatherPub s₁ s₂ := by
  sig_pub [Spec.Gcm.sealGatherWithPowersContract, Spec.Gcm.sealGatherWithPowersSig,
    Spec.Gcm.sealGatherWithPowersPre, Spec.Gcm.sealGatherSig, Spec.Gcm.withPowersParam,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, q6, q7, a0, a1, a2, a3, hd⟩ := hp
  exact ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, a0, a1, a2, a3, hd⟩

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather_with_powers`:
no slices, no nonce, additional data or text; the tag at `0x5000`, the
powers, zero, at `0x6000`. -/
def gatherSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := if a = 0x9011 then 0x50 else if a = 0x9019 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 128⟩, ⟨0x4000, 0⟩, ⟨0x9000, 32⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

/-- The powers' bytes in `gatherSat` are zero. -/
theorem gatherSat_zero : ∀ i < 16 * 8, gatherSat.mem (stackArg gatherSat 3 + BitVec.ofNat 64 i) = 0 := by
  intro i hi
  have hP : stackArg gatherSat 3 = 0x6000 := by decide
  rw [hP]
  show (if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x9011 then 0x50
    else if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x9019 then 0x60 else 0) = 0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega)), ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega))]

theorem gatherSat_pre : ∃ s, (Spec.Gcm.sealGatherWithPowersContract AArch64.abi 2624).pre s := by
  refine ⟨gatherSat, ?_⟩
  sig_pre [Spec.Gcm.sealGatherWithPowersContract, Spec.Gcm.sealGatherWithPowersSig,
    Spec.Gcm.sealGatherWithPowersPre, Spec.Gcm.sealGatherPre, Spec.Gcm.sealGatherSig, Spec.Gcm.withPowersParam,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq, gatherSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) gatherSat_zero

theorem gather_implies : gatherAArch64.Implies (Spec.Gcm.sealGatherWithPowersContract AArch64.abi 2624) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h,
    gatherSat_pre⟩

theorem sealGatherPw_verified (F : SealPwFn) :
    Verified AArch64.target (sealGatherPw F.fn) (Spec.Gcm.sealGatherWithPowersContract AArch64.abi 2624) :=
  Verified.of_correct (k := gatherAArch64) (sealGatherPw_correct F) (sealGatherPw_ct F) gather_implies

end VG.Proof.AesGcm.AArch64.GatherPw
