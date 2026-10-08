import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.GatherSeal
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo

/-! # Prepared-context Gather contracts -/
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Gather
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.SealGather

theorem gatherPrePrepared_of {s : State}
    (h : (Proof.AesGcm.sealGatherPreparedScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM CtxMode.prepared s := by
  sig_pre [Proof.AesGcm.sealGatherPreparedScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPreparedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, kw, nd, nt, nw, ad, at_, aw, dt, dw, dds, ⟨dl, da⟩, tw, tds, ⟨tl, ta⟩, wds, wl, wa⟩,
    rk, rn, ra, rdd, rt, rw, ⟨rds, ⟨rl, -⟩, bk, bn, ba, bd, bt, bw, bds, bl, -⟩, ok, on, oa, od, ot, ow, ⟨ods, ol⟩,
    hr, hg, hpw⟩ := h
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, Proof.AesGcm.stkG,
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.prepared]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, wa, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, hg, hpw⟩

theorem gatherPostPrepared_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.sealGatherPreparedScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.sealGatherPreparedScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPost, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPubPrepared_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.sealGatherPreparedScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherPreparedScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPreparedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi)⟩

theorem gatherSatPrepared_pre : ∃ s, (Proof.AesGcm.sealGatherPreparedScratchContract X86_64.abi 4888).pre s := by
  refine ⟨gatherSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherPreparedScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPreparedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq,
    gatherSatP, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowersRepr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem gatherPrepared_implies : (Proof.AesGcm.sealGatherX86_64M CtxMode.prepared).Implies
    (Proof.AesGcm.sealGatherPreparedScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPrePrepared_of h, fun _ _ _ h => gatherPostPrepared_of h, fun _ _ _ _ h => gatherPubPrepared_of h, gatherSatPrepared_pre⟩

theorem sealGatherPrepared_core (S : SealFn CtxMode.prepared) {t : Nat} (ht : t < 2 ^ 31) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.prepared) (F : FinFn) :
    Verified X86_64.target (sealGather S.fn t I.fn A.fn T.fn F.fn)
      (Proof.AesGcm.sealGatherPreparedScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.prepared) (sealGather_correct S t I A T F (ht := ht))
    (sealGather_ct S ht I A T F) gatherPrepared_implies

theorem gatherFrameSatPrepared_pre : ∃ s, (Spec.Gcm.sealGatherPreparedContract X86_64.abi 5128).pre s := by
  refine ⟨gatherFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.sealGatherPreparedContract, Spec.Gcm.sealGatherPreparedSig, Spec.Gcm.sealGatherPrecomputedSig,
    Spec.Gcm.sealGatherPreparedPre, X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq,
    gatherFrameSatP, gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowersRepr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem sealGatherPrepared_framed (S : SealFn CtxMode.prepared) {t : Nat} (ht : t < 2 ^ 31) (I : InitFn)
    (A : AadFn) (T : ToFn CtxMode.prepared) (F : FinFn) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5 (sealGather S.fn t I.fn A.fn T.fn F.fn))
      (Spec.Gcm.sealGatherPreparedContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherPreparedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Spec.Gcm.sealGatherPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240)
    (sealGatherPrepared_core S ht I A T F) (by decide) (by decide) (by decide) (sealGather_spAll S t I A T F)
    (sealGather_xdepth S t I A T F) (Proof.AesGcm.sealGatherPreparedPre_local _)
    (Proof.AesGcm.sealGatherPrecomputedPost_local _) gatherFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64.Gather
