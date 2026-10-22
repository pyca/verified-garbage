module

public import VerifiedGarbage.Spec.Gcm.Prepared16

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16To
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.ScratchGather

/-! # Sixteen prepared powers: Prepared-context Gather contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.Gather
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.SealGather

theorem gatherPrePrepared16_of {s : State}
    (h : (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM (CtxMode.preparedN 8) s := by
  sig_pre [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
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
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.preparedN]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, wa, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, hg, hpw⟩

theorem gatherPostPrepared16_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPost, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPubPrepared16_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi)⟩

theorem gatherSatPrepared16_pre : ∃ s, (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888).pre s := by
  refine ⟨gatherSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherPrepared16ScratchContract, Proof.AesGcm.sealGatherPreparedScratchSig, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Spec.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq,
    gatherSatP, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem gatherPrepared16_implies : (Proof.AesGcm.sealGatherX86_64M (CtxMode.preparedN 8)).Implies
    (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPrePrepared16_of h, fun _ _ _ h => gatherPostPrepared16_of h, fun _ _ _ _ h => gatherPubPrepared16_of h, gatherSatPrepared16_pre⟩

/-- `vg_aes_gcm_seal_gather_prepared`'s code: a TLS record's text sealed by
`Sp` from the entry (`withFront long`), and the others by `sealGather`. -/
theorem sealGatherPrepared16_core (Sh : ShortFn (CtxMode.preparedN 8)) (I : InitFn) (A : AadFn)
    (T : ToFn (CtxMode.preparedN 8)) (F : FinFn) (Sp : SplitFn (CtxMode.preparedN 8)) (long : Bool) :
    Verified X86_64.target
      (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Proof.AesGcm.sealGatherPrepared16ScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M (CtxMode.preparedN 8))
    (withFront_correct Sh I A T F Sp long) (withFront_ct Sh I A T F Sp long) gatherPrepared16_implies

theorem gatherFrameSatPrepared16_pre : ∃ s, (Spec.Gcm.sealGatherPrepared16Contract X86_64.abi 5128).pre s := by
  refine ⟨gatherFrameSatP, ?_⟩
  sig_pre [Spec.Gcm.sealGatherPrepared16Contract, Spec.Gcm.sealGatherPreparedSig, Spec.Gcm.sealGatherPrecomputedSig,
    Spec.Gcm.sealGatherPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq,
    gatherFrameSatP, gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowers16Repr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem sealGatherPrepared16_framed (Sh : ShortFn (CtxMode.preparedN 8)) (I : InitFn)
    (A : AadFn) (T : ToFn (CtxMode.preparedN 8)) (F : FinFn) (Sp : SplitFn (CtxMode.preparedN 8)) (long : Bool) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn)))
      (Spec.Gcm.sealGatherPrepared16Contract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Gcm.sealGatherPreparedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Spec.Gcm.sealGatherPrepared16Pre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240)
    (sealGatherPrepared16_core Sh I A T F Sp long) (by decide) (by decide) (by decide)
    (withFront_spAll Sh I A T F Sp long) (withFront_xdepth Sh I A T F Sp long)
    (Proof.AesGcm.sealGatherPrepared16Pre_local _) (Proof.AesGcm.sealGatherPrecomputedPost_local _)
    gatherFrameSatPrepared16_pre

end VG.Proof.AesGcm.X86_64.Gather
