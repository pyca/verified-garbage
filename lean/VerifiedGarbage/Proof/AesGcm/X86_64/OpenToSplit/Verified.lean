module

-- separate module: the proof, which needs none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.AesGcm.Flag
public import VerifiedGarbage.Proof.AesGcm.ScratchOpenTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenToSplit.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# AES-GCM decryption out of place, in one pass, x86-64: `Verified`

Untrusted: everything here is checked by Lean. `openToSplit` meets the contracts
of `Proof/AesGcm/RoundsTo.lean` for prepared key contexts with a working
space appended (`Proof/AesGcm/ScratchOpenTo.lean`) and 152 bytes of stack
(its frame of 88, the call's return address and the 56 bytes of
`vg_aes_gcm_open_split`), and so, in a frame of 2624 bytes holding its
working space (`Verified.stackArgScratch`), those contracts with 2776 bytes
of stack, whatever the length: for a flagged key context
(`openToSplitFlagged_framed`), and for one of `vg_aes_gcm_init`
(`openToSplitBase_framed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenToSplit

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

theorem toPre_prepared {s : State} (h : (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).pre s) :
    ToPreS CtxMode.prepared s := by
  sig_pre [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa'⟩, rk, rn, ra, rs, rdd, rt, rw, -,
    bk, bn, ba, bs, bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da dw rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, kw, nw, aw, sw, tw, dw, wa', rk, rn, ra, rs, rdd, rt, rw, bk, bn, ba, bs,
    bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, w₁, w₂, ro, dl, hpw⟩

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-! ## The code -/

theorem openToSplit_spAll (f : Impl.AesGcm.X86_64.Fn) (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.AesGcm.X86_64.OpenToSplit.openToSplit f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.AesGcm.X86_64.OpenToSplit.openToSplit, Impl.AesGcm.X86_64.OpenToSplit.callArgs,
    Impl.AesGcm.X86_64.OpenTo.after, Impl.AesGcm.X86_64.OpenTo.wipe, Code.all, h, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openToSplit_xdepth (f : Impl.AesGcm.X86_64.Fn) (h : f.code.x86_64Depth ≤ 56) :
    (Impl.AesGcm.X86_64.OpenToSplit.openToSplit f).x86_64Depth ≤ 152 := by
  simp only [Impl.AesGcm.X86_64.OpenToSplit.openToSplit, Impl.AesGcm.X86_64.OpenToSplit.callArgs,
    Impl.AesGcm.X86_64.OpenTo.after, Impl.AesGcm.X86_64.OpenTo.wipe, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, Nat.max_le]
  omega

/-! ## The contracts with the working space -/

theorem toPost_prepared {s s' : State} (h : OpenTo.toPost s s') :
    (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).post s s' := by
  sig_post [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq]
  exact fun _ => h

theorem toPub_prepared {s₁ s₂ : State} (hp : (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).pub s₁ s₂) :
    toPubS s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig, Spec.Gcm.openToLeak,
    X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, a₆⟩ := hp
  refine ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_⟩, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | 6, _ => exact a₆
  | n + 7, h => exact absurd h (by omega)

/-- A state satisfying the precondition of `openToSplit`: `OpenTo.toSatP`, with
`work` at `0x7000`. -/
def toSatS : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9029 then 0x60 else
      if a = 0x9039 then 0x70 else 0) else 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 56⟩]
  wr := [⟨0x5000, 0⟩, ⟨0x7000, 2560⟩]

theorem toSatS_pre : ∃ s, (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152).pre s := by
  refine ⟨toSatS, ?_⟩
  sig_pre [Proof.AesGcm.openToPreparedScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq, toSatS, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

theorem prepared_implies :
    (toSK CtxMode.prepared).Implies (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152) :=
  ⟨fun _ h => toPre_prepared h, fun _ _ _ h => toPost_prepared h, fun _ _ _ _ h => toPub_prepared h, toSatS_pre⟩

/-- `openToSplit`, calling an instance of `vg_aes_gcm_open_split` for a prepared
key context, with its working space as an argument. -/
theorem openToSplitPrepared_core (F : OpenSplitFn CtxMode.prepared) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn)
      (Proof.AesGcm.openToPreparedScratchContract X86_64.abi 152) :=
  Verified.of_correct (k := toSK CtxMode.prepared)
    (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openToSplit_wp F hs; exact ⟨t, s', he, ha, hp⟩) (openToSplit_ct F)
    prepared_implies

/-! ## In its frame -/

theorem toSatP2776_pre : ∃ s, (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776).pre s := by
  refine ⟨OpenTo.toSatP, ?_⟩
  sig_pre [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq, OpenTo.toSatP,
    OpenTo.toSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

/-- `openToSplit` in its frame of 2624 bytes, holding its working space. -/
theorem openToSplitPrepared_framed (F : OpenSplitFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn))
      (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2776) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openToPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.openToPowersPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 152)
    (leak := some (Spec.Gcm.openToLeak X86_64.abi.ptrBits)) (bytes := 2624) (openToSplitPrepared_core F)
    (by decide) (by decide) (by decide) (openToSplit_spAll F.fn F.spAll) (openToSplit_xdepth F.fn F.xd)
    (Proof.AesGcm.openToPreparedPre_local _) (Proof.AesGcm.openToRoundsPost_local _) toSatP2776_pre
    (hleak := Proof.AesGcm.openToLeak_local _)

/-! ## Choosing by length -/

/-- `u` is `s` but for `rax` and the flags. -/
structure Same (s u : State) : Prop where

/-! ## With 16 prepared powers -/

theorem toPre_prepared16 {s : State} (h : (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).pre s) :
    ToPreS CtxMode.prepared16 s := by
  sig_pre [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa'⟩, rk, rn, ra, rs, rdd, rt, rw, -,
    bk, bn, ba, bs, bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da dw rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, kw, nw, aw, sw, tw, dw, wa', rk, rn, ra, rs, rdd, rt, rw, bk, bn, ba, bs,
    bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, w₁, w₂, ro, dl, hpw⟩

theorem toPost_prepared16 {s s' : State} (h : OpenTo.toPost s s') :
    (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).post s s' := by
  sig_post [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq]
  exact fun _ => h

theorem toPub_prepared16 {s₁ s₂ : State} (hp : (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).pub s₁ s₂) :
    toPubS s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig, Spec.Gcm.openToLeak,
    X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, a₆⟩ := hp
  refine ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_⟩, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | 6, _ => exact a₆
  | n + 7, h => exact absurd h (by omega)

theorem toSatS16_pre : ∃ s, (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152).pre s := by
  refine ⟨toSatS, ?_⟩
  sig_pre [Proof.AesGcm.openToPrepared16ScratchContract, Proof.AesGcm.openToPreparedScratchSig,
    Proof.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq, toSatS, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowers16Repr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

theorem prepared16_implies :
    (toSK CtxMode.prepared16).Implies (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152) :=
  ⟨fun _ h => toPre_prepared16 h, fun _ _ _ h => toPost_prepared16 h, fun _ _ _ _ h => toPub_prepared16 h, toSatS16_pre⟩

/-- `openToSplit`, calling an instance of `vg_aes_gcm_open_split` for a prepared
key context, with its working space as an argument. -/
theorem openToSplitPrepared16_core (F : OpenSplitFn CtxMode.prepared16) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn)
      (Proof.AesGcm.openToPrepared16ScratchContract X86_64.abi 152) :=
  Verified.of_correct (k := toSK CtxMode.prepared16)
    (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openToSplit_wp F hs; exact ⟨t, s', he, ha, hp⟩) (openToSplit_ct F)
    prepared16_implies

theorem toSatP16_2776_pre : ∃ s, (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776).pre s := by
  refine ⟨OpenTo.toSatP, ?_⟩
  sig_pre [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq, OpenTo.toSatP,
    OpenTo.toSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowers16Repr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

/-- `openToSplit` in its frame of 2624 bytes, holding its working space. -/
theorem openToSplitPrepared16_framed (F : OpenSplitFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn))
      (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2776) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openToPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.openToPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 152)
    (leak := some (Spec.Gcm.openToLeak X86_64.abi.ptrBits)) (bytes := 2624) (openToSplitPrepared16_core F)
    (by decide) (by decide) (by decide) (openToSplit_spAll F.fn F.spAll) (openToSplit_xdepth F.fn F.xd)
    (Proof.AesGcm.openToPrepared16Pre_local _) (Proof.AesGcm.openToRoundsPost_local _) toSatP16_2776_pre
    (hleak := Proof.AesGcm.openToLeak_local _)

theorem toPre_base {s : State} (h : (Proof.AesGcm.openToScratchContract X86_64.abi 152).pre s) :
    ToPreS CtxMode.base s := by
  sig_pre [Proof.AesGcm.openToScratchContract, Proof.AesGcm.openToScratchSig,
    Spec.Gcm.openToPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa'⟩, rk, rn, ra, rs, rdd, rt, rw, -,
    bk, bn, ba, bs, bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, ro, dl⟩ := h
  rw [dl] at wr kd nd ad sd dt da dw rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, kw, nw, aw, sw, tw, dw, wa', rk, rn, ra, rs, rdd, rt, rw, bk, bn, ba, bs,
    bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, w₁, w₂, ro, dl, trivial⟩

/-! ## For a key context of `vg_aes_gcm_init` -/

theorem toPost_base {s s' : State} (h : OpenTo.toPost s s') :
    (Proof.AesGcm.openToScratchContract X86_64.abi 152).post s s' := by
  sig_post [Proof.AesGcm.openToScratchContract, Proof.AesGcm.openToScratchSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq]
  exact fun _ => h

theorem toPub_base {s₁ s₂ : State} (hp : (Proof.AesGcm.openToScratchContract X86_64.abi 152).pub s₁ s₂) :
    toPubS s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToScratchContract, Proof.AesGcm.openToScratchSig, Spec.Gcm.openToLeak,
    X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, a₆⟩ := hp
  refine ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_⟩, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | 6, _ => exact a₆
  | n + 7, h => exact absurd h (by omega)

/-- A state satisfying the precondition of `openToSplit`: `OpenTo.toSat`, with
`work` at `0x7000`. -/
def toSatSB : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9029 then 0x60 else
      if a = 0x9039 then 0x70 else 0) else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 56⟩]
  wr := [⟨0x5000, 0⟩, ⟨0x7000, 2560⟩]

theorem toSatSB_pre : ∃ s, (Proof.AesGcm.openToScratchContract X86_64.abi 152).pre s := by
  refine ⟨toSatSB, ?_⟩
  sig_pre [Proof.AesGcm.openToScratchContract, Proof.AesGcm.openToScratchSig,
    Spec.Gcm.openToPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq, toSatSB, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

theorem base_implies :
    (toSK CtxMode.base).Implies (Proof.AesGcm.openToScratchContract X86_64.abi 152) :=
  ⟨fun _ h => toPre_base h, fun _ _ _ h => toPost_base h, fun _ _ _ _ h => toPub_base h, toSatSB_pre⟩

/-- `openToSplit`, calling an instance of `vg_aes_gcm_open_split` for a prepared
key context, with its working space as an argument. -/
theorem openToSplitBase_core (F : OpenSplitFn CtxMode.base) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn)
      (Proof.AesGcm.openToScratchContract X86_64.abi 152) :=
  Verified.of_correct (k := toSK CtxMode.base)
    (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openToSplit_wp F hs; exact ⟨t, s', he, ha, hp⟩) (openToSplit_ct F)
    base_implies

theorem toSatB2776_pre : ∃ s, (Proof.AesGcm.openToRoundsContract X86_64.abi 2776).pre s := by
  refine ⟨OpenTo.toSat, ?_⟩
  sig_pre [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig,
    Spec.Gcm.openToPre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq, OpenTo.toSat,
    OpenTo.toSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false]

/-- `openToSplit` in its frame of 2624 bytes, holding its working space. -/
theorem openToSplitBase_framed (F : OpenSplitFn CtxMode.base) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn))
      (Proof.AesGcm.openToRoundsContract X86_64.abi 2776) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openToPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 152)
    (leak := some (Spec.Gcm.openToLeak X86_64.abi.ptrBits)) (bytes := 2624) (openToSplitBase_core F)
    (by decide) (by decide) (by decide) (openToSplit_spAll F.fn F.spAll) (openToSplit_xdepth F.fn F.xd)
    (Proof.AesGcm.openToPre_local _) (Proof.AesGcm.openToRoundsPostBase_local _) toSatB2776_pre
    (hleak := Proof.AesGcm.openToLeakBase_local _)

/-! ## On the prepared key context whose powers are present -/

theorem toPre_flaggedS {t : Nat} {s : State} (h : (Proof.AesGcm.Flag.openToFlaggedScratchContract t X86_64.abi 152).pre s) :
    ToPreS (CtxMode.flaggedT t) s := by
  sig_pre [Proof.AesGcm.Flag.openToFlaggedScratchContract, Proof.AesGcm.Flag.openToFlaggedScratchSig,
    Proof.AesGcm.Flag.openToFlaggedPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa'⟩, rk, rn, ra, rs, rdd, rt, rw, -,
    bk, bn, ba, bs, bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da dw rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, kw, nw, aw, sw, tw, dw, wa', rk, rn, ra, rs, rdd, rt, rw, bk, bn, ba, bs,
    bd, bt, bw, barg, wk, wn, wa, ws, wd, wt, ww, w₁, w₂, ro, dl, hpw⟩

theorem toPost_flaggedS {t : Nat} {s s' : State} (h : OpenTo.toPost s s') :
    (Proof.AesGcm.Flag.openToFlaggedScratchContract t X86_64.abi 152).post s s' := by
  sig_post [Proof.AesGcm.Flag.openToFlaggedScratchContract, Proof.AesGcm.Flag.openToFlaggedScratchSig,
    Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq]
  exact fun _ => h

theorem toPub_flaggedS {t : Nat} {s₁ s₂ : State} (hp : (Proof.AesGcm.Flag.openToFlaggedScratchContract t X86_64.abi 152).pub s₁ s₂) :
    toPubS s₁ s₂ := by
  sig_pub [Proof.AesGcm.Flag.openToFlaggedScratchContract, Proof.AesGcm.Flag.openToFlaggedScratchSig, Spec.Gcm.openToLeak,
    X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, a₆⟩ := hp
  refine ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_⟩, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | 6, _ => exact a₆
  | n + 7, h => exact absurd h (by omega)

/-- A state satisfying the precondition of `openToSplit`: `OpenTo.toSatP`, with
`work` at `0x7000`. -/
def toSatSF : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1400 then 48 else if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9029 then 0x60 else
      if a = 0x9039 then 0x70 else 0) else 0
  rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 56⟩]
  wr := [⟨0x5000, 0⟩, ⟨0x7000, 2560⟩]

theorem toSatSF_pre {t : Nat} (ht : t ≤ 48) : ∃ s, (Proof.AesGcm.Flag.openToFlaggedScratchContract t X86_64.abi 152).pre s := by
  refine ⟨toSatSF, ?_⟩
  sig_pre [Proof.AesGcm.Flag.openToFlaggedScratchContract, Proof.AesGcm.Flag.openToFlaggedScratchSig,
    Proof.AesGcm.Flag.openToFlaggedPre, X86_64.abi, X86_64.argRegs, stackArgs_seven, List.append_eq, toSatSF, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem ht
        (fun _ hi => by simp only [Proof.AesGcm.Flag.ctx_ne1024 hi, OpenTo.ctx_lowF (Nat.lt_of_lt_of_le hi (by decide)), ite_false])
        (by decide)

theorem flaggedS_implies {t : Nat} (ht : t ≤ 48) :
    (toSK (CtxMode.flaggedT t)).Implies (Proof.AesGcm.Flag.openToFlaggedScratchContract t X86_64.abi 152) :=
  ⟨fun _ h => toPre_flaggedS h, fun _ _ _ h => toPost_flaggedS h, fun _ _ _ _ h => toPub_flaggedS h, toSatSF_pre ht⟩

/-- `openToSplit`, calling an instance of `vg_aes_gcm_open_split` for a prepared
key context, with its working space as an argument. -/
theorem openToSplitFlagged_core {t : Nat} (ht : t ≤ 48) (F : OpenSplitFn (CtxMode.flaggedT t)) :
    Verified X86_64.target (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn)
      (Proof.AesGcm.Flag.openToFlaggedScratchContract t X86_64.abi 152) :=
  Verified.of_correct (k := toSK (CtxMode.flaggedT t))
    (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openToSplit_wp F hs; exact ⟨t, s', he, ha, hp⟩) (openToSplit_ct F)
    (flaggedS_implies ht)

/-! ## In its frame -/

theorem toSatF2776_pre {t : Nat} (ht : t ≤ 48) : ∃ s, (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2776).pre s := by
  refine ⟨OpenTo.toSatF, ?_⟩
  sig_pre [Proof.AesGcm.Flag.openToFlaggedRoundsContract, Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPreparedSig,
    Proof.AesGcm.Flag.openToFlaggedPre, X86_64.abi, X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq, OpenTo.toSatF,
    OpenTo.toSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem ht
        (fun _ hi => by simp only [Proof.AesGcm.Flag.ctx_ne1024 hi, OpenTo.ctx_lowF (Nat.lt_of_lt_of_le hi (by decide)), ite_false])
        (by decide)

/-- `openToSplit` in its frame of 2624 bytes, holding its working space. -/
theorem openToSplitFlagged_framed {t : Nat} (ht : t ≤ 48) (F : OpenSplitFn (CtxMode.flaggedT t)) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit F.fn))
      (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2776) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.openToPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.AesGcm.Flag.openToFlaggedPre t X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 152)
    (leak := some (Spec.Gcm.openToLeak X86_64.abi.ptrBits)) (bytes := 2624) (openToSplitFlagged_core ht F)
    (by decide) (by decide) (by decide) (openToSplit_spAll F.fn F.spAll) (openToSplit_xdepth F.fn F.xd)
    (Proof.AesGcm.Flag.openToFlaggedPre_local t _) (Proof.AesGcm.Flag.openToFlaggedRoundsPost_local _) (toSatF2776_pre ht)
    (hleak := Proof.AesGcm.Flag.openToFlaggedLeak_local _)

end VG.Proof.AesGcm.X86_64.OpenToSplit
