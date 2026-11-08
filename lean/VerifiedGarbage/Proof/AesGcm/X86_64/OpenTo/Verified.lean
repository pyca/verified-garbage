module

public import VerifiedGarbage.Proof.AesGcm.Flag
-- separate module: the proof, which needs none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# AES-GCM decryption out of place, by a copy, x86-64: `Verified`

Untrusted: everything here is checked by Lean. The code's static facts (no
load of `mxcsr`, `rsp` written only in its frame, 2728 bytes of stack: its
frame of 88 and the call's), and the contracts of `Proof/AesGcm/RoundsTo.lean`
on this target, with 2728 bytes of stack, which imply the one the proof is
written against (`toK`), for the key contexts of `vg_aes_gcm_prepare`
(`openToPrepared_verified`) and of `vg_aes_gcm_prepare16`
(`openToPrepared16_verified`), and for a flagged one
(`openToFlagged_verified`). On the key context of `vg_aes_gcm_init`,
`vg_aes_gcm_open_to` decrypts in one pass (`OpenToSplit`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenTo

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Impl.AesGcm.X86_64.OpenTo (openTo)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width)
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

/-! ## The code -/

theorem openTo_spAll (w : Width) (f : Fn) (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (openTo w f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [openTo, Impl.AesGcm.X86_64.OpenTo.callArgs, Impl.AesGcm.X86_64.OpenTo.after,
    Impl.AesGcm.X86_64.OpenTo.wipe, Code.all, h, Bool.true_and, Bool.and_true]
  cases w <;> decide +kernel

/-! ## The contracts -/

theorem stackArgs_six (s : State) : List.map (stackArg s) (List.range 6) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5] := rfl

theorem toPre_prepared {s : State} (h : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728).pre s) :
    ToPre CtxMode.prepared s := by
  sig_pre [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig, Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, da⟩, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg,
    wk, wn, wa, ws, wd, wt, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg, wk, wn, wa,
    ws, wd, wt, w₁, w₂, ro, dl, hpw⟩

theorem toPre_prepared16 {s : State} (h : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728).pre s) :
    ToPre CtxMode.prepared16 s := by
  sig_pre [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig, Proof.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, da⟩, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg,
    wk, wn, wa, ws, wd, wt, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg, wk, wn, wa,
    ws, wd, wt, w₁, w₂, ro, dl, hpw⟩

theorem toPost_prepared {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728).post s s' := by
  sig_post [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig, Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq]
  exact fun _ => h

theorem toPost_prepared16 {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728).post s s' := by
  sig_post [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig, Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq]
  exact fun _ => h

theorem toPub_prepared {s₁ s₂ : State} (hp : (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728).pub s₁ s₂) :
    toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅⟩ := hp
  refine ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | n + 6, h => exact absurd h (by omega)

theorem toPub_prepared16 {s₁ s₂ : State} (hp : (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728).pub s₁ s₂) :
    toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅⟩ := hp
  refine ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | n + 6, h => exact absurd h (by omega)

/-! ## Satisfiability -/

/-- A state satisfying the precondition of `vg_aes_gcm_open_to`: no nonce,
additional data, text or tag; `src`, `dst` and `tag` at `0x4000`, `0x5000`
and `0x6000`. -/
def toSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9029 then 0x60 else 0) else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩]
  wr := [⟨0x5000, 0⟩]

/-- The key context at `0x1000` is below the stack arguments. -/
theorem ctx_low {i : Nat} (hi : i < 128 * 8) : ¬ (0x9000 ≤ (0x1000 + BitVec.ofNat 64 i : Addr).toNat) := by
  have h : (0x1000 : Addr).toNat = 4096 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), h]
  omega

/-- `toSat`, with a key context of 1024 bytes. -/
def toSatP : State :=
  { toSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩] }

theorem toSatP_pre : ∃ s, (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728).pre s := by
  refine ⟨toSatP, ?_⟩
  sig_pre [Proof.AesGcm.openToPreparedRoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPowersPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq, toSatP, toSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [ctx_low hi, ite_false]

theorem toSatP16_pre : ∃ s, (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728).pre s := by
  refine ⟨toSatP, ?_⟩
  sig_pre [Proof.AesGcm.openToPrepared16RoundsContract, Spec.Gcm.openToPrecomputedSig, Spec.Gcm.openToPrecomputedSig,
    Proof.Gcm.openToPrepared16Pre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq, toSatP, toSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.preparedPowers16Repr_of_zeroMem fun _ hi => by simp only [ctx_low hi, ite_false]

/-! ## `Verified` -/

theorem prepared_implies :
    (toK CtxMode.prepared).Implies (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728) :=
  ⟨fun _ h => toPre_prepared h, fun _ _ _ h => toPost_prepared h, fun _ _ _ _ h => toPub_prepared h, toSatP_pre⟩

theorem prepared16_implies :
    (toK CtxMode.prepared16).Implies (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728) :=
  ⟨fun _ h => toPre_prepared16 h, fun _ _ _ h => toPost_prepared16 h, fun _ _ _ _ h => toPub_prepared16 h,
    toSatP16_pre⟩

/-- `vg_aes_gcm_open_to_prepared`, calling an instance of `vg_aes_gcm_open_prepared`. -/
theorem openToPrepared_verified (w : Width) (F : OpenFn CtxMode.prepared) :
    Verified X86_64.target (openTo w F.fn) (Proof.AesGcm.openToPreparedRoundsContract X86_64.abi 2728) :=
  Verified.of_correct (k := toK CtxMode.prepared) (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openTo_wp w F hs; exact ⟨t, s', he, ha, hp⟩) (openTo_ct w F) prepared_implies

/-- `vg_aes_gcm_open_to_prepared16`, calling an instance of `vg_aes_gcm_open_prepared16`. -/
theorem openToPrepared16_verified (w : Width) (F : OpenFn CtxMode.prepared16) :
    Verified X86_64.target (openTo w F.fn) (Proof.AesGcm.openToPrepared16RoundsContract X86_64.abi 2728) :=
  Verified.of_correct (k := toK CtxMode.prepared16) (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openTo_wp w F hs; exact ⟨t, s', he, ha, hp⟩) (openTo_ct w F) prepared16_implies


/-! ## On the prepared key context whose powers are present -/

theorem toPre_flagged {t : Nat} {s : State} (h : (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2728).pre s) :
    ToPre (CtxMode.flaggedT t) s := by
  sig_pre [Proof.AesGcm.Flag.openToFlaggedRoundsContract, Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPreparedSig, Proof.AesGcm.Flag.openToFlaggedPre, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, da⟩, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg,
    wk, wn, wa, ws, wd, wt, ro, dl, hpw⟩ := h
  rw [dl] at wr kd nd ad sd dt da rdd bd wd
  exact ⟨rd, wr, kd, nd, ad, sd, dt, da, rk, rn, ra, rs, rdd, rt, rarg, bk, bn, ba, bs, bd, bt, barg, wk, wn, wa,
    ws, wd, wt, w₁, w₂, ro, dl, hpw⟩

theorem toPost_flagged {t : Nat} {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2728).post s s' := by
  sig_post [Proof.AesGcm.Flag.openToFlaggedRoundsContract, Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPreparedSig, Proof.AesGcm.openToRoundsPost, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq]
  exact fun _ => h

theorem toPub_flagged {t : Nat} {s₁ s₂ : State} (hp : (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2728).pub s₁ s₂) :
    toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.Flag.openToFlaggedRoundsContract, Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPreparedSig, Spec.Gcm.openToLeak, X86_64.abi, X86_64.argRegs,
    stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, hl, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅⟩ := hp
  refine ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, fun i hi => ?_, hl⟩
  match i, hi with
  | 0, _ => exact a₀
  | 1, _ => exact a₁
  | 2, _ => exact a₂
  | 3, _ => exact a₃
  | 4, _ => exact a₄
  | 5, _ => exact a₅
  | n + 6, h => exact absurd h (by omega)

theorem ctx_lowF {i : Nat} (hi : i < 129 * 8) : ¬ (0x9000 ≤ (0x1000 + BitVec.ofNat 64 i : Addr).toNat) := by
  have h : (0x1000 : Addr).toNat = 4096 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), h]
  omega

/-- `toSat`, with a prepared key context of 1032 bytes. -/
def toSatF : State :=
  { toSat with
    mem := fun a => if a = 0x1400 then 48 else toSat.mem a
    rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩] }

theorem toSatF_pre {t : Nat} (ht : t ≤ 48) : ∃ s, (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2728).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Proof.AesGcm.Flag.openToFlaggedRoundsContract, Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPreparedSig,
    Proof.AesGcm.Flag.openToFlaggedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq, toSatF, toSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.Flag.flaggedPowers_of_zeroMem ht
        (fun _ hi => by simp only [Proof.AesGcm.Flag.ctx_ne1024 hi, ctx_lowF (Nat.lt_of_lt_of_le hi (by decide)), ite_false])
        (by decide)

theorem flagged_implies {t : Nat} (ht : t ≤ 48) :
    (toK (CtxMode.flaggedT t)).Implies (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2728) :=
  ⟨fun _ h => toPre_flagged h, fun _ _ _ h => toPost_flagged h, fun _ _ _ _ h => toPub_flagged h, toSatF_pre ht⟩

/-- `vg_aes_gcm_open_to_prepared`'s code on a context whose powers are present,
calling `vg_aes_gcm_open_prepared`. -/
theorem openToFlagged_verified {t : Nat} (ht : t ≤ 48) (w : Width) (F : OpenFn (CtxMode.flaggedT t)) :
    Verified X86_64.target (openTo w F.fn) (Proof.AesGcm.Flag.openToFlaggedRoundsContract t X86_64.abi 2728) :=
  Verified.of_correct (k := toK (CtxMode.flaggedT t)) (fun _ hs => by obtain ⟨t, s', he, ha, hp⟩ := openTo_wp w F hs; exact ⟨t, s', he, ha, hp⟩) (openTo_ct w F) (flagged_implies ht)

end VG.Proof.AesGcm.X86_64.OpenTo
