module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8

/-!
# AES-GCM decryption out of place, by a copy, AArch64: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_open_to`, with the 2624 bytes of stack below the stack pointer
that its frame and its call use (`Proof.AesGcm.openToRoundsContract`),
implies the one the proof is written against (`toK openShape`,
`to_implies`), and so the code, calling an implementation of
`vg_aes_gcm_open` by its shared contract, is `Verified` against it
(`openTo_verified`); and so for `vg_aes_gcm_open_to_with_powers`
(`Proof.AesGcm.openToWithPowersRoundsContract`, `toK pwShape`,
`toPw_implies`), calling an implementation of `vg_aes_gcm_open_with_powers`
(`openToPw_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.OpenTo

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.OpenTo
open VG.Proof.AesGcm.AArch64.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem openTo_correct {S : Shape} (F : OpenFn S) (s : State) (hs : (toK S).pre s) :
    ∃ t s', Exec isa (openTo S.n F.fn) s t s' ∧ abiPreserved s s' ∧ (toK S).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := openTo_wp F hs
  exact ⟨t, s', he, ha, hp⟩

/-- The code, calling a function of shape `S`, against a contract that
implies `toK S`. -/
theorem verified_of {S : Shape} (F : OpenFn S) {C : Contract isa} (hi : (toK S).Implies C) :
    Verified AArch64.target (openTo S.n F.fn) C :=
  Verified.of_correct (k := toK S) (openTo_correct F) (openTo_ct F) hi

/-! ## `vg_aes_gcm_open_to` -/

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem toPre_of_spec {s : State} (h : (Proof.AesGcm.openToRoundsContract AArch64.abi 2624).pre s) :
    ToPre openShape s := by
  sig_pre [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, da⟩, bk, bn, ba, bs, bd, bt, barg, ok, on, oa, os, od, ot, hR, dl⟩ := h
  rw [dl] at wr kd nd ad sd dt da bd od
  exact ⟨w₁, w₂, rd, wr, kd, nd, ad, sd, dt, nofun, da, bk, bn, ba, bs, bd, bt, nofun, barg, ok, on, oa, os, od, ot,
    nofun, hR, dl, trivial⟩

theorem toPost_of {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToRoundsContract AArch64.abi 2624).post s s' := by
  sig_post [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Proof.AesGcm.openToRoundsPost,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq]
  exact fun _ => h

theorem toPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.openToRoundsContract AArch64.abi 2624).pub s₁ s₂) :
    toPub openShape.n s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToLeak,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a0, a1, a2, a3⟩ := hp
  refine ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, fun i hi => ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp only [openShape] at hi; omega
  rcases this with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

/-- A state satisfying the precondition of `vg_aes_gcm_open_to`: no nonce,
additional data, text or tag. -/
def toSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x9000, 32⟩]
  wr := [⟨0, 0⟩]

theorem toSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract AArch64.abi 2624).pre s := by
  sig_implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    AArch64.abi, AArch64.argRegs, stackArgs_four, List.append_eq] [toSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using toSat

theorem to_implies : (toK openShape).Implies (Proof.AesGcm.openToRoundsContract AArch64.abi 2624) :=
  ⟨fun _ h => toPre_of_spec h, fun _ _ _ h => toPost_of h, fun _ _ _ _ h => toPub_of h, toSat_pre⟩

theorem openTo_verified (F : OpenFn openShape) :
    Verified AArch64.target (openTo 2 F.fn) (Proof.AesGcm.openToRoundsContract AArch64.abi 2624) :=
  verified_of F to_implies

/-! ## `vg_aes_gcm_open_to_with_powers` -/

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

theorem toPwPre_of_spec {s : State} (h : (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2624).pre s) :
    ToPre pwShape s := by
  sig_pre [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig,
    Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToSig, Spec.Gcm.withPowersParam, Spec.Gcm.openToPre,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil,
    List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
    List.cons_append, List.singleton_append, Sig.descRegion, Function.comp_def, Bool.not_false,
    Bool.false_eq_true, ite_true, ite_false, List.filter_nil] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, nd, ad, sd, dt, dp, da⟩, bk, bn, ba, bs, bd, bt, bp, barg, ok, on, oa, os, od, ot, op,
    hR, dl, rep⟩ := h
  rw [dl] at wr kd nd ad sd dt dp da bd od
  exact ⟨w₁, w₂, rd, wr, kd, nd, ad, sd, dt, by simpa [pwShape, pwR] using dp, da, bk, bn, ba, bs, bd, bt,
    by simpa [pwShape, pwR] using bp, barg, ok, on, oa, os, od, ot, by simpa [pwShape, pwR] using op, hR, dl,
    by simpa [pwShape, pwX] using rep⟩

theorem toPwPost_of {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2624).post s s' := by
  sig_post [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig, Spec.Gcm.openToSig,
    Spec.Gcm.withPowersParam, Proof.AesGcm.openToWithPowersRoundsPost, Proof.AesGcm.openToRoundsPost,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq]
  exact fun _ => h

theorem toPwPub_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2624).pub s₁ s₂) : toPub pwShape.n s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig, Spec.Gcm.openToSig,
    Spec.Gcm.withPowersParam, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, a0, a1, a2, a3, a4⟩ := hp
  refine ⟨sp, l, x0, x1, x2, x3, x4, x5, x6, x7, fun i hi => ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by simp only [pwShape] at hi; omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

/-- `toSat` with the powers' buffer, of zeros, at 0 (`[sp + 32]`). -/
def toSatPw : State :=
  { toSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0, 128⟩, ⟨0x9000, 40⟩] }

theorem toSatPw_pre : ∃ s, (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2624).pre s := by
  refine ⟨toSatPw, ?_⟩
  sig_pre [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig,
    Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToSig, Spec.Gcm.withPowersParam, Spec.Gcm.openToPre,
    AArch64.abi, AArch64.argRegs, stackArgs_five, List.append_eq, toSatPw, toSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) fun _ _ => rfl

theorem toPw_implies : (toK pwShape).Implies (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2624) :=
  ⟨fun _ h => toPwPre_of_spec h, fun _ _ _ h => toPwPost_of h, fun _ _ _ _ h => toPwPub_of h, toSatPw_pre⟩

theorem openToPw_verified (F : OpenFn pwShape) :
    Verified AArch64.target (openTo 3 F.fn) (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2624) :=
  verified_of F toPw_implies

end VG.Proof.AesGcm.AArch64.OpenTo
