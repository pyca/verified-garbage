module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Prepared
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.GeneratorStageContract
public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
public import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGenerator
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Pack
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import Mathlib.Algebra.Group.Nat.Defs
/-! # The stage, from the generator search to the domain check

The generation's own search, then, once it finds a g, the packing of
p ‖ q ‖ g and the domain check, leave the status of `Proof.Dsa.GeneratorStage.stage`
in the generation's status slot, and the packed domain when it is valid. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Validate.lean`, which only this module imported.
section

/-! # Domain-check results control native seed retry or acceptance -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem validate_ok (M : Mont) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = VG.Proof.Bignum.off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 16) (hq : p.qLen < 2 ^ 16)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.validate M.mm p.pLen p.qLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd W 19 (BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 3))) ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.validate
  refine WP.seq (WP.mono (validateCore_ok M p L R hbase hp hq hs src hF hS)
    fun u ⟨hr, Lu, Ru, fu, ku⟩ => ?_)
  have hz := validateTest_ok hr
  have fv : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem u.mem :=
    fu.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)
  have finish (status : Nat) (hstatus : status < 2 ^ 16) :
      WP isa (.block (Impl.Dsa.AArch64.Generation.stackStatus status)) u fun t =>
        Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) ∧
        Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
    refine WP.mono (stackStatus_ok Lu Ru status hstatus) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    refine ⟨Lt, Rt, fv.trans ?_, (ku.trans kt).mono (by decide)⟩
    intro a ha
    apply ft a
    right
    have hn := ha ⟨F, frameBytes⟩ (by simp)
    change ¬ ofs F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  cases hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params with
  | false =>
    refine WP.ite true (by simp [hz, hc]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hc, Bool.false_eq_true, ite_false] using finish 3 (by decide)
  | true =>
    refine WP.ite false (by simp [hz, hc]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simpa only [hc, ite_true] using finish 1 (by decide)

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (GeneratorSearchPlan GeneratorSearchMemory)
open VG.Proof.RsaOaep.AArch64 (Lay Rep upd)

variable {pLen : Nat} {s : State}

/-- q's bytes, for p's. -/
abbrev qLen (pLen : Nat) : Nat := Impl.Dsa.AArch64.Generator.qLen pLen

/-- What the stage computes. -/
abbrev result (pLen : Nat) (s : State) : Option Spec.Dsa.Params :=
  Proof.Dsa.GeneratorStage.stage (pOf pLen s.mem (s.gpr .x0)) (qOf pLen s.mem (s.gpr .x0))
    (Proof.Dsa.GeneratorStage.candidates pLen (tape s))

/-- The memory the stage writes. -/
def stageChanged (pLen : Nat) (s : State) : List Region :=
  [⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩, ⟨s.gpr .x0, Impl.Dsa.Layout.activeBytes⟩,
    ⟨off (s.gpr .x0) g, pLen⟩, ⟨off (s.gpr .x0) packed, 2 * pLen + qLen pLen⟩,
    ⟨off (s.gpr .x0) domainCheck, Impl.Dsa.Layout.usedBytes⟩, ⟨frameBase s, frameBytes⟩]

/-- What the stage leaves. -/
structure Staged (pLen : Nat) (s u t : State) : Prop where
  lay : Lay t (frameBase s) (hashBase s)
  rep : ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0 ∧
    W 19 = BitVec.ofNat 64 (if (result pLen s).isSome then 1 else 3)
  packed : ∀ a, result pLen s = some a →
    Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) = Spec.Dsa.encodeParams pLen (qLen pLen) a
  frame : Frame (stageChanged pLen s) u.mem t.mem
  rd : t.rd = u.rd
  wr : t.wr = u.wr

theorem Supported.lengths {pLen : Nat} (hb : Supported pLen) : Spec.Dsa.lengthsValid pLen (qLen pLen) := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem Supported.q_le {pLen : Nat} (hb : Supported pLen) : 2 ≤ qLen pLen ∧ qLen pLen ≤ 32 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem StageABI.parts (hb : Supported pLen) (A : StageABI pLen s) {d n e k : Nat}
    (hd : d + n ≤ usedBytes pLen) (he : e + k ≤ usedBytes pLen) (h : d + n ≤ e ∨ e + k ≤ d) :
    (⟨off (s.gpr .x0) d, n⟩ : Region).Disjoint ⟨off (s.gpr .x0) e, k⟩ :=
  (arena hb A).parts_disjoint hd he h

theorem StageABI.framePart (hb : Supported pLen) (A : StageABI pLen s) {d n : Nat} (h : d + n ≤ usedBytes pLen) :
    (⟨frameBase s, frameBytes⟩ : Region).Disjoint ⟨off (s.gpr .x0) d, n⟩ :=
  (arena hb A).frame_part h

/-- The search's result is the generator `Proof.Dsa.GeneratorStage.stage` starts from. -/
theorem plan_remaining (hb : Supported pLen) (A : StageABI pLen s) :
    (plan hb A).remaining 0 = Spec.Dsa.generator (pOf pLen s.mem (s.gpr .x0)) (qOf pLen s.mem (s.gpr .x0))
      (Proof.Dsa.GeneratorStage.candidates pLen (tape s)) := by
  simp only [GeneratorSearchPlan.remaining, plan, Arena.generatorPlan, arena, List.drop_zero,
    Proof.Dsa.GeneratorStage.candidates]
  rfl

theorem StageABI.packed_sep (hb : Supported pLen) (A : StageABI pLen s) {d n : Nat} (hd : d + n ≤ packed) :
    (⟨off (s.gpr .x0) d, n⟩ : Region).Disjoint ⟨off (s.gpr .x0) packed, 2 * pLen + qLen pLen⟩ := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have := hb.q_le
  have hp0 := used_small hb (d := packed) (n := 0) (by decide) (by decide)
  exact A.parts hb (by omega)
    (used_small hb (by decide) (by unfold arithmeticBytes; omega)) (Or.inl hd)

/-- The search's status: 1 when it finds a g, 3 when it does not. -/
def statusOf (pl : GeneratorSearchPlan) : BitVec 64 := if (pl.remaining 0).isSome then 1 else 3

/-- The g the search finds. -/
abbrev gOf (pl : GeneratorSearchPlan) : Nat := (pl.remaining 0).getD 0

/-- The domain the stage checks. -/
abbrev domainOf (pLen : Nat) (s : State) (pl : GeneratorSearchPlan) : Spec.Dsa.Params :=
  ⟨pOf pLen s.mem (s.gpr .x0), qOf pLen s.mem (s.gpr .x0), gOf pl⟩

/-- What the generator search leaves. -/
structure Searched (hb : Supported pLen) (A : StageABI pLen s) (u t : State) : Prop where
  lay : Lay t (frameBase s) (hashBase s)
  rep : ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0 ∧ W 19 = statusOf (plan hb A)
  scr : Scr t (s.gpr .x0) (usedBytes pLen)
  bytes : (plan hb A).remaining 0 ≠ none →
    Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.p) pLen =
        Spec.Dsa.encodeBE pLen (pOf pLen s.mem (s.gpr .x0)) ∧
      Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.q) (qLen pLen) =
        Spec.Dsa.encodeBE (qLen pLen) (qOf pLen s.mem (s.gpr .x0)) ∧
      Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) g) pLen = Spec.Dsa.encodeBE pLen (gOf (plan hb A))
  frame : Frame (stageChanged pLen s) u.mem t.mem
  rd : t.rd = u.rd
  wr : t.wr = u.wr

theorem Searched.congr {hb : Supported pLen} {A : StageABI pLen s} {u t t' : State} (h : Searched hb A u t)
    (hm : t'.mem = t.mem) (hk : Keep [.x3, .x4] t t') : Searched hb A u t' := by
  obtain ⟨V, W, R, h5, h19⟩ := h.rep
  exact ⟨h.lay.congr hk.sp hk.wr (by rw [hm]), ⟨V, W, hm ▸ R, h5, h19⟩, h.scr.congr hk.wr,
    fun hs => by rw [hm]; exact h.bytes hs, hm ▸ h.frame, hk.rd.trans h.rd, hk.wr.trans h.wr⟩

theorem search_ok (M : Mont) (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorSearch M.mm pLen) u (Searched hb A u) := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have coreCh : (plan hb A).core.changed = [⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩,
      ⟨s.gpr .x0, Impl.Dsa.Layout.activeBytes⟩, ⟨off (s.gpr .x0) g, pLen⟩, ⟨frameBase s, frameBytes⟩] := rfl
  have keepPart : ∀ {d n : Nat}, VG.Impl.Dsa.Generation.Layout.q ≤ d → d + n ≤ g →
      ∀ r ∈ (plan hb A).core.changed, Region.Disjoint ⟨off (s.gpr .x0) d, n⟩ r := fun h1 h2 r hr => by
    rw [coreCh] at hr
    have := (arena hb A).gWork_separate h1 h2 r (by simpa [Arena.gWork, arena, Arena.part] using hr)
    simpa [arena, Arena.part] using this
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.nativeGenerator_ok M (prepared hb A E))
    fun t ⟨W', mt, outcome, ft, rdt, wrt⟩ => ?_
  obtain ⟨V, R⟩ := mt.rep
  have bytesT : ∀ {d n : Nat}, VG.Impl.Dsa.Generation.Layout.q ≤ d → d + n ≤ g →
      Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) d) n = Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) d) n := fun h1 h2 => by
    have g0 := used_small hb (d := g) (n := 0) (by decide) (by decide)
    have gl : g ≤ 2 ^ 64 := by decide
    rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (keepPart h1 h2) (by omega), A.bytes_entered hb E (by unfold Impl.Dsa.AArch64.Generator.spill VG.Impl.Dsa.Generation.Layout.control g at *; omega)]
  refine ⟨mt.layout, ⟨V, W', R, mt.base, ?_⟩, (A.scr E).congr wrt, fun hs => ?_, ft.mono ?_, rdt, wrt⟩
  · rcases outcome with ⟨h3, hn⟩ | ⟨gv, h1, hgv, _⟩
    · rw [h3]; simp [statusOf, ← hn]
    · rw [h1]; simp [statusOf, hgv]
  · rcases outcome with ⟨_, hn⟩ | ⟨gv, _, hgv, bg⟩
    · exact absurd hn hs
    refine ⟨?_, ?_, ?_⟩
    rotate_left 2
    · change Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) g) pLen = Spec.Dsa.encodeBE pLen gv at bg
      simpa [gOf, hgv] using bg
    · rw [bytesT (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega)]
      have := VG.Proof.Dsa.encodeBE_decodeBE (pBytes pLen s)
      rw [bytesAt_length] at this
      exact this.symm
    · rw [bytesT (Nat.le_refl _) (by unfold VG.Impl.Dsa.Generation.Layout.q g; omega)]
      have := VG.Proof.Dsa.encodeBE_decodeBE (qBytes pLen s)
      rw [bytesAt_length] at this
      exact this.symm
  · intro r hr; rw [coreCh] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [stageChanged]

/-- What packing leaves. -/
structure Packed (hb : Supported pLen) (A : StageABI pLen s) (u t : State) : Prop where
  lay : Lay t (frameBase s) (hashBase s)
  rep : ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0
  scr : Scr t (s.gpr .x0) (usedBytes pLen)
  bytes : Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) =
    Spec.Dsa.encodeParams pLen (qLen pLen) (domainOf pLen s (plan hb A))
  frame : Frame (stageChanged pLen s) u.mem t.mem
  rd : t.rd = u.rd
  wr : t.wr = u.wr

theorem pack_stage_ok (hb : Supported pLen) (A : StageABI pLen s) {u t : State} (S : Searched hb A u t)
    (h19 : statusOf (plan hb A) = 1) :
    WP isa (Impl.Dsa.AArch64.Generation.pack pLen (qLen pLen)) t (Packed hb A u) := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have c1 : packed = 27008 := rfl
  have c2 : g = 26240 := rfl
  have c3 : VG.Impl.Dsa.Generation.Layout.p = 25472 := rfl
  have c4 : VG.Impl.Dsa.Generation.Layout.q = 25408 := rfl
  have c5 : arithmeticBytes = 12288 := rfl
  have c6 : domainCheck = 40960 := rfl
  have c12 : usedBytes pLen = domainCheck + 128 * pLen := rfl
  have p128 : 128 ≤ pLen := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hpk := used_small hb (d := packed) (n := 2 * pLen + qLen pLen) (by decide) (by unfold arithmeticBytes; omega)
  have hs : (plan hb A).remaining 0 ≠ none := by
    intro hn; simp [statusOf, hn] at h19
  obtain ⟨pE, qE, gE⟩ := S.bytes hs
  obtain ⟨V, W, R, h5, _⟩ := S.rep
  have src (d n : Nat) (bs : List Byte) (hl : bs.length = n) (hd : d + n ≤ packed)
      (hbs : Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) d) n = bs) :
      Src t (off (W 5) packed) (2 * pLen + qLen pLen) (off (W 5) d) bs := by
    rw [h5]
    subst hl
    exact VG.Proof.Dsa.AArch64.Generation.arena_source S.scr (by unfold packed at hd; omega)
      (by have := used_lt hb; unfold packed at hd; omega) hbs (A.packed_sep hb hd)
  have hS : (⟨hashBase s, oRsa⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen pLen⟩ := by
    rw [h5]; exact A.packed_sep hb (d := VG.Impl.Dsa.Generation.Layout.hash) (by decide)
  have hF : (⟨frameBase s, frameBytes⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen pLen⟩ := by
    rw [h5]; exact A.framePart hb hpk
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.pack_ok S.lay R (VG.Proof.Dsa.encodeBE_length _ _)
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) ⟨by omega, qn.1, by omega⟩
    (src _ _ _ (VG.Proof.Dsa.encodeBE_length _ _) (by unfold VG.Impl.Dsa.Generation.Layout.p packed; omega) pE)
    (src _ _ _ (VG.Proof.Dsa.encodeBE_length _ _) (by unfold VG.Impl.Dsa.Generation.Layout.q packed; omega) qE)
    (src _ _ _ (VG.Proof.Dsa.encodeBE_length _ _) (by unfold g packed; omega) gE)
    (fun i hi => by rw [h5, off_off]; exact S.scr.region (by omega) (by decide)) hF hS)
    fun t₁ ⟨bytes₁, L₁, R₁, f₁, k₁⟩ => ⟨L₁, ⟨V, W, R₁, h5⟩, S.scr.congr k₁.wr, by rw [← h5]; exact bytes₁,
      S.frame.trans (f₁.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; rw [h5]; simp [stageChanged])),
      k₁.rd.trans S.rd, k₁.wr.trans S.wr⟩

/-- The domain check's inputs. -/
def checkInput (hb : Supported pLen) (s : State) (pl : GeneratorSearchPlan) : Proof.Dsa.AArch64.ParametersInput :=
  ⟨off (s.gpr .x0) domainCheck, pLen, qLen pLen, Spec.Dsa.encodeParams pLen (qLen pLen) (domainOf pLen s pl),
    hb.lengths, VG.Proof.Dsa.Generation.encodeParams_length _ _ _⟩

theorem StageABI.domainCheck_room (hb : Supported pLen) : domainCheck + Impl.Dsa.Layout.usedBytes ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem StageABI.packed_domain (hb : Supported pLen) (A : StageABI pLen s) :
    (⟨off (s.gpr .x0) packed, 2 * pLen + qLen pLen⟩ : Region).Disjoint
      ⟨off (s.gpr .x0) domainCheck, Impl.Dsa.Layout.usedBytes⟩ := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  exact A.parts hb (used_small hb (by decide) (by unfold arithmeticBytes; omega)) (StageABI.domainCheck_room hb)
    (Or.inl (by unfold packed domainCheck; omega))

theorem Packed.check_src {hb : Supported pLen} {A : StageABI pLen s} {u t : State} (P : Packed hb A u t) :
    Src t (checkInput hb s (plan hb A)).base Impl.Dsa.Layout.usedBytes (off (s.gpr .x0) packed)
      (checkInput hb s (plan hb A)).params := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hpk := used_small hb (d := packed) (n := 2 * pLen + qLen pLen) (by decide) (by unfold arithmeticBytes; omega)
  have := VG.Proof.Dsa.AArch64.Generation.arena_source (bs := Spec.Dsa.encodeParams pLen (qLen pLen) (domainOf pLen s (plan hb A)))
    P.scr (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; exact hpk)
    (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; have := used_lt hb; omega)
    (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; exact P.bytes)
    (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; exact A.packed_domain hb)
  exact this

theorem Packed.check_scr {hb : Supported pLen} {A : StageABI pLen s} {u t : State} (P : Packed hb A u t) :
    Scr t (checkInput hb s (plan hb A)).base Impl.Dsa.Layout.usedBytes :=
  P.scr.sub (StageABI.domainCheck_room hb) (by decide)

theorem stage_ok (M : Mont) (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    WP isa (Impl.Dsa.AArch64.Generator.stage M.mm pLen) u (Staged pLen s u) := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hhash := used_small hb (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hpk := used_small hb (d := packed) (n := 2 * pLen + qLen pLen) (by decide) (by unfold arithmeticBytes; omega)
  have rem := plan_remaining hb A
  unfold Impl.Dsa.AArch64.Generator.stage
  refine WP.seq (WP.mono (search_ok M hb A E) fun t S => ?_)
  obtain ⟨V, W, R, h5, h19⟩ := S.rep
  apply VG.Proof.Dsa.AArch64.Generation.onSuccess_ok S.lay R
  · intro t' hm' kt h1
    have S' := S.congr hm' kt
    have hst : statusOf (plan hb A) = 1 := h19.symm.trans h1
    obtain ⟨gv, hgv⟩ : ∃ gv, (plan hb A).remaining 0 = some gv := by
      cases h : (plan hb A).remaining 0 with
      | none => simp [statusOf, h] at hst
      | some gv => exact ⟨gv, rfl⟩
    unfold Impl.Dsa.AArch64.Generation.finishDomain
    refine WP.seq (WP.mono (pack_stage_ok hb A S' hst) fun t₁ P => ?_)
    obtain ⟨V₁, W₁, R₁, h5₁⟩ := P.rep
    have pfit := (A.p_bounds hb).2
    have bounds := VG.Proof.Dsa.Generation.generator_bounds (Nat.lt_trans Nat.zero_lt_one (A.positive hb)) _
      (rem ▸ hgv)
    have qfit : qOf pLen s.mem (s.gpr .x0) < 256 ^ qLen pLen :=
      Nat.lt_of_lt_of_eq (VG.Proof.Dsa.decodeBE_lt _) (by rw [bytesAt_length]; rfl)
    have gdef : gOf (plan hb A) = gv := by simp [gOf, hgv]
    have check := VG.Proof.Dsa.Generation.check_encodedParams (a := domainOf pLen s (plan hb A)) hb.lengths pfit qfit
      (by show gOf (plan hb A) < _; rw [gdef]; exact Nat.lt_trans bounds.2 pfit)
    refine WP.mono (VG.Proof.Dsa.AArch64.Generation.validate_ok M (checkInput hb s (plan hb A)) P.lay R₁
      (by rw [h5₁]; rfl) (by change pLen < 2 ^ 16; omega) (by change qLen pLen < 2 ^ 16; omega)
      P.check_scr (by rw [h5₁]; exact P.check_src)
      (A.framePart hb (StageABI.domainCheck_room hb))
      (A.parts hb hhash (StageABI.domainCheck_room hb) (Or.inl (by decide))))
      fun t₂ ⟨L₂, R₂, f₂, k₂⟩ => ?_
    have res : result pLen s = if Spec.Dsa.parametersValid (domainOf pLen s (plan hb A))
        then some (domainOf pLen s (plan hb A)) else none := by
      rw [rem] at hgv
      simp only [result, Proof.Dsa.GeneratorStage.stage, hgv, Option.bind_eq_bind, Option.bind_some, domainOf, gdef]
    refine ⟨L₂, ⟨V₁, _, R₂, by simpa [VG.Proof.RsaOaep.AArch64.upd] using h5₁, ?_⟩, fun a' ha' => ?_, ?_, k₂.rd.trans P.rd, k₂.wr.trans P.wr⟩
    · simp only [VG.Proof.RsaOaep.AArch64.upd, ite_true, checkInput, check, res]
      by_cases hv : Spec.Dsa.parametersValid (domainOf pLen s (plan hb A)) <;> simp [hv]
    · rw [res] at ha'
      split at ha'
      · obtain rfl := Option.some.inj ha'
        rw [VG.Proof.Dsa.Generation.frame_bytesAt f₂ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact A.packed_domain hb
          · exact (A.framePart hb hpk).symm) (by omega)]
        exact P.bytes
      · exact absurd ha' (by simp)
    · refine P.frame.trans (f₂.mono ?_)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [stageChanged, checkInput]
  · intro t' hm' kt h1
    have S' := S.congr hm' kt
    have hn : (plan hb A).remaining 0 = none := by
      cases h : (plan hb A).remaining 0 with
      | none => rfl
      | some gv => exact absurd (h19.trans (by simp [statusOf, h])) h1
    have res : result pLen s = none := by
      rw [rem] at hn
      simp only [result, Proof.Dsa.GeneratorStage.stage, hn, Option.bind_eq_bind, Option.bind_none]
    obtain ⟨V', W', R', h5', h19'⟩ := S'.rep
    refine ⟨S'.lay, ⟨V', W', R', h5', by rw [h19', res]; simp [statusOf, hn]⟩, fun a ha => absurd ha (by rw [res]; simp),
      S'.frame, S'.rd, S'.wr⟩

end VG.Proof.Dsa.AArch64.Generator
