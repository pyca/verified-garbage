module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedCTState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkTake
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorPlanCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedValidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackMemoryCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Impl.Dsa.Generation.Layout
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
import VerifiedGarbage.Impl.RsaOaep.X86_64
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupState
import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSearchPlanCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchInitCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashChoice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroupCT
/-! # Public seed and witness cursors for the complete parameter search -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedPrimeResultCT.lean`, which only this module imported.
section

/-! # Public prime-search outcomes select the next generator phase -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MillerRabin.X86_64

def SeedPublic.primeResult (p : SeedPublic) : Option (Option Nat × List Byte) :=
  Spec.Dsa.primeFromSeed (8 * p.context.geo.pLen) (8 * p.context.geo.qLen)
    (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes) p.seed.bytes (p.context.rand.bytes.drop p.used)

def SeedPublic.primeStatus (p : SeedPublic) : BitVec 64 :=
  match p.primeResult with
  | none => 0
  | some (none, _) => 3
  | some (some _, _) => 1

def SeedPublic.generatorPublic (p : SeedPublic) (value : Nat) (rest : List Byte)
    (domain : VG.Proof.Dsa.Generation.PDomain p.context.geo.pLen value) : SeedGeneratorPublic :=
  ⟨{ p with used := p.context.rand.bytes.length - rest.length, bound := Nat.sub_le _ _ }, value, domain⟩

def SeedPrimeAfter (n pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 19 = p.primeStatus) ∧
  (p.primeStatus = 1 → ∃ value rest, p.primeResult = some (some value, rest) ∧
    ∃ domain, SeedGeneratorBefore n pLen qLen (p.generatorPublic value rest domain) s)

theorem seedPrime_after (H : GenerationHashes) (T : PrimeTest)
    {n pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore n pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) s
      (SeedPrimeAfter n pLen qLen p) := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, hf, hw, hq⟩, hp, bq⟩ := h
  subst pLen; subst qLen
  refine WP.mono (seedPrime_ok H T hm p.seed p.length seed h1 bq h16 p.bound)
    fun t ⟨Wt, used, bound, ht, u16, slots, bq', outcome, ff, rd, wr⟩ => ?_
  rcases outcome with ⟨hs, hr⟩ | ⟨hs, value, hr, domain, bp, be⟩ | ⟨hs, hr⟩
  · have status : p.primeStatus = 0 := by simp [SeedPublic.primeStatus, SeedPublic.primeResult, hr]
    exact ⟨⟨Wt, ht, hs.trans status.symm⟩, by simp [status]⟩
  · have result : p.primeResult = some (some value, p.context.rand.bytes.drop used) := hr
    have status : p.primeStatus = 1 := by simp [SeedPublic.primeStatus, result]
    refine ⟨⟨Wt, ht, hs.trans status.symm⟩, fun _ =>
      ⟨value, p.context.rand.bytes.drop used, result, domain, ?_⟩⟩
    refine ⟨⟨⟨⟨Wt, ht, ?_, ?_, ?_⟩, seed.frame ff rd wr,
      hf.congr (ht.layout.rsp.trans hm.layout.rsp.symm) wr, wr.trans hw, rfl⟩, rfl, bq'⟩, bp, be⟩
    · exact (slots 1 (by simp [searchSlots])).trans h1
    · change Wt 16 = BitVec.ofNat 64 (p.context.rand.bytes.length - (p.context.rand.bytes.drop used).length)
      rw [List.length_drop, Nat.sub_sub_self bound]
      exact u16
    · exact (slots 10 (by simp [searchSlots])).trans h10
  · have status : p.primeStatus = 3 := by simp [SeedPublic.primeStatus, SeedPublic.primeResult, hr]
    exact ⟨⟨Wt, ht, hs.trans status.symm⟩, by simp [status]⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedValidateCT.lean`, which only this module imported.
section

/-! # Final domain validation uses the generation arena and exact packed bytes -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.X86_64


variable {checkName : String}

structure ValidationContext where
  context : GenerationContext
  params : List Byte
  length : params.length = 2 * context.geo.pLen + context.geo.qLen

theorem GenerationGeometry.validationRoom (p : GenerationGeometry) :
    domainCheck + Impl.Dsa.Layout.usedBytes ≤ usedBytes p.pLen := by
  rcases p.width with h | h | h <;> rw [h] <;> decide

def ValidationContext.plan (p : ValidationContext) : ValidatePublic where
  input := p.context.geo.parametersInput p.params p.length
  B := p.context.geo.B
  F := p.context.geo.F
  S := p.context.geo.hash
  base := rfl
  frame := p.context.geo.frame_part p.context.geo.validationRoom
  hash := p.context.geo.parts_disjoint
    (p.context.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide))
    p.context.geo.validationRoom (Or.inl (by decide))
  stack := (p.context.geo.stack_part p.context.geo.validationRoom).sub_left
    (below_sub (by decide) (by decide))
  paramsStack := by
    change (below p.context.geo.F 8).Disjoint ⟨off p.context.geo.B packed, p.params.length⟩
    rw [p.length]
    have pn : p.context.geo.pLen ≤ 384 := by rcases p.context.geo.width with h | h | h <;> omega
    have qn : p.context.geo.qLen ≤ 32 := by rcases p.context.geo.qWidth with h | h <;> omega
    exact (p.context.geo.stack_part (p.context.geo.small_bound (d := packed)
      (n := 2 * p.context.geo.pLen + p.context.geo.qLen) (by decide)
      (by unfold arithmeticBytes; omega))).sub_left (below_sub (by decide) (by decide))

def SeedValidateBefore (pLen qLen : Nat) (p : ValidationContext) (s : State) : Prop :=
  GenerationMemoryBefore p.context s ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B packed) (2 * p.context.geo.pLen + p.context.geo.qLen) = p.params ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

theorem seedValidate_before {pLen qLen : Nat} {p : ValidationContext} {s : State}
    (h : SeedValidateBefore pLen qLen p s) : ValidateBefore pLen qLen p.plan s := by
  obtain ⟨⟨W, hm⟩, bytes, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have pn : p.context.geo.pLen ≤ 384 := by rcases p.context.geo.width with hh | hh | hh <;> omega
  have qn : p.context.geo.qLen ≤ 32 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  have packedBound := p.context.geo.small_bound (d := packed)
    (n := 2 * p.context.geo.pLen + p.context.geo.qLen) (by decide) (by unfold arithmeticBytes; omega)
  have sep := p.context.geo.parts_disjoint packedBound p.context.geo.validationRoom
    (Or.inl (by unfold packed domainCheck; omega))
  have source : Src s (off p.context.geo.B domainCheck) Impl.Dsa.Layout.usedBytes
      (off p.context.geo.B packed) p.params := by
    apply arena_source hm.scratch
    · simpa only [p.length] using packedBound
    · rw [p.length]; omega
    · simpa only [p.length] using bytes
    · simpa only [p.length, GenerationGeometry.part] using sep
  exact ⟨hm.layout, ⟨V, W, R, (hm.slots 5 (by simp [generationSlots])).trans p.context.baseSlot⟩,
    hm.scratch.sub p.context.geo.validationRoom (by decide), source, hp, hq⟩

theorem seedValidate_ct (M : Mont) (Sq : MontS) (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (SeedValidateBefore pLen qLen))
      (Impl.Dsa.X86_64.Generation.validate (checkName := checkName) Sq.mm M.mm pLen qLen) (fun _ _ => True) :=
  two_map ValidationContext.plan (fun _ _ h => seedValidate_before h) (validate_ct (checkName := checkName) M Sq pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FinishDomainCT.lean`, which only this module imported.
section

/-! # Compose domain packing with the final verified parameter check -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

structure DomainFinishPublic where
  context : GenerationContext
  params : Spec.Dsa.Params

def DomainFinishPublic.validation (p : DomainFinishPublic) : ValidationContext :=
  ⟨p.context, Spec.Dsa.encodeParams p.context.geo.pLen p.context.geo.qLen p.params,
    VG.Proof.Dsa.Generation.encodeParams_length _ _ _⟩

def DomainFinishBefore (pLen qLen : Nat) (p : DomainFinishPublic) (s : State) : Prop :=
  GenerationMemoryBefore p.context s ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B VG.Impl.Dsa.Generation.Layout.p) p.context.geo.pLen =
    Spec.Dsa.encodeBE p.context.geo.pLen p.params.p ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B q) p.context.geo.qLen =
    Spec.Dsa.encodeBE p.context.geo.qLen p.params.q ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B g) p.context.geo.pLen =
    Spec.Dsa.encodeBE p.context.geo.pLen p.params.g ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

theorem domainFinish_pack {pLen qLen : Nat} {p : DomainFinishPublic} {s : State}
    (h : DomainFinishBefore pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pack pLen qLen) s (SeedValidateBefore pLen qLen p.validation) := by
  obtain ⟨⟨W, hm⟩, bp, bq, bg, hp, hq⟩ := h
  have step := seedPack_ok hm _ _ _ (VG.Proof.Dsa.encodeBE_length _ _)
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) bp bq bg
  rw [hp, hq] at step
  refine WP.mono step fun t ⟨ht, bytes, _, _, _⟩ => ⟨⟨W, ht⟩, ?_, hp, hq⟩
  change Spec.Rsa.bytesAt t.mem (off p.context.geo.B packed) (2 * p.context.geo.pLen + p.context.geo.qLen) =
    Spec.Dsa.encodeParams p.context.geo.pLen p.context.geo.qLen p.params
  simpa only [Spec.Dsa.encodeParams, hp, hq] using bytes

theorem finishDomain_ct (M : Mont) (Sq : MontS) (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (DomainFinishBefore pLen qLen))
      (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.finishDomain
  refine RelCT.seq (two_post
    ((two_map DomainFinishPublic.context (fun _ _ h => h.1) (pack_ct pLen qLen sizes)).mono
      (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => domainFinish_pack h)) ?_
  exact two_map DomainFinishPublic.validation (fun _ _ h => h) (seedValidate_ct (checkName := checkName) M Sq pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedGeneratorCT.lean`, which only this module imported.
section

/-! # Generator selection supplies public inputs to the final validation gate -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64

def SeedGeneratorPublic.result (p : SeedGeneratorPublic) : Option Nat :=
  Spec.Dsa.generator p.value p.qValue
    ((Spec.Dsa.generationChunks p.seed.context.geo.pLen p.seed.context.hs.bytes).map Spec.Dsa.decodeBE)

def SeedGeneratorPublic.status (p : SeedGeneratorPublic) : BitVec 64 :=
  if p.result.isSome then 1 else 3

def SeedGeneratorPublic.finish (p : SeedGeneratorPublic) : DomainFinishPublic :=
  ⟨p.seed.context, ⟨p.value, p.qValue, p.result.getD 0⟩⟩

def SeedGeneratorAfter (pLen qLen : Nat) (p : SeedGeneratorPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.seed.context W s ∧ W 19 = p.status) ∧
  (p.status = 1 → DomainFinishBefore pLen qLen p.finish s)

theorem seedGenerator_ct (M : Mont) (Sq : MontS) (n pLen qLen : Nat)
    (hl : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen))
      (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm pLen) (fun _ _ => True) :=
  two_map SeedGeneratorPublic.plan (fun _ _ h => seedGenerator_start h) (nativeGenerator_ct M Sq pLen hl)

theorem seedGenerator_after (M : Mont) (Sq : MontS) {n pLen qLen : Nat}
    {p : SeedGeneratorPublic} {s : State} (h : SeedGeneratorBefore n pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm pLen) s (SeedGeneratorAfter pLen qLen p) := by
  obtain ⟨⟨⟨⟨W, hm, _⟩, _, _, _, hq⟩, hp, bq⟩, bp, be⟩ := h
  have step := seedGenerator_ok M Sq hm p.value p.qValue p.domain bp be bq
  rw [hp] at step
  refine WP.mono step fun t ⟨Wt, ht, _, bp', bq', outcome, _, _, _⟩ => ?_
  rcases outcome with ⟨hs, hr⟩ | ⟨gv, hs, hr, _, _, bg⟩
  · have status : p.status = 3 := by simp [SeedGeneratorPublic.status, SeedGeneratorPublic.result, hp, hr]
    exact ⟨⟨Wt, ht, hs.trans status.symm⟩, by simp [status]⟩
  · have result : p.result = some gv := by simpa [SeedGeneratorPublic.result, hp] using hr
    have status : p.status = 1 := by simp [SeedGeneratorPublic.status, result]
    refine ⟨⟨Wt, ht, hs.trans status.symm⟩, fun _ => ⟨⟨Wt, ht⟩, ?_, bq', ?_, hp, hq⟩⟩
    · simpa [SeedGeneratorPublic.finish, hp] using bp'
    · simpa [SeedGeneratorPublic.finish, result, hp] using bg

theorem seedGeneratorAfter_congr {pLen qLen : Nat} {p : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorAfter pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedGeneratorAfter pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨⟨Wt, ht⟩, bp, bq, bg, hp, hq⟩ := next ha
  exact ⟨⟨Wt, ht.congr hm hk⟩, hm ▸ bp, hm ▸ bq, hm ▸ bg, hp, hq⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedGeneratorFinishCT.lean`, which only this module imported.
section

/-! # Complete generator search, phase gate, packing, and validation timing -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

theorem seedGeneratorFinish_ct (M : Mont) (Sq : MontS) (n pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore n pLen qLen))
      (.seq (generatorSearch Sq.mm M.mm pLen) (onSuccess (finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen)))
      (fun _ _ => True) := by
  have width : pLen = 128 ∨ pLen = 256 ∨ pLen = 384 := by
    rcases sizes with h | h | h <;> simp [h.1]
  refine RelCT.seq (two_post (seedGenerator_ct M Sq n pLen qLen width)
    (fun _ _ h => seedGenerator_after M Sq h)) ?_
  apply onSuccess_ct (Φ := SeedGeneratorAfter pLen qLen) (fun p : SeedGeneratorPublic => p.seed.context) SeedGeneratorPublic.status
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedGeneratorAfter_congr h hm hk)
  exact two_map SeedGeneratorPublic.finish (fun _ _ h => h.1.2 h.2) (finishDomain_ct (checkName := checkName) M Sq pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedSearchStateCT.lean`, which only this module imported.
section

/-! # Instantiate the public prime-search state from actual persistent-frame words -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem seedPrime_memory {p : SeedPublic} {s : State} {W : Nat → BitVec 64}
    (hm : GenerationMemory p.context W s) (seed : GenerationTapeMemory p.seed s)
    (h1 : W 1 = p.seed.ptr) (h10 : W 10 = p.seedCursor)
    (hq : Spec.Rsa.bytesAt s.mem (off p.context.geo.B q) p.context.geo.qLen =
      Spec.Dsa.encodeBE p.context.geo.qLen (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)) :
    SearchMemory p.searchPlan W s := by
  have state := hm.searchState p.seed p.length seed h1 hq
  have h5 : W 5 = p.context.saved 5 := hm.slots 5 (by simp [generationSlots])
  refine {
    layout := state.layout
    rep := state.rep
    slots := seedPrime_words hm h1 h10
    label := state.label.congr rfl rfl rfl ?_
    seedRead := state.seedRead
    wrappedWrite := state.wrappedWrite
    hashWrite := state.hashWrite
    seed := state.seed
    scratch := state.scratch
    qSource := ?_
    tape := state.tape
    shapedWrite := ?_
    pWrite := ?_
    exponentWrite := ?_
    witnessWrite := ?_
    arena := ?_
    tapeCover := state.tapeCover }
  · change p.context.saved 28 = W 28
    exact (hm.slots 28 (by simp [generationSlots])).symm
  · have src := state.qSource
    change Src s (off p.context.geo.B arithmetic) arithmeticBytes (off (W 5) q) _ at src
    change Src s (off p.context.geo.B arithmetic) arithmeticBytes (off (p.context.saved 5) q) _
    rw [h5] at src
    exact src
  · have write := state.shapedWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (W 5) shaped) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (p.context.saved 5) shaped) i) 1
    rw [h5] at write
    exact write
  · have write := state.pWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (W 5) VG.Impl.Dsa.Generation.Layout.p) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (p.context.saved 5) VG.Impl.Dsa.Generation.Layout.p) i) 1
    rw [h5] at write
    exact write
  · have write := state.exponentWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (W 5) exponent) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (p.context.saved 5) exponent) i) 1
    rw [h5] at write
    exact write
  · have write := state.witnessWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (W 5) witness) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (off (off (p.context.saved 5) witness) i) 1
    rw [h5] at write
    exact write
  · have a := state.arena
    change Scr s (W 5) domainCheck at a
    change Scr s (p.context.saved 5) domainCheck
    rw [h5] at a
    exact a

theorem seedPrime_start {n pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore n pLen qLen p s) : SearchStart n pLen qLen p.search s := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, hf, hw, heQ⟩, heP, hq⟩ := h
  exact ⟨⟨W, seedPrime_memory hm seed h1 h10 hq, h16⟩,
    hm.scratch.sub (p.context.geo.small_bound (d := control) (n := 24) (by decide) (by decide)) (by decide),
    hf, hw, p.bound, heP, heQ, rfl⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PSearchLoopCT.lean`, which only this module imported.
section

/-! # Timing of the bounded native p search, including its exact retry cursor -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

private def searchLoopInv (n pLen qLen remaining : Nat) : State → State → Prop :=
  Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchBefore n pLen qLen p s

section
variable (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
variable (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
variable (sizes : GenerationSizes pLen qLen)
variable (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
variable (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
variable (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
variable (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
variable (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
variable (hd : (if qLen = 20 then G1 else G256).D = qLen)

include hG hmatch hsize hhash hseedsize hd sizes

theorem searchIteration_ready {p : SearchPublic} {s : State} (h : SearchBefore n pLen qLen p s) :
    WP isa (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) s (SearchIterationAfter n pLen qLen p) := by
  unfold pSearchIteration
  simp only [seqs]
  refine WP.seq (WP.mono (searchBody_ready G1 G256 T hG hmatch hsize hhash hseedsize hd h)
    fun _ ht => searchIteration_tail ⟨ht, h.2.2.2.2.2⟩ ?_ ?_)
  all_goals rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

include hn

private theorem searchLoop_step (remaining : Nat) :
    RelCT isa (searchLoopInv n pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (fun s t => isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
        (isa.eval .e s = some true → ∃ next < remaining, searchLoopInv n pLen qLen next s t)) := by
  have step : RelCT isa (searchLoopInv n pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchIterationAfter n pLen qLen p s) := by
    refine two_post ((searchIteration_ct G1 G256 T n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (searchIteration_ready G1 G256 T n H pLen qLen sizes hG hmatch hsize hhash hseedsize hd h.2)
      fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have next := hs.2 cont
  have bound : p.counter + 1 < 32 * pLen := by
    have hb := (of_decide_eq_true cont).2
    rw [show p.plan.attempt.construct.len = pLen from next.2.2.2.2.2.1] at hb
    exact hb
  refine ⟨32 * pLen - (p.counter + 1), by omega, p.next cont, ⟨rfl, next⟩, rfl, ht.2 cont⟩

theorem pSearchLoop_ct : RelCT isa (Two (SearchBefore n pLen qLen))
    (.loop (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) .e) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht⟩ es et
  exact RelCT.loop (searchLoopInv n pLen qLen)
    (searchLoop_step G1 G256 T n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd)
    (32 * pLen - p.counter) s t a b s' t' ⟨p, ⟨rfl, hs⟩, rfl, ht⟩ es et

end
end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/NativeSearchCT.lean`, which only this module imported.
section

/-! # The complete bounded native p search has a public trace -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem primeSearch_ct (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchStart n pLen qLen)) (primeSearch G1 G256 T.run pLen qLen)
      (fun _ _ => True) := by
  unfold primeSearch pSearch
  refine RelCT.seq (two_post ((two_map SearchPublic.returnFrame (fun _ _ h => searchStart_frame h)
    controlBase_ct).mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    (fun _ _ h => searchBase_ready h)) (RelCT.seq (searchInit_ct n pLen qLen) ?_)
  exact pSearchLoop_ct G1 G256 T n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedPrimeCT.lean`, which only this module imported.
section

/-! # The accepted subgroup enters the complete public-trace prime search -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem seedPrime_ct (H : GenerationHashes) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore n pLen qLen))
      (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) (fun _ _ => True) := by
  have hq : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  exact two_map SeedPublic.search (fun _ _ h => seedPrime_start h)
    (primeSearch_ct H.sha1 H.sha256 T n hn (generationHash qLen) pLen qLen sizes
      (H.streamOK qLen) (H.hash_matches qLen) (H.hash_size qLen)
      (generationHash_seed hq) (H.seed_size hq) (H.hash_width hq))

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedPrimeFinishCT.lean`, which only this module imported.
section

/-! # Prime search composes with generator selection and final domain checking -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

theorem seedGeneratorBefore_congr {n pLen qLen : Nat} {p : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore n pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedGeneratorBefore n pLen qLen p t :=
  ⟨seedPrimeBefore_congr h.1 hm hk, hm ▸ h.2.1, hm ▸ h.2.2⟩

theorem seedPrimeAfter_congr {n pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeAfter n pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedPrimeAfter n pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨value, rest, hr, domain, ht⟩ := next ha
  exact ⟨value, rest, hr, domain, seedGeneratorBefore_congr ht hm hk⟩

theorem seedPrimeAfter_related {n pLen qLen : Nat} {s t : State}
    (h : Two (fun p s => SeedPrimeAfter n pLen qLen p s ∧ p.primeStatus = 1) s t) :
    Two (SeedGeneratorBefore n pLen qLen) s t := by
  obtain ⟨p, hs, ht⟩ := h
  obtain ⟨vs, rs, hrs, ds, hgs⟩ := hs.1.2 hs.2
  obtain ⟨vt, rt, hrt, dt, hgt⟩ := ht.1.2 ht.2
  have eqs := Option.some.inj (hrs.symm.trans hrt)
  have hv := Option.some.inj (congrArg Prod.fst eqs)
  have hr : rs = rt := congrArg Prod.snd eqs
  subst vt; subst rt
  exact ⟨p.generatorPublic vs rs ds, hgs, hgt⟩

theorem seedPrimeFinish_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore n pLen qLen))
      (.seq (primeSearch H.sha1 H.sha256 T.run pLen qLen)
        (onSuccess (.seq (generatorSearch Sq.mm M.mm pLen) (onSuccess (finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen)))))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H T n hn pLen qLen sizes)
    (fun _ _ h => seedPrime_after H T h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter n pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (seedGeneratorFinish_ct (checkName := checkName) M Sq n pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SeedAttemptCT.lean`, which only this module imported.
section

/-! # Timing of the complete native DSA seed attempt -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

def SeedAttemptBefore (n pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  SeedBefore n qLen p s ∧ p.context.geo.pLen = pLen

theorem seedAttempt_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedAttemptBefore n pLen qLen))
      (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen) (fun _ _ => True) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  unfold seedAttempt
  refine RelCT.seq (two_post
    (two_map (fun p : SeedPublic => p) (fun _ _ h => h.1) (seedSubgroup_ct H T n hn qLen width))
    (fun _ _ h => seedSubgroup_after H T h.1 h.2)) ?_
  apply onSuccess_ct (Φ := SeedSubgroupAfter n pLen qLen) SeedPublic.context SeedPublic.subgroupStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedSubgroupAfter_congr h hm hk)
  exact two_map SeedPublic.afterSubgroup (fun _ _ h => h.1.2 h.2) (seedPrimeFinish_ct (checkName := checkName) H M Sq T n hn pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

structure ParameterPublic where
  context : GenerationContext
  seedUsed : Nat
  seedBound : seedUsed ≤ context.seeds.bytes.length
  randUsed : Nat
  randBound : randUsed ≤ context.rand.bytes.length
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout context.geo.B wr

def ParameterBefore (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 10 = BitVec.ofNat 64 p.seedUsed ∧ W 16 = BitVec.ofNat 64 p.randUsed) ∧
  FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

def ParameterPublic.exhausted (p : ParameterPublic) : Bool :=
  decide (p.context.seeds.bytes.length - p.seedUsed < p.context.geo.qLen)

def ParameterChecked (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore n pLen qLen p s ∧ isa.eval .b s = some p.exhausted

def ParameterAvailable (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ParameterBefore n pLen qLen p s ∧ p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length

def ParameterPublic.seed (p : ParameterPublic)
    (room : p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length) : SeedPublic where
  context := p.context
  seed := p.context.seeds.slice p.seedUsed p.context.geo.qLen room
  length := by
    change ((p.context.seeds.bytes.drop p.seedUsed).take p.context.geo.qLen).length = _
    simp only [List.length_take, List.length_drop]; omega
  used := p.randUsed
  seedCursor := BitVec.ofNat 64 (p.seedUsed + p.context.geo.qLen)
  bound := p.randBound
  ws := p.ws
  wr := p.wr
  header := p.header

def ParameterTaken (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  ∃ room, SeedAttemptBefore n pLen qLen (p.seed room) s

theorem parameter_check {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterBefore n pLen qLen p s) :
    WP isa (.block (chunkCheck seedTape qLen)) s (ParameterChecked n pLen qLen p) := by
  obtain ⟨⟨W, hm, h10, h16⟩, hf, hw, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : qLen < 2 ^ 31 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  have total := (hm.slots 9 (by simp [generationSlots])).trans p.context.seedsLengthSlot
  refine WP.mono (chunkCheck_ok hm.layout R seedTape (by decide) (by decide)
    hl h10 total p.seedBound p.context.seeds.size) fun t ⟨hc, hmem, hk⟩ => ?_
  exact ⟨⟨⟨W, hm.congr2 hmem hk, h10, h16⟩,
    hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, hp, hq⟩,
    by simp only [eval, hc, ParameterPublic.exhausted, hq]⟩

theorem parameter_available {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterChecked n pLen qLen p s) (hb : isa.eval .b s = some false) :
    ParameterAvailable n pLen qLen p s := by
  have hn := of_decide_eq_false (Option.some.inj (h.2.symm.trans hb))
  exact ⟨h.1, by have := p.seedBound; omega⟩

theorem parameter_take {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterAvailable n pLen qLen p s) :
    WP isa (.block (tapeTake seedTape qLen)) s (ParameterTaken n pLen qLen p) := by
  obtain ⟨⟨⟨W, hm, h10, h16⟩, hf, hw, hp, hq⟩, room⟩ := h
  subst qLen
  obtain ⟨V, R⟩ := hm.rep
  have hl : p.context.geo.qLen < 2 ^ 31 := by rcases p.context.geo.qWidth with hh | hh <;> omega
  refine WP.mono (chunkTake_ok hm.layout R seedTape (by decide) (by decide)
    (by decide) (by decide) (by decide) hl h10) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (p.context.frame_single ft) kt.2.1 kt.2.2
  refine ⟨room, ⟨⟨_, ht, ?_, ?_, ?_⟩, ht.seeds.slice room,
    hf.congr (kt.gpr (by decide)) kt.2.2, kt.2.2.trans hw, rfl⟩, hp⟩
  · have base := (hm.slots 8 (by simp [generationSlots])).trans p.context.seedsSlot
    simp [seedTape, upd, ParameterPublic.seed, GenerationTape.slice, base]
  · simpa [seedTape, upd, ParameterPublic.seed] using h16
  · simp [seedTape, upd, ParameterPublic.seed]

end VG.Proof.Dsa.X86_64.Generation
