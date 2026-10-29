module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterCTState
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAttempt
/-! # The outer search repeats exactly when a complete seed attempt requests retry -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/ParameterBodyCT.lean`, which only this module imported.
section

/-! # One public seed attempt advances the outer search and witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64

def ParameterPublic.result (p : ParameterPublic) : Option (Option Spec.Dsa.Params × List Byte) :=
  VG.Proof.Dsa.Generation.seedResult (8 * p.context.geo.pLen) (8 * p.context.geo.qLen)
    ((p.context.seeds.bytes.drop p.seedUsed).take p.context.geo.qLen)
    ((Spec.Dsa.generationChunks p.context.geo.pLen p.context.hs.bytes).map Spec.Dsa.decodeBE)
    (p.context.rand.bytes.drop p.randUsed)

def ParameterPublic.status (p : ParameterPublic) : BitVec 64 :=
  match p.result with
  | none => 0
  | some (none, _) => 3
  | some (some _, _) => 1

def ParameterPublic.nextRand (p : ParameterPublic) : Nat :=
  match p.result with
  | none => p.randUsed
  | some (_, rest) => p.context.rand.bytes.length - rest.length

def ParameterBodyAfter (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧
    W 10 = BitVec.ofNat 64 (p.seedUsed + p.context.geo.qLen) ∧ W 19 = p.status ∧
    (p.status = 3 → W 16 = BitVec.ofNat 64 p.nextRand)) ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen ∧
  p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length

theorem parameter_body_ct (H : GenerationHashes) (G : GeneratorStage)  (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterTaken pLen qLen))
      (seedAttempt H.sha1 H.sha256 G.run T.run pLen qLen) (fun _ _ => True) := by
  apply (seedAttempt_ct H G T pLen qLen sizes).mono ?_ (fun _ _ h => h)
  rintro s t ⟨p, ⟨room, hs⟩, ⟨room', ht⟩, hsp⟩
  exact ⟨p.seed room, hs, ht, hsp⟩

theorem parameter_body_ready (H : GenerationHashes) (G : GeneratorStage)  (T : PrimeTest)
    {pLen qLen : Nat} {p : ParameterPublic} {s : State} (h : ParameterTaken pLen qLen p s) :
    WP isa (seedAttempt H.sha1 H.sha256 G.run T.run pLen qLen) s (ParameterBodyAfter pLen qLen p) := by
  obtain ⟨room, ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, hq⟩, hp⟩⟩ := h
  change p.context.geo.pLen = pLen at hp
  change p.context.geo.qLen = qLen at hq
  subst pLen; subst qLen
  refine WP.mono (seedAttempt_ok H G T hm (p.seed room).seed (p.seed room).length seed h1 h16 p.randBound)
    fun t ⟨Wt, used, ht, bound, u16, slots, outcome, _, _, wr⟩ => ?_
  change used ≤ p.context.rand.bytes.length at bound
  have cursor := (slots 10 (by simp [searchSlots])).trans h10
  have status : Wt 19 = p.status ∧ (p.status = 3 → Wt 16 = BitVec.ofNat 64 p.nextRand) := by
    change SeedOutcome p.context p.result Wt used t at outcome
    rcases outcome with ⟨hs, hr⟩ | ⟨hs, hr⟩ | ⟨hs, a, hr, _⟩
    · exact ⟨by simpa [ParameterPublic.status, hr] using hs,
        by simp [ParameterPublic.status, hr]⟩
    · refine ⟨by simpa [ParameterPublic.status, hr] using hs, fun _ => ?_⟩
      simpa only [ParameterPublic.nextRand, hr, List.length_drop, Nat.sub_sub_self bound] using u16
    · exact ⟨by simpa [ParameterPublic.status, hr] using hs,
        by simp [ParameterPublic.status, hr]⟩
  exact ⟨⟨Wt, ht, cursor, status⟩, rfl, rfl, room⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64

def ParameterPublic.continues (p : ParameterPublic) : Bool := !p.exhausted && (p.status == (3#64))

def ParameterPublic.next (p : ParameterPublic) (hc : p.continues = true) : ParameterPublic where
  context := p.context
  seedUsed := p.seedUsed + p.context.geo.qLen
  seedBound := by
    have hn : p.exhausted = false := by cases he : p.exhausted <;> simp_all [continues]
    have hb := p.seedBound
    have h := of_decide_eq_false hn
    omega
  randUsed := p.nextRand
  randBound := by
    cases hr : p.result with
    | none => simpa [nextRand, hr] using p.randBound
    | some res => simp only [nextRand, hr]; exact Nat.sub_le _ _

def ParameterIterationAfter (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  isa.eval (.zero .x .x0) s = some p.continues ∧
    ∀ hc : p.continues = true, ParameterBefore pLen qLen (p.next hc) s

theorem parameter_status {pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterBodyAfter pLen qLen p s) :
    WP isa (.block tapeStatus) s (ParameterIterationAfter pLen qLen p) := by
  obtain ⟨⟨W, hm, hu, hs, hr⟩, hp, hq, room⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = false := by apply decide_eq_false; omega
  refine WP.mono (tapeStatus_ok hm.layout R) fun t ⟨hz, hmem, hk⟩ => ?_
  refine ⟨?_, fun hc => ?_⟩
  · change eval (.zero .x .x0) t = some p.continues
    rw [hz]
    simp only [hs, ParameterPublic.continues, exhausted, Bool.not_false, Bool.true_and]
  · have retry : p.status = 3 := by
      simpa [ParameterPublic.continues, exhausted] using hc
    exact ⟨⟨W, hm.congr2 hmem (hk.mono (by decide)), hu, hr retry⟩,
      hp, hq⟩

theorem parameter_exhausted {pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterChecked pLen qLen p s) (hb : isa.eval (.nonzero .x .x0) s = some true) :
    WP isa (.block ([VG.Impl.Bignum.AArch64.movi .x0 3] ++ Impl.Dsa.AArch64.Random.store 152 .x0 ++ [VG.Impl.Bignum.AArch64.movi .x0 1])) s
      (ParameterIterationAfter pLen qLen p) := by
  obtain ⟨⟨W, hm, _⟩, _⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = true := Option.some.inj (h.2.symm.trans hb)
  have cont : p.continues = false := by simp [ParameterPublic.continues, exhausted]
  refine WP.mono (tapeExhausted_ok hm.layout R) fun t ⟨hz, _⟩ => ?_
  exact ⟨by simpa only [cont] using hz, fun hc => by rw [cont] at hc; contradiction⟩

end VG.Proof.Dsa.AArch64.Generation
