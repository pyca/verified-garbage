module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorPlanCT

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrime
/-! # Prime search composes with generator selection and final domain checking -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SeedPrimeResultCT.lean`, which only this module imported.
section

/-! # Public prime-search outcomes select the next generator phase -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64

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

def SeedPrimeAfter (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 19 = p.primeStatus) ∧
  (p.primeStatus = 1 → ∃ value rest, p.primeResult = some (some value, rest) ∧
    ∃ domain, SeedGeneratorBefore pLen qLen (p.generatorPublic value rest domain) s)

theorem seedPrime_after (H : GenerationHashes) (T : PrimeTest)
    {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore pLen qLen p s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) s
      (SeedPrimeAfter pLen qLen p) := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, hq⟩, hp, bq⟩ := h
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
      rfl⟩, rfl, bq'⟩, bp, be⟩
    · exact (slots 1 (by simp [searchSlots])).trans h1
    · change Wt 16 = BitVec.ofNat 64 (p.context.rand.bytes.length - (p.context.rand.bytes.drop used).length)
      rw [List.length_drop, Nat.sub_sub_self bound]
      exact u16
    · exact (slots 10 (by simp [searchSlots])).trans h10
  · have status : p.primeStatus = 3 := by simp [SeedPublic.primeStatus, SeedPublic.primeResult, hr]
    exact ⟨⟨Wt, ht, hs.trans status.symm⟩, by simp [status]⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem seedGeneratorBefore_congr {pLen qLen : Nat} {p : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedGeneratorBefore pLen qLen p t :=
  ⟨seedPrimeBefore_congr h.1 hm hk, hm ▸ h.2.1, hm ▸ h.2.2⟩

theorem seedPrimeAfter_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeAfter pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedPrimeAfter pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨value, rest, hr, domain, ht⟩ := next ha
  exact ⟨value, rest, hr, domain, seedGeneratorBefore_congr ht hm hk⟩

theorem seedPrimeAfter_related {pLen qLen : Nat} {s t : State}
    (h : Two (fun p s => SeedPrimeAfter pLen qLen p s ∧ p.primeStatus = 1) s t) :
    Two (SeedGeneratorBefore pLen qLen) s t := by
  obtain ⟨p, hs, ht, hsp⟩ := h
  obtain ⟨vs, rs, hrs, ds, hgs⟩ := hs.1.2 hs.2
  obtain ⟨vt, rt, hrt, dt, hgt⟩ := ht.1.2 ht.2
  have eqs := Option.some.inj (hrs.symm.trans hrt)
  have hv := Option.some.inj (congrArg Prod.fst eqs)
  have hr : rs = rt := congrArg Prod.snd eqs
  subst vt; subst rt
  exact ⟨p.generatorPublic vs rs ds, hgs, hgt, hsp⟩

theorem seedPrimeFinish_ct (H : GenerationHashes) (G : GeneratorStage)  (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore pLen qLen))
      (.seq (primeSearch H.sha1 H.sha256 T.run pLen qLen)
        (onSuccess (generatorCall G.run pLen)))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H T pLen qLen sizes)
    (fun _ _ h => seedPrime_after H T h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (generatorCall_ct G pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64.Generation
