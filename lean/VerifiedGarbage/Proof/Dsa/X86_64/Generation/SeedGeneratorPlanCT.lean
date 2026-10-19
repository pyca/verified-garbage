module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSearchPlanCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeGeneratorCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public accepted primes determine the generator-search plan -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure SeedGeneratorPublic where
  seed : SeedPublic
  value : Nat
  domain : VG.Proof.Dsa.Generation.PDomain seed.context.geo.pLen value

def SeedGeneratorPublic.qValue (p : SeedGeneratorPublic) : Nat :=
  Spec.Dsa.qCandidate (8 * p.seed.context.geo.qLen) p.seed.seed.bytes

def SeedGeneratorPublic.plan (p : SeedGeneratorPublic) : GeneratorSearchPlan := by
  have fit : p.value < 256 ^ p.seed.context.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using p.domain.upper
  have decode := VG.Proof.Dsa.decodeBE_encodeBE fit
  have expFit : (p.value - 1) / p.qValue < 256 ^ p.seed.context.geo.pLen :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) fit
  exact p.seed.context.generatorPlan (upd p.seed.words 16 (BitVec.ofNat 64 p.seed.used))
    (Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value)
    (Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue))
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _)
    (by rw [decode]; omega_using [p.domain.large])
    (by rw [decode]; exact p.domain.odd) p.qValue
    (by rw [decode, VG.Proof.Dsa.decodeBE_encodeBE expFit])

def SeedGeneratorBefore (n pLen qLen : Nat) (p : SeedGeneratorPublic) (s : State) : Prop :=
  SeedPrimeBefore n pLen qLen p.seed s ∧
  Spec.Rsa.bytesAt s.mem (off p.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value ∧
  Spec.Rsa.bytesAt s.mem (off p.seed.context.geo.B exponent) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue)

theorem seedGenerator_start {n pLen qLen : Nat} {p : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore n pLen qLen p s) : GeneratorSearchStart pLen p.plan s := by
  obtain ⟨⟨⟨⟨W, hm, h1, h16, h10⟩, _, _, _, _⟩, hp, _⟩, bp, be⟩ := h
  have state := hm.generatorState p.plan.core.pb p.plan.core.eb p.plan.core.pLength p.plan.core.eLength
    p.plan.core.pPositive p.plan.core.pOdd p.qValue p.plan.exponentValue bp be
  refine ⟨⟨W, { state with slots := ?_ }⟩, hp⟩
  intro k hk
  change W k = upd p.seed.words 16 (BitVec.ofNat 64 p.seed.used) k
  by_cases h16k : k = 16
  · subst k; simpa [upd] using h16
  by_cases h1k : k = 1
  · subst k; simpa [upd, SeedPublic.words] using h1
  by_cases h10k : k = 10
  · subst k; simpa [upd, SeedPublic.words] using h10
  have member : k ∈ generationSlots := by
    simp only [generatorSlots, generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    omega
  simpa [upd, SeedPublic.words, h16k, h1k, h10k] using hm.slots k member

end VG.Proof.Dsa.X86_64.Generation
