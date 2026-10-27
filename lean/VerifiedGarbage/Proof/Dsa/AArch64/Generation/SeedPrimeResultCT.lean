module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorPlanCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrime

/-! # Public prime-search outcomes select the next generator phase -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Proof.MillerRabin.AArch64

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

theorem seedPrime_after (H : GenerationHashes) (M : Mont) (T : PrimeTest)
    {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore pLen qLen p s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) s
      (SeedPrimeAfter pLen qLen p) := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, hq⟩, hp, bq⟩ := h
  subst pLen; subst qLen
  refine WP.mono (seedPrime_ok H M T hm p.seed p.length seed h1 bq h16 p.bound)
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
