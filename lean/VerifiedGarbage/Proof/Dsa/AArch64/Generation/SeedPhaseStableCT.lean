module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroup
/-! # Status inspection preserves the seed phase inputs -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SeedSubgroupResultCT.lean`, which only this module imported.
section

/-! # Subgroup outcomes determine the public phase status and entropy cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def SeedPublic.subgroupResult (p : SeedPublic) : Option (Bool × List Byte) :=
  Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)
    (p.context.rand.bytes.drop p.used)

def SeedPublic.subgroupStatus (p : SeedPublic) : BitVec 64 :=
  match p.subgroupResult with
  | none => 0
  | some (b, _) => if b then 1 else 3

def SeedPublic.afterSubgroup (p : SeedPublic) : SeedPublic :=
  { p with
    used := match p.subgroupResult with
      | none => p.used
      | some (_, rest) => p.context.rand.bytes.length - rest.length
    bound := by cases p.subgroupResult with
      | none => exact p.bound
      | some res => exact Nat.sub_le _ _ }

def SeedSubgroupAfter (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 19 = p.subgroupStatus) ∧
  (p.subgroupStatus = 1 → SeedPrimeBefore pLen qLen p.afterSubgroup s)

theorem seedSubgroup_after (H : GenerationHashes) (T : PrimeTest)
    {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedBefore qLen p s) (hp : p.context.geo.pLen = pLen) :
    WP isa (.seq (.block (Impl.Dsa.AArch64.Generation.seedArguments qLen))
      (Impl.Dsa.AArch64.Generation.subgroup H.sha1 H.sha256 T.run qLen)) s
      (SeedSubgroupAfter pLen qLen p) := by
  obtain ⟨⟨W, hm, h1, h16, h10⟩, seed, he⟩ := h
  have step := seedSubgroup_ok H T hm p.seed p.length seed h1 h16 p.bound
  subst qLen
  refine WP.mono step fun t ⟨used', status, bound, ht, bytes, fail, result, ff, rd, wr⟩ => ?_
  have statusEq : status = p.subgroupStatus := by
    cases hr : p.subgroupResult with
    | none => simpa [SeedPublic.subgroupStatus, hr] using fail hr
    | some res =>
      obtain ⟨b, rest⟩ := res
      have hs := (result b rest hr).1
      cases b <;> simpa [SeedPublic.subgroupStatus, hr] using hs
  refine ⟨⟨_, ht, by simpa [upd] using statusEq⟩, ?_⟩
  intro accepted
  have cursor : used' = p.afterSubgroup.used := by
    cases hr : p.subgroupResult with
    | none => simp [SeedPublic.subgroupStatus, hr] at accepted
    | some res =>
      obtain ⟨b, rest⟩ := res
      simpa [SeedPublic.afterSubgroup, hr] using (result b rest hr).2
  refine ⟨⟨⟨_, ht, ?_, ?_, ?_⟩, seed.frame ff rd wr, rfl⟩, hp, bytes⟩
  · simpa [seedWords, upd, SeedPublic.afterSubgroup] using h1
  · simp [upd, cursor]
  · simpa [seedWords, upd, SeedPublic.afterSubgroup] using h10

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Proof.MlKem.AArch64

theorem seedBefore_congr {qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedBefore qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedBefore qLen p t := by
  obtain ⟨⟨W, hW, h1, h16, h10⟩, seed, he⟩ := h
  exact ⟨⟨W, hW.congr hm hk, h1, h16, h10⟩,
    seed.frame (by rw [hm]; exact Frame.refl _ _) hk.rd hk.wr,
    he⟩

theorem seedPrimeBefore_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeBefore pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedPrimeBefore pLen qLen p t :=
  ⟨seedBefore_congr h.1 hm hk, h.2.1, hm ▸ h.2.2⟩

theorem seedSubgroupAfter_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedSubgroupAfter pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedSubgroupAfter pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  exact ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => seedPrimeBefore_congr (next ha) hm hk⟩

end VG.Proof.Dsa.AArch64.Generation
