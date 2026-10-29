module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSearchPlanCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero

/-! # Subgroup outcomes determine the public phase status and entropy cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

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

def SeedSubgroupAfter (n pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 19 = p.subgroupStatus) ∧
  (p.subgroupStatus = 1 → SeedPrimeBefore n pLen qLen p.afterSubgroup s)

theorem seedSubgroup_after (H : GenerationHashes) (T : PrimeTest)
    {n pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedBefore n qLen p s) (hp : p.context.geo.pLen = pLen) :
    WP isa (.seq (.block (Impl.Dsa.X86_64.Generation.seedArguments qLen))
      (Impl.Dsa.X86_64.Generation.subgroup H.sha1 H.sha256 T.run qLen)) s
      (SeedSubgroupAfter n pLen qLen p) := by
  obtain ⟨⟨W, hm, h1, h16, h10⟩, seed, hf, hw, he⟩ := h
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
  refine ⟨⟨⟨_, ht, ?_, ?_, ?_⟩, seed.frame ff rd wr, ?_, wr.trans hw, rfl⟩, hp, bytes⟩
  · simpa [seedWords, upd, SeedPublic.afterSubgroup] using h1
  · simp [upd, cursor]
  · simpa [seedWords, upd, SeedPublic.afterSubgroup] using h10
  · exact hf.congr (ht.layout.rsp.trans hm.layout.rsp.symm) wr

end VG.Proof.Dsa.X86_64.Generation
