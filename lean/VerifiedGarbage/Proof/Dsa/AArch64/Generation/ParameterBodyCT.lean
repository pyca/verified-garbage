module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterCTState
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAttempt

/-! # One public seed attempt advances the outer search and witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Proof.MillerRabin.AArch64

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

theorem parameter_body_ct (H : GenerationHashes) (M : Mont)  (K : Kernel)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterTaken pLen qLen))
      (seedAttempt H.sha1 H.sha256 M.mm K.run pLen qLen) (fun _ _ => True) := by
  apply (seedAttempt_ct H M K pLen qLen sizes).mono ?_ (fun _ _ h => h)
  rintro s t ⟨p, ⟨room, hs⟩, ⟨room', ht⟩, hsp⟩
  exact ⟨p.seed room, hs, ht, hsp⟩

theorem parameter_body_ready (H : GenerationHashes) (M : Mont)  (K : Kernel)
    {pLen qLen : Nat} {p : ParameterPublic} {s : State} (h : ParameterTaken pLen qLen p s) :
    WP isa (seedAttempt H.sha1 H.sha256 M.mm K.run pLen qLen) s (ParameterBodyAfter pLen qLen p) := by
  obtain ⟨room, ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, hq⟩, hp⟩⟩ := h
  change p.context.geo.pLen = pLen at hp
  change p.context.geo.qLen = qLen at hq
  subst pLen; subst qLen
  refine WP.mono (seedAttempt_ok H M K hm (p.seed room).seed (p.seed room).length seed h1 h16 p.randBound)
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
