module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorPlanCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FinishDomainCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import Mathlib.Basic.IsEmpty.Defs

/-! # Generator selection supplies public inputs to the final validation gate -/

@[expose] public section
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
