module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterBodyCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # The outer search repeats exactly when a complete seed attempt requests retry -/

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
