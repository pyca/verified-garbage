module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchBodyCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public retry condition and strictly advancing generator tape cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def GeneratorSearchPublic.continues (p : GeneratorSearchPublic) : Bool := !p.exhausted && !p.accepted

def GeneratorSearchPublic.next (p : GeneratorSearchPublic) (hc : p.continues = true) : GeneratorSearchPublic where
  plan := p.plan
  used := p.used + p.plan.core.len
  bound := by
    have hn : p.exhausted = false := by
      cases he : p.exhausted <;> simp_all [continues]
    have hb := p.bound
    have h := of_decide_eq_false hn
    omega

def GeneratorSearchIterationAfter (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  isa.eval .e s = some p.continues ∧
    ∀ hc : p.continues = true, GeneratorSearchBefore len (p.next hc) s

theorem generatorSearch_status {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchBodyAfter len p s) :
    WP isa (.block tapeStatus) s (GeneratorSearchIterationAfter len p) := by
  obtain ⟨⟨W, hm, hu, hs⟩, he, room⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = false := by
    apply decide_eq_false
    omega
  refine WP.mono (tapeStatus_ok hm.layout R) fun t ⟨hz, hmem, hk⟩ => ?_
  refine ⟨?_, fun hc => ⟨⟨W, generatorMemory_congr hm hmem (hk.mono (by decide)), hu⟩, he⟩⟩
  simp only [eval, hz, hs, GeneratorSearchPublic.continues, exhausted, Bool.not_false, Bool.true_and]
  cases p.accepted <;> rfl

theorem generatorSearch_exhausted {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchChecked len p s) (hb : isa.eval .b s = some true) :
    WP isa (.block (stackStatus 3 ++ ([.mov32 .rax (.imm 1), .alu .test .rax (.reg .rax)] : List Instr))) s
      (GeneratorSearchIterationAfter len p) := by
  obtain ⟨⟨W, hm, _⟩, _⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = true := Option.some.inj (h.2.symm.trans hb)
  have cont : p.continues = false := by simp [GeneratorSearchPublic.continues, exhausted]
  refine WP.mono (tapeExhausted_ok hm.layout R) fun t ⟨hz, _⟩ => ?_
  exact ⟨by simp only [eval, hz, cont], fun hc => by rw [cont] at hc; contradiction⟩

end VG.Proof.Dsa.X86_64.Generation
