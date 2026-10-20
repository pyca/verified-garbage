module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterBodyCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess

/-! # The outer search repeats exactly when a complete seed attempt requests retry -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64

def ParameterPublic.continues (p : ParameterPublic) : Bool := !p.exhausted && (p.status == 3)

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
  ws := p.ws
  wr := p.wr
  header := p.header

def ParameterIterationAfter (n pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  isa.eval .e s = some p.continues ∧
    ∀ hc : p.continues = true, ParameterBefore n pLen qLen (p.next hc) s

theorem parameter_status {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterBodyAfter n pLen qLen p s) :
    WP isa (.block tapeStatus) s (ParameterIterationAfter n pLen qLen p) := by
  obtain ⟨⟨W, hm, hu, hs, hr⟩, hf, hw, hp, hq, room⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = false := by apply decide_eq_false; omega
  refine WP.mono (tapeStatus_ok hm.layout R) fun t ⟨hz, hmem, hk⟩ => ?_
  refine ⟨?_, fun hc => ?_⟩
  · simp only [eval, hz, hs, ParameterPublic.continues, exhausted, Bool.not_false, Bool.true_and]
  · have retry : p.status = 3 := by
      simpa only [ParameterPublic.continues, exhausted, Bool.not_false, Bool.true_and, beq_iff_eq] using hc
    exact ⟨⟨W, hm.congr hmem hk, hu, hr retry⟩,
      hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, hp, hq⟩

theorem parameter_exhausted {n pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterChecked n pLen qLen p s) (hb : isa.eval .b s = some true) :
    WP isa (.block (stackStatus 3 ++ ([.mov32 .rax (.imm 1), .alu .test .rax (.reg .rax)] : List Instr))) s
      (ParameterIterationAfter n pLen qLen p) := by
  obtain ⟨⟨W, hm, _⟩, _⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = true := Option.some.inj (h.2.symm.trans hb)
  have cont : p.continues = false := by simp [ParameterPublic.continues, exhausted]
  refine WP.mono (tapeExhausted_ok hm.layout R) fun t ⟨hz, _⟩ => ?_
  exact ⟨by simp only [eval, hz, cont], fun hc => by rw [cont] at hc; contradiction⟩

end VG.Proof.Dsa.X86_64.Generation
