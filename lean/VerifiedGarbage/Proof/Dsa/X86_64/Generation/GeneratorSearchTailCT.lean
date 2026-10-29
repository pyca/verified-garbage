module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchCTState

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInvariant
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorEvaluateCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorDecisionCT
/-! # Public retry condition and strictly advancing generator tape cursor -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorStepCT.lean`, which only this module imported.
section

/-! # Timing of a complete generator attempt, including both retry decisions -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem generatorStep_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorStep Sq.mm M.mm len) (fun _ _ => True) := by
  unfold generatorStep
  refine RelCT.seq (two_post (generatorInputRange_ct len hl)
    (fun _ _ h => generatorInputRange_mask h))
    (RelCT.seq (generatorTest_ct len GeneratorPlan.inputValid) ?_)
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
      (generatorStatus_ct len 3 (Or.inr rfl))
  · have body : RelCT isa (Two (GeneratorBefore len))
        (seqs [generatorEvaluate Sq.mm M.mm len, generatorRangeFromFrame len true,
          .block [.alu .test .rax (.reg .rax)],
          .ite .e (.block (stackStatus 3)) (.block (stackStatus 1))]) (fun _ _ => True) := by
      simp only [seqs]
      refine RelCT.seq (two_post (generatorEvaluate_ct M Sq len hl)
        (fun _ _ h => generatorEvaluate_ready M Sq h))
        (RelCT.seq (two_post (generatorOutputRange_ct len hl)
          (fun _ _ h => generatorOutputRange_mask h))
          (RelCT.seq (generatorTest_ct len GeneratorPlan.outputValid) ?_))
      refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 3 (Or.inr rfl))
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 1 (Or.inl rfl))
    exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1) body

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorSearchBodyCT.lean`, which only this module imported.
section

/-! # A complete generator attempt preserves the tape and returns a public status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def GeneratorSearchPublic.accepted (p : GeneratorSearchPublic) : Bool :=
  if room : p.used + p.plan.core.len ≤ p.plan.tape.length then decide (p.plan.chunk p.used room).accepts else false

def GeneratorSearchBodyAfter (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧
    W 20 = BitVec.ofNat 64 (p.used + p.plan.core.len) ∧ W 19 = if p.accepted then 1 else 3) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_body_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchTaken len)) (generatorStep Sq.mm M.mm len) (fun _ _ => True) := by
  apply (generatorStep_ct M Sq len hl).mono
  · rintro s t ⟨p, ⟨⟨Ws, hs, _, ps⟩, he, room⟩, ⟨⟨Wt, ht, _, pt⟩, _, _⟩⟩
    exact ⟨p.plan.chunk p.used room, ⟨⟨Ws, hs.chunk room ps⟩, he⟩, ⟨⟨Wt, ht.chunk room pt⟩, he⟩⟩
  · exact fun _ _ h => h

theorem generatorSearch_body_ready (M : Mont) (Sq : MontS) {len : Nat}
    {p : GeneratorSearchPublic} {s : State} (h : GeneratorSearchTaken len p s) :
    WP isa (generatorStep Sq.mm M.mm len) s (GeneratorSearchBodyAfter len p) := by
  obtain ⟨⟨W, hm, hu, hp⟩, he, room⟩ := h
  have hc := hm.chunk room hp
  have step := generatorStep_ok M Sq hc
  change WP isa (generatorStep Sq.mm M.mm p.plan.core.len) s _ at step
  rw [he] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have memory := hm.frame ht.layout ht.rep (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff hk.2.1 hk.2.2
  refine ⟨⟨_, memory, ?_, ?_⟩, he, room⟩
  · simpa [upd] using hu
  · simp [upd, GeneratorSearchPublic.accepted, room]

end VG.Proof.Dsa.X86_64.Generation
end

end

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
