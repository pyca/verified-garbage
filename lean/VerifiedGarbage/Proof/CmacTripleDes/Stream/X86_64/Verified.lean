module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Init
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Finish
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.AbsorbCorrect
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.CT
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Implies
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.SboxTables

/-!
# Streaming TDEA-CMAC on x86-64: `Verified`

Correctness, constant time and satisfiability under this target's contracts
(`Contract.lean`), and the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`), which imply them, with
no stack: the functions call nothing.

`absorb` is constant time in two parts: the taint analysis covers each
(`CT.lean`), the second from the registers the first leaves, which its
correctness proof pins to the public arguments (`AAfter₁`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.Stream.X86_64

/-! ## `absorb` is constant time -/

theorem absorb₂_agree {s₀ s₀' a b : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L)
    (hp' : APre s₀' St D S L) (q : s₀.gpr .rsi = s₀'.gpr .rsi) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp)
    (h₁ : AAfter₁ s₀ St D S L a) (h₂ : AAfter₁ s₀' St D S L b) : X86_64.Taint.Agree τAbsorb₂ a b := by
  have wf : ∀ (σ t : State), APre σ St D S L → AAfter₁ σ St D S L t → X86_64.Taint.Wf τAbsorb₂ t := by
    intro σ t hσ ht
    have hw : t.wr = [⟨St, 416⟩, ⟨S, 688⟩] := by rw [ht.wr, hσ.wr]
    refine ⟨fun _ => ⟨by simp [hw, τAbsorb₂], by simp [hw, hσ.st_s], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τAbsorb₂, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw, ht.rbx, ht.r15]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => by rw [h₁.wr, h₂.wr, hp.wr, hp'.wr],
    wf _ _ hp h₁, wf _ _ hp' h₂, ?_, ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τAbsorb₂, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.r13, h₂.r13, q]
    · rw [h₁.r14, h₂.r14, q]
    · rw [h₁.r15, h₂.r15]
    · rw [h₁.rsp, h₂.rsp, q1]
  · intro sl h; simp [τAbsorb₂] at h
  · intro sl h; simp [τAbsorb₂] at h

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86_64.pre s₀) (h0' : absorbX86_64.pre s₀')
    (hq : absorbX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  have ag := absorb_agree h0 h0' hq
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .r8) (s₀.gpr .rcx).toNat := by
    rw [q1, q3, q4, q5]; exact APre.of h0'
  generalize s₀.gpr .rdi = St at hp hp'
  generalize s₀.gpr .rdx = D at hp hp'
  generalize s₀.gpr .r8 = S at hp hp'
  generalize (s₀.gpr .rcx).toNat = L at hp hp'
  obtain ⟨_, hA⟩ := absorb₁_taint
  obtain ⟨_, hB⟩ := absorb₂_taint
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') τAbsorb
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag) hA).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorb₁_after hp, absorb₁_after hp'⟩
  have b := RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b)
    τAbsorb₂ (fun a b h => absorb₂_agree hp hp' q2 q6 h.1 h.2) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq b

theorem absorb_ct : ConstantTime isa absorbX86_64.pre absorbX86_64.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_mx : streamInit.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem absorb_mx : absorb.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem finish_mx : finish.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem init_correct (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩

theorem absorb_correct (s : State) (hs : absorbX86_64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := absorb_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec absorb_mx he hg, hp⟩

theorem finish_correct (s : State) (hs : finishX86_64.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finish_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec finish_mx he hg, hp⟩

theorem init_verified : Verified X86_64.target streamInit (streamInitScratchContract X86_64.abi 0) :=
  Verified.of_correct init_correct init_ct init_implies

theorem absorb_verified : Verified X86_64.target absorb (absorbScratchContract X86_64.abi 0) :=
  Verified.of_correct absorb_correct absorb_ct absorb_implies

theorem finish_verified : Verified X86_64.target finish (finishScratchContract X86_64.abi 0) :=
  Verified.of_correct finish_correct finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.X86_64
