module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Init
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Finish
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.AbsorbCorrect
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.CT
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Implies
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming TDEA-CMAC on AArch64: `Verified`

Correctness, constant time and satisfiability under this target's contracts
(`Contract.lean`), and the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`), which imply them, with
no stack: the functions call nothing.

`absorb` is constant time in three parts: the taint analysis covers each
(`CT.lean`), the second and the third from the registers the part before
leaves, which its correctness proof pins to the public arguments (`AAfter₁`,
`AAfter₂`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.Stream.AArch64

/-- States agree on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbAArch64.pre s₀) (h0' : absorbAArch64.pre s₀')
    (hq : absorbAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x3).toNat := by
    rw [q0, q2, q3, q4]; exact APre.of h0'
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x2 = D at hp hp'
  generalize s₀.gpr .x4 = S at hp hp'
  generalize (s₀.gpr .x3).toNat = L at hp hp'
  obtain ⟨_, hA⟩ := absorb₁_taint
  obtain ⟨_, hB⟩ := absorb₂_taint
  obtain ⟨_, hC⟩ := absorb₃_taint
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [q0, q1, q2, q3, q4]) hA).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorb₁_after hp, absorb₁_after hp'⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q5]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x21, h.2.x21, q1]
      · rw [h.1.x22, h.2.x22, q1]
      · rw [h.1.x23, h.2.x23]) hB).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨absorb₂_after hp h.1, absorb₂_after hp' h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q5]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20, q1]
      · rw [h.1.x21, h.2.x21, q1]
      · rw [h.1.x22, h.2.x22, q1]
      · rw [h.1.x23, h.2.x23]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)

theorem absorb_ct : ConstantTime isa absorbAArch64.pre absorbAArch64.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_correct (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (WP.mono (init_wp hs) fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩) (by lit_decide)

theorem absorb_correct (s : State) (hs : absorbAArch64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbAArch64.post s s' :=
  WP.withPreservedV (absorb_wp hs) (by lit_decide)

theorem finish_correct (s : State) (hs : finishAArch64.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishAArch64.post s s' :=
  WP.withPreservedV (WP.mono (finish_wp hs) fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩) (by lit_decide)

theorem init_verified : Verified AArch64.target streamInit (streamInitScratchContract AArch64.abi 0) :=
  Verified.of_correct init_correct init_ct init_implies

theorem absorb_verified : Verified AArch64.target absorb (absorbScratchContract AArch64.abi 0) :=
  Verified.of_correct absorb_correct absorb_ct absorb_implies

theorem finish_verified : Verified AArch64.target finish (finishScratchContract AArch64.abi 0) :=
  Verified.of_correct finish_correct finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.AArch64
