module
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.AbsorbBlocks
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratchW
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Init
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Init
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Finish
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Finish
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.AbsorbCorrect
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.AbsorbCorrect
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Implies
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Implies
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Absorb
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Absorb
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.X86.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.X86.Init
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.FinalizeCorrect
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Init
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Streaming TDEA-CMAC on x86: `Verified`

Correctness, constant time and satisfiability under this target's contracts
(`Contract.lean`), and the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`, `StreamScratchW.lean`),
which imply them: with 20 bytes of stack for `stream_init` and 24 for
`absorb` and `finish` (the arguments of the code they run inline, which they
push, and a word in the return address's place).

Two runs of `absorb` from states that agree on the public arguments are
related piece by piece (`RelCT`): the taint analysis covers the code between
the runs of `update`, from `esp`, the stack arguments and `ebp`, which the
correctness proof pins to a value of the public arguments (`AAft`), and each
run of `update`, in its frame, is constant time by its own proof
(`upd_rel`), its arguments pinned by `AMid₁` and `AMid₂`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86.pre s₀) (h0' : absorbX86.pre s₀')
    (hq : absorbX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  have hp := APre.of h0
  have hp' := APre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have eSt : aSt s₀ = aSt s₀' := qa 0 (by decide)
  have eC : aC s₀ = aC s₀' := by rw [aC, aC, countX86, countX86, qa 1 (by decide), qa 2 (by decide)]
  have eD : aD s₀ = aD s₀' := qa 3 (by decide)
  have eL : aL s₀ = aL s₀' := by rw [aL, aL, qa 4 (by decide)]
  have eS : aSc s₀ = aSc s₀' := qa 5 (by decide)
  have e2 : d2Of s₀ = d2Of s₀' := by rw [d2Of, d2Of, eC, eL, eSt, eD]
  have ag : ∀ {rs : List Reg} {a b : State}, Pt 6 s₀ a → Pt 6 s₀' b → (∀ r ∈ rs, a.gpr r = b.gpr r) →
      VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) a b :=
    fun h₁ h₂ hr => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ hr
  have bp : ∀ {v v' : Nat} {a b : State}, v = v' → AAft s₀ v a → AAft s₀' v' b → ∀ r ∈ [Reg.ebp], a.gpr r = b.gpr r :=
    fun e h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp, e]
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _) fun r hr => by simp at hr)
    (c := absorbPre) (by taint_decide)).wp (F₁ := AMid₁ s₀) (F₂ := AMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c₁ := ((upd_rel (E := aE s₀) (P := fun a b => AMid₁ s₀ a ∧ AMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eC, eL]; exact h.2.args, h.1.ctx.esp,
        by rw [h.2.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀))) (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨upd1_after hp h.1, upd1_after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 6))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2))
    (c := chain2) (by taint_decide)).wp (F₁ := AMid₂ s₀) (F₂ := AMid₂ s₀')
    fun _ _ h => ⟨WP.mono (chain2_mid hp h.1) fun _ h => h.1, WP.mono (chain2_mid hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have c₂ := ((upd_rel (E := aE s₀) (P := fun a b => AMid₂ s₀ a ∧ AMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eC, eL, e2]; exact h.2.args, h.1.aft.ctx.esp,
        by rw [h.2.aft.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)))
      (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀') + 8 * nbOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨upd2_after hp h.1, upd2_after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀') + 8 * nbOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 6))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2)) (c := absorbPost) (by taint_decide)
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbX86.pre absorbX86.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_verified : Verified X86.target streamInit (streamInitScratchContract X86.abi 20) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct init_implies

theorem absorb_verified : Verified X86.target absorb (absorbScratchContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => absorb_wp hs) absorb_ct absorb_implies

theorem finish_verified : Verified X86.target finish (finishScratchContract86 X86.abi 24) :=
  Verified.of_correct (fun _ hs => finish_wp hs) finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.X86
