module

public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Block
public import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# Keeping `d8`–`d15` around a core that writes them

The modes' code writes no vector register, so the functions built on a core
keep the low halves of `v8`–`v15` (`preservedV`) if each run of the core's
`crypt` does, even though its instructions write them: `VSafeBut k c` says
that every instruction of `c` keeps them but within its occurrences of `k`,
and `vKeep_of_vSafeBut` that every run of `c` keeps them, given that every run
of `k` does. `vsafe_but` proves `VSafeBut k c` for code built of blocks,
sequences, branches, loops and `k`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

/-- The low halves of `v8`–`v15` in `s'` are those of `s`. -/
def VKeep (s s' : State) : Prop :=
  ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem VKeep.trans {a b c : State} (h₁ : VKeep a b) (h₂ : VKeep b c) : VKeep a c :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

/-- Every instruction of the code keeps `v8`–`v15`, but within its
occurrences of `k`. -/
inductive VSafeBut (k : Prog isa) : Prog isa → Prop
  | core : VSafeBut k k
  | block {is : List Instr} : is.all keepsV = true → VSafeBut k (.block is)
  | seq {a b : Prog isa} : VSafeBut k a → VSafeBut k b → VSafeBut k (.seq a b)
  | ite {cnd : Cond} {a b : Prog isa} : VSafeBut k a → VSafeBut k b → VSafeBut k (.ite cnd a b)
  | loop {b : Prog isa} {cnd : Cond} : VSafeBut k b → VSafeBut k (.loop b cnd)

/-- Every run of `c` keeps `v8`–`v15`'s low halves, if every run of `k` does. -/
theorem vKeep_of_vSafeBut {k c : Prog isa} (h : VSafeBut k c)
    (hk : ∀ s t s', Exec isa k s t s' → VKeep s s') : ∀ s t s', Exec isa c s t s' → VKeep s s' := by
  induction h with
  | core => exact hk
  | block hb =>
    intro s t s' he
    exact Exec.preservedV he (by rw [Code.allInstrs_eq]; exact hb)
  | seq _ _ iha ihb =>
    intro s t s' he
    cases he with
    | seq e₁ e₂ => exact (iha _ _ _ e₁).trans (ihb _ _ _ e₂)
  | ite _ _ iha ihb =>
    intro s t s' he
    cases he with
    | iteT _ e => exact iha _ _ _ e
    | iteF _ e => exact ihb _ _ _ e
  | @loop b cnd _ ihb =>
    intro s t s' he
    generalize hc : Code.loop b cnd = p at he
    induction he with
    | loopExit e _ => cases hc; exact ihb _ _ _ e
    | loopNext e _ _ _ ih₂ => cases hc; exact (ihb _ _ _ e).trans (ih₂ rfl)
    | _ => cases hc

/-- `VSafeBut k c`, for `c` built of blocks, sequences, branches, loops and
`k` (the definitions around them unfolded as needed). -/
tactic_template "vsafe_but" : tactic => `(tactic| repeat' (first
  | with_reducible exact VSafeBut.core
  | exact VSafeBut.block (by decide)
  | apply VSafeBut.seq
  | apply VSafeBut.ite
  | apply VSafeBut.loop))

/-- A block's final state, as `runBlock` gives it. -/
theorem block_final {is : List Instr} {s s' s₁ : State} {t : List Leak} (he : Exec isa (.block is) s t s')
    (hr : runBlock isa is s = some s₁) : s' = s₁ := by
  induction is generalizing s t with
  | nil =>
    have h := WP.block_nil_iff.mp (⟨t, s', he, rfl⟩ : WP isa (.block []) s (· = s'))
    exact h.symm.trans (Option.some.inj (runBlock_nil.symm.trans hr))
  | cons i is ih =>
    obtain ⟨s₂, e, t', s'', he', rfl⟩ := WP.block_cons_iff.mp (⟨t, s', he, rfl⟩ : WP isa (.block (i :: is)) s (· = s'))
    rw [runBlock, e, Option.bind_some] at hr
    exact ih he' hr

end VG.Proof.Blowfish.AArch64
