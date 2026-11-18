module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
public import VerifiedGarbage.Proof.Framework.TaintCT

/-!
# What constant-time code leaves in its registers (AArch64)

`rtaintCT` is `rtaintL` (`ResidueTaint.lean`) for two runs that leak the
same (`TaintCT`): a load or a store accesses the same address in both, so
its base register, whose sum with the offset that address is, holds the
same value in both, and is public from then on (`pubBase`). The step of
`rtaintL` itself needs that register public, and fails otherwise: the
address of a table of constants (`adrSym`), which the two runs need not
share (`State.syms`), or a pointer loaded from memory the analysis does not
follow, is then public after its first use. Branches need not be on public
conditions either.

`noResidue_of_check`: code proven constant time under its contract, whose
analysis from everything public ends in `RTaintL.done r`, returns without
secret residue with an `r`-bit result. The two runs `NoResidue` compares
satisfy the precondition and agree on what the contract's `pub` says, so
their traces are equal (`TaintCT.agree_of_check`).
-/

@[expose] public section

namespace VG.AArch64.RTaintCT

open VG.AArch64

/-- The base register and offset of the first address of a load or a store
through a general-purpose register. -/
def base : Instr → Option (Reg × Nat)
  | .ldr _ _ n off | .str _ _ n off | .ldrb _ n off | .strb _ n off | .ldp _ _ n off
  | .stp _ _ n off | .ldrq _ n off | .strq _ n off => some (n, off)
  | _ => none

theorem addrs_of_base {i : Instr} {n : Reg} {off : Nat} (h : base i = some (n, off)) (s : State) :
    (addrs i s).head? = some (s.gpr n + BitVec.ofNat 64 off) := by
  cases i <;> simp only [base, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    (obtain ⟨rfl, rfl⟩ := h; rfl)

/-- `τ`, with `n` public. -/
def withPub (τ : RTaintL.T) (n : Reg) : RTaintL.T :=
  (((τ.1.1.1.insert n, τ.1.1.2), τ.1.2), τ.2)

theorem agree_withPub {τ : RTaintL.T} {n : Reg} {s₁ s₂ : State} (h : RTaintL.Agree τ s₁ s₂)
    (hn : s₁.gpr n = s₂.gpr n) : RTaintL.Agree (withPub τ n) s₁ s₂ := by
  obtain ⟨⟨⟨⟨hsp, hg⟩, hv⟩, hr⟩, hq⟩ := h
  refine ⟨⟨⟨⟨hsp, fun r hr' => ?_⟩, hv⟩, hr⟩, hq⟩
  rcases RegSet.mem_insert.mp hr' with rfl | hr'
  · exact hn
  · exact hg r hr'

/-- `τ`, with the base register of `i` public. -/
def pubBase (τ : RTaintL.T) (i : Instr) : RTaintL.T :=
  match base i with
  | some (n, _) => withPub τ n
  | none => τ

theorem agree_pubBase {τ : RTaintL.T} {i : Instr} {s₁ s₂ : State} (h : RTaintL.Agree τ s₁ s₂)
    (ha : addrs i s₁ = addrs i s₂) : RTaintL.Agree (pubBase τ i) s₁ s₂ := by
  unfold pubBase
  split
  · rename_i n off hb
    have e := addrs_of_base hb s₁
    rw [ha, addrs_of_base hb s₂, Option.some.injEq] at e
    have e' := congrArg (· - BitVec.ofNat 64 off) e.symm
    simp only [BitVec.add_sub_cancel] at e'
    exact agree_withPub h e'
  · exact h

def step (τ : RTaintL.T) (i : Instr) : Option RTaintL.T := RTaintL.step (pubBase τ i) i

theorem step_sound {τ τ' : RTaintL.T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : RTaintL.Agree τ s₁ s₂) (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') (hadr : addrs i s₁ = addrs i s₂) : RTaintL.Agree τ' s₁' s₂' :=
  (RTaintL.step_sound (agree_pubBase ha hadr) hs e₁ e₂).2

theorem addrs_length (i : Instr) (s₁ s₂ : State) : (addrs i s₁).length = (addrs i s₂).length := by
  cases i <;> rfl

end RTaintCT

open RTaintCT in
/-- `rtaintL` for two runs that leak the same (see `RTaintCT`). -/
def rtaintCT : VG.TaintCT isa where
  T := RTaintL.T
  Agree := RTaintL.Agree
  step := RTaintCT.step
  step_sound ha hs e₁ e₂ hadr := RTaintCT.step_sound ha hs e₁ e₂ hadr
  addrs_length := RTaintCT.addrs_length
  meet := rtaintL.meet
  meet_left := rtaintL.meet_left
  meet_right := rtaintL.meet_right
  le := rtaintL.le
  le_sound := rtaintL.le_sound
  call _ := none
  call_sound _ hs := nomatch hs
  callAddrs_length _ _ := rfl
  ret _ := none
  ret_sound _ hs := nomatch hs
  retAddrs_length _ _ := rfl
  push _ _ := none
  push_sound _ hs := nomatch hs
  pop _ _ := none
  pop_sound _ hs := nomatch hs

namespace RTaintCT

/-- Code proven constant time under its contract, whose analysis
(`rtaintCT`) from everything public ends in `RTaintL.done r`, returns without
secret residue, with an `r`-bit result. -/
theorem noResidue_of_check {c : Prog isa} {k : Contract isa} {r : Nat}
    (hct : ConstantTime isa k.pre k.pub c)
    (h : ∃ hc, (rtaintCT.check RTaintL.init c hc).any (RTaintL.done r) = true) :
    NoResidue c k r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : rtaintCT.check RTaintL.init c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    exact RTaintL.outside_of_done
      (TaintCT.agree_of_check hct hτ h₁ h₂ hp (RTaintL.agree_init ho hu) e₁ e₂) h

end RTaintCT

end VG.AArch64
