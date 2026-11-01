module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# AES-GCM on RISC-V: constant time, the combinators

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTBase.lean`): `CT I c`, two runs of `c` from states that
both satisfy `I` leak the same. The invariants `I` fix what is public
(pointers, lengths, rounds) as parameters and leave the secrets (memory, the
values the state represents, our caller's registers) existential, so that
the correctness lemmas, applied to each run, give the invariant of the next
piece (`CT.seq`). Branches are on registers the invariants fix (`CT.ite`);
blocks are checked by the taint analysis from registers the invariants fix
(`CT.taint`); the calls are constant time by their own proofs, with the same
arguments in both runs (`CT.gh`, `CT.ctr`, `CT.key`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64

/-- Both runs satisfy `I`. -/
abbrev Both (I : State → Prop) : State → State → Prop := fun s₁ s₂ => I s₁ ∧ I s₂

/-- Two runs from states satisfying `I` leak the same. -/
abbrev CT (I : State → Prop) (c : Prog isa) : Prop := RelCT isa (Both I) c fun _ _ => True

namespace CT

theorem mono {I J : State → Prop} {c : Prog isa} (h : CT I c) (hi : ∀ s, J s → I s) : CT J c :=
  RelCT.mono h (fun _ _ hh => ⟨hi _ hh.1, hi _ hh.2⟩) fun _ _ _ => trivial

theorem seq {I J : State → Prop} {c₁ c₂ : Prog isa} (h₁ : CT I c₁) (w : ∀ s, I s → WP isa c₁ s J)
    (h₂ : CT J c₂) : CT I (.seq c₁ c₂) :=
  ((h₁.wp fun s₁ s₂ h => ⟨w s₁ h.1, w s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2).seq h₂

theorem ite {I : State → Prop} {c : Cond} {t e : Prog isa} (b : Bool)
    (ev : ∀ s, I s → isa.eval c s = some b) (ht : b = true → CT I t) (he : b = false → CT I e) :
    CT I (.ite c t e) := by
  refine RelCT.ite (fun _ _ h => by rw [ev _ h.1, ev _ h.2]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [ev _ hp.1] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [ev _ hp.1] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

theorem taint {I : State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {h : VG.Taint.Hint VG.RISCV64.taint.T}
    (hc : (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) c h).isSome = true) : CT I c :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun x y hh => ⟨(hp x y hh.1 hh.2).1, fun r h' => (hp x y hh.1 hh.2).2 r (Taint.mem_ofRegs.mp h')⟩) hc

theorem skip {I : State → Prop} : CT I (.block []) := by
  intro _ _ _ _ _ _ _ e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      exact ⟨h₁.2.symm.trans h₂.2, trivial⟩

theorem gh {I : State → Prop} {name : String}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ H Y D S : Addr, ∃ n : Nat,
      GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) :
    CT I (.call name Impl.Gcm.RISCV64.ghash) :=
  gh_rel fun _ _ hh => h _ _ hh.1 hh.2

theorem ctr {I : State → Prop} {name : String}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K C D S : Addr, ∃ R n : Nat,
      CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) :
    CT I (.call name Impl.Aes.RISCV64.ctr32) :=
  ctr_rel fun _ _ hh => h _ _ hh.1 hh.2

theorem key {I : State → Prop} {name : String}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K : Addr, ∃ kl : Nat, ∃ C S : Addr,
      KeyCall s₁ K kl C S ∧ KeyCall s₂ K kl C S ∧ s₁.sp = s₂.sp) :
    CT I (.call name Impl.Aes.RISCV64.expandKey) :=
  key_rel fun _ _ hh => h _ _ hh.1 hh.2

end CT

/-- Constant time, from an invariant both initial states satisfy. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → ∃ I : State → Prop, I σ₁ ∧ I σ₂ ∧ CT I c) :
    ConstantTime isa pre pub c := fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => by
  obtain ⟨I, i₁, i₂, hc⟩ := h _ _ h₁ h₂ hp
  exact (hc _ _ _ _ _ _ ⟨i₁, i₂⟩ e₁ e₂).1

/-- Code the taint analysis checks from the registers `rs`, in states that
agree on them and on the stack pointer. -/
theorem CT.taintEq {I : State → Prop} {c : Prog isa} (rs : List Reg) (v : Reg → BitVec 64) (sp : Addr)
    (hp : ∀ s, I s → s.sp = sp ∧ ∀ r ∈ rs, s.gpr r = v r) {h : VG.Taint.Hint VG.RISCV64.taint.T}
    (hc : (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) c h).isSome = true) : CT I c :=
  CT.taint rs (fun _ _ h₁ h₂ => ⟨(hp _ h₁).1.trans (hp _ h₂).1.symm, fun r hr =>
    ((hp _ h₁).2 r hr).trans ((hp _ h₂).2 r hr).symm⟩) hc

end VG.Proof.AesGcm.RISCV64
