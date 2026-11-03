module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.Framework.Arm.Syms

/-!
# RSAES-OAEP on ARMv7: the indirect calls of a table's functions

`tcall_vp`, `tcallF_vp`: the call of a table's function `j`
(`Impl.RsaOaep.Arm.tcall`, `tcallF`: its address into `r4`, then `blx r4`,
alone or in the frame of its stack arguments) is a piece (`VP`) as the call
of the function it reaches is, when both runs reach it at the same address,
with the same `sp`. `VP.syms`: a piece keeps the addresses of the statics,
which the calls need to know which function the table's address names.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm
open VG.Proof.Rsa.Arm.Recover (VP Two)
open VG.Impl.RsaOaep.Arm (tcall tcallF tload)

/-- A piece keeps the addresses of the statics. -/
theorem VP.syms {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) :
    VP (fun σ s => F σ s ∧ s.syms = σ.syms) c (fun σ s => G σ s ∧ s.syms = σ.syms) := by
  refine ⟨fun σ s hs => WP.mono_syms (h.wp σ s hs.1) fun _ hq sy => ⟨hq, sy.trans hs.2⟩, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨h₁, y₁⟩, ⟨h₂, y₂⟩⟩ e₁ e₂
  have r := ((h.ct.mono (P' := fun a b => F σ₁ a ∧ F σ₂ b) (fun a b hab => ⟨σ₁, σ₂, hab⟩) fun _ _ q => q).wp
    (F₁ := G σ₁) (F₂ := G σ₂) fun _ _ hh => ⟨h.wp _ _ hh.1, h.wp _ _ hh.2⟩) _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, ⟨r.2.2.1, (Exec.syms e₁).trans y₁⟩, ⟨r.2.2.2, (Exec.syms e₂).trans y₂⟩⟩

theorem push_some_gpr {rs : List Reg} {s u : State} (h : isa.push (.push rs) s = some u) :
    u.gpr = s.gpr ∧ u.syms = s.syms := by
  simp only [isa, push] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- The call of the table's function `j`, among `ts`: after the load of its
address into `r4` (`hl`), it reaches `(n, c)` (`ht`), at the same address in
both runs (`hpub`). -/
theorem tcall_vp {F F₁ G : State → State → Prop} {j : Nat} {ts : List (String × Prog isa)}
    {n : String} {c : Prog isa} (hne : ts ≠ []) (hl : VP F (.block (tload j)) F₁)
    (ht : ∀ σ s, F₁ σ s → icallTarget isa s ((s.gpr .r4).setWidth 64) ts = some (n, c))
    (hpub : ∀ σ₁ σ₂ s₁ s₂, F₁ σ₁ s₁ → F₁ σ₂ s₂ → s₁.gpr .r4 = s₂.gpr .r4)
    (h : VP F₁ (.call n c) G) : VP F (tcall j ts) G := by
  refine VP.seq hl ⟨fun σ s hs => WP.icalls_of_call rfl (ht σ s hs) (h.wp σ s hs), ?_⟩
  obtain ⟨p, ts', rfl⟩ : ∃ p ts', ts = p :: ts' := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons p ts' => exact ⟨p, ts', rfl⟩
  refine RelCT.icalls_of_call h.ct fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨_, rfl, ?_, ht σ₁ s₁ h₁, ?_, rfl⟩
  · show some ((s₂.gpr .r4).setWidth 64) = some ((s₁.gpr .r4).setWidth 64)
    rw [hpub _ _ _ _ h₁ h₂]
  · rw [hpub _ _ _ _ h₁ h₂]; exact ht σ₂ s₂ h₂

/-- The same, in a frame pushing `rs`, with the same `sp` in both runs. -/
theorem tcallF_vp {F F₁ G : State → State → Prop} {j : Nat} {ts : List (String × Prog isa)} {rs : List Reg}
    {k : Nat} {n : String} {c : Prog isa} (hne : ts ≠ []) (hl : VP F (.block (tload j)) F₁)
    (ht : ∀ σ s, F₁ σ s → icallTarget isa s ((s.gpr .r4).setWidth 64) ts = some (n, c))
    (hpub : ∀ σ₁ σ₂ s₁ s₂, F₁ σ₁ s₁ → F₁ σ₂ s₂ → s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp)
    (h : VP F₁ (.frame (.push rs) (.call n c) (.pop .r1 k)) G) : VP F (tcallF j ts rs k) G := by
  have tgt : ∀ σ s u, F₁ σ s → isa.push (.push rs) s = some u →
      icallTarget isa u ((u.gpr .r4).setWidth 64) ts = some (n, c) := fun σ s u hs hp => by
    obtain ⟨g, y⟩ := push_some_gpr hp
    rw [g, icallTarget_congr (s₂ := s) fun q _ => by
      show (u.syms q.1).setWidth 64 = (s.syms q.1).setWidth 64
      rw [y]]
    exact ht σ s hs
  refine VP.seq hl ⟨fun σ s hs => WP.frame_icalls_of_call (fun u hp => ⟨_, rfl, tgt σ s u hs hp⟩) (h.wp σ s hs), ?_⟩
  obtain ⟨p, ts', rfl⟩ : ∃ p ts', ts = p :: ts' := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons p ts' => exact ⟨p, ts', rfl⟩
  refine RelCT.frame_icalls_of_call h.ct fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
  · show addrs (.push rs) s₁ = addrs (.push rs) s₂
    simp only [addrs, (hpub _ _ _ _ h₁ h₂).2]
  · have e₁ := tgt σ₁ s₁ _ h₁ hp₁
    have e₂ := tgt σ₂ s₂ _ h₂ hp₂
    have g : u₂.gpr .r4 = u₁.gpr .r4 := by
      rw [(push_some_gpr hp₁).1, (push_some_gpr hp₂).1, (hpub _ _ _ _ h₁ h₂).1]
    rw [g] at e₂
    exact ⟨_, rfl, congrArg (fun v => some (BitVec.setWidth 64 v)) g, e₁, e₂, rfl⟩

end VG.Proof.RsaOaep.Arm
