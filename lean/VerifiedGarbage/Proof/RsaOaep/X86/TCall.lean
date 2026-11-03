module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Impl.RsaOaep.X86
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# RSAES-OAEP on x86: the indirect calls of a table's functions

`tcall_vp`: the call of a table's function `j` (`Impl.RsaOaep.X86.tcall`:
its address into `esi`, then `call esi` in the frame of its arguments) is a
piece (`VP`) as the call of the function it reaches is in that frame, when
both runs reach it at the same address, with the same `esp`. `VP.syms`: a
piece keeps the addresses of the statics, which the calls need to know
which function the table's address names.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaOaep.X86 (tcall sTab)
open VG.Impl.RsaPss.X86 (ld)
open VG.Impl.RsaPkcs1Sig.X86 (at_)

/-- A piece keeps the addresses of the statics. -/
theorem VP.syms {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) :
    VP (fun σ s => F σ s ∧ s.syms = σ.syms) c (fun σ s => G σ s ∧ s.syms = σ.syms) := by
  refine ⟨fun σ s hs => WP.mono_syms (h.wp σ s hs.1) fun _ hq sy => ⟨hq, sy.trans hs.2⟩, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨h₁, y₁⟩, ⟨h₂, y₂⟩⟩ e₁ e₂
  have r := ((h.ct.mono (P' := fun a b => F σ₁ a ∧ F σ₂ b) (fun a b hab => ⟨σ₁, σ₂, hab⟩) fun _ _ q => q).wp
    (F₁ := G σ₁) (F₂ := G σ₂) fun _ _ hh => ⟨h.wp _ _ hh.1, h.wp _ _ hh.2⟩) _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, ⟨r.2.2.1, (Exec.syms e₁).trans y₁⟩, ⟨r.2.2.2, (Exec.syms e₂).trans y₂⟩⟩

/-- The call of the table's function `j`, among `ts`, in a frame pushing
`rs`: after the load of its address into `esi` (`hl`), it reaches `(n, c)`
(`ht`), at the same address in both runs, with the same `esp` (`hpub`). -/
theorem tcall_vp {F F₁ G : State → State → Prop} {j : Nat} {ts : List (String × Prog isa)} {rs : List Reg}
    {n : String} {c : Prog isa} (hne : ts ≠ [])
    (hl : VP F (.block [ld .esi sTab, .mov .esi (.mem (at_ .esi (4 * j)))]) F₁)
    (ht : ∀ σ s, F₁ σ s → icallTarget isa s ((s.gpr .esi).setWidth 64) ts = some (n, c))
    (hpub : ∀ σ₁ σ₂ s₁ s₂, F₁ σ₁ s₁ → F₁ σ₂ s₂ → s₁.gpr .esi = s₂.gpr .esi ∧ s₁.gpr .esp = s₂.gpr .esp)
    (h : VP F₁ (.frame (.push rs) (.call n c) (.pop .eax rs.length)) G) : VP F (tcall j ts rs) G := by
  have tgt : ∀ σ s u, F₁ σ s → isa.push (.push rs) s = some u →
      icallTarget isa u ((u.gpr .esi).setWidth 64) ts = some (n, c) := fun σ s u hs hp => by
    obtain ⟨-, -, -, rfl⟩ := push_some hp
    rw [pushed_gpr _ _ (by decide), icallTarget_congr (s₂ := s) fun q _ => by
      show ((pushed rs s).syms q.1).setWidth 64 = (s.syms q.1).setWidth 64
      rw [show (pushed rs s).syms = s.syms from pushRegs_syms s rs]]
    exact ht σ s hs
  refine VP.seq hl ⟨fun σ s hs => WP.frame_icalls_of_call (fun u hp => ⟨_, rfl, tgt σ s u hs hp⟩) (h.wp σ s hs), ?_⟩
  obtain ⟨p, ts', rfl⟩ : ∃ p ts', ts = p :: ts' := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons p ts' => exact ⟨p, ts', rfl⟩
  refine RelCT.frame_icalls_of_call h.ct fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
  · show addrs (.push rs) s₁ = addrs (.push rs) s₂
    simp only [addrs, (hpub _ _ _ _ h₁ h₂).2]
  · obtain ⟨-, -, -, rfl⟩ := push_some hp₁
    obtain ⟨-, -, -, rfl⟩ := push_some hp₂
    have e₁ := tgt σ₁ s₁ _ h₁ hp₁
    have e₂ := tgt σ₂ s₂ _ h₂ hp₂
    have g : (pushed rs s₂).gpr .esi = (pushed rs s₁).gpr .esi := by
      rw [pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide), (hpub _ _ _ _ h₁ h₂).1]
    rw [g] at e₂
    exact ⟨_, rfl, congrArg (fun v => some (BitVec.setWidth 64 v)) g, e₁, e₂, rfl⟩

end VG.Proof.RsaOaep.X86
