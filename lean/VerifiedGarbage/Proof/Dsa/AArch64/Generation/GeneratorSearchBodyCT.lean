module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchCTState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStepCT

/-! # A complete generator attempt preserves the tape and returns a public status -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def GeneratorSearchPublic.accepted (p : GeneratorSearchPublic) : Bool :=
  if room : p.used + p.plan.core.len ≤ p.plan.tape.length then decide (p.plan.chunk p.used room).accepts else false

def GeneratorSearchBodyAfter (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧
    W 20 = BitVec.ofNat 64 (p.used + p.plan.core.len) ∧ W 19 = if p.accepted then 1 else 3) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_body_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchTaken len)) (generatorStep M.mm len) (fun _ _ => True) := by
  apply (generatorStep_ct M len hl).mono
  · rintro s t ⟨p, ⟨⟨Ws, hs, _, ps⟩, he, room⟩, ⟨⟨Wt, ht, _, pt⟩, _, _⟩, hsp⟩
    exact ⟨p.plan.chunk p.used room, ⟨⟨Ws, hs.chunk room ps⟩, he⟩, ⟨⟨Wt, ht.chunk room pt⟩, he⟩, hsp⟩
  · exact fun _ _ h => h

theorem generatorSearch_body_ready (M : Mont)  {len : Nat}
    {p : GeneratorSearchPublic} {s : State} (h : GeneratorSearchTaken len p s) :
    WP isa (generatorStep M.mm len) s (GeneratorSearchBodyAfter len p) := by
  obtain ⟨⟨W, hm, hu, hp⟩, he, room⟩ := h
  have hc := hm.chunk room hp
  have step := generatorStep_ok M hc
  change WP isa (generatorStep M.mm p.plan.core.len) s _ at step
  rw [he] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have memory := hm.frame ht.layout ht.rep (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff hk.rd hk.wr
  refine ⟨⟨_, memory, ?_, ?_⟩, he, room⟩
  · simpa [upd] using hu
  · simp [upd, GeneratorSearchPublic.accepted, room]

end VG.Proof.Dsa.AArch64.Generation
