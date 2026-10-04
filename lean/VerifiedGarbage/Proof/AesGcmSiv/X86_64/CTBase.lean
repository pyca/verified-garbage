import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Open
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-GCM-SIV on x86-64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`). Both runs have the same public
arguments, kept in the slots of `W` (`Slots`), so the taint analysis starts
from the registers that agree and those slots, public (`sivT`, `both_agree`);
what correctness says about each run is added with `RelCT.wp`.
-/

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

/-- The taint: the registers `rs`, `r13`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region) and the slots of the
public arguments `[272, 320)` public. -/
def sivT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r13, .r15, .rsp]), flags := false, lens := [0, 4096], bases := [(.r15, 1, 0)],
    slots := [(1, 272, 48)] }

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (s : State) : Prop where
  env : Env K W SP s
  sl : Slots W R N A D al n s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 4096⟩]

/-- Two runs with the same public arguments, agreeing on the registers `rs`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (rs : List Reg) (s₁ s₂ : State) :
    Prop where
  o₁ : One K W SP R N A D al n s₁
  o₂ : One K W SP R N A D al n s₂
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- Bytes of a word that both memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} {v : BitVec 64} (h₁ : m₁.readW a 64 = v) (h₂ : m₂.readW a 64 = v)
    {j : Nat} (hj : j < 8) : m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  have e : bytesAt m₁ a 8 = bytesAt m₂ a 8 := by rw [← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, h₁, h₂]
  have := congrArg (fun l => l.getD j 0) e
  simpa only [Proof.Cmac.getD_bytesAt _ _ hj] using this

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D al n rs s₁ s₂) : X86_64.Taint.Agree (sivT rs) s₁ s₂ := by
  have wf : ∀ {s : State}, Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 4096⟩] → X86_64.Taint.Wf (sivT rs) s := fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 4096 ≤ 2 ^ 64; decide
    · simp only [sivT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.o₁.wr, h.o₂.wr], wf h.o₁.env h.o₁.wr,
    wf h.o₂.env h.o₂.wr, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.o₁.env.r13, h.o₂.env.r13]
      · rw [h.o₁.env.r15, h.o₂.env.r15]
      · rw [h.o₁.env.rsp, h.o₂.env.rsp]
  · simp only [sivT, List.mem_singleton] at hsl; subst hsl; simp [sivT]
  · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 4096⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
      fun s hw => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
    have hw : ∀ d, k = d + (k - d) → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
      fun d e => by rw [add_ofNat_assoc, ← e]
    simp only [sivT, List.mem_singleton] at hsl; subst hsl
    rw [hb s₁ h.o₁.wr, hb s₂ h.o₂.wr]
    simp only at hk₁ hk₂
    have S₁ := h.o₁.sl
    have S₂ := h.o₂.sl
    have key : ∀ d, d ∈ [272, 280, 288, 296, 304, 312] → d ≤ k → k < d + 8 →
        s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
      rw [hw d (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact word_byte S₁.rounds S₂.rounds (by omega)
      · exact word_byte S₁.nonce S₂.nonce (by omega)
      · exact word_byte S₁.aad S₂.aad (by omega)
      · exact word_byte S₁.alen S₂.alen (by omega)
      · exact word_byte S₁.data S₂.data (by omega)
      · exact word_byte S₁.len S₂.len (by omega)
    have hq : (k - 272) / 8 = 0 ∨ (k - 272) / 8 = 1 ∨ (k - 272) / 8 = 2 ∨ (k - 272) / 8 = 3 ∨
        (k - 272) / 8 = 4 ∨ (k - 272) / 8 = 5 := by omega
    exact key (272 + 8 * ((k - 272) / 8)) (by
      rcases hq with h | h | h | h | h | h <;> rw [h] <;> decide) (by omega) (by omega)

/-- Code the taint analysis checks from `sivT rs`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, (taint.check (sivT rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (sivT rs) (fun s₁ s₂ h => both_agree hDW hn (hP _ _ h)) hc

/-- Code the taint analysis checks from `sivT rs`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, ((taint.check (sivT rs) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (both_agree hDW hn (hP _ _ hp)) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

theorem eval_e_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .e s₁ = isa.eval .e s₂ := h
theorem eval_ne_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .ne s₁ = isa.eval .ne s₂ := by
  show s₁.zf.map _ = s₂.zf.map _; rw [h]
theorem eval_b_eq {s₁ s₂ : State} (h : s₁.cf = s₂.cf) : isa.eval .b s₁ = isa.eval .b s₂ := h

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.AesGcmSiv.X86_64
