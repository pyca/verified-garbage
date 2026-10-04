import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-CCM on x86-64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`). Both runs have the same public
arguments, kept in the slots of `W` (`Slots`), so the taint analysis starts
from the registers that agree and those slots, public (`ccmT`, `both_agree`);
what correctness says about each run is added with `RelCT.wp`.
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

/-- The taint: the registers `rs`, `r13`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region) and the slots of the
public arguments `[160, 216)` and `[232, 240)` public. -/
def ccmT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r13, .r15, .rsp]), flags := false, lens := [0, 2560], bases := [(.r15, 1, 0)],
    slots := [(1, 160, 56), (1, 232, 8)] }

/-- Two runs with the same public arguments: both in the environment, with
the same slots and writable regions, agreeing on the registers `rs`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (rs : List Reg) (s₁ s₂ : State) :
    Prop where
  e₁ : Env K W SP s₁
  e₂ : Env K W SP s₂
  sl₁ : Slots W R N A D nl al n tl s₁.mem
  sl₂ : Slots W R N A D nl al n tl s₂.mem
  wr₁ : s₁.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  wr₂ : s₂.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- Bytes of a word that both memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} {v : BitVec 64} (h₁ : m₁.readW a 64 = v) (h₂ : m₂.readW a 64 = v)
    {j : Nat} (hj : j < 8) : m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  have e : bytesAt m₁ a 8 = bytesAt m₂ a 8 := by rw [← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, h₁, h₂]
  rw [← getElem_bytesAt m₁ a hj, ← getElem_bytesAt m₂ a hj]
  exact List.getElem_of_eq e _

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D nl al n tl rs s₁ s₂) : X86_64.Taint.Agree (ccmT rs) s₁ s₂ := by
  have wf : ∀ {s : State}, Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.Wf (ccmT rs) s := fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 2560 ≤ 2 ^ 64; decide
    · simp only [ccmT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.wr₁, h.wr₂], wf h.e₁ h.wr₁, wf h.e₂ h.wr₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.e₁.r13, h.e₂.r13]
      · rw [h.e₁.r15, h.e₂.r15]
      · rw [h.e₁.rsp, h.e₂.rsp]
  · simp only [ccmT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp [ccmT]
  · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k := fun s hw => by
      simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
    have hw : ∀ d, k = d + (k - d) → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
      fun d e => by rw [add_ofNat_assoc, ← e]
    simp only [ccmT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> rw [hb s₁ h.wr₁, hb s₂ h.wr₂]
    · simp only at hk₁ hk₂
      have S₁ := h.sl₁
      have S₂ := h.sl₂
      have key : ∀ d, d ∈ [160, 168, 176, 184, 192, 200, 208] → d ≤ k → k < d + 8 →
          s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
        rw [hw d (by omega)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact word_byte S₁.nonce S₂.nonce (by omega)
        · exact word_byte S₁.nlen S₂.nlen (by omega)
        · exact word_byte S₁.aad S₂.aad (by omega)
        · exact word_byte S₁.alen S₂.alen (by omega)
        · exact word_byte S₁.data S₂.data (by omega)
        · exact word_byte S₁.len S₂.len (by omega)
        · exact word_byte S₁.tl S₂.tl (by omega)
      have hq : (k - 160) / 8 = 0 ∨ (k - 160) / 8 = 1 ∨ (k - 160) / 8 = 2 ∨ (k - 160) / 8 = 3 ∨
          (k - 160) / 8 = 4 ∨ (k - 160) / 8 = 5 ∨ (k - 160) / 8 = 6 := by omega
      exact key (160 + 8 * ((k - 160) / 8)) (by
        rcases hq with h | h | h | h | h | h | h <;> rw [h] <;> decide) (by omega) (by omega)
    · simp only at hk₁ hk₂
      rw [hw 232 (by omega)]
      exact word_byte h.sl₁.rounds h.sl₂.rounds (by omega)

/-- Code the taint analysis checks from `ccmT rs`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl al n tl rs s₁ s₂)
    (hc : ∃ hc, (taint.check (ccmT rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (ccmT rs) (fun s₁ s₂ h => both_agree hDW hn (hP _ _ h)) hc

/-- Code the taint analysis checks from `ccmT rs`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl al n tl rs s₁ s₂)
    (hc : ∃ hc, ((taint.check (ccmT rs) c hc).map (·.flags)) = some true) :
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

/-- `a; (b; (c; d))`, related as `(a; (b; c)); d`. -/
theorem rel_assoc3 {P Q : State → State → Prop} {a b c d : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b c)) d) Q) : RelCT isa P (.seq a (.seq b (.seq c d))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `a; (b; c)`, related as `(a; b); c`. -/
theorem rel_assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := RelCT.assoc h

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  sl : Slots W R N A D nl al n tl s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 2560⟩]

theorem Both.of {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (o₁ : One K W SP R N A D nl al n tl s₁) (o₂ : One K W SP R N A D nl al n tl s₂)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : Both K W SP R N A D nl al n tl rs s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, h⟩

theorem Both.one₁ {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (h : Both K W SP R N A D nl al n tl rs s₁ s₂) : One K W SP R N A D nl al n tl s₁ := ⟨h.e₁, h.sl₁, h.wr₁⟩

theorem Both.one₂ {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (h : Both K W SP R N A D nl al n tl rs s₁ s₂) : One K W SP R N A D nl al n tl s₂ := ⟨h.e₂, h.sl₂, h.wr₂⟩

/-- Registers with the same value in both runs agree. -/
theorem agree_of {s₁ s₂ : State} {l : List (Reg × BitVec 64)} (h₁ : ∀ p ∈ l, s₁.gpr p.1 = p.2)
    (h₂ : ∀ p ∈ l, s₂.gpr p.1 = p.2) : ∀ r ∈ l.map Prod.fst, s₁.gpr r = s₂.gpr r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  rw [h₁ p hp, h₂ p hp]

/-- `a; (b; (c; (d; e)))`, related as `(a; (b; (c; d))); e`. -/
theorem rel_assoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) : RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

end VG.Proof.AesCcm.X86_64
