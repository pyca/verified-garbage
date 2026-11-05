module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Public arithmetic headers within the DSA generation arena -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def primeHeaderT (rs : List Reg) (S : List Nat) : VG.X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi]), flags := false, lens := [0, 0, 0, 28928], bases := [(.rdi, 3, 28672)],
    slots := S.map fun j => (3, 28672 + 8 * j, 8) }

/-- The arena as the last of four writable regions (the finite search). -/
def PrimeHeaderLayout4 (B : Addr) (wr : List Region) : Prop :=
  ∃ f save out : Region, ∃ n : Nat, wr = [f, save, out, ⟨B, n⟩] ∧ 28928 ≤ n ∧ wr.Pairwise Region.Disjoint ∧
    ∀ r ∈ wr, r.len ≤ 2 ^ 64

def refillHeaderT (rs : List Reg) (S : List Nat) : VG.X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi]), flags := false, lens := [0, 0, 0, 0, 0, 28928, 0], bases := [(.rdi, 5, 28672)],
    slots := S.map fun j => (5, 28672 + 8 * j, 8) }

/-- The arena as the sixth of seven writable regions (the refillable-tape
search: its frames, the controller's words, the saved registers, and
`out`, `used`, `scratch` and `state`). -/
def PrimeHeaderLayout7 (B : Addr) (wr : List Region) : Prop :=
  ∃ f c save out used st : Region, ∃ n : Nat, wr = [f, c, save, out, used, ⟨B, n⟩, st] ∧ 28928 ≤ n ∧
    wr.Pairwise Region.Disjoint ∧ ∀ r ∈ wr, r.len ≤ 2 ^ 64

def PrimeHeaderLayout (B : Addr) (wr : List Region) : Prop :=
  PrimeHeaderLayout4 B wr ∨ PrimeHeaderLayout7 B wr

theorem primeHeader_agree {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {rs : List Reg}
    {s₁ s₂ : State} (hk : PrimeHeaderLayout4 B wr) (hS : ∀ e ∈ vs, e.1 < 32)
    (h₁ : HP (off B 28672) wr vs s₁) (h₂ : HP (off B 28672) wr vs s₂)
    (hr' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.X86_64.Taint.Agree (primeHeaderT rs (vs.map (·.1))) s₁ s₂ := by
  obtain ⟨f, save, out, n, hw, hn, hd, hl⟩ := hk
  have wf : ∀ {s : State}, HP (off B 28672) wr vs s → VG.X86_64.Taint.Wf (primeHeaderT rs (vs.map (·.1))) s := fun h => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [h.wr, hw]; exact .cons (Nat.zero_le _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _) (.cons hn .nil)))
    · rw [h.wr]; exact hd
    · rw [h.wr]; exact hl
    · simp only [primeHeaderT, List.mem_singleton] at hp; subst hp
      simp only [VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [h.rdi]
  have hb : ∀ {s : State}, HP (off B 28672) wr vs s → ∀ k,
      VG.X86_64.Taint.byteAddr s 3 k = B + BitVec.ofNat 64 k := fun h k => by
    simp only [VG.X86_64.Taint.byteAddr, VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], wf h₁, wf h₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, VG.X86_64.Taint.noLo, VG.X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with h | h
    · exact hr' r h
    · simp only [List.mem_singleton] at h; subst h; rw [h₁.rdi, h₂.rdi]
  · simp only [primeHeaderT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    have := hS e he
    simp only [primeHeaderT, List.getD_cons_succ, List.getD_cons_zero, Function.comp]
    omega
  · simp only [primeHeaderT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    simp only [Function.comp] at hk₁ hk₂ ⊢
    have ea : B + BitVec.ofNat 64 k = off (off B 28672) (8 * e.1) + BitVec.ofNat 64 (k - (28672 + 8 * e.1)) := by
      rw [off_off, off, VG.Offset.add_ofNat_add_ofNat]
      congr 2
      omega
    rw [hb h₁, hb h₂, ea]
    exact word_bytes ((h₁.hdr e he).trans (h₂.hdr e he).symm) (by omega)

theorem refillHeader_agree {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {rs : List Reg}
    {s₁ s₂ : State} (hk : PrimeHeaderLayout7 B wr) (hS : ∀ e ∈ vs, e.1 < 32)
    (h₁ : HP (off B 28672) wr vs s₁) (h₂ : HP (off B 28672) wr vs s₂)
    (hr' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.X86_64.Taint.Agree (refillHeaderT rs (vs.map (·.1))) s₁ s₂ := by
  obtain ⟨f, c, save, out, used, st, n, hw, hn, hd, hl⟩ := hk
  have wf : ∀ {s : State}, HP (off B 28672) wr vs s → VG.X86_64.Taint.Wf (refillHeaderT rs (vs.map (·.1))) s := fun h => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [h.wr, hw]
      exact .cons (Nat.zero_le _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _) (.cons (Nat.zero_le _)
        (.cons (Nat.zero_le _) (.cons hn (.cons (Nat.zero_le _) .nil))))))
    · rw [h.wr]; exact hd
    · rw [h.wr]; exact hl
    · simp only [refillHeaderT, List.mem_singleton] at hp; subst hp
      simp only [VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [h.rdi]
  have hb : ∀ {s : State}, HP (off B 28672) wr vs s → ∀ k,
      VG.X86_64.Taint.byteAddr s 5 k = B + BitVec.ofNat 64 k := fun h k => by
    simp only [VG.X86_64.Taint.byteAddr, VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], wf h₁, wf h₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, VG.X86_64.Taint.noLo, VG.X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with h | h
    · exact hr' r h
    · simp only [List.mem_singleton] at h; subst h; rw [h₁.rdi, h₂.rdi]
  · simp only [refillHeaderT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    have := hS e he
    simp only [refillHeaderT, List.getD_cons_succ, List.getD_cons_zero, Function.comp]
    omega
  · simp only [refillHeaderT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    simp only [Function.comp] at hk₁ hk₂ ⊢
    have ea : B + BitVec.ofNat 64 k = off (off B 28672) (8 * e.1) + BitVec.ofNat 64 (k - (28672 + 8 * e.1)) := by
      rw [off_off, off, VG.Offset.add_ofNat_add_ofNat]
      congr 2
      omega
    rw [hb h₁, hb h₂, ea]
    exact word_bytes ((h₁.hdr e he).trans (h₂.hdr e he).symm) (by omega)

theorem primeHeader_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (B : α → Addr) (wr : α → List Region)
    (S : List Nat) (vs : α → List (Nat × BitVec 64)) (rs : List Reg) (hS : ∀ j ∈ S, j < 32)
    (hvs : ∀ a, (vs a).map (·.1) = S)
    (hΦ : ∀ a s, Φ a s → PrimeHeaderLayout (B a) (wr a) ∧ HP (off (B a) 28672) (wr a) (vs a) s) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (primeHeaderT rs S) c hc).isSome = true)
    {hc₇ : VG.Taint.Hint VG.X86_64.Taint.T} (h₇ : (taint.check (refillHeaderT rs S) c hc₇).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, ha₁, ha₂⟩ e₁ e₂
  rcases (hΦ a _ ha₁).1 with hl | hl
  · refine RelCT.taint (A := taint) (P := Two fun a s => Φ a s ∧ PrimeHeaderLayout4 (B a) (wr a))
      (primeHeaderT rs S) (fun _ _ ⟨a, h₁, h₂⟩ => by
        rw [← hvs a]
        exact primeHeader_agree h₁.2 (fun e he => hS _ (by rw [← hvs a]; exact List.mem_map_of_mem he))
          (hΦ a _ h₁.1).2 (hΦ a _ h₂.1).2 (hpin a _ _ h₁.1 h₂.1)) h _ _ _ _ _ _ ⟨a, ⟨ha₁, hl⟩, ha₂, hl⟩ e₁ e₂
  · refine RelCT.taint (A := taint) (P := Two fun a s => Φ a s ∧ PrimeHeaderLayout7 (B a) (wr a))
      (refillHeaderT rs S) (fun _ _ ⟨a, h₁, h₂⟩ => by
        rw [← hvs a]
        exact refillHeader_agree h₁.2 (fun e he => hS _ (by rw [← hvs a]; exact List.mem_map_of_mem he))
          (hΦ a _ h₁.1).2 (hΦ a _ h₂.1).2 (hpin a _ _ h₁.1 h₂.1)) h₇ _ _ _ _ _ _ ⟨a, ⟨ha₁, hl⟩, ha₂, hl⟩ e₁ e₂

/-! ## The arena as the second of three writable regions, in a called test -/

def calleeHeaderT (rs : List Reg) (S : List Nat) : VG.X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi]), flags := false, lens := [0, 28928, 0], bases := [(.rdi, 1, 28672)],
    slots := S.map fun j => (1, 28672 + 8 * j, 8) }

def CalleeHeaderLayout (B : Addr) (wr : List Region) : Prop :=
  ∃ f used : Region, ∃ n : Nat, wr = [f, ⟨B, n⟩, used] ∧ 28928 ≤ n ∧ wr.Pairwise Region.Disjoint ∧
    ∀ r ∈ wr, r.len ≤ 2 ^ 64

theorem calleeHeader_agree {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {rs : List Reg}
    {s₁ s₂ : State} (hk : CalleeHeaderLayout B wr) (hS : ∀ e ∈ vs, e.1 < 32)
    (h₁ : HP (off B 28672) wr vs s₁) (h₂ : HP (off B 28672) wr vs s₂)
    (hr' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.X86_64.Taint.Agree (calleeHeaderT rs (vs.map (·.1))) s₁ s₂ := by
  obtain ⟨f, used, n, hw, hn, hd, hl⟩ := hk
  have wf : ∀ {s : State}, HP (off B 28672) wr vs s → VG.X86_64.Taint.Wf (calleeHeaderT rs (vs.map (·.1))) s := fun h => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [h.wr, hw]; exact .cons (Nat.zero_le _) (.cons hn (.cons (Nat.zero_le _) .nil))
    · rw [h.wr]; exact hd
    · rw [h.wr]; exact hl
    · simp only [calleeHeaderT, List.mem_singleton] at hp; subst hp
      simp only [VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [h.rdi]
  have hb : ∀ {s : State}, HP (off B 28672) wr vs s → ∀ k,
      VG.X86_64.Taint.byteAddr s 1 k = B + BitVec.ofNat 64 k := fun h k => by
    simp only [VG.X86_64.Taint.byteAddr, VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], wf h₁, wf h₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, VG.X86_64.Taint.noLo, VG.X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with h | h
    · exact hr' r h
    · simp only [List.mem_singleton] at h; subst h; rw [h₁.rdi, h₂.rdi]
  · simp only [calleeHeaderT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    have := hS e he
    simp only [calleeHeaderT, List.getD_cons_succ, List.getD_cons_zero, Function.comp]
    omega
  · simp only [calleeHeaderT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    simp only [Function.comp] at hk₁ hk₂ ⊢
    have ea : B + BitVec.ofNat 64 k = off (off B 28672) (8 * e.1) + BitVec.ofNat 64 (k - (28672 + 8 * e.1)) := by
      rw [off_off, off, VG.Offset.add_ofNat_add_ofNat]
      congr 2
      omega
    rw [hb h₁, hb h₂, ea]
    exact word_bytes ((h₁.hdr e he).trans (h₂.hdr e he).symm) (by omega)

theorem calleeHeader_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (B : α → Addr) (wr : α → List Region)
    (S : List Nat) (vs : α → List (Nat × BitVec 64)) (rs : List Reg) (hS : ∀ j ∈ S, j < 32)
    (hvs : ∀ a, (vs a).map (·.1) = S)
    (hΦ : ∀ a s, Φ a s → CalleeHeaderLayout (B a) (wr a) ∧ HP (off (B a) 28672) (wr a) (vs a) s) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (calleeHeaderT rs S) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (calleeHeaderT rs S) (fun _ _ ⟨a, h₁, h₂⟩ => by
    rw [← hvs a]
    exact calleeHeader_agree (hΦ a _ h₁).1 (fun e he => hS _ (by rw [← hvs a]; exact List.mem_map_of_mem he))
      (hΦ a _ h₁).2 (hΦ a _ h₂).2 (hpin a _ _ h₁ h₂)) h

end VG.Proof.Dsa.X86_64.Generation
