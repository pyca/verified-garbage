module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # FFDH parameter generation on x86-64: public headers in the nested workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def innerT (rs : List Reg) (S : List Nat) : VG.X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi]), flags := false, lens := [0, 8, 512], bases := [(.rdi, 2, 256)],
    slots := S.map fun j => (2, 256 + 8 * j, 8) }

def InnerKW (B : Addr) (wr : List Region) : Prop :=
  ∃ o u : Region, ∃ n : Nat, wr = [o, u, ⟨B, n⟩] ∧ 8 ≤ u.len ∧ 512 ≤ n ∧ wr.Pairwise Region.Disjoint ∧
    ∀ r ∈ wr, r.len ≤ 2 ^ 64

theorem InnerKW.kw {B : Addr} {wr : List Region} (h : InnerKW B wr) : KW B wr := by
  obtain ⟨o, u, n, hw, hu, hn, hd, hl⟩ := h
  exact ⟨o, u, n, hw, hu, by omega, hd, hl⟩

theorem innerT_agree {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {rs : List Reg}
    {s₁ s₂ : State} (hk : InnerKW B wr) (hS : ∀ e ∈ vs, e.1 < 32)
    (h₁ : HP (off B 256) wr vs s₁) (h₂ : HP (off B 256) wr vs s₂)
    (hr' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.X86_64.Taint.Agree (innerT rs (vs.map (·.1))) s₁ s₂ := by
  obtain ⟨o, u, n, hw, hu, hn, hd, hl⟩ := hk
  have wf : ∀ {s : State}, HP (off B 256) wr vs s → VG.X86_64.Taint.Wf (innerT rs (vs.map (·.1))) s := fun h => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [h.wr, hw]; exact .cons (Nat.zero_le _) (.cons hu (.cons hn .nil))
    · rw [h.wr]; exact hd
    · rw [h.wr]; exact hl
    · simp only [innerT, List.mem_singleton] at hp; subst hp
      simp only [VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [h.rdi]
  have hb : ∀ {s : State}, HP (off B 256) wr vs s → ∀ k,
      VG.X86_64.Taint.byteAddr s 2 k = B + BitVec.ofNat 64 k := fun h k => by
    simp only [VG.X86_64.Taint.byteAddr, VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], wf h₁, wf h₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, VG.X86_64.Taint.noLo, VG.X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with h | h
    · exact hr' r h
    · simp only [List.mem_singleton] at h; subst h; rw [h₁.rdi, h₂.rdi]
  · simp only [innerT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    have := hS e he
    simp only [innerT, List.getD_cons_succ, List.getD_cons_zero, Function.comp]
    omega
  · simp only [innerT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    simp only [Function.comp] at hk₁ hk₂ ⊢
    have ea : B + BitVec.ofNat 64 k = off (off B 256) (8 * e.1) + BitVec.ofNat 64 (k - (256 + 8 * e.1)) := by
      rw [off_off, off, VG.Offset.add_ofNat_add_ofNat]
      congr 2
      omega
    rw [hb h₁, hb h₂, ea]
    exact word_bytes ((h₁.hdr e he).trans (h₂.hdr e he).symm) (by omega)

theorem inner_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (B : α → Addr) (wr : α → List Region)
    (S : List Nat) (vs : α → List (Nat × BitVec 64)) (rs : List Reg) (hS : ∀ j ∈ S, j < 32)
    (hvs : ∀ a, (vs a).map (·.1) = S)
    (hΦ : ∀ a s, Φ a s → InnerKW (B a) (wr a) ∧ HP (off (B a) 256) (wr a) (vs a) s) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (innerT rs S) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (innerT rs S) (fun _ _ ⟨a, h₁, h₂⟩ => by
    rw [← hvs a]
    exact innerT_agree (hΦ a _ h₁).1 (fun e he => hS _ (by rw [← hvs a]; exact List.mem_map_of_mem he))
      (hΦ a _ h₁).2 (hΦ a _ h₂).2 (hpin a _ _ h₁ h₂)) h

end VG.Proof.Ffdh.X86_64.ParameterCandidate
