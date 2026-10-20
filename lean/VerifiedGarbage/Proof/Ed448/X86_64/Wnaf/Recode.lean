module

public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Invariant
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! Complete public recoding into 461 signed byte digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64
open VG.Impl.Ed448.Wnaf (residual)

private theorem init_ok {s : State} {base : Addr} (hs : Scr s base) (dst k : Nat) :
    WP isa (.block [.mov32 .rbx (.imm 0), .mov32 .rcx (.imm 16)]) s (RecInv base dst k s 0) := by
  xrun
  refine ⟨?_, rfl, ⟨16, by decide, rfl, ?_⟩, ?_, rfl, rfl, Outside.refl _ _ _ _, ?_⟩
  · exact ⟨hs.rdi, hs.wr, hs.nowrap⟩
  · simp only [residual, pow_zero, Nat.div_one]
  · intro r hr
    have hb : r ≠ .rbx := fun h => hr (by simp [h])
    have hc : r ≠ .rcx := fun h => hr (by simp [h, clob])
    simp only [RegUpd.gpr_setReg, hb, hc, ite_false]
  · intro i hi; omega

private theorem body_ok {base : Addr} {src dst k n : Nat} {s₀ s : State}
    (h : RecInv base dst k s₀ n s) (hn : n < 456)
    (hsrc : 1 ≤ src) (hsep : src + 460 ≤ dst) (hb : dst + 461 ≤ 8192)
    (bs : Window.Bits base src k s₀) :
    WP isa (.block (recodeStep src dst)) s fun u =>
      RecInv base dst k s₀ (n + 1) u ∧ u.zf = some (decide (n + 1 = 456)) := by
  obtain ⟨c, hc, hr, he⟩ := h.carry
  rw [recodeStep, WP.block_append_iff]
  refine WP.mono (step_ok h.scr (by omega) h.rbx hc hr he
    (loadBits_bits_ok h.scr (by omega) hsrc hn h.rbx (h.bits hsrc hsep hb bs))) fun a ha => ?_
  have ia := h.advance (by omega) hb ha
  refine WP.mono (cmp456_ok (by omega) ia.rbx) fun u ⟨hz, hu⟩ => ⟨ia.keeps hu, hz⟩

private theorem loop_ok {base : Addr} {src dst k : Nat} {s₀ s : State}
    (h : RecInv base dst k s₀ 0 s) (hsrc : 1 ≤ src) (hsep : src + 460 ≤ dst) (hb : dst + 461 ≤ 8192)
    (bs : Window.Bits base src k s₀) :
    WP isa (.loop (.block (recodeStep src dst)) .ne) s (RecInv base dst k s₀ 456) := by
  refine WP.loop (M := isa) (fun m u => ∃ n, n < 456 ∧ m = 456 - n ∧ RecInv base dst k s₀ n u)
    ?_ 456 s ⟨0, by decide, rfl, h⟩
  rintro m u ⟨n, hn, rfl, hi⟩
  refine WP.mono (body_ok hi hn hsrc hsep hb bs) fun v ⟨hv, hz⟩ => ?_
  have he : isa.eval .ne v = some (!decide (n + 1 = 456)) := by
    simp only [eval, hz, Option.map_some]
  by_cases hn' : n + 1 = 456
  · refine .inl ⟨?_, hn' ▸ hv⟩
    rw [he, hn']; rfl
  · refine .inr ⟨?_, 456 - (n + 1), by omega, n + 1, by omega, rfl, hv⟩
    rw [he, decide_eq_false hn']; rfl

private theorem zero_ok {s : State} :
    WP isa (.block [.mov32 .rax (.imm 0), .mov32 .rdx (.imm 0)]) s fun u =>
      u.gpr .rax = 0 ∧ u.gpr .rdx = 0 ∧ Keeps [.rax, .rdx] s u := by
  xrun
  exact ⟨fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_setReg, h.1, h.2, ite_false], rfl, rfl, rfl⟩

private theorem tail_ok {base : Addr} {dst k : Nat} {s₀ : State} (hk : k < 2 ^ 456)
    (hb : dst + 461 ≤ 8192) : ∀ m n, 456 ≤ n → n + m ≤ 461 → ∀ s,
      RecInv base dst k s₀ n s → WP isa (recodeTail dst m) s (RecInv base dst k s₀ (n + m)) := by
  intro m
  induction m with
  | zero => intro n _ _ s h; exact WP.block_nil h
  | succ m ih =>
    intro n hn hnm s h
    obtain ⟨c, hc, hr, he⟩ := h.carry
    have hq : k / 2 ^ n = 0 := Proof.Ed448.SignedWindow.bit_zero hk hn
    have hp : WP isa (.block [.mov32 .rax (.imm 0), .mov32 .rdx (.imm 0)]) s fun u =>
        u.gpr .rax = BitVec.ofNat 64 (k / 2 ^ n % 32) ∧
        u.gpr .rdx = BitVec.ofNat 64 (k / 2 ^ n % 2) ∧ Keeps [.rax, .rdx] s u := by
      rw [hq]; exact zero_ok
    refine WP.seq (WP.mono (step_ok h.scr (by omega) h.rbx hc hr he hp) fun u hu => ?_)
    have hnext := ih (n + 1) (by omega) (by omega) u (h.advance (by omega) hb hu)
    rw [show n + 1 + m = n + (m + 1) by omega] at hnext
    exact hnext

theorem recode_ok {s : State} {base : Addr} (hs : Scr s base) {src dst k : Nat}
    (hsrc : 1 ≤ src) (hsep : src + 460 ≤ dst) (hb : dst + 461 ≤ 8192)
    (bs : Window.Bits base src k s) (hk : k < 2 ^ 456) :
    WP isa (recode src dst) s (RecInv base dst k s 461) := by
  refine WP.seq (WP.mono (init_ok hs dst k) fun a ha => ?_)
  refine WP.seq (WP.mono (loop_ok ha hsrc hsep hb bs) fun b hb' => ?_)
  exact tail_ok hk hb 5 456 (by decide) (by decide) b hb'

end VG.Proof.Ed448.X86_64.Wnaf
