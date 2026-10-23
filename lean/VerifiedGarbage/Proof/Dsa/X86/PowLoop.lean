module

public import VerifiedGarbage.Proof.Dsa.X86.PowSteps
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # The loop of DSA's exponentiation

An iteration (`step`) multiplies the result (slot 6) by the base (slot 5) where
the exponent's (slot 8) low bit is set, squares the base, and shifts the
exponent, each multiplication a call (`stepSt_ok`); `32 e` iterations consume
the exponent (`loopSt_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

section
variable {n m size : Nat} {base : Addr} {s₀ : State}

theorem stepSt_ok {t : State} {y b k e : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n) (he : 2 ≤ e)
    (hen : e ≤ 2 * n)
    (hy : wordsVal t.mem base (slot n 6) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal t.mem base (slot n 5) n = b * 2 ^ (64 * n) % m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : t.gpr .esi = BitVec.ofNat 32 k) :
    WP isa (step n e) t fun u => St n m size base s₀ u ∧
      u.gpr .esi = BitVec.ofNat 32 (k - 1) ∧ u.zf = some (decide (k = 1)) ∧
      wordsVal u.mem base (slot n 6) n =
        (if val32 t.mem base (slot n 8) e % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      wordsVal u.mem base (slot n 5) n = (b * b) * 2 ^ (64 * n) % m ∧
      val32 u.mem base (slot n 8) e = val32 t.mem base (slot n 8) e / 2 := by
  have h := S.ctx
  have hm1 := h.gt_one
  have cop := h.coprime
  have wv : ∀ {m₁ m₂ : Mem} {j : Nat}, (∀ k ≤ 2 * n, val32 m₂ base (slot n j) k = val32 m₁ base (slot n j) k) →
      wordsVal m₂ base (slot n j) n = wordsVal m₁ base (slot n j) n := fun H => by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, H _ (Nat.le_refl _)]
  unfold step
  refine WP.seq (WP.mono (maskSt_ok S) fun s₁ ⟨S₁, i₁, M₁, V₁⟩ => ?_)
  have y₁ : wordsVal s₁.mem base (slot n 6) n = y * 2 ^ (64 * n) % m := by rw [wv (V₁ 6 (by decide)), hy]
  have b₁ : wordsVal s₁.mem base (slot n 5) n = b * 2 ^ (64 * n) % m := by rw [wv (V₁ 5 (by decide)), hb]
  have bl₁ : wordsVal s₁.mem base (slot n 5) n < m := by rw [b₁]; exact Nat.mod_lt _ (by omega)
  refine WP.seq (WP.mono (mulSt_ok (o := 7) (a := 6) (b := 5) S₁ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) bl₁) fun s₂ ⟨S₂, i₂, L₂, P₂, V₂, M₂⟩ => ?_)
  have p₂ : wordsVal s₂.mem base (slot n 7) n = y * b * 2 ^ (64 * n) % m := by
    have v := VG.Proof.Dsa.mont_product cop (a := y) (b := b) (by rw [y₁, Nat.mod_mod])
      (by rw [b₁, Nat.mod_mod]) P₂
    rwa [Nat.mod_eq_of_lt L₂] at v
  refine WP.seq (WP.mono (selectSt_ok (bit := decide (w32 t.mem base (slot n 8) % 2 = 1)) S₂ (by
      rw [M₂, M₁]; simp only [decide_eq_true_eq])) fun s₃ ⟨S₃, i₃, Y₃, V₃⟩ => ?_)
  have b₃ : wordsVal s₃.mem base (slot n 5) n = b * 2 ^ (64 * n) % m := by
    rw [wv (V₃ 5 (by decide) (by decide)), wv (V₂ 5 (by decide) (by decide) (by decide)), b₁]
  refine WP.seq (WP.mono (mulSt_ok (o := 5) (a := 5) (b := 5) S₃ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [b₃]; exact Nat.mod_lt _ (by omega)))
    fun s₄ ⟨S₄, i₄, L₄, P₄, V₄, _⟩ => ?_)
  have b₄ : wordsVal s₄.mem base (slot n 5) n = b * b * 2 ^ (64 * n) % m := by
    have v := VG.Proof.Dsa.mont_product cop (a := b) (b := b) (by rw [b₃, Nat.mod_mod])
      (by rw [b₃, Nat.mod_mod]) P₄
    rwa [Nat.mod_eq_of_lt L₄] at v
  have e₄ : val32 s₄.mem base (slot n 8) e = val32 t.mem base (slot n 8) e := by
    rw [V₄ 8 (by decide) (by decide) (by decide) e hen, V₃ 8 (by decide) (by decide) e hen,
      V₂ 8 (by decide) (by decide) (by decide) e hen, V₁ 8 (by decide) e hen]
  refine WP.seq (WP.mono (shiftSt_ok S₄ he hen) fun s₅ ⟨S₅, i₅, E₅, V₅⟩ => ?_)
  have c₅ : s₅.gpr .esi = BitVec.ofNat 32 k := by rw [i₅, i₄, i₃, i₂, i₁, hc]
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun u fu zu => WP.block_nil ?_
  have mu : u.mem = s₅.mem := fu.mem.trans uv.mem
  have ku : Keeps powerClob s₅ u := (uv.keeps.mono (by decide)).trans (fu.keeps _)
  have Cu : Context n m base size u := ⟨S₅.ctx.scr.of_keeps ku (by decide), S₅.ctx.size_le,
    mu ▸ S₅.ctx.modulus, S₅.ctx.gt_one, mu ▸ S₅.ctx.inverse⟩
  refine ⟨⟨Cu, S₅.room, S₅.keeps.trans ku, mu ▸ S₅.mem⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fu.gpr, uv.gpr, c₅, counter_sub hk32 hk]
  · rw [zu, uv.gpr, c₅, counter_sub hk32 hk, counter_zero hk32 hk]
  · rw [mu, wv (V₅ 6 (by decide) (by decide)), wv (V₄ 6 (by decide) (by decide) (by decide)), Y₃]
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [val32_parity]
    by_cases hbit : w32 t.mem base (slot n 8) % 2 = 1
    · simp only [hbit, decide_true, ite_true]; exact p₂
    · simp only [hbit, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [wv (V₂ 6 (by decide) (by decide) (by decide)), y₁]
  · rw [mu, wv (V₅ 5 (by decide) (by decide)), b₄]
  · rw [mu, E₅, e₄]

structure LoopInv (n m size e target steps i : Nat) (base : Addr) (s₀ t : State) : Prop where
  st : St n m size base s₀ t
  counter : t.gpr .esi = BitVec.ofNat 32 (steps - i)
  bound : val32 t.mem base (slot n 8) e < 2 ^ (steps - i)
  value : ∃ y b,
    wordsVal t.mem base (slot n 6) n = y * 2 ^ (64 * n) % m ∧
    wordsVal t.mem base (slot n 5) n = b * 2 ^ (64 * n) % m ∧
    (y * b ^ val32 t.mem base (slot n 8) e) % m = target

theorem loopSt_ok {t : State} {a e : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n) (he : 2 ≤ e)
    (hen : e ≤ 2 * n)
    (hy : wordsVal t.mem base (slot n 6) n = 2 ^ (64 * n) % m)
    (hb : wordsVal t.mem base (slot n 5) n = a * 2 ^ (64 * n) % m)
    (hk32 : 32 * e < 2 ^ 32) (hc : t.gpr .esi = BitVec.ofNat 32 (32 * e)) :
    WP isa (.loop (step n e) .ne) t
      (LoopInv n m size e (a ^ val32 t.mem base (slot n 8) e % m) (32 * e) (32 * e) base s₀) := by
  let steps := 32 * e
  let target := a ^ val32 t.mem base (slot n 8) e % m
  have hspos : 0 < steps := by dsimp [steps]; omega
  have init : LoopInv n m size e target steps 0 base s₀ t := by
    refine ⟨S, ?_, ?_, ⟨1, a, ?_, hb, ?_⟩⟩
    · simpa only [Nat.sub_zero] using hc
    · simpa only [Nat.sub_zero] using val32_lt t.mem base (slot n 8) e
    · simpa only [Nat.one_mul] using hy
    · simp only [Nat.one_mul]; rfl
  refine WP.loop (M := isa)
    (fun k u => ∃ i, k = steps - i ∧ i < steps ∧ LoopInv n m size e target steps i base s₀ u)
    ?_ steps t ⟨0, rfl, hspos, init⟩
  rintro k u ⟨i, rfl, hi, I⟩
  obtain ⟨y, b, Y, B, V⟩ := I.value
  refine WP.mono (stepSt_ok I.st hn he hen Y B (by omega) (by dsimp [steps] at *; omega) I.counter)
    fun w ⟨S', count, zf, Y', B', E'⟩ => ?_
  have next : LoopInv n m size e target steps (i + 1) base s₀ w := by
    refine ⟨S', ?_, ?_, ⟨_, _, Y', B', ?_⟩⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega]
    · rw [E']
      have hp : 2 ^ (steps - i) = 2 ^ (steps - (i + 1)) * 2 := by
        rw [show steps - i = steps - (i + 1) + 1 by omega, Nat.pow_succ]
      have bound := I.bound
      rw [hp] at bound
      omega
    · rw [E', exponent_step_value]
      exact V
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, ?_⟩
    · have eq : steps - i = 1 := by omega
      simp only [eval, zf, eq, decide_true, Option.map_some, Bool.not_true]
    · change LoopInv n m size e target steps steps base s₀ w
      rw [hdone] at next
      exact next
  · refine .inr ⟨?_, steps - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    have ne : steps - i ≠ 1 := by omega
    simp only [eval, zf, decide_eq_false ne, Option.map_some, Bool.not_false]

theorem LoopInv.finished {e target steps : Nat} {t : State}
    (I : LoopInv n m size e target steps steps base s₀ t) :
    wordsVal t.mem base (slot n 6) n = target * 2 ^ (64 * n) % m := by
  have bound := I.bound
  simp only [Nat.sub_self, Nat.pow_zero] at bound
  have ez : val32 t.mem base (slot n 8) e = 0 := by omega
  obtain ⟨y, b, Y, _, V⟩ := I.value
  rw [ez, Nat.pow_zero, Nat.mul_one] at V
  rw [Y, Nat.mul_mod y, V, Nat.mul_mod_mod]

end

end VG.Proof.Dsa.X86.Pow
