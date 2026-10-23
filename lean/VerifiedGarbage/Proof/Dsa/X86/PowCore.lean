module

public import VerifiedGarbage.Proof.Dsa.X86.PowLoop
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Shared IA-32 DSA exponentiation: arithmetic and memory effects

The setup leaves `2^(65 n) mod m` in slot 4, and each Montgomery square of
`2^(64 n + c) mod m` is `2^(64 n + 2 c) mod m` (`square_value`), so six of
them leave `R² mod m`, `R = 2^(64 n)` (`squarings_ok`). Then the result is
`R mod m` and the base is encoded (`encode_ok`), the loop raises it to the
exponent, and a product with one decodes it (`core_ok`).
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

theorem square_value {n m c X out : Nat} (hR : Nat.Coprime (2 ^ (64 * n)) m)
    (hX : X = 2 ^ (64 * n + c) % m) (h : out * 2 ^ (64 * n) % m = X * X % m) (hlt : out < m) :
    out = 2 ^ (64 * n + 2 * c) % m := by
  have v := VG.Proof.Bignum.mont_cancel hR (o := out) (c := 2 ^ (64 * n + 2 * c)) (by
    rw [h, hX, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add]
    congr 2
    omega)
  rwa [Nat.mod_eq_of_lt hlt] at v

section
variable {n m size : Nat} {base : Addr} {s₀ : State}

theorem squarings_ok {t : State} (hn : 2 ≤ n) (j : Nat) :
    ∀ k, St n m size base s₀ t →
    wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n + n * 2 ^ j) % m →
    WP isa (squarings n k) t fun u => St n m size base s₀ u ∧
      wordsVal u.mem base (slot n 4) n = 2 ^ (64 * n + n * 2 ^ (j + k)) % m ∧
      ∀ i, 5 ≤ i → i < 9 → ∀ k ≤ 2 * n, val32 u.mem base (slot n i) k = val32 t.mem base (slot n i) k
  | 0, S, hx => WP.block_nil ⟨S, hx, fun _ _ _ _ _ => rfl⟩
  | k + 1, S, hx => by
    refine WP.seq (WP.mono (squarings_ok hn j k S hx) fun u ⟨Su, xu, Vu⟩ => ?_)
    refine WP.mono (mulSt_ok (o := 4) (a := 4) (b := 4) Su hn (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by rw [xu]; exact Nat.mod_lt _ (by have := Su.ctx.gt_one; omega)))
      fun w ⟨Sw, _, L, P, V, _⟩ => ⟨Sw, ?_, fun i hi5 hi k hk => ?_⟩
    · rw [square_value Su.ctx.coprime xu P L, show j + (k + 1) = (j + k) + 1 from rfl, Nat.pow_succ,
        Nat.mul_comm (2 ^ (j + k)) 2, Nat.mul_left_comm]
    · rw [V i (by omega) hi (by omega) k hk, Vu i hi5 hi k hk]

theorem encode_ok {t : State} (S : St n m size base s₀ t) (hn : 2 ≤ n)
    (hr2 : wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (encode n) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n 6) n = 2 ^ (64 * n) % m ∧
      wordsVal u.mem base (slot n 5) n = wordsVal t.mem base (slot n 5) n * 2 ^ (64 * n) % m ∧
      ∀ k ≤ 2 * n, val32 u.mem base (slot n 8) k = val32 t.mem base (slot n 8) k := by
  have cop := S.ctx.coprime
  have hm1 := S.ctx.gt_one
  have wv : ∀ {m₁ m₂ : Mem} {j : Nat}, (∀ k ≤ 2 * n, val32 m₂ base (slot n j) k = val32 m₁ base (slot n j) k) →
      wordsVal m₂ base (slot n j) n = wordsVal m₁ base (slot n j) n := fun H => by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, H _ (Nat.le_refl _)]
  have RR : 2 ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by rw [← Nat.pow_add]; congr 1; omega
  unfold encode
  refine WP.seq (WP.mono (oneSt_ok S (i := 7) (by decide) (by decide)) fun s₁ ⟨S₁, i₁, O₁, V₁⟩ => ?_)
  have x₁ : wordsVal s₁.mem base (slot n 4) n = 2 ^ (128 * n) % m := by rw [wv (V₁ 4 (by decide) (by decide)), hr2]
  refine WP.seq (WP.mono (mulSt_ok (o := 6) (a := 4) (b := 7) S₁ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [O₁]; exact hm1)) fun s₂ ⟨S₂, i₂, L₂, P₂, V₂, _⟩ => ?_)
  have y₂ : wordsVal s₂.mem base (slot n 6) n = 2 ^ (64 * n) % m := by
    have v := VG.Proof.Dsa.mont_decode cop (A := wordsVal s₁.mem base (slot n 4) n) (a := 2 ^ (64 * n))
      (by rw [x₁, Nat.mod_mod, RR]) (by rw [P₂, O₁])
    rwa [Nat.mod_eq_of_lt L₂] at v
  have x₂ : wordsVal s₂.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [wv (V₂ 4 (by decide) (by decide) (by decide)), x₁]
  refine WP.mono (mulSt_ok (o := 5) (a := 5) (b := 4) S₂ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [x₂]; exact Nat.mod_lt _ (by omega)))
    fun u ⟨Su, iu, Lu, Pu, Vu, _⟩ => ⟨Su, by rw [iu, i₂, i₁], ?_, ?_, fun k hk => ?_⟩
  · rw [wv (Vu 6 (by decide) (by decide) (by decide)), y₂]
  · have b₂ : wordsVal s₂.mem base (slot n 5) n = wordsVal t.mem base (slot n 5) n := by
      rw [wv (V₂ 5 (by decide) (by decide) (by decide)), wv (V₁ 5 (by decide) (by decide))]
    have v := VG.Proof.Bignum.mont_cancel cop (o := wordsVal u.mem base (slot n 5) n)
      (c := wordsVal t.mem base (slot n 5) n * 2 ^ (64 * n)) (by
        rw [Pu, x₂, b₂, Nat.mul_mod_mod, RR, Nat.mul_assoc])
    rwa [Nat.mod_eq_of_lt Lu] at v
  · rw [Vu 8 (by decide) (by decide) (by decide) k hk, V₂ 8 (by decide) (by decide) (by decide) k hk,
      V₁ 8 (by decide) (by decide) k hk]

theorem finish_ok {t : State} {T : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n)
    (hY : wordsVal t.mem base (slot n 6) n = T * 2 ^ (64 * n) % m) (hT : T < m) :
    WP isa (finish n) t fun u => St n m size base s₀ u ∧ wordsVal u.mem base (slot n 6) n = T := by
  unfold finish
  refine WP.seq (WP.mono (oneSt_ok S (i := 7) (by decide) (by decide)) fun s₁ ⟨S₁, _, O₁, V₁⟩ => ?_)
  have y₁ : wordsVal s₁.mem base (slot n 6) n = T * 2 ^ (64 * n) % m := by
    rw [wordsVal_eq_val32, V₁ 6 (by decide) (by decide) _ (Nat.le_refl _), ← wordsVal_eq_val32, hY]
  refine WP.mono (mulSt_ok (o := 6) (a := 6) (b := 7) S₁ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [O₁]; exact S.ctx.gt_one)) fun u ⟨Su, _, Lu, Pu, _⟩ => ⟨Su, ?_⟩
  have v := VG.Proof.Dsa.mont_decode S.ctx.coprime (A := wordsVal s₁.mem base (slot n 6) n) (a := T)
    (by rw [y₁, Nat.mod_mod]) (by rw [Pu, O₁])
  rwa [Nat.mod_eq_of_lt Lu, Nat.mod_eq_of_lt hT] at v

theorem core_ok {s : State} {base : Addr} {size n e m : Nat}
    (hs : Scr s base size) (R : CallRoom (s.gpr .esp) base size) (hz : contextBytes n ≤ size)
    (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (core n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      OutsS base (s.gpr .esp) (coreRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have hnz : contextBytes n ≤ 2 ^ 64 := by omega
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b8
  unfold core setup
  refine WP.seq (WP.seq (WP.mono (contextSeed_ok (bits := 65 * n) hs (by omega) (by omega) (by omega) hz hv hm1
    hodd) fun u ⟨Cu, _, Xu, Ou, Ku⟩ => ?_))
  have hset : ∀ r ∈ setupRanges n, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2 := by
    intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0, 8), List.mem_cons_self .., by decide, by decide⟩
    all_goals exact in_core (by decide) (by simp only [contextBytes, slot_lin] at b8 ⊢; omega)
  have Su : St n m size base s u := ⟨Cu, R, Ku, (OutsS.of_outs Ou).core hset⟩
  have keep₀ : ∀ i, 5 ≤ i → i < 9 → ∀ k ≤ 2 * n, val32 u.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
    intro i hi5 hi k hk
    have bi := slot_bound (n := n) hi
    have l5 := Nat.mul_le_mul_right (16 * n + 8) hi5
    simp only [stride] at bi
    apply Ou.val32
    · simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true]
      simp only [slot_lin] at *
      omega
    · omega
  refine WP.mono (squarings_ok hn 0 6 Su (by
    rw [Xu, Nat.pow_zero, Nat.mul_one, show 64 * n + n = 65 * n by omega])) fun w ⟨Sw, Xw, Vw⟩ => ?_
  refine WP.seq (WP.mono (encode_ok Sw hn (by
    rw [Xw, show 64 * n + n * 2 ^ (0 + 6) = 128 * n by rw [show (2 : Nat) ^ (0 + 6) = 64 from rfl]; omega]))
    fun v ⟨Sv, _, Yv, Bv, Ev⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v₁ u₁ _ => WP.block_nil ?_)
  have k₁ : Keeps powerClob v v₁ := u₁.keeps.mono (by decide)
  have S₁ : St n m size base s v₁ := ⟨⟨Sv.ctx.scr.of_keeps k₁ (by decide), Sv.ctx.size_le,
    u₁.mem ▸ Sv.ctx.modulus, Sv.ctx.gt_one, u₁.mem ▸ Sv.ctx.inverse⟩, Sv.room, Sv.keeps.trans k₁, u₁.mem ▸ Sv.mem⟩
  have B₀ : wordsVal v₁.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n * 2 ^ (64 * n) % m := by
    rw [u₁.mem, Bv, wordsVal_eq_val32, wordsVal_eq_val32 (d := slot n 5), Vw 5 (by decide) (by decide) _ (Nat.le_refl _),
      keep₀ 5 (by decide) (by decide) _ (Nat.le_refl _)]
  have E₀ : val32 v₁.mem base (slot n 8) e = val32 s.mem base (slot n 8) e := by
    rw [u₁.mem, Ev e hen, Vw 8 (by decide) (by decide) e hen, keep₀ 8 (by decide) (by decide) e hen]
  refine WP.seq (WP.mono (loopSt_ok S₁ hn he hen (by rw [u₁.mem]; exact Yv) B₀ (by omega) u₁.gpr) fun x I => ?_)
  refine WP.mono (finish_ok I.st hn I.finished (Nat.mod_lt _ (by omega))) fun t ⟨St, V⟩ => ⟨?_, St.mem, St.keeps⟩
  rw [V, E₀]

end

end VG.Proof.Dsa.X86.Pow
