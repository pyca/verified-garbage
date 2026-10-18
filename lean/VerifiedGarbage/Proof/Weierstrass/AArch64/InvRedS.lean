module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
public import VerifiedGarbage.Proof.Divstep.TcS

/-!
# Inversion by divsteps on AArch64: the reduction of signed coefficients

One word of Montgomery reduction of a signed number of `n + 1` words, left
signed in `n + 1` words (`mredS_ok`, `Divstep.mredRaw`), and a signed number
in `(-p, 2p)` brought into `[0, p)` (`normC_ok`, `Divstep.norm`): `mredC` is
the two together.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- `[t + 8]` (`n + 1` words) holding `r ∈ (-p, 2p)` becomes `norm p r`, in `[0, p)`. -/
theorem normC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkA M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0) {t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (ht8 : t % 8 = 0) (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    {r : Int} (hr0 : -(p : Int) < r) (hr1 : r < 2 * p)
    (hR : (wordsVal s.mem base (t + 8) (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      r % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (normC M t)) s fun u =>
      (wordsVal u.mem base (t + 8) (M.n + 1) : Int) = Divstep.norm p r ∧
      KeepRegs [.x2, .x3, .x9] s u ∧ Outside base (t + 8) (8 * (M.n + 1)) s.mem u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [normC, List.append_assoc]
  -- `r`'s sign.
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := t + 8 * (M.n + 1)) (by omega_arith) (by omega_arith) .x3) fun s₃ ⟨l₃, k₃, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₃ (by rw [k₃.gpr _ (by decide), h12])) fun s₄ ⟨g₄, mk₄, k₄, _⟩ => ?_
  have hs₄ := (hs.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  have z₄ : s₄.gpr .x12 = 0 := by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), h12]
  have m₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem]
  -- `R₁ = R + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (chainAdd_ok hs₄ (m := some .x9) ⟨by decide, mk₄⟩ z₄ (d := t + 8) (mo := M.mo) (n := M.n) hmo
    hmo8 (by omega_arith) (by omega_arith) (by omega_arith)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have z₅ : s₅.gpr .x12 = 0 := by rw [k₅.gpr _ (by decide), z₄]
  have P₅ : wordsVal s₅.mem base M.mo M.n = p := by rw [O₅.wordsVal (by omega_arith) (by omega_arith), m₄, hP]
  -- `R₂ = R₁ - p`.
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₅ z₅ (d := t + 8) (mo := M.mo) (n := M.n) hmo hmo8 (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have z₆ : s₆.gpr .x12 = 0 := by rw [k₆.gpr _ (by decide), z₅]
  have P₆ : wordsVal s₆.mem base M.mo M.n = p := by rw [O₆.wordsVal (by omega_arith) (by omega_arith), P₅]
  -- `R₂`'s sign.
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₆ (d := t + 8 * (M.n + 1)) (by omega_arith) (by omega_arith) .x3) fun s₇ ⟨l₇, k₇, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₇ (by rw [k₇.gpr _ (by decide), z₆])) fun s₈ ⟨g₈, mk₈, k₈, _⟩ => ?_
  have hs₈ := (hs₆.of_keeps k₇ (by decide)).of_keeps k₈ (by decide)
  have z₈ : s₈.gpr .x12 = 0 := by rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), z₆]
  have m₈ : s₈.mem = s₆.mem := by rw [k₈.mem, k₇.mem]
  -- `R₃ = R₂ + (p if negative)`.
  refine WP.mono (chainAdd_ok hs₈ (m := some .x9) ⟨by decide, mk₈⟩ z₈ (d := t + 8) (mo := M.mo) (n := M.n) hmo
    hmo8 (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨e₉, k₉, O₉⟩ => ?_
  refine ⟨?_, ((((((Keeps.regs k₃).mono (by decide)).trans ((Keeps.regs k₄).mono (by decide))).trans
    (k₅.mono (by decide))).trans (k₆.mono (by decide))).trans ((Keeps.regs k₇).mono (by decide))).trans
    (((Keeps.regs k₈).mono (by decide)).trans (k₉.mono (by decide))), fun x hx => ?_⟩
  rotate_left
  · rw [O₉ x hx, m₈, O₆ x hx, O₅ x hx, m₄]
  -- The arithmetic.
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hQ : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by rw [pow64_succ, Nat.mul_comm]
  have l₃' : s₃.gpr .x3 = word s.mem base (t + 8 + 8 * M.n) := by
    rw [l₃, show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith]
  have l₇' : s₇.gpr .x3 = word s₆.mem base (t + 8 + 8 * M.n) := by
    rw [l₇, show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith]
  exact Divstep.norm_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (r := r)
    (R := wordsVal s.mem base (t + 8) (M.n + 1)) (R₁ := wordsVal s₅.mem base (t + 8) (M.n + 1))
    (R₂ := wordsVal s₆.mem base (t + 8) (M.n + 1)) (R₃ := wordsVal u.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hpA hr0 hr1 (hQ ▸ wordsVal_lt _ _ _ _) (by rw [← hQ]; exact hR)
    (by rw [e₅]; simp only [mk]; rw [masked_top (by rw [g₄, l₃']), m₄, hP, hQ])
    (hQ ▸ wordsVal_lt _ _ _ _) (by rw [P₅, hQ] at e₆; exact e₆)
    (by rw [e₉]; simp only [mk]; rw [masked_top (by rw [g₈, l₇']), m₈, P₆, hQ])

/-- `[dst] ≡ mredRaw p m T` (`n + 1` words, signed), for `[t]` (`n + 1` words)
holding `T`, `|T| ≤ 2^63 p`. -/
theorem mredS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkA M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0) {dst t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (ht8 : t % 8 = 0) (hd : dst + 8 * (M.n + 1) ≤ size) (hd8 : dst % 8 = 0)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (hdt : dst + 8 * (M.n + 1) ≤ t ∨ t + 8 * (M.n + 2) ≤ dst)
    {T : Int} (hT : |T| ≤ 2 ^ 63 * p)
    (hW : (wordsVal s.mem base t (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (mredS M dst t)) s fun u =>
      (wordsVal u.mem base dst (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
        Divstep.mredRaw p M.minv.toNat T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s u ∧
      ∃ m₁, Outside base t (8 * (M.n + 2)) s.mem m₁ ∧ Outside base dst (8 * (M.n + 1)) m₁ u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [mredS, List.append_assoc]
  -- `x16 = k`, `[t]` sign-extended.
  rw [WP.block_append_iff]
  refine WP.mono (mredHead_ok hs h12 ht ht8) fun s₁ ⟨x₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have z₁ : s₁.gpr .x12 = 0 := by rw [k₁.gpr _ (by decide), h12]
  have P₁ : wordsVal s₁.mem base M.mo M.n = p := by rw [O₁.wordsVal (by omega_arith) (by omega_arith), hP]
  -- `[t] += k p`.
  rw [WP.block_append_iff]
  refine WP.mono (mulAdd_ok hs₁ (w := .x16) (by decide) z₁ (dst := t) (src := M.mo) (k := M.n) (K := M.n + 2)
    (by omega_arith) hmo hmo8 ht ht8 htm) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- `[dst] = R`.
  refine WP.mono (copyW_ok hs₂ (dst := dst) (src := t + 8) (by omega_arith) hd8 (M.n + 1) (by omega_arith) hd
    (by omega_arith)) fun u ⟨eu, ku, Ou⟩ => ?_
  refine ⟨?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (ku.mono (by decide)), s₂.mem,
    fun x hx => by rw [O₂ x hx, O₁ x (by omega_arith)], Ou⟩
  -- The arithmetic.
  have hp0 : 0 < p := by
    have := hM.inv
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at this; exact absurd this (by decide)
    · exact h
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hQ : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by rw [pow64_succ, Nat.mul_comm]
  have hQ' : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [show M.n + 2 = M.n + 1 + 1 from rfl, pow64_succ, hQ, Nat.mul_comm]
  have eR : wordsVal s₂.mem base t (M.n + 2) % 2 ^ 64 + 2 ^ 64 * wordsVal s₂.mem base (t + 8) (M.n + 1) =
      wordsVal s₂.mem base t (M.n + 2) := by
    rw [show M.n + 2 = M.n + 1 + 1 from rfl, wordsVal, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (BitVec.isLt _)]
  have key := Divstep.mredRaw_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := M.minv.toNat)
    (t := T) (W := wordsVal s.mem base t (M.n + 1)) (k := (s₁.gpr .x16).toNat)
    (E := wordsVal s₂.mem base t (M.n + 2)) (R := wordsVal s₂.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hp0 hpA hM.inv hT (hQ ▸ wordsVal_lt _ _ _ _) (by rw [← hQ]; exact hW)
    (by rw [x₁, wordsVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)])
    (by rw [e₂, e₁, P₁, sgnW_top, hQ', hQ])
    (by have := eR; omega_arith)
  rw [eu, hQ]
  exact key

end VG.Proof.Weierstrass.AArch64
