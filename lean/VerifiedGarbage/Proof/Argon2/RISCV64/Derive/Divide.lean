module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Divide
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp

/-!
# Fixed-time division on RISCV64

`code_ok`: `Impl.Argon2.RISCV64.Divide.code` leaves `n / D` in `a3` and
`n mod D` in `a4`, for the numerator `n` in the low 32 bits of `a1` and the
divisor `D` in `a2`, `0 < D < 2³¹`. After `k` bits (`bits_ok`) the low 32
bits of `a1` hold the `32 - k` bits of `n` not yet consumed, shifted up by
`k`, and `a3`, `a4` the quotient and remainder of the `k` consumed ones: each
bit is one step of binary long division (`Proof.Argon2.divide_step`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive.Divide

open VG VG.RISCV64
open VG.Impl.Argon2.RISCV64.Divide (bit bits code)
open VG.RISCV64.Wp (Upd wp_add wp_sub wp_li)
open VG.Proof.Argon2.RISCV64 (wp_mul wp_srlw wp_srl wp_sll)

/-- Only `a1`, `a3`, `a4` and `a5` change. -/
structure Keep (s t : State) : Prop where
  other : ∀ r, r ≠ .a1 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (h' : Keep t u) : Keep s u :=
  ⟨fun r a b c d => (h'.other r a b c d).trans (h.other r a b c d), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.of_upd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d = .a1 ∨ d = .a3 ∨ d = .a4 ∨ d = .a5) : Keep s t :=
  ⟨fun r a b c e => u.other r (by
    rcases hd with rfl | rfl | rfl | rfl <;> with_reducible assumption), u.mem, u.rd, u.wr, u.sp⟩

/-- The numbers after `k` bits of `n`. -/
def Stage (n D k : Nat) (s : State) : Prop :=
  ((s.gpr .a1).setWidth 32).toNat = (n % 2 ^ (32 - k)) * 2 ^ k ∧
    (s.gpr .a3).toNat = n / 2 ^ (32 - k) / D ∧
    (s.gpr .a4).toNat = n / 2 ^ (32 - k) % D

theorem toNat_lsl1 (x : BitVec 64) : (x <<< 1).toNat = x.toNat * 2 % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]

theorem toNat_lsr (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- One bit. -/
theorem bit_ok {s : State} {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31)
    (hb : (s.gpr .a2).toNat = D) (h9 : (s.gpr .a6).toNat = 1) {n k : Nat} (hn : n < 2 ^ 32)
    (hk : k < 32) (h : Stage n D k s) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, Stage n D (k + 1) t → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (bit ++ is)) s Q := by
  obtain ⟨hc, hq6, ha⟩ := h
  have hm : k + (31 - k) = 31 := by omega_arith
  have pos : ∀ j, 0 < 2 ^ j := fun j => Nat.two_pow_pos j
  have e32 : 32 - k = 31 - k + 1 := by omega_arith
  have p31 : 2 ^ (31 - k) * 2 ^ k = 2 ^ 31 := by rw [← Nat.pow_add, Nat.add_comm, hm]
  have hRlt : n % 2 ^ (32 - k) < 2 ^ (32 - k) := Nat.mod_lt _ (pos _)
  have hRb := (Nat.div_add_mod' (n % 2 ^ (32 - k)) (2 ^ (31 - k))).symm
  have hb1 : n % 2 ^ (32 - k) / 2 ^ (31 - k) ≤ 1 := by
    have h' : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [e32, Nat.pow_succ]
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [h', hRlt]))
  have hR'lt : n % 2 ^ (32 - k) % 2 ^ (31 - k) < 2 ^ (31 - k) := Nat.mod_lt _ (pos _)
  have hqlt : n / 2 ^ (32 - k) / D < 2 ^ 32 := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)
  have hrlt : n / 2 ^ (32 - k) % D < D := Nat.mod_lt _ hD
  generalize hN : n / 2 ^ (32 - k) = N at hq6 ha hqlt hrlt
  generalize hRR : n % 2 ^ (32 - k) = R at hc hRlt hRb hb1 hR'lt
  generalize hbb : R / 2 ^ (31 - k) = b at hRb hb1
  generalize hR' : R % 2 ^ (31 - k) = R' at hRb hR'lt
  have N' : n / 2 ^ (32 - (k + 1)) = 2 * N + b := by
    rw [← hN, ← hbb, ← hRR, show 32 - (k + 1) = 31 - k by omega_arith, e32, Nat.pow_succ,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / 2 ^ (31 - k)) 2
    omega_using [this]
  have R'' : n % 2 ^ (32 - (k + 1)) = R' := by
    rw [← hR', ← hRR, show 32 - (k + 1) = 31 - k by omega_arith, e32, Nat.pow_succ, Nat.mod_mul_right_mod]
  have step := Proof.Argon2.divide_step (n := N) (d := D) (q := N / D) (r := N % D)
    (bit := b) (Nat.div_add_mod' N _).symm hrlt hb1
  dsimp only at step
  obtain ⟨st₁, st₂⟩ := step
  have res := Proof.Argon2.divide_result hD st₁ st₂
  have pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hPb : R' * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    have := Nat.mul_le_mul_right (2 ^ k) (show R' + 1 ≤ 2 ^ (31 - k) by omega_arith)
    rw [Nat.add_mul, Nat.one_mul, p31] at this
    exact this
  have hL : ((s.gpr .a1).setWidth 32).toNat = b * 2 ^ 31 + R' * 2 ^ k := by
    rw [hc, hRb, Nat.add_mul, Nat.mul_assoc, p31]
  have hP : R' * 2 ^ (k + 1) = 2 * (R' * 2 ^ k) := by rw [pk, Nat.mul_left_comm]
  generalize hPP : R' * 2 ^ k = P at hP hPb hL
  generalize hKK : 2 ^ k = K at hPb pk
  have hK : 0 < K := hKK ▸ pos k
  simp only [bit, List.cons_append, List.nil_append]
  refine wp_srlw (by decide) (by decide) fun s₁ u₁ => ?_
  have v₁ : (s₁.gpr .a5).toNat = b := by
    rw [u₁.gpr, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hL,
      Nat.mod_eq_of_lt (by
        rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;>
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith))]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> omega_arith
  refine wp_sll (by decide) fun s₂ u₂ => ?_
  have v₂ : ((s₂.gpr .a1).setWidth 32).toNat = 2 * P := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_setWidth, toNat_lsl1]
    have hx : (s.gpr .a1).toNat % 2 ^ 32 = b * 2 ^ 31 + P := by
      rw [← BitVec.toNat_setWidth, hL]
    rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mul_mod, hx]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> omega_arith
  refine wp_sll (by decide) fun s₃ u₃ => ?_
  refine wp_add fun s₄ u₄ => ?_
  have v₄ : (s₄.gpr .a4).toNat = 2 * (N % D) + b := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), BitVec.toNat_add, toNat_lsl1,
      u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha, v₁]
    omega_arith
  refine wp_sub fun s₅ u₅ => ?_
  have d₄ : (s₄.gpr .a2).toNat = D := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hb]
  refine wp_srl (by decide) fun s₆ u₆ => ?_
  generalize ht : (if 2 * (N % D) + b < D then 0 else 1) = t
  have ht1 : t ≤ 1 := by rw [← ht]; split <;> omega_arith
  have v₆ : (s₆.gpr .a5).toNat = 1 - t := by
    rw [u₆.gpr, toNat_lsr, u₅.gpr, BitVec.toNat_sub, v₄, d₄, ← ht]
    split
    · rw [show 2 ^ 64 - D + (2 * (N % D) + b) = 2 ^ 64 - (D - (2 * (N % D) + b)) by omega_arith,
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    · rw [show 2 ^ 64 - D + (2 * (N % D) + b) = (2 * (N % D) + b - D) + 2 ^ 64 by omega_arith,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
  refine wp_sub fun s₇ u₇ => ?_
  have v₇ : (s₇.gpr .a5).toNat = t := by
    have e9 : (s₆.gpr .a6).toNat = 1 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h9]
    rw [u₇.gpr, BitVec.toNat_sub, v₆, e9]
    rcases (by omega_arith : t = 0 ∨ t = 1) with rfl | rfl <;> decide
  refine wp_sll (by decide) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => ?_
  refine wp_mul fun s₁₀ u₁₀ => ?_
  refine wp_sub fun s₁₁ u₁₁ => hq s₁₁ ⟨?_, ?_, ?_⟩ ?_
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), v₂, R'', hP]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, BitVec.toNat_add,
      u₈.gpr, u₈.other _ (by decide), toNat_lsl1, v₇, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hq6, N', ← res.1, ← ht]
    omega_arith
  · have d₉ : (s₉.gpr .a2).toNat = D := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), d₄]
    have r₉ : (s₉.gpr .a4).toNat = 2 * (N % D) + b := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), v₄]
    have e₉ : (s₉.gpr .a5).toNat = t := by rw [u₉.other _ (by decide), u₈.other _ (by decide), v₇]
    rw [u₁₁.gpr, u₁₀.other _ (by decide), u₁₀.gpr, BitVec.toNat_sub, BitVec.toNat_mul, e₉, d₉, r₉,
      N', ← res.2, ← ht]
    have sub : ∀ x v : Nat, x ≤ v → v < 2 ^ 64 → (2 ^ 64 - x % 2 ^ 64 + v) % 2 ^ 64 = v - x :=
      fun x v h₁ h₂ => by
        rw [Nat.mod_eq_of_lt (a := x) (by omega_arith), show 2 ^ 64 - x + v = (v - x) + 2 ^ 64 by omega_arith,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    split
    · rw [Nat.zero_mul, sub 0 _ (by omega_arith) (by omega_arith)]; rfl
    · rw [Nat.one_mul, sub D _ (by omega_arith) (by omega_arith)]
  · exact (((((((((((Keep.of_upd u₁ (by simp)).trans (Keep.of_upd u₂ (by simp))).trans (Keep.of_upd u₃ (by simp))).trans (Keep.of_upd u₄ (by simp))).trans (Keep.of_upd u₅ (by simp))).trans (Keep.of_upd u₆ (by simp))).trans (Keep.of_upd u₇ (by simp))).trans (Keep.of_upd u₈ (by simp))).trans (Keep.of_upd u₉ (by simp))).trans (Keep.of_upd u₁₀ (by simp))).trans (Keep.of_upd u₁₁ (by simp)))

theorem bits_ok {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31) {n : Nat}
    (hn : n < 2 ^ 32) {is : List Instr} {Q : State → Prop} :
    ∀ k ≤ 32, ∀ s : State, (s.gpr .a2).toNat = D → (s.gpr .a6).toNat = 1 → Stage n D 0 s →
      (∀ t, Stage n D k t → Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (bits k ++ is)) s Q
  | 0, _, s, _, _, h, hq => hq s h (Keep.refl s)
  | k + 1, hk, s, hb, h9, h, hq => by
    simp only [bits, List.append_assoc]
    refine bits_ok hD hD2 hn k (by omega_arith) s hb h9 h fun t ht kt => ?_
    refine bit_ok hD hD2 (by rw [kt.other _ (by decide) (by decide) (by decide) (by decide), hb])
      (by rw [kt.other _ (by decide) (by decide) (by decide) (by decide), h9]) hn (by omega_arith) ht
      fun u hu ku => hq u hu (kt.trans ku)

/-- Only `a1` and `a3`–`a6` change. -/
structure KeepD (s t : State) : Prop where
  other : ∀ r, r ≠ .a1 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → r ≠ .a6 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- The division: `r6 := n / D`, `r7 := n mod D`, for `n` the low 32 bits of
`a1`. -/
theorem code_ok {s : State} {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31)
    (hb : (s.gpr .a2).toNat = D) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, (t.gpr .a3).toNat = ((s.gpr .a1).setWidth 32).toNat / D →
      (t.gpr .a4).toNat = ((s.gpr .a1).setWidth 32).toNat % D → KeepD s t →
      WP isa (.block is) t Q) :
    WP isa (.block (code ++ is)) s Q := by
  have hn := ((s.gpr .a1).setWidth 32).isLt
  simp only [code, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => ?_
  have e4 : s₃.gpr .a1 = s.gpr .a1 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine bits_ok hD hD2 hn 32 (Nat.le_refl _) s₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₃.gpr]; rfl) ⟨?_, ?_, ?_⟩ fun t ⟨hc, h6, h7⟩ kt => ?_
  · rw [e4, Nat.mod_eq_of_lt hn]; simp
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, show 32 - 0 = 32 from rfl,
      Nat.div_eq_of_lt hn, Nat.zero_div]; rfl
  · rw [u₃.other _ (by decide), u₂.gpr, show 32 - 0 = 32 from rfl, Nat.div_eq_of_lt hn,
      Nat.zero_mod]; rfl
  · refine hq t (by rw [h6]; simp) (by rw [h7]; simp) ⟨fun r a b c d e => ?_, ?_, ?_, ?_, ?_⟩
    · rw [kt.other r a b c d, u₃.other _ e, u₂.other _ c, u₁.other _ b]
    · rw [kt.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [kt.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [kt.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [kt.sp, u₃.sp, u₂.sp, u₁.sp]

end VG.Proof.Argon2.RISCV64.Derive.Divide
