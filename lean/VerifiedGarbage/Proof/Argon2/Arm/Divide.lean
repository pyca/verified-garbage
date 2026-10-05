import VerifiedGarbage.Proof.Blake2.Arm.Stream.Verified
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Impl.Argon2.Arm.Divide

/-!
# Fixed-time division on ARMv7

`code_ok`: `Impl.Argon2.Arm.Divide.code` leaves `n / D` in `r1` and `n mod D`
in `r0`, for the numerator `n` in `r1` and the divisor `D` in `r2`,
`0 < D < 2³¹`. After `k` bits (`bits_ok`) `r1` holds the `32 - k` bits of `n`
not yet consumed above the quotient of the `k` consumed ones, and `r0` their
remainder: each bit is one step of binary long division
(`Proof.Argon2.divide_step`).
-/

namespace VG.Proof.Argon2.Arm.Divide

open VG VG.Arm
open VG.Impl.Argon2.Arm.Divide (bit bits code)
open VG.Proof.MdStream.Arm (Upd WP.cons wp_mov wp_add wp_sub wp_and op2_reg op2_imm)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

section
variable {is : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}

/-- `subs`, and its carry: no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

end

/-- Only `r0`, `r1`, `r3` and the flags change. -/
structure Keep (s t : VG.Arm.State) : Prop where
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keep.refl (s : VG.Arm.State) : Keep s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s t u : VG.Arm.State} (h : Keep s t) (h' : Keep t u) : Keep s u :=
  ⟨fun r a b c => (h'.other r a b c).trans (h.other r a b c), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.of_upd {s t : VG.Arm.State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hd : d = .r0 ∨ d = .r1 ∨ d = .r3) : Keep s t :=
  ⟨fun r a b c => u.other r (by rcases hd with rfl | rfl | rfl <;> with_reducible assumption), u.mem, u.rd, u.wr, u.sp⟩

/-- The numbers after `k` bits of `n`. -/
def Stage (n D k : Nat) (s : VG.Arm.State) : Prop :=
  (s.gpr .r1).toNat = (n % 2 ^ (32 - k)) * 2 ^ k + n / 2 ^ (32 - k) / D ∧
    (s.gpr .r0).toNat = n / 2 ^ (32 - k) % D

/-- One bit. -/
theorem bit_ok {s : VG.Arm.State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31)
    (hb : s.gpr .r2 = D) {n k : Nat} (hn : n < 2 ^ 32) (hk : k < 32)
    (h : Stage n D.toNat k s) {is : List Instr} {Q : VG.Arm.State → Prop}
    (hq : ∀ t, Stage n D.toNat (k + 1) t → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (bit ++ is)) s Q := by
  obtain ⟨hc, ha⟩ := h
  have hm : k + (31 - k) = 31 := by omega
  have pos : ∀ j, 0 < 2 ^ j := fun j => Nat.two_pow_pos j
  have e32 : 32 - k = 31 - k + 1 := by omega
  have p31 : 2 ^ (31 - k) * 2 ^ k = 2 ^ 31 := by rw [← Nat.pow_add, Nat.add_comm, hm]
  have hRlt : n % 2 ^ (32 - k) < 2 ^ (32 - k) := Nat.mod_lt _ (pos _)
  have hRb := (Nat.div_add_mod' (n % 2 ^ (32 - k)) (2 ^ (31 - k))).symm
  have hb1 : n % 2 ^ (32 - k) / 2 ^ (31 - k) ≤ 1 := by
    have h' : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [e32, Nat.pow_succ]
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have hR'lt : n % 2 ^ (32 - k) % 2 ^ (31 - k) < 2 ^ (31 - k) := Nat.mod_lt _ (pos _)
  have hqlt : n / 2 ^ (32 - k) / D.toNat < 2 ^ k := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.div_lt_of_lt_mul ?_)
    rw [← Nat.pow_add, show 32 - k + k = 32 by omega]; exact hn
  have hrlt : n / 2 ^ (32 - k) % D.toNat < D.toNat := Nat.mod_lt _ hD
  -- Abbreviations, as numbers.
  generalize hN : n / 2 ^ (32 - k) = N at hc ha hqlt hrlt
  generalize hRR : n % 2 ^ (32 - k) = R at hc hRlt hRb hb1 hR'lt
  generalize hbb : R / 2 ^ (31 - k) = b at hRb hb1
  generalize hR' : R % 2 ^ (31 - k) = R' at hRb hR'lt
  -- The next stage's numbers.
  have N' : n / 2 ^ (32 - (k + 1)) = 2 * N + b := by
    rw [← hN, ← hbb, ← hRR, show 32 - (k + 1) = 31 - k by omega, e32, Nat.pow_succ,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / 2 ^ (31 - k)) 2
    omega
  have R'' : n % 2 ^ (32 - (k + 1)) = R' := by
    rw [← hR', ← hRR, show 32 - (k + 1) = 31 - k by omega, e32, Nat.pow_succ, Nat.mod_mul_right_mod]
  have step := Proof.Argon2.divide_step (n := N) (d := D.toNat) (q := N / D.toNat) (r := N % D.toNat)
    (bit := b) (Nat.div_add_mod' N _).symm hrlt hb1
  dsimp only at step
  obtain ⟨st₁, st₂⟩ := step
  have res := Proof.Argon2.divide_result hD st₁ st₂
  -- The instructions, with `K = 2 ^ k` and `P = R' · K`.
  have pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hP : R' * 2 ^ (k + 1) = 2 * (R' * 2 ^ k) := by rw [pk, Nat.mul_left_comm]
  have hPb : R' * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    have := Nat.mul_le_mul_right (2 ^ k) (show R' + 1 ≤ 2 ^ (31 - k) by omega)
    rw [Nat.add_mul, Nat.one_mul, p31] at this
    exact this
  have hr1 : (s.gpr .r1).toNat = b * 2 ^ 31 + R' * 2 ^ k + N / D.toNat := by
    rw [hc, hRb, Nat.add_mul, Nat.mul_assoc, p31]
  generalize hPP : R' * 2 ^ k = P at hP hPb hr1
  generalize hKK : 2 ^ k = K at hPb hqlt pk
  simp only [bit, List.cons_append, List.nil_append]
  refine wp_adds (op2_reg _ _) fun s₁ u₁ c₁ => ?_
  have cb : s₁.c = decide (b = 1) := by
    rw [c₁, hr1]; rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega
  have v₁ : (s₁.gpr .r1).toNat = 2 * P + 2 * (N / D.toNat) := by
    rw [u₁.gpr, BitVec.toNat_add, hr1]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show 1 * 2 ^ 31 + P + N / D.toNat + (1 * 2 ^ 31 + P + N / D.toNat) =
        (2 * P + 2 * (N / D.toNat)) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  refine wp_adc (op2_reg _ _) fun s₂ u₂ _ => ?_
  have v₂ : (s₂.gpr .r0).toNat = 2 * (N % D.toNat) + b := by
    rw [u₂.gpr, u₁.other _ (by decide), cb, BitVec.toNat_add, BitVec.toNat_add, ha]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega
  refine wp_subsC (op2_reg _ _) fun s₃ u₃ c₃ => ?_
  have d₂ : s₂.gpr .r2 = D := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
  rw [d₂] at u₃ c₃
  rw [v₂] at c₃
  refine wp_adc (op2_imm (by decide)) fun s₄ u₄ _ => ?_
  -- The quotient bit.
  generalize ht : (if 2 * (N % D.toNat) + b < D.toNat then 0 else 1) = t
  have ht1 : t ≤ 1 := by rw [← ht]; split <;> omega
  have v₄ : (s₄.gpr .r1).toNat = 2 * P + 2 * (N / D.toNat) + t := by
    rw [u₄.gpr, c₃, u₃.other _ (by decide), u₂.other _ (by decide), BitVec.toNat_add, BitVec.toNat_add, v₁,
      ← ht]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, ite_true, show ¬ D.toNat ≤ 2 * (N % D.toNat) + b by omega, decide_false,
        Bool.false_eq_true, ite_false]
      simp; omega
    · simp only [hv, ite_false, show D.toNat ≤ 2 * (N % D.toNat) + b by omega, decide_true, ite_true]
      simp; omega
  refine wp_and (op2_imm (by decide)) fun s₅ u₅ => ?_
  have v₅ : s₅.gpr .r3 = BitVec.ofNat 32 t := by
    apply BitVec.eq_of_toNat_eq
    rw [u₅.gpr, BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, v₄,
      BitVec.toNat_ofNat]
    omega
  refine wp_sub (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_and (op2_reg _ _) fun s₇ u₇ => ?_
  refine wp_add (op2_reg _ _) fun s₈ u₈ => hq s₈ ⟨?_, ?_⟩ ?_
  · -- `r1`: the remaining bits above the quotient.
    rw [R'', hP, N', ← res.1, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), v₄, ← ht]
    omega
  · -- `r0`: the remainder.
    have d₆ : s₆.gpr .r2 = D := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), d₂]
    rw [N', ← res.2, u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), d₆, v₅,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, ← ht]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, ite_true]
      rw [show BitVec.ofNat 32 0 - 1 = BitVec.allOnes 32 by decide, BitVec.allOnes_and, BitVec.sub_add_cancel,
        v₂]
    · simp only [hv, ite_false]
      rw [show BitVec.ofNat 32 1 - 1 = 0#32 by decide, show (0#32) &&& D = 0#32 by simp, BitVec.add_zero,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, v₂]; omega), v₂]
  · exact (Keep.of_upd u₁ (by simp)).trans ((Keep.of_upd u₂ (by simp)).trans ((Keep.of_upd u₃ (by simp)).trans
      ((Keep.of_upd u₄ (by simp)).trans ((Keep.of_upd u₅ (by simp)).trans ((Keep.of_upd u₆ (by simp)).trans
        ((Keep.of_upd u₇ (by simp)).trans (Keep.of_upd u₈ (by simp))))))))

theorem bits_ok {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31) {n : Nat}
    (hn : n < 2 ^ 32) {is : List Instr} {Q : VG.Arm.State → Prop} :
    ∀ k ≤ 32, ∀ s : VG.Arm.State, s.gpr .r2 = D → Stage n D.toNat 0 s →
      (∀ t, Stage n D.toNat k t → Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (bits k ++ is)) s Q
  | 0, _, s, _, h, hq => hq s h (Keep.refl s)
  | k + 1, hk, s, hb, h, hq => by
    simp only [bits, List.append_assoc]
    refine bits_ok hD hD2 hn k (by omega) s hb h fun t ht kt => ?_
    refine bit_ok hD hD2 (by rw [kt.other _ (by decide) (by decide) (by decide), hb]) hn (by omega) ht
      fun u hu ku => hq u hu (kt.trans ku)

/-- The division: `r1 := n / D`, `r0 := n mod D`. -/
theorem code_ok {s : VG.Arm.State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31)
    (hb : s.gpr .r2 = D) {is : List Instr} {Q : VG.Arm.State → Prop}
    (hq : ∀ t, (t.gpr .r1).toNat = (s.gpr .r1).toNat / D.toNat →
      (t.gpr .r0).toNat = (s.gpr .r1).toNat % D.toNat → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Argon2.Arm.Divide.code ++ is)) s Q := by
  have hn := (s.gpr .r1).isLt
  simp only [VG.Impl.Argon2.Arm.Divide.code, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine bits_ok hD hD2 hn 32 (Nat.le_refl _) s₁ (by rw [u₁.other _ (by decide), hb]) ⟨?_, ?_⟩
    fun t ⟨hc, ha⟩ kt => ?_
  · rw [u₁.other _ (by decide), Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, Nat.zero_div]; simp
  · rw [u₁.gpr, Nat.div_eq_of_lt hn, Nat.zero_mod]; rfl
  · refine hq t (by rw [hc]; simp [Nat.mod_one]) (by rw [ha]; simp) ((Keep.of_upd u₁ (by simp)).trans kt)

end VG.Proof.Argon2.Arm.Divide
