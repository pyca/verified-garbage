module

public import VerifiedGarbage.Proof.Argon2.Arm.Derive.Locals
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Common
import VerifiedGarbage.Proof.Argon2.Divide
public import VerifiedGarbage.Impl.Argon2.Arm.Divide
public import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! ### `Argon2.Arm.Divide`, which only this module used -/

section

/-!
# Fixed-time division on ARMv7

`code_ok`: `Impl.Argon2.Arm.Divide.code` leaves `n / D` in `r1` and `n mod D`
in `r0`, for the numerator `n` in `r1` and the divisor `D` in `r2`,
`0 < D < 2³¹`. After `k` bits (`bits_ok`) `r1` holds the `32 - k` bits of `n`
not yet consumed above the quotient of the `k` consumed ones, and `r0` their
remainder: each bit is one step of binary long division
(`Proof.Argon2.divide_step`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Divide

open VG VG.Arm
open VG.Impl.Argon2.Arm.Divide (bit bits code)
open VG.Proof.MdStream.Arm (Upd WP.cons wp_mov wp_add wp_sub wp_and op2_reg op2_imm)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs`, and its carry: no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [reduceExec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

end

/-- Only `r0`, `r1`, `r3` and the flags change. -/
structure Keep (s t : State) : Prop where
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (h' : Keep t u) : Keep s u :=
  ⟨fun r a b c => (h'.other r a b c).trans (h.other r a b c), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.of_upd {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hd : d = .r0 ∨ d = .r1 ∨ d = .r3) : Keep s t :=
  ⟨fun r a b c => u.other r (by rcases hd with rfl | rfl | rfl <;> with_reducible assumption), u.mem, u.rd, u.wr, u.sp⟩

/-- The numbers after `k` bits of `n`. -/
def Stage (n D k : Nat) (s : State) : Prop :=
  (s.gpr .r1).toNat = (n % 2 ^ (32 - k)) * 2 ^ k + n / 2 ^ (32 - k) / D ∧
    (s.gpr .r0).toNat = n / 2 ^ (32 - k) % D

/-- One bit. -/
theorem bit_ok {s : State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31)
    (hb : s.gpr .r2 = D) {n k : Nat} (hn : n < 2 ^ 32) (hk : k < 32)
    (h : Stage n D.toNat k s) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, Stage n D.toNat (k + 1) t → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (bit ++ is)) s Q := by
  obtain ⟨hc, ha⟩ := h
  obtain hm : k + (31 - k) = 31 := by omega_using [hk]
  obtain pos : ∀ j, 0 < 2 ^ j := fun j => Nat.two_pow_pos j
  obtain e32 : 32 - k = 31 - k + 1 := by omega_using [hk]
  obtain p31 : 2 ^ (31 - k) * 2 ^ k = 2 ^ 31 := by rw [← Nat.pow_add, Nat.add_comm, hm]
  obtain hRlt : n % 2 ^ (32 - k) < 2 ^ (32 - k) := Nat.mod_lt _ (pos _)
  obtain hRb := (Nat.div_add_mod' (n % 2 ^ (32 - k)) (2 ^ (31 - k))).symm
  obtain hb1 : n % 2 ^ (32 - k) / 2 ^ (31 - k) ≤ 1 := by
    obtain h' : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [e32, Nat.pow_succ]
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [h', hRlt]))
  obtain hR'lt : n % 2 ^ (32 - k) % 2 ^ (31 - k) < 2 ^ (31 - k) := Nat.mod_lt _ (pos _)
  obtain hqlt : n / 2 ^ (32 - k) / D.toNat < 2 ^ k := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.div_lt_of_lt_mul ?_)
    rw [← Nat.pow_add, show 32 - k + k = 32 by omega_using [hk]]; exact hn
  obtain hrlt : n / 2 ^ (32 - k) % D.toNat < D.toNat := Nat.mod_lt _ hD
  -- Abbreviations, as numbers.
  generalize hN : n / 2 ^ (32 - k) = N at hc ha hqlt hrlt
  generalize hRR : n % 2 ^ (32 - k) = R at hc hRlt hRb hb1 hR'lt
  generalize hbb : R / 2 ^ (31 - k) = b at hRb hb1
  generalize hR' : R % 2 ^ (31 - k) = R' at hRb hR'lt
  -- The next stage's numbers.
  obtain N' : n / 2 ^ (32 - (k + 1)) = 2 * N + b := by
    rw [← hN, ← hbb, ← hRR, show 32 - (k + 1) = 31 - k by omega_using [hk], e32, Nat.pow_succ,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / 2 ^ (31 - k)) 2
    omega_using [this]
  obtain R'' : n % 2 ^ (32 - (k + 1)) = R' := by
    rw [← hR', ← hRR, show 32 - (k + 1) = 31 - k by omega_using [hk], e32, Nat.pow_succ, Nat.mod_mul_right_mod]
  obtain step := Proof.Argon2.divide_step (n := N) (d := D.toNat) (q := N / D.toNat) (r := N % D.toNat)
    (bit := b) (Nat.div_add_mod' N _).symm hrlt hb1
  dsimp only at step
  obtain ⟨st₁, st₂⟩ := step
  obtain res := Proof.Argon2.divide_result hD st₁ st₂
  -- The instructions, with `K = 2 ^ k` and `P = R' · K`.
  obtain pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  obtain hP : R' * 2 ^ (k + 1) = 2 * (R' * 2 ^ k) := by rw [pk, Nat.mul_left_comm]
  obtain hPb : R' * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    have := Nat.mul_le_mul_right (2 ^ k) (show R' + 1 ≤ 2 ^ (31 - k) by omega_using [hR'lt])
    rw [Nat.add_mul, Nat.one_mul, p31] at this
    exact this
  obtain hr1 : (s.gpr .r1).toNat = b * 2 ^ 31 + R' * 2 ^ k + N / D.toNat := by
    rw [hc, hRb, Nat.add_mul, Nat.mul_assoc, p31]
  generalize hPP : R' * 2 ^ k = P at hP hPb hr1
  generalize hKK : 2 ^ k = K at hPb hqlt pk
  simp only [bit, List.cons_append, List.nil_append]
  refine wp_adds (op2_reg _ _) fun s₁ u₁ c₁ => ?_
  obtain cb : s₁.c = decide (b = 1) := by
    rw [c₁, hr1]; rcases (by omega_using [hb1] : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega_using [hD, hD2, hN, ha, hrlt, hc, hPP, hP, hPb, hqlt, N', st₁, st₂, res, hr1]
  obtain v₁ : (s₁.gpr .r1).toNat = 2 * P + 2 * (N / D.toNat) := by
    rw [u₁.gpr, BitVec.toNat_add, hr1]
    rcases (by omega_using [hb1] : b = 0 ∨ b = 1) with rfl | rfl
    · rw [Nat.mod_eq_of_lt (by omega_using [hPb, hqlt])]; omega_using []
    · rw [show 1 * 2 ^ 31 + P + N / D.toNat + (1 * 2 ^ 31 + P + N / D.toNat) =
        (2 * P + 2 * (N / D.toNat)) + 2 ^ 32 by omega_using [], Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_using [hPb, hqlt])]
  refine wp_adc (op2_reg _ _) fun s₂ u₂ _ => ?_
  obtain v₂ : (s₂.gpr .r0).toNat = 2 * (N % D.toNat) + b := by
    rw [u₂.gpr, u₁.other _ (by decide), cb, BitVec.toNat_add, BitVec.toNat_add, ha]
    rcases (by omega_using [hb1] : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega_using [hrlt, hD2]
  refine wp_subsC (op2_reg _ _) fun s₃ u₃ c₃ => ?_
  obtain d₂ : s₂.gpr .r2 = D := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
  rw [d₂] at u₃ c₃
  rw [v₂] at c₃
  refine wp_adc (op2_imm (by decide)) fun s₄ u₄ _ => ?_
  -- The quotient bit.
  generalize ht : (if 2 * (N % D.toNat) + b < D.toNat then 0 else 1) = t
  obtain ht1 : t ≤ 1 := by rw [← ht]; split <;> omega_using []
  obtain v₄ : (s₄.gpr .r1).toNat = 2 * P + 2 * (N / D.toNat) + t := by
    rw [u₄.gpr, c₃, u₃.other _ (by decide), u₂.other _ (by decide), BitVec.toNat_add, BitVec.toNat_add, v₁,
      ← ht]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, ite_true, show ¬ D.toNat ≤ 2 * (N % D.toNat) + b by omega_using [hv], decide_false,
        Bool.false_eq_true, ite_false]
      simp; omega_using [hPb, hqlt]
    · simp only [hv, ite_false, show D.toNat ≤ 2 * (N % D.toNat) + b by omega_using [hv], decide_true, ite_true]
      simp; omega_using [hPb, hqlt]
  refine wp_and (op2_imm (by decide)) fun s₅ u₅ => ?_
  obtain v₅ : s₅.gpr .r3 = BitVec.ofNat 32 t := by
    apply BitVec.eq_of_toNat_eq
    rw [u₅.gpr, BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, v₄,
      BitVec.toNat_ofNat]
    omega_using [ht1]
  refine wp_sub (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_and (op2_reg _ _) fun s₇ u₇ => ?_
  refine wp_add (op2_reg _ _) fun s₈ u₈ => hq s₈ ⟨?_, ?_⟩ ?_
  · -- `r1`: the remaining bits above the quotient.
    rw [R'', hP, N', ← res.1, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), v₄, ← ht]
    omega_using []
  · -- `r0`: the remainder.
    obtain d₆ : s₆.gpr .r2 = D := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), d₂]
    rw [N', ← res.2, u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), d₆, v₅,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, ← ht]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, ite_true]
      rw [show BitVec.ofNat 32 0 - 1 = BitVec.allOnes 32 by decide, BitVec.allOnes_and, BitVec.sub_add_cancel,
        v₂]
    · simp only [hv, ite_false]
      rw [show BitVec.ofNat 32 1 - 1 = 0#32 by decide, show (0#32) &&& D = 0#32 by simp, BitVec.add_zero,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, v₂]; omega_using [hv]), v₂]
  · exact (Keep.of_upd u₁ (by simp)).trans ((Keep.of_upd u₂ (by simp)).trans ((Keep.of_upd u₃ (by simp)).trans
      ((Keep.of_upd u₄ (by simp)).trans ((Keep.of_upd u₅ (by simp)).trans ((Keep.of_upd u₆ (by simp)).trans
        ((Keep.of_upd u₇ (by simp)).trans (Keep.of_upd u₈ (by simp))))))))

theorem bits_ok {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31) {n : Nat}
    (hn : n < 2 ^ 32) {is : List Instr} {Q : State → Prop} :
    ∀ k ≤ 32, ∀ s : State, s.gpr .r2 = D → Stage n D.toNat 0 s →
      (∀ t, Stage n D.toNat k t → Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (bits k ++ is)) s Q
  | 0, _, s, _, h, hq => hq s h (Keep.refl s)
  | k + 1, hk, s, hb, h, hq => by
    simp only [bits, List.append_assoc]
    refine bits_ok hD hD2 hn k (by omega_using [hk]) s hb h fun t ht kt => ?_
    refine bit_ok hD hD2 (by rw [kt.other _ (by decide) (by decide) (by decide), hb]) hn (by omega_using [hk]) ht
      fun u hu ku => hq u hu (kt.trans ku)

/-- The division: `r1 := n / D`, `r0 := n mod D`. -/
theorem code_ok {s : State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31)
    (hb : s.gpr .r2 = D) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, (t.gpr .r1).toNat = (s.gpr .r1).toNat / D.toNat →
      (t.gpr .r0).toNat = (s.gpr .r1).toNat % D.toNat → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (code ++ is)) s Q := by
  obtain hn := (s.gpr .r1).isLt
  simp only [code, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine bits_ok hD hD2 hn 32 (Nat.le_refl _) s₁ (by rw [u₁.other _ (by decide), hb]) ⟨?_, ?_⟩
    fun t ⟨hc, ha⟩ kt => ?_
  · rw [u₁.other _ (by decide), Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, Nat.zero_div]; simp
  · rw [u₁.gpr, Nat.div_eq_of_lt hn, Nat.zero_mod]; rfl
  · refine hq t (by rw [hc]; simp [Nat.mod_one]) (by rw [ha]; simp) ((Keep.of_upd u₁ (by simp)).trans kt)

end VG.Proof.Argon2.Arm.Divide

end

end


/-!
# Argon2 on ARMv7: the parameters

`parameters_ok`: the body's first instructions point `r11` to the locals and
store there `4 · lanes` (the divisor), the segment length (by the fixed-time
division), the lane length and its size in bytes (`Prm`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov op2_lsl)
open VG.Impl.Argon2.Arm.Derive (parameters divisorOff segLenOff laneLenOff strideOff argOff)

/-- The parameters in the locals. -/
structure Prm (s₀ s : State) : Prop where
  divisor : lw s₀ s divisorOff = BitVec.ofNat 32 (4 * lanesN s₀)
  segLen : lw s₀ s segLenOff = BitVec.ofNat 32 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 32 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 32 ((prm s₀).laneLen * 1024)

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.keep {s₀ s t : State} (h : Inv s₀ s) (k : Divide.Keep s t) : Inv s₀ t :=
  h.step k.sp (k.other _ (by decide) (by decide) (by decide)) k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

/-- `x << n`, as a number, when it does not overflow. -/
theorem shl_nat {x : BitVec 32} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 32) : (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.addSp .r11 0 :: parameters) ++ is)) (entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, List.cons_append, List.append_assoc]
  refine inv_start fun s₁ i₁ _ _ => ?_
  refine wp_ldarg hp i₁ (i := Impl.Argon2.Arm.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  obtain i₂ := i₁.upd u₂ (by decide)
  refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => ?_
  obtain i₃ := i₂.upd u₃ (by decide)
  obtain e₃ : (s₃.gpr .r2).toNat = 4 * lanesN s₀ := by
    rw [u₃.gpr, u₂.gpr, shl_nat (by have : (arg s₀ 7).toNat < 2 ^ 24 := hL; show (arg s₀ 7).toNat * 4 < _; omega_using [this])]
    show (arg s₀ 7).toNat * 4 = 4 * (arg s₀ 7).toNat
    omega_using []
  refine wp_stloc hp i₃ (d := divisorOff) (by decide) fun s₄ i₄ v₄ _ g₄ _ => ?_
  refine wp_ldarg hp i₄ (i := Impl.Argon2.Arm.Derive.memoryCostArg) (by decide) fun s₅ u₅ => ?_
  obtain i₅ := i₄.upd u₅ (by decide)
  obtain r2₅ : s₅.gpr .r2 = s₃.gpr .r2 := by rw [u₅.other _ (by decide), g₄]
  refine Divide.code_ok (D := s₃.gpr .r2) (by rw [e₃]; omega_using [hL1]) (by rw [e₃]; omega_using [hL]) r2₅ fun s₆ c₆ _ k₆ => ?_
  obtain i₆ := i₅.keep k₆
  rw [u₅.gpr, e₃] at c₆
  obtain c₆' : (s₆.gpr .r1).toNat = (prm s₀).segmentLen := by rw [c₆, hseg]; rfl
  refine wp_stloc hp i₆ (d := segLenOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ _ => ?_
  obtain hll : (prm s₀).laneLen ≤ blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  obtain hsegL : (prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_mov (op2_lsl (by decide)) fun s₈ u₈ => ?_
  obtain i₈ := i₇.upd u₈ (by decide)
  obtain e₈ : (s₈.gpr .r1).toNat = (prm s₀).laneLen := by
    rw [u₈.gpr, g₇, shl_nat (by rw [c₆']; omega), c₆', hlane]; omega_using []
  refine wp_stloc hp i₈ (d := laneLenOff) (by decide) fun s₉ i₉ v₉ o₉ g₉ _ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₀ u₁₀ => ?_
  obtain i₁₀ := i₉.upd u₁₀ (by decide)
  obtain e₁₀ : (s₁₀.gpr .r1).toNat = (prm s₀).laneLen * 1024 := by
    rw [u₁₀.gpr, g₉, shl_nat (by rw [e₈]; omega_using [hsegL]), e₈]
  refine wp_stloc hp i₁₀ (d := strideOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ _ _ => k s₁₁ i₁₁ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), lw_mem u₈.mem,
      o₇ _ (by decide) (by decide), lw_mem k₆.mem, lw_mem u₅.mem, v₄]
    exact BitVec.eq_of_toNat_eq (by rw [e₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hL])])
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), lw_mem u₈.mem, v₇]
    exact BitVec.eq_of_toNat_eq (by rw [c₆', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [c₆'])])
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, v₉]
    exact BitVec.eq_of_toNat_eq (by rw [e₈, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hsegL])])
  · rw [v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hsegL])])

end

end VG.Proof.Argon2.Arm.Derive
