module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Round
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: a round of the reduction

`redRound k` (`Impl/Weierstrass/RISCV64/GenWide.lean`): for the quotient word
`q = T₀ m' mod 2⁶⁴`, `T + q m` is a multiple of `2⁶⁴`, and the `k + 1` words of
`T` become `(T + q m) / 2⁶⁴` (`redRound_ok`), but for a carry out of the top
word, which the caller's bounds rule out.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- `T₀ + q m₀ = 2⁶⁴ ([T₀ ≠ 0] + ⌊q m₀ / 2⁶⁴⌋)` for `q = T₀ m' mod 2⁶⁴`, as `m₀ m' ≡ -1`. -/
theorem quot_nat {t m' n0 : Nat} (ht : t < 2 ^ 64) (hinv : n0 * m' % 2 ^ 64 = 2 ^ 64 - 1) :
    t * m' % 2 ^ 64 * n0 % 2 ^ 64 + t = if t = 0 then 0 else 2 ^ 64 := by
  have e : t * m' % 2 ^ 64 * n0 % 2 ^ 64 = t * (2 ^ 64 - 1) % 2 ^ 64 := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m' n0, hinv, Nat.mod_mul_mod]
  rw [e]
  by_cases h0 : t = 0
  · subst h0; simp
  · simp only [h0, ↓reduceIte]
    have : t * (2 ^ 64 - 1) = (2 ^ 64 - t) + 2 ^ 64 * (t - 1) := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_sub, Nat.mul_one]
      have : 2 ^ 64 ≤ t * 2 ^ 64 := Nat.le_mul_of_pos_left _ (by omega)
      rw [Nat.mul_comm (2 ^ 64) t]
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A number's words from the second. -/
theorem colsV_shift (f : Nat → Nat) : ∀ n, colsV f (n + 1) = f 0 + 2 ^ 64 * colsV (fun i => f (i + 1)) n
  | 0 => by simp [colsV]
  | n + 1 => by
    have e : ((2 : Nat) ^ 64) ^ (n + 1) = 2 ^ 64 * (2 ^ 64) ^ n := Nat.pow_succ'
    rw [colsV_succ, colsV_shift f n, colsV_succ, Nat.mul_add, e, Nat.mul_assoc]
    omega

theorem wp_mulhu {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mulhu d n m :: is)) s Q :=
  WP.cons exec_mulhu (k _ (Upd.write _ _ _))

/-- The modulus's `k` words at `N`. -/
abbrev nv (k : Nat) (m : Mem) (b : Addr) : Nat := colsV (fun i => dw m b (N k + 8 * i)) k

/-- What a round of the reduction needs. -/
structure RedOk (k : Nat) (b : Addr) (m' : Nat) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  t6 : s.gpr .t6 = BitVec.ofNat 64 m'
  m'lt : m' < 2 ^ 64
  inv : dw s.mem b (N k) * m' % 2 ^ 64 = 2 ^ 64 - 1
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem N_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) :
    N k = T k + 8 * (k + 2) ∧ N k % 8 = 0 ∧ N k + 8 * k ≤ 2048 := by
  unfold N T; omega

theorem red_alg {E R C C0 Tc Nc q Tw0 Nw0 Tj1 Tj2 a b c w : Nat}
    (hrow : R + E * C = Tc + Nc * q + C0) (h0 : 2 ^ 64 * C0 = Tw0 + q * Nw0)
    (h1 : a + 2 ^ 64 * c = Tj1 + C) (h2 : b + 2 ^ 64 * w = Tj2 + c) :
    2 ^ 64 * (R + E * a + E * (2 ^ 64 * b) + E * (2 ^ 64 * (2 ^ 64 * w))) =
      Tw0 + 2 ^ 64 * (Tc + E * Tj1 + E * (2 ^ 64 * Tj2)) + q * (Nw0 + 2 ^ 64 * Nc) := by
  have m1 := congrArg (E * ·) h1
  have m2 := congrArg (fun x => E * (2 ^ 64 * x)) h2
  simp only [Nat.mul_add] at m1 m2
  rw [show q * (Nw0 + 2 ^ 64 * Nc) = q * Nw0 + 2 ^ 64 * (q * Nc) by rw [Nat.mul_add, Nat.mul_left_comm]]
  rw [Nat.mul_comm Nc q] at hrow
  omega

/-- The carry word of the quotient's first product: `2⁶⁴ C₀ = T₀ + q m₀`. -/
theorem c0_nat {t m' n0 : Nat} (ht : t < 2 ^ 64) (hn : n0 < 2 ^ 64) (hinv : n0 * m' % 2 ^ 64 = 2 ^ 64 - 1)
    {hi c : Nat} (hp : t * m' % 2 ^ 64 * n0 % 2 ^ 64 + 2 ^ 64 * hi = t * m' % 2 ^ 64 * n0)
    (hc : c = if t = 0 then 0 else 1) :
    2 ^ 64 * (hi + c) = t + t * m' % 2 ^ 64 * n0 ∧ hi + c < 2 ^ 64 := by
  have hq := quot_nat ht hinv
  have hql : t * m' % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hxy : t * m' % 2 ^ 64 * n0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  subst hc
  generalize t * m' % 2 ^ 64 * n0 = P at *
  by_cases h0 : t = 0 <;> simp only [h0, ↓reduceIte] at hq ⊢ <;> omega

theorem sltu0_toNat (x : BitVec 64) :
    (if BitVec.ofNat 64 0 < x then (1 : BitVec 64) else 0).toNat = if x.toNat = 0 then 0 else 1 := by
  by_cases h : x.toNat = 0
  · have : ¬ BitVec.ofNat 64 0 < x := by rw [BitVec.lt_def]; simp [h]
    simp only [this, h, ↓reduceIte]; rfl
  · have : BitVec.ofNat 64 0 < x := by rw [BitVec.lt_def]; simp; omega
    simp only [this, h, ↓reduceIte]; rfl

/-- A round of the reduction. -/
theorem redRound_ok {k : Nat} {b : Addr} {m' : Nat} {s : State} (h : RedOk k b m' s) :
    WP isa (.block (redRound k)) s fun s' =>
      (∀ r, r ∉ .a4 :: clobS → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 1)⟩] s.mem s'.mem ∧
      ∃ w, 2 ^ 64 * (tv k s'.mem b (k + 1) + (2 ^ 64) ^ (k + 1) * w) =
        tv k s.mem b (k + 2) + dw s.mem b (T k) * m' % 2 ^ 64 * nv k s.mem b := by
  obtain ⟨t8, ttop⟩ := T_facts k (by have := h.k7; omega) h.k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by have := h.k7; omega) h.k30
  have hb := h.nowrap
  have hc := h.ctx
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h.k7; omega⟩
  unfold redRound
  simp only [Nat.add_sub_cancel]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => wp_mul fun s2 u2 => ?_
  refine ld_ok (ctx_of hc (by rw [u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u2.wr, u1.wr]))
    (by omega) (by omega) fun s3 u3 => wp_mulhu fun s4 u4 => wp_li (by decide) fun s5 u5 =>
      wp_sltu fun s6 u6 => wp_add fun s7 u7 => ?_
  show WP isa (.block (macRow (j + 1) .a3 (N (j + 1)) 1 j ++ [.load .d .a7 .a3 (T (j + 1) + 8 * (j + 1)),
    .add .t0 .a7 .a5, .sltu .t3 .t0 .a5, .store .d .t0 .a3 (T (j + 1) + 8 * j),
    .load .d .a7 .a3 (T (j + 1) + 8 * (j + 1 + 1)), .add .a7 .a7 .t3, .store .d .a7 .a3 (T (j + 1) + 8 * (j + 1))])) s7 _
  -- What the quotient block leaves.
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have g7 : ∀ r, r ∉ .a4 :: clobS → s7.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u7.other r hr.2.2.2.2.1, u6.other r hr.2.2.2.1, u5.other r hr.2.2.2.1, u4.other r hr.2.2.2.2.1,
      u3.other r hr.2.2.2.2.2.1, u2.other r hr.1, u1.other r hr.2.2.2.2.2.2]
  have hc7 : Ctx b s7 := ctx_of hc (g7 _ (by decide)) (by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  have hT0 : (s1.gpr .a7).toNat = dw s.mem b (T (j + 1)) := by rw [u1.gpr]; rfl
  have hq : (s7.gpr .a4).toNat = dw s.mem b (T (j + 1)) * m' % 2 ^ 64 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, BitVec.toNat_mul, hT0, u1.other _ (by decide), h.t6,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.m'lt]
  have hn0 : (s3.gpr .a6).toNat = dw s.mem b (N (j + 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, show N (j + 1) = N (j + 1) + 8 * 0 by rfl]; rfl
  have hC0 : 2 ^ 64 * (s7.gpr .a5).toNat = dw s.mem b (T (j + 1)) +
      dw s.mem b (T (j + 1)) * m' % 2 ^ 64 * dw s.mem b (N (j + 1)) := by
    have hp := mul_words (s4.gpr .a4) (s3.gpr .a6)
    have e4a : s4.gpr .a4 = s3.gpr .a4 := u4.other _ (by decide)
    have e3a : (s3.gpr .a4).toNat = dw s.mem b (T (j + 1)) * m' % 2 ^ 64 := by
      rw [u3.other _ (by decide), u2.gpr, BitVec.toNat_mul, hT0, u1.other _ (by decide), h.t6,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.m'lt]
    have e4 : s4.gpr .a5 = BitVec.ofNat 64 ((s3.gpr .a4).toNat * (s3.gpr .a6).toNat / 2 ^ 64) := by
      rw [u4.gpr]
    have e6 : (s6.gpr .t3).toNat = if dw s.mem b (T (j + 1)) = 0 then 0 else 1 := by
      rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.other _ (by decide),
        u3.other _ (by decide), u2.other _ (by decide), sltu0_toNat, hT0]
    rw [e4a, e3a, hn0] at hp
    rw [BitVec.toNat_mul, e3a, hn0] at hp
    obtain ⟨c1, c2⟩ := c0_nat (dw_lt _ _ _) (dw_lt _ _ _) h.inv
      hp e6
    rw [u7.gpr, BitVec.toNat_add, u6.other _ (by decide), u5.other _ (by decide), e4, e3a, hn0,
      Nat.mod_eq_of_lt c2]
    exact c1
  -- The row.
  have hR : RowOk (j + 1) b b .a3 (N (j + 1)) 1 j s7 :=
    { ctx := hc7
      nowrap := hb
      hx := hc7.a3
      hxb := by decide
      hxo := fun i hi => by omega
      xal := fun i _ => al8 hc7.al (by omega)
      xin := fun i hi => hc7.inR (by omega)
      xdis := fun i hi j' hj' => Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
      top := by omega
      t8 := t8 }
  refine WP.block_append (WP.mono (row_ok hR j (Nat.le_refl _)) fun s8 h8 => ?_)
  have hc8 : Ctx b s8 := ctx_of hc7 (h8.gpr _ (by decide)) h8.wr
  refine ld_ok hc8 (by omega) (by omega) fun s9 u9 => wp_add fun s10 u10 => wp_sltu fun s11 u11 => ?_
  have hc11 : Ctx b s11 := ctx_of hc8 (by rw [u11.other _ (by decide), u10.other _ (by decide),
    u9.other _ (by decide)]) (by rw [u11.wr, u10.wr, u9.wr])
  refine sd_ok hc11 (by omega) (by omega) fun s12 u12 => ?_
  have hc12 : Ctx b s12 := ctx_of hc11 (by rw [u12.gpr]) u12.wr
  refine ld_ok hc12 (by omega) (by omega) fun s13 u13 => wp_add fun s14 u14 => ?_
  have hc14 : Ctx b s14 := ctx_of hc12 (by rw [u14.other _ (by decide), u13.other _ (by decide)])
    (by rw [u14.wr, u13.wr])
  refine sd_ok hc14 (by omega) (by omega) fun s15 u15 => WP.block_nil ?_
  -- Memory.
  have m11 : s11.mem = s8.mem := by rw [u11.mem, u10.mem, u9.mem]
  have m12 : s12.mem = s8.mem.writeW (b + BitVec.ofNat 64 (T (j + 1) + 8 * j)) (s11.gpr .t0) := by
    rw [u12.mem, m11]
  have m15 : s15.mem = s12.mem.writeW (b + BitVec.ofNat 64 (T (j + 1) + 8 * (j + 1))) (s14.gpr .a7) := by
    rw [u15.mem, u14.mem, u13.mem]
  -- Words of `T` the tail reads, as they were.
  have fr : ∀ d, T (j + 1) + 8 * j ≤ d → d + 8 ≤ 2048 → dw s8.mem b d = dw s.mem b d := fun d hd hd' => by
    rw [dw_frame h8.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (.inr hd) (by omega) (by omega), m7]
  have hw1 : (s9.gpr .a7).toNat = dw s.mem b (T (j + 1) + 8 * (j + 1)) := by
    rw [u9.gpr, ← fr _ (by omega) (by omega)]; rfl
  have hw2 : (s13.gpr .a7).toNat = dw s.mem b (T (j + 1) + 8 * (j + 1 + 1)) := by
    rw [u13.gpr, m12, show dw s.mem b (T (j + 1) + 8 * (j + 1 + 1)) = dw s8.mem b (T (j + 1) + 8 * (j + 1 + 1))
      from (fr _ (by omega) (by omega)).symm]
    show dw _ b _ = _
    rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]
  refine ⟨fun r hr => ?_, by rw [u15.rd, u14.rd, u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, h8.rd, u7.rd, u6.rd, u5.rd,
      u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u15.wr, u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, h8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr],
    by rw [u15.sp, u14.sp, u13.sp, u12.sp, u11.sp, u10.sp, u9.sp, h8.sp, u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp,
      u1.sp], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u15.gpr, u14.other r hr.2.2.2.2.2.2, u13.other r hr.2.2.2.2.2.2, u12.gpr, u11.other r hr.2.2.2.1,
      u10.other r hr.2.1, u9.other r hr.2.2.2.2.2.2, h8.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1,
        hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]), g7 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
        hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2])]
  · rw [m15, m12, ← m7]
    refine (((h8.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · -- The value.
    have hv := h8.val
    rw [colsV_add', colsV_mul, m7, hq] at hv
    have hlow : colsV (fun i => dw s15.mem b (T (j + 1) + 8 * i)) j = colsV (fun i => dw s8.mem b (T (j + 1) + 8 * i)) j :=
      colsV_congr fun i hi => by
        rw [m15, m12, dw_write_other _ _ _ (by omega) (by omega) (by omega),
          dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have hj0 : dw s15.mem b (T (j + 1) + 8 * j) = (s11.gpr .t0).toNat := by
      rw [m15, m12, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self]
    have hj1 : dw s15.mem b (T (j + 1) + 8 * (j + 1)) = (s14.gpr .a7).toNat := by rw [m15, dw_write_self]
    -- The tail's sums.
    have e10 := carry (s9.gpr .a7) (s9.gpr .a5)
    have t0v : s11.gpr .t0 = s9.gpr .a7 + s9.gpr .a5 := by rw [u11.other _ (by decide), u10.gpr]
    have t3v : s11.gpr .t3 = if s9.gpr .a7 + s9.gpr .a5 < s9.gpr .a5 then 1 else 0 := by
      rw [u11.gpr, u10.gpr, u10.other _ (by decide)]
    have a5v : s9.gpr .a5 = s8.gpr .a5 := u9.other _ (by decide)
    have a7v : s14.gpr .a7 = s13.gpr .a7 + s11.gpr .t3 := by
      rw [u14.gpr, u13.other .t3 (by decide), u12.gpr]
    have h1 : (s11.gpr .t0).toNat + 2 ^ 64 * (s11.gpr .t3).toNat =
        dw s.mem b (T (j + 1) + 8 * (j + 1)) + (s8.gpr .a5).toNat := by
      rw [t0v, t3v, e10, hw1, a5v]
    have h2 : (s14.gpr .a7).toNat + 2 ^ 64 * (((s13.gpr .a7).toNat + (s11.gpr .t3).toNat) / 2 ^ 64) =
        dw s.mem b (T (j + 1) + 8 * (j + 1 + 1)) + (s11.gpr .t3).toNat := by
      rw [a7v, BitVec.toNat_add, Nat.mod_add_div, hw2]
    refine ⟨((s13.gpr .a7).toNat + (s11.gpr .t3).toNat) / 2 ^ 64, ?_⟩
    have alg := red_alg hv hC0 h1 h2
    show 2 ^ 64 * (colsV (fun i => dw s15.mem b (T (j + 1) + 8 * i)) (j + 1 + 1) + _) = _
    rw [colsV_succ, colsV_succ, hlow, hj0, hj1]
    simp only [nv, tv]
    rw [colsV_shift (fun i => dw s.mem b (T (j + 1) + 8 * i)) (j + 1 + 1), colsV_succ, colsV_succ,
      colsV_shift (fun i => dw s.mem b (N (j + 1) + 8 * i)) j]
    have p1 : ((2 : Nat) ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 := Nat.pow_succ ..
    have p2 : ((2 : Nat) ^ 64) ^ (j + 1 + 1) = (2 ^ 64) ^ j * (2 ^ 64 * 2 ^ 64) := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    simp only [Nat.mul_zero, Nat.add_zero] at alg ⊢
    rw [p1, p2]
    simp only [Nat.mul_assoc] at alg ⊢
    exact alg


end VG.Proof.Weierstrass.RISCV64.GenWide
