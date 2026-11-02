module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Row
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: a round of the multiplication

`mulRound k i` (`Impl/Weierstrass/RISCV64/GenWide.lean`): the `k + 2` words of
`T` become the `k + 1` words of `T` before plus `a bᵢ` (`mulRound_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- The `n` words of `T`. -/
abbrev tv (k : Nat) (m : Mem) (b : Addr) (n : Nat) : Nat := colsV (fun i => dw m b (T k + 8 * i)) n

/-- The `n` words at `X`. -/
abbrev xv (m : Mem) (X : Addr) (n : Nat) : Nat := colsV (fun i => dw m X (8 * i)) n

theorem colsV_add' (f g : Nat → Nat) : ∀ n, colsV (fun i => f i + g i) n = colsV f n + colsV g n
  | 0 => rfl
  | n + 1 => by simp only [colsV]; rw [colsV_add' f g n, Nat.mul_add]; omega

theorem colsV_mul (f : Nat → Nat) (c : Nat) : ∀ n, colsV (fun i => f i * c) n = colsV f n * c
  | 0 => by simp [colsV]
  | n + 1 => by simp only [colsV]; rw [colsV_mul f c n, Nat.add_mul, Nat.mul_assoc]

theorem colsV_succ (f : Nat → Nat) (n : Nat) : colsV f (n + 1) = colsV f n + (2 ^ 64) ^ n * f n := rfl

/-- What a round needs of the working space and of `a`. -/
structure MulOk (k : Nat) (b A : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  aal : A.toNat % 8 = 0
  ain : ∀ i < k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  adis : ∀ i < k, ∀ j ≤ k + 2,
    Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * j⟩
  k7 : 7 ≤ k
  k32 : k ≤ 30

theorem MulOk.of {k : Nat} {b A : Addr} {s s' : State} (h : MulOk k b A s) (h3 : s'.gpr .a3 = s.gpr .a3)
    (h4 : s'.gpr .t4 = s.gpr .t4) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : MulOk k b A s' :=
  ⟨ctx_of h.ctx h3 hwr, h.nowrap, h4.trans h.a, h.aal, by rw [hrd, hwr]; exact h.ain, h.adis, h.k7, h.k32⟩

theorem T_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) : T k % 8 = 0 ∧ T k + 8 * (k + 2) ≤ 2048 := by
  unfold T; omega

/-- `T` after a round of `a bᵢ`: only `T`'s `k + 2` words written. -/
theorem mulRound_ok {k : Nat} {b A B : Addr} {i : Nat} {s : State} (h : MulOk k b A s)
    (h5 : s.gpr .t5 = B) (hBal : (B + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0) (hi : 8 * i < 2048)
    (hBin : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (mulRound k i)) s fun s' =>
      (∀ r, r ∉ .a4 :: clobS → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s.mem s'.mem ∧
      tv k s'.mem b (k + 2) = tv k s.mem b (k + 1) + xv s.mem A k * dw s.mem B (8 * i) := by
  obtain ⟨t8, ttop⟩ := T_facts k (by have := h.k7; omega) h.k32
  have hb := h.nowrap
  unfold mulRound
  refine wp_ld hi (by rw [h5]) hBal hBin fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  show WP isa (.block (macRow k .t4 0 0 k ++ [.load .d .a7 .a3 (T k + 8 * k), .add .t0 .a7 .a5,
    .sltu .t3 .t0 .a5, .store .d .t0 .a3 (T k + 8 * k), .store .d .t3 .a3 (T k + 8 * (k + 1))])) s2 _
  -- The row.
  have hR : RowOk k b A .t4 0 0 k s2 :=
    { ctx := ctx_of h.ctx (by rw [u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u2.wr, u1.wr])
      nowrap := hb
      hx := by rw [u2.other _ (by decide), u1.other _ (by decide), h.a]
      hxb := by decide
      hxo := fun i hi => by omega
      xal := fun i _ => al8 h.aal (by omega)
      xin := fun i hi => by rw [u2.rd, u2.wr, u1.rd, u1.wr, Nat.zero_add, Nat.add_zero]; exact h.ain i hi
      xdis := fun i hi j hj => by rw [Nat.zero_add, Nat.add_zero]; exact h.adis i hi j (by omega)
      top := by omega
      t8 := t8 }
  refine WP.block_append (WP.mono (row_ok hR k (Nat.le_refl _)) fun s3 h3 => ?_)
  have hc3 : Ctx b s3 := ctx_of hR.ctx (h3.gpr _ (by decide)) h3.wr
  refine ld_ok hc3 (by omega) (by omega) fun s4 u4 => wp_add fun s5 u5 => wp_sltu fun s6 u6 => ?_
  have hc6 : Ctx b s6 := ctx_of hc3 (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide)])
    (by rw [u6.wr, u5.wr, u4.wr])
  refine sd_ok hc6 (by omega) (by omega) fun s7 u7 => ?_
  have hc7 : Ctx b s7 := ctx_of hc6 (by rw [u7.gpr]) u7.wr
  refine sd_ok hc7 (by omega) (by omega) fun s8 u8 => WP.block_nil ?_
  -- Registers.
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have g2 : ∀ r, r ∉ .a4 :: clobS → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other r hr.2.2.2.2.1, u1.other r hr.1]
  have g6 : ∀ r, r ∉ .a4 :: clobS → s6.gpr r = s3.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u6.other r hr.2.2.2.1, u5.other r hr.2.1, u4.other r hr.2.2.2.2.2.2]
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have hm8 : s8.mem = (s3.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * k)) (s6.gpr .t0)).writeW
      (b + BitVec.ofNat 64 (T k + 8 * (k + 1))) (s6.gpr .t3) := by
    rw [u8.mem, u7.mem, u7.gpr, m6]
  refine ⟨fun r hr => by
      rw [u8.gpr, u7.gpr, g6 r hr, h3.gpr r (fun h' => hr (List.mem_cons_of_mem _ h')), g2 r hr],
    by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, h3.rd, u2.rd, u1.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, h3.wr, u2.wr, u1.wr],
    by rw [u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, h3.sp, u2.sp, u1.sp], ?_, ?_⟩
  · rw [hm8, ← m2]
    refine ((h3.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · -- The words of the row, then the top two.
    have hv := h3.val
    have hTk : dw s3.mem b (T k + 8 * k) = dw s2.mem b (T k + 8 * k) :=
      dw_frame h3.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
    have a7 : (s4.gpr .a7).toNat = dw s2.mem b (T k + 8 * k) := by rw [u4.gpr, ← hTk]; rfl
    have a5 : s4.gpr .a5 = s3.gpr .a5 := u4.other _ (by decide)
    have e6 := carry (s4.gpr .a7) (s4.gpr .a5)
    have t0 : s6.gpr .t0 = s4.gpr .a7 + s4.gpr .a5 := by rw [u6.other _ (by decide), u5.gpr]
    have t3 : s6.gpr .t3 = if s4.gpr .a7 + s4.gpr .a5 < s4.gpr .a5 then 1 else 0 := by
      rw [u6.gpr, u5.gpr, u5.other _ (by decide)]
    have hlow : tv k s8.mem b k = tv k s3.mem b k :=
      colsV_congr fun j hj => by
        rw [hm8, dw_write_other _ _ _ (by omega) (by omega) (by omega),
          dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have hk0 : dw s8.mem b (T k + 8 * k) = (s6.gpr .t0).toNat := by
      rw [hm8, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self]
    have hk1 : dw s8.mem b (T k + 8 * (k + 1)) = (s6.gpr .t3).toNat := by rw [hm8, dw_write_self]
    have hrow : colsV (fun i => dw s2.mem b (T k + 8 * (i + 0)) + dw s2.mem A (0 + 8 * (i + 0)) *
        (s2.gpr .a4).toNat) k = tv k s.mem b k + xv s.mem A k * dw s.mem B (8 * i) := by
      rw [colsV_add', colsV_mul, m2]
      simp only [Nat.add_zero, Nat.zero_add]
      rw [u2.other _ (by decide), u1.gpr]; rfl
    have a50 : (s2.gpr .a5).toNat = 0 := by rw [u2.gpr]; rfl
    rw [hrow, a50, Nat.add_zero] at hv
    show tv k s8.mem b k + (2 ^ 64) ^ k * dw s8.mem b (T k + 8 * k) +
        (2 ^ 64) ^ (k + 1) * dw s8.mem b (T k + 8 * (k + 1)) =
      tv k s.mem b k + (2 ^ 64) ^ k * dw s.mem b (T k + 8 * k) + xv s.mem A k * dw s.mem B (8 * i)
    rw [hlow, hk0, hk1, t0, t3, show (2 ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 from Nat.pow_succ .., ← m2]
    rw [m2] at a7 ⊢
    rw [a5] at e6
    rw [← m2] at hv
    generalize (2 ^ 64) ^ k = E at *
    have key : E * (s4.gpr .a7 + s3.gpr .a5).toNat +
        E * 2 ^ 64 * (if s4.gpr .a7 + s3.gpr .a5 < s3.gpr .a5 then (1 : BitVec 64) else 0).toNat =
        E * (s4.gpr .a7).toNat + E * (s3.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e6]
    rw [m2] at hv
    change tv k s3.mem b k + E * (s3.gpr .a5).toNat = _ at hv
    rw [a5, ← a7]
    omega

end VG.Proof.Weierstrass.RISCV64.GenWide
