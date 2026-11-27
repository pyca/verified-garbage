module

-- separate module: its proofs build in parallel with the field's code literal, which its importer's
-- constant time evaluates
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The doubling of a square's products modulo a wide modulus on RISC-V

The square `a²` as the rows of the products `aᵢ aⱼ`, `i < j`, doubled, plus
the squares `aᵢ²` (`rows_sum`, `sq_sum`), and the code that doubles those
rows' sum at `SQ` and adds the squares (`dword_ok`, `diag_ok`, `diags_ok`),
which `Impl/Weierstrass/RISCV64/Wide8.lean` uses; and `fnWith k fast core`'s
contract by register (`fnWith_rv`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-! ## The square's numbers -/

theorem colsV_split (f : Nat → Nat) (p : Nat) :
    ∀ n, colsV f (p + n) = colsV f p + (2 ^ 64) ^ p * colsV (fun j => f (p + j)) n
  | 0 => by simp [colsV]
  | n + 1 => by
    rw [← Nat.add_assoc, colsV_succ, colsV_split f p n, colsV_succ, Nat.mul_add, Nat.pow_add, Nat.mul_assoc]
    omega_using []

/-- A sum of `n` terms. -/
def sumN (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumN g n + g n

/-- Row `i` of the square's products: `aᵢ 2^(64 (2 i + 1)) a[i + 1 …]`. -/
def rowTerm (a : Nat → Nat) (k i : Nat) : Nat :=
  a i * (2 ^ 64) ^ (2 * i + 1) * colsV (fun j => a (i + 1 + j)) (k - 1 - i)

theorem sumN_add (g h : Nat → Nat) : ∀ n, sumN (fun i => g i + h i) n = sumN g n + sumN h n
  | 0 => rfl
  | n + 1 => by simp only [sumN]; rw [sumN_add g h n]; omega_using []

theorem sumN_congr {g h : Nat → Nat} : ∀ {n}, (∀ i < n, g i = h i) → sumN g n = sumN h n
  | 0, _ => rfl
  | n + 1, e => by simp only [sumN]; rw [sumN_congr fun i hi => e i (by omega_using [hi]), e n (by omega_using [])]

theorem sumN_cols (a : Nat → Nat) (c : Nat) : ∀ n, sumN (fun i => a i * (2 ^ 64) ^ i * c) n = colsV a n * c
  | 0 => by simp [sumN, colsV]
  | n + 1 => by simp only [sumN]; rw [sumN_cols a c n, colsV_succ]; grind

theorem rows_sum (a : Nat → Nat) :
    ∀ k, sumN (rowTerm a k) k = sumN (fun j => a j * (2 ^ 64) ^ j * colsV a j) k
  | 0 => rfl
  | k + 1 => by
    obtain h : ∀ i < k, rowTerm a (k + 1) i = rowTerm a k i + a i * (2 ^ 64) ^ i * (colsV a 0 + a k * (2 ^ 64) ^ k) :=
      fun i hi => by
        unfold rowTerm
        rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega_using [hi], colsV_succ, show i + 1 + (k - 1 - i) = k by omega_using [hi]]
        obtain e : ((2 : Nat) ^ 64) ^ (2 * i + 1) * (2 ^ 64) ^ (k - 1 - i) = (2 ^ 64) ^ i * (2 ^ 64) ^ k := by
          rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [hi]
        simp only [colsV, Nat.zero_add]
        generalize colsV (fun j => a (i + 1 + j)) (k - 1 - i) = C
        generalize ((2 : Nat) ^ 64) ^ (2 * i + 1) = X at e
        generalize ((2 : Nat) ^ 64) ^ (k - 1 - i) = Y at e
        generalize ((2 : Nat) ^ 64) ^ i = U at e
        generalize ((2 : Nat) ^ 64) ^ k = V at e
        calc a i * X * (C + Y * a k) = a i * X * C + a i * (X * Y) * a k := by grind
          _ = _ := by rw [e]; grind
    obtain hk : rowTerm a (k + 1) k = 0 := by simp [rowTerm, colsV]
    show sumN (rowTerm a (k + 1)) k + rowTerm a (k + 1) k = sumN _ k + _
    rw [hk, Nat.add_zero, sumN_congr h, sumN_add, rows_sum a k, sumN_cols]
    simp only [colsV, Nat.zero_add]
    grind

/-- The square as its rows, doubled, and its squares. -/
theorem sq_sum (a : Nat → Nat) :
    ∀ k, colsV a k * colsV a k =
      sumN (fun i => a i * a i * (2 ^ 64) ^ (2 * i)) k + 2 * sumN (fun j => a j * (2 ^ 64) ^ j * colsV a j) k
  | 0 => by simp [colsV, sumN]
  | k + 1 => by
    simp only [sumN]
    obtain ih := sq_sum a k
    rw [colsV_succ, show 2 * k = k + k by omega_using [], Nat.pow_add]
    generalize sumN (fun i => a i * a i * (2 ^ 64) ^ (2 * i)) k = D at ih ⊢
    generalize sumN (fun j => a j * (2 ^ 64) ^ j * colsV a j) k = X at ih ⊢
    generalize colsV a k = A at ih ⊢
    generalize ((2 : Nat) ^ 64) ^ k = E
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, ih]
    grind

/-! ## The square's product -/

theorem sq_facts (k : Nat) (h₁ : 7 ≤ k) (h : k ≤ 30) :
    SQ k % 8 = 0 ∧ SQ k + 8 * (2 * k) ≤ 2048 ∧ N k + 8 * k ≤ SQ k ∧ T k + 64 * k = 2048 ∧ T k + 8 * (k + 2) ≤ N k := by
  unfold SQ SO SB SA N T; omega_using [h₁, h]

/-- The square's product's words. -/
abbrev PR (k : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (SQ k), 8 * (2 * k)⟩

/-- What the square needs of the working space and of `a`. -/
structure SqOk (k : Nat) (b A : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  aal : A.toNat % 8 = 0
  ain : ∀ i < k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  adis : ∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k b)
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem SqOk.of {k : Nat} {b A : Addr} {s s' : State} (h : SqOk k b A s) (h3 : s'.gpr .a3 = s.gpr .a3)
    (h4 : s'.gpr .t4 = s.gpr .t4) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SqOk k b A s' :=
  ⟨ctx_of h.ctx h3 hwr, h.nowrap, h4.trans h.a, h.aal, by rw [hrd, hwr]; exact h.ain, h.adis, h.k7, h.k30⟩

/-- A part of the own working space within it. -/
theorem ownA_sub {k : Nat} (b : Addr) {d n : Nat} (hd : T k ≤ d) (hn : d + n ≤ T k + 64 * k) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (ownA k b) :=
  Offset.sub b hd hn

/-- The `n` words of `P` from word `j`. -/
abbrev pv (k : Nat) (m : Mem) (b : Addr) (j n : Nat) : Nat := colsV (fun i => dw m b (SQ k + 8 * (j + i))) n

/-- `a`'s words through a frame of the own working space. -/
theorem dwA_frame {k : Nat} {b A : Addr} {m m' : Mem} (hf : Frame [PR k b] m m') (hk : 7 ≤ k) (hk' : k ≤ 30)
    (hdis : ∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k b)) {i : Nat}
    (hi : i < k) : dw m' A (8 * i) = dw m A (8 * i) := by
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k hk hk'
  exact dw_frame hf fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact disj_sub (hdis i hi) (ownA_sub b (by omega_using [nq, tn]) (by omega_using [qtop, tq]))

/-! ## The doubling and the squares -/

theorem dbl_nat {W B T1 bi : Nat} (hW : W < 2 ^ 64) (hB : B = W / 2 ^ 63) (hbi : bi ≤ 1)
    (hT : T1 = (W * 2 % 2 ^ 64 + bi) % 2 ^ 64) : T1 + 2 ^ 64 * B = 2 * W + bi ∧ B ≤ 1 := by
  omega_using [hW, hB, hbi, hT]

/-- Word `j` of `P` doubled with the bit `bi`, plus `x` and the carry `a5`. -/
theorem dword_ok {k : Nat} {b : Addr} {s : State} (hc : Ctx b s) (hk : 7 ≤ k) (hk' : k ≤ 30) {j : Nat}
    (hj : j < 2 * k) {x bi bo : Reg} (hx7 : x ≠ .a7) (hxo : x ≠ bo)
    (hi7 : bi ≠ .a7) (hio : bi ≠ bo) (ho7 : bo ≠ .a7) (ho6 : bo ≠ .a6) (ho5 : bo ≠ .a5) (ho3 : bo ≠ .a3)
    (hbi : (s.gpr bi).toNat ≤ 1) (hc5 : (s.gpr .a5).toNat ≤ 1) :
    WP isa (.block (dword k j x bi bo)) s fun s' =>
      dw s'.mem b (SQ k + 8 * j) + 2 ^ 64 * (s'.gpr .a5).toNat + 2 ^ 64 * (s'.gpr bo).toNat =
        2 * dw s.mem b (SQ k + 8 * j) + (s.gpr bi).toNat + (s.gpr x).toNat + (s.gpr .a5).toNat ∧
      (s'.gpr .a5).toNat ≤ 1 ∧ (s'.gpr bo).toNat ≤ 1 ∧
      (∀ r, r ∉ [.a7, .a6, .a5, bo] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (SQ k + 8 * j), 8⟩] s.mem s'.mem := by
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k hk hk'
  unfold dword
  refine ld_ok hc (by omega_using [hj, qtop]) (by omega_using [q8]) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 => ?_
  refine wp_add fun s4 u4 => wp_add fun s5 u5 => wp_sltu fun s6 u6 => wp_add fun s7 u7 => wp_sltu fun s8 u8 =>
    wp_add fun s9 u9 => ?_
  obtain hc9 : Ctx b s9 := ctx_of hc (by
      rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
        u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
        u2.other _ (Ne.symm ho3), u1.other _ (by decide)])
    (by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine sd_ok hc9 (by omega_using [hj, qtop]) (by omega_using [q8]) fun s10 u10 => WP.block_nil ?_
  -- What each step read.
  obtain w1 : (s1.gpr .a7).toNat = dw s.mem b (SQ k + 8 * j) := by rw [u1.gpr]; rfl
  obtain a7_2 : s2.gpr .a7 = s1.gpr .a7 := u2.other _ (Ne.symm ho7)
  obtain bi3 : s3.gpr bi = s.gpr bi := by rw [u3.other _ hi7, u2.other _ hio, u1.other _ hi7]
  obtain x4 : s4.gpr x = s.gpr x := by rw [u4.other _ hx7, u3.other _ hx7, u2.other _ hxo, u1.other _ hx7]
  obtain x5 : s5.gpr x = s.gpr x := by rw [u5.other _ hx7, x4]
  obtain a5_6 : s6.gpr .a5 = s.gpr .a5 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (Ne.symm ho5), u1.other _ (by decide)]
  obtain bo9 : s9.gpr bo = s2.gpr bo := by
    rw [u9.other _ ho5, u8.other _ ho5, u7.other _ ho7, u6.other _ ho6, u5.other _ ho7, u4.other _ ho7,
      u3.other _ ho7]
  -- The numbers.
  obtain hB : (s9.gpr bo).toNat = dw s.mem b (SQ k + 8 * j) / 2 ^ 63 := by
    rw [bo9, u2.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, w1]
  obtain hT1 : (s4.gpr .a7).toNat = (dw s.mem b (SQ k + 8 * j) * 2 % 2 ^ 64 + (s.gpr bi).toNat) % 2 ^ 64 := by
    rw [u4.gpr, BitVec.toNat_add, u3.gpr, bi3, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, a7_2, w1, Nat.pow_one]
  obtain c1e : s6.gpr .a6 = if s4.gpr .a7 + s4.gpr x < s4.gpr x then 1 else 0 := by
    rw [u6.gpr, u5.gpr, u5.other _ hx7]
  obtain s6a7 : s6.gpr .a7 = s4.gpr .a7 + s4.gpr x := by rw [u6.other _ (by decide), u5.gpr]
  obtain c2e : s8.gpr .a5 = if s6.gpr .a7 + s6.gpr .a5 < s6.gpr .a5 then 1 else 0 := by
    rw [u8.gpr, u7.gpr, u7.other .a5 (by decide)]
  obtain a6_8 : s8.gpr .a6 = s6.gpr .a6 := by rw [u8.other _ (by decide), u7.other _ (by decide)]
  obtain t3 : s9.gpr .a7 = s6.gpr .a7 + s6.gpr .a5 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr]
  obtain m9 : s9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hm : s10.mem = s.mem.writeW (b + BitVec.ofNat 64 (SQ k + 8 * j)) (s9.gpr .a7) := by rw [u10.mem, m9]
  obtain e1 := carry (s4.gpr .a7) (s4.gpr x)
  obtain e2 := carry (s6.gpr .a7) (s6.gpr .a5)
  obtain l1 := carry_le (s4.gpr .a7 + s4.gpr x < s4.gpr x)
  obtain l2 := carry_le (s6.gpr .a7 + s6.gpr .a5 < s6.gpr .a5)
  rw [← c1e] at e1 l1
  rw [← c2e] at e2 l2
  rw [s6a7] at e2
  obtain h5 : (s9.gpr .a5).toNat = (s8.gpr .a5).toNat + (s6.gpr .a6).toNat := by
    rw [u9.gpr, BitVec.toNat_add, a6_8, Nat.mod_eq_of_lt (by omega_using [e1, e2])]
  obtain hw := dw_lt s.mem b (SQ k + 8 * j)
  obtain hx := (s.gpr x).isLt
  obtain ⟨d1, d2⟩ := dbl_nat (B := (s9.gpr bo).toNat) hw hB hbi hT1
  have g10 : s10.gpr = s9.gpr := u10.gpr
  rw [x4] at e1
  rw [a5_6, x4] at e2
  obtain cc := (s4.gpr .a7 + s.gpr x).isLt
  refine ⟨?_, ?_, by rw [g10]; omega_using [d2], fun r hr => ?_, by rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr],
    by rw [u10.sp, u9.sp, u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp], ?_⟩
  · rw [g10, hm, dw_write_self, t3, h5, s6a7, a5_6, x4]
    omega_using [hbi, hc5, w1, bo9, hB, hT1, c1e, c2e, e1, e2, l1, l2, h5, hw, hx, d1, d2, cc]
  · rw [g10, h5]
    omega_using [hc5, e1, e2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u10.gpr, u9.other r hr.2.2.1, u8.other r hr.2.2.1, u7.other r hr.1, u6.other r hr.2.1, u5.other r hr.1,
      u4.other r hr.1, u3.other r hr.1, u2.other r hr.2.2.2, u1.other r hr.1]
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega_using []) (by omega_using []) (by omega_using [hj, qtop]))

/-- Words `2 i` and `2 i + 1` of `P` doubled, with the bit `a2` and the carry
`a5`, plus `aᵢ²`. -/
theorem diag_ok {k : Nat} {b A : Addr} {s : State} (h : SqOk k b A s) {i : Nat} (hi : i < k)
    (h2 : (s.gpr .a2).toNat ≤ 1) (h5 : (s.gpr .a5).toNat ≤ 1) :
    WP isa (.block (diag k i)) s fun s' =>
      dw s'.mem b (SQ k + 8 * (2 * i)) + 2 ^ 64 * dw s'.mem b (SQ k + 8 * (2 * i + 1)) +
          2 ^ 64 * 2 ^ 64 * ((s'.gpr .a2).toNat + (s'.gpr .a5).toNat) =
        2 * (dw s.mem b (SQ k + 8 * (2 * i)) + 2 ^ 64 * dw s.mem b (SQ k + 8 * (2 * i + 1))) +
          ((s.gpr .a2).toNat + (s.gpr .a5).toNat) + dw s.mem A (8 * i) * dw s.mem A (8 * i) ∧
      (s'.gpr .a2).toNat ≤ 1 ∧ (s'.gpr .a5).toNat ≤ 1 ∧
      (∀ r, r ∉ [.t0, .a1, .a2, .a4, .a5, .a6, .a7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 (SQ k + 8 * (2 * i)), 16⟩] s.mem s'.mem := by
  have k7 := h.k7
  have k30 := h.k30
  obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
  have hc := h.ctx
  unfold diag
  refine wp_ld (by omega_using [hi, k30]) (by rw [h.a]) (al8 h.aal (by omega_using [])) (h.ain _ (by omega_using [hi])) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => ?_
  obtain hc3 : Ctx b s3 := ctx_of hc (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [u3.wr, u2.wr, u1.wr])
  obtain a2_3 : s3.gpr .a2 = s.gpr .a2 := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  obtain a5_3 : s3.gpr .a5 = s.gpr .a5 := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  obtain m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine WP.block_append (WP.mono (dword_ok hc3 k7 k30 (j := 2 * i) (x := .t0) (bi := .a2) (bo := .a4) (by omega_using [hi])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a2_3]; exact h2) (by rw [a5_3]; exact h5)) fun s4 ⟨e4, c4, b4, g4, rd4, wr4, sp4, f4⟩ => ?_)
  obtain hc4 : Ctx b s4 := ctx_of hc3 (g4 _ (by decide)) wr4
  refine WP.mono (dword_ok hc4 k7 k30 (j := 2 * i + 1) (x := .a1) (bi := .a4) (bo := .a2) (by omega_using [hi])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    b4 c4) fun s5 ⟨e5, c5, b5, g5, rd5, wr5, sp5, f5⟩ => ?_
  -- The words of the square of `aᵢ`.
  obtain hp := mul_words (s1.gpr .a6) (s1.gpr .a6)
  obtain hai : (s1.gpr .a6).toNat = dw s.mem A (8 * i) := by rw [u1.gpr]; rfl
  obtain lo : s3.gpr .t0 = s1.gpr .a6 * s1.gpr .a6 := by rw [u3.other _ (by decide), u2.gpr]
  obtain hi' : s4.gpr .a1 = BitVec.ofNat 64 ((s1.gpr .a6).toNat * (s1.gpr .a6).toNat / 2 ^ 64) := by
    rw [g4 _ (by decide), u3.gpr, u2.other _ (by decide)]
  obtain w1 : dw s4.mem b (SQ k + 8 * (2 * i + 1)) = dw s.mem b (SQ k + 8 * (2 * i + 1)) := by
    rw [dw_frame f4 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega_using [])) (by omega_using [hi, qtop]) (by omega_using [hi, qtop]), m3]
  obtain w0 : dw s5.mem b (SQ k + 8 * (2 * i)) = dw s4.mem b (SQ k + 8 * (2 * i)) :=
    dw_frame f5 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega_using [])) (by omega_using [hi, qtop]) (by omega_using [hi, qtop])
  rw [lo, a2_3, a5_3, m3] at e4
  rw [hi', w1] at e5
  rw [hai] at hp
  refine ⟨?_, b5, c5, fun r hr => ?_, by rw [rd5, rd4, u3.rd, u2.rd, u1.rd], by rw [wr5, wr4, u3.wr, u2.wr, u1.wr],
    by rw [sp5, sp4, u3.sp, u2.sp, u1.sp], ?_⟩
  · rw [w0]
    rw [hai] at e5
    omega_using [e4, e5, hp]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g5 r (by simp [hr.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
      g4 r (by simp [hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
      u3.other r hr.2.1, u2.other r hr.1, u1.other r hr.2.2.2.2.2.1]
  · rw [← m3]
    exact (f4.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega_using [])⟩).trans
      (f5.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (by omega_using []) (by omega_using [])⟩)

/-- A step's two words in the sum: `diags_ok`'s last step, among its two equations alone
(`grind` reads every hypothesis). -/
private theorem diag_sum {X Y Z P E r0 r1 w0 w1 c' c ai : Nat} (hv : X + P * c = 2 * Y + Z)
    (e : r0 + E * r1 + E * E * c' = 2 * (w0 + E * w1) + c + ai * ai) :
    X + P * r0 + P * E * r1 + P * (E * E) * c' = 2 * (Y + P * w0 + P * E * w1) + (Z + ai * ai * P) := by
  calc X + P * r0 + P * E * r1 + P * (E * E) * c' = X + P * (r0 + E * r1 + E * E * c') := by grind
    _ = X + P * (2 * (w0 + E * w1) + c + ai * ai) := by rw [e]
    _ = (X + P * c) + 2 * (P * w0 + P * E * w1) + ai * ai * P := by grind
    _ = _ := by rw [hv]; grind

/-- After `i` steps of the doubling and the squares, from `sR`. -/
structure DiagInv (k : Nat) (b A : Addr) (sR : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [.t0, .a1, .a2, .a4, .a5, .a6, .a7] → s.gpr r = sR.gpr r
  rd : s.rd = sR.rd
  wr : s.wr = sR.wr
  sp : s.sp = sR.sp
  frame : Frame [PR k b] sR.mem s.mem
  rest : ∀ j, 2 * i ≤ j → j < 2 * k → dw s.mem b (SQ k + 8 * j) = dw sR.mem b (SQ k + 8 * j)
  c2 : (s.gpr .a2).toNat ≤ 1
  c5 : (s.gpr .a5).toNat ≤ 1
  val : pv k s.mem b 0 (2 * i) + (2 ^ 64) ^ (2 * i) * ((s.gpr .a2).toNat + (s.gpr .a5).toNat) =
    2 * pv k sR.mem b 0 (2 * i) + sumN (fun j => dw sR.mem A (8 * j) * dw sR.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) i

theorem diags_ok {k : Nat} {b A : Addr} {sR : State} (h : SqOk k b A sR) (h2 : sR.gpr .a2 = 0)
    (h5 : sR.gpr .a5 = 0) :
    ∀ i ≤ k, WP isa (.block ((List.range i).flatMap (diag k))) sR (DiagInv k b A sR i)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl,
      by rw [h2]; decide, by rw [h5]; decide, by simp [pv, colsV, sumN, h2, h5]⟩
  | i + 1, hi => by
    have k7 := h.k7
    have k30 := h.k30
    obtain ⟨q8, qtop, nq, tq, tn⟩ := sq_facts k k7 k30
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (diags_ok h h2 h5 i (by omega_using [hi])) fun s hs => ?_)
    obtain hS : SqOk k b A s := h.of (hs.gpr _ (by decide)) (hs.gpr _ (by decide)) hs.rd hs.wr
    refine WP.mono (diag_ok hS (i := i) (by omega_using [hi]) hs.c2 hs.c5) fun s' ⟨e, c2', c5', g', rd', wr', sp', f'⟩ => ?_
    obtain out : ∀ j, (j < 2 * i ∨ 2 * i + 2 ≤ j) → j < 2 * k →
        dw s'.mem b (SQ k + 8 * j) = dw s.mem b (SQ k + 8 * j) := fun j hj hj' =>
      dw_frame f' fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact Offset.disjoint b (by omega_using [hj]) (by omega_using [qtop, hj']) (by omega_using [hi, qtop])
    obtain hA : dw s.mem A (8 * i) = dw sR.mem A (8 * i) := dwA_frame hs.frame k7 k30 h.adis (by omega_using [hi])
    refine ⟨fun r hr => by rw [g' r hr, hs.gpr r hr], by rw [rd', hs.rd], by rw [wr', hs.wr], by rw [sp', hs.sp],
      hs.frame.trans (f'.sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (by omega_using []) (by omega_using [hi])⟩),
      fun j hj hj' => by rw [out j (.inr (by omega_using [hj])) hj', hs.rest j (by omega_using [hj]) hj'], c2', c5', ?_⟩
    have hv := hs.val
    obtain p0 := hs.rest (2 * i) (Nat.le_refl _) (by omega_using [hi])
    obtain p1 := hs.rest (2 * i + 1) (by omega_using []) (by omega_using [hi])
    obtain low : pv k s'.mem b 0 (2 * i) = pv k s.mem b 0 (2 * i) :=
      colsV_congr fun j hj => by rw [Nat.zero_add, out j (.inl hj) (by omega_using [hi, hj])]
    show pv k s'.mem b 0 (2 * i + 1 + 1) + (2 ^ 64) ^ (2 * i + 1 + 1) * _ =
      2 * pv k sR.mem b 0 (2 * i + 1 + 1) + (sumN _ i + _)
    simp only [pv, colsV_succ, Nat.zero_add] at low hv ⊢
    rw [low]
    rw [hA, p0, p1] at e
    generalize colsV (fun i => dw s.mem b (SQ k + 8 * i)) (2 * i) = X at hv ⊢
    generalize colsV (fun i => dw sR.mem b (SQ k + 8 * i)) (2 * i) = Y at hv ⊢
    generalize sumN (fun j => dw sR.mem A (8 * j) * dw sR.mem A (8 * j) * (2 ^ 64) ^ (2 * j)) i = Z at hv ⊢
    generalize dw s'.mem b (SQ k + 8 * (2 * i)) = r0 at e ⊢
    generalize dw s'.mem b (SQ k + 8 * (2 * i + 1)) = r1 at e ⊢
    generalize dw sR.mem b (SQ k + 8 * (2 * i)) = w0 at e ⊢
    generalize dw sR.mem b (SQ k + 8 * (2 * i + 1)) = w1 at e ⊢
    generalize (s'.gpr .a2).toNat + (s'.gpr .a5).toNat = c' at e ⊢
    generalize (s.gpr .a2).toNat + (s.gpr .a5).toNat = c at e hv
    generalize dw sR.mem A (8 * i) = ai at e ⊢
    obtain E1 : ((2 : Nat) ^ 64) ^ (2 * i + 1 + 1) = (2 ^ 64) ^ (2 * i) * (2 ^ 64 * 2 ^ 64) := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    obtain E0 : ((2 : Nat) ^ 64) ^ (2 * i + 1) = (2 ^ 64) ^ (2 * i) * 2 ^ 64 := Nat.pow_succ ..
    rw [E1, E0]
    generalize ((2 : Nat) ^ 64) ^ (2 * i) = P at hv ⊢
    generalize (2 : Nat) ^ 64 = E at e ⊢
    exact diag_sum hv e

end VG.Proof.Weierstrass.RISCV64.GenWide

/-! ## The contract by register -/

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X448.RISCV64.R64 (dw colsV)
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV rvOwn rvOwnEnd)

/-- `fnWith k fast core` meets a contract by register, from `fnWith_ok`. -/
theorem fnWith_rv {S : Modulus} (hk : 7 ≤ S.k) (hk' : S.k ≤ 30) {fast : Prog isa} {core : List Instr}
    {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop} (hfast : FastSpec S.k fast pre res)
    (hcore : CoreSpec S.k core pre res) {s : State} (hs : rvPre S s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fnWith S.k fast core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) S.k) ∧
      Keeps S.k (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn S.k) (rvOwnEnd S.k) := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, rvOwn_gt (show 6 < S.k by omega_using [hk])] at fo fa fb
  simp only [arg, numAt_xv] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ :=
    fnWith_ok hk hk' hfast hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame (by omega_using [hk]) hk' fo f⟩

end VG.Proof.Weierstrass.RISCV64.GenWide
