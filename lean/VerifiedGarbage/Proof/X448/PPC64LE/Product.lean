module

public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X448 on PPC64LE: the fourteen doublewords of a product, row by row

`row64 x y` adds `a_i · [y]` into the doublewords `ACC[i, i + 8)` of the
product (`row64_ok`, the loop invariant `RowInv64`: after `i` rows,
`ACC[0, i + 7)` holds the doublewords of `x_{<i} · y`): each of its steps
(`rowStep64_ok`) adds `a_i b_j`, the doubleword there and the carry word, a
sum below `2¹²⁸`, whose low word it stores and whose high word is the next
carry. The fourteen doublewords are the product's 28 limbs (`accW_val32`), as
the reduction reads them.

`columns_ok`: `mulX`'s columns (`Impl/X448/PPC64LE.lean`) leave the product
of the operands' words in `opA` and `opB` in the registers `pw 0`, …,
`pw 13`: each column `k` clears `pw (k + 2)` and adds its terms `a_i b_j`
(`i + j = k`) into the accumulator `pw k, pw (k + 1), pw (k + 2)`
(`termR_ok`, by `acc3_ok`), so that after `k` columns `pw 0`, …, `pw (k - 1)`
and the accumulator hold the sum of the first `k` (`ColS`, `colR_ok`). From
word 9 on, `pw` reuses the registers of operands' words no later column
reads (`live_facts`).
-/

-- separate module: its proofs cost more than its imports, and its importer's changes need not
-- re-check them

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P)

/-! ## Doublewords -/

/-- `N` doublewords from `acc` are their `2N` words. -/
theorem accW_val32 (acc : Nat) (m : Mem) (b : Addr) :
    ∀ N, accW acc m b N = val32 (fun k => wd m b (acc + 4 * k)) (2 * N)
  | 0 => rfl
  | N + 1 => by
    rw [accW, accW_val32 acc m b N, show 2 * (N + 1) = 2 * N + 1 + 1 by omega, val32_succ, val32_succ,
      dw_split, show acc + 4 * (2 * N) = acc + 8 * N by omega,
      show acc + 4 * (2 * N + 1) = acc + 8 * N + 4 by omega,
      show 32 * (2 * N + 1) = 64 * N + 32 by omega, show 32 * (2 * N) = 64 * N by omega,
      Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm 64 N]
    rw [Nat.mul_add, Nat.add_assoc, ← Nat.mul_assoc, Nat.add_assoc]

/-- The doublewords from `acc`, split at `i`. -/
theorem accW_add (acc : Nat) (m : Mem) (b : Addr) (i : Nat) :
    ∀ k, accW acc m b (i + k) = accW acc m b i + (2 ^ 64) ^ i * accW (acc + 8 * i) m b k
  | 0 => by simp [accW]
  | k + 1 => by
    rw [← Nat.add_assoc, accW, accW_add acc m b i k, accW, Nat.mul_add, Nat.pow_add, Nat.mul_assoc,
      ← Nat.add_assoc acc (8 * i) (8 * k), Nat.mul_add ((2 ^ 64) ^ i), Nat.add_assoc]

/-- An element's fourteen limbs are its seven doublewords. -/
theorem V_eq_cols (m : Mem) (b : Addr) (o : Nat) : V m b o = colsV (ew m b o) 7 := by
  have h := accW_val32 o m b 7
  have e : ∀ k, accW o m b k = colsV (ew m b o) k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [accW, colsV, ih]
  rw [← e, h]; rfl

section
variable {b : Addr} {is : List Instr} {s : State} {Q : State → Prop}

/-- `ld t, off(n)` for `n = b + e` in the working space. -/
theorem ldr_ok (hc : Ctx b s) {n t : Reg} (hn : n ≠ .r0) {e off : Nat}
    (he : s.gpr n = b + BitVec.ofNat 64 e) (hd : e + off + 8 ≤ 4096) (h4 : off % 4 = 0)
    (k : ∀ s', Upd s s' t (s.mem.readW (b + BitVec.ofNat 64 (e + off)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  have ex := exec_load_d (s := s) (t := t) (n := n) (off := off) hn ⟨by omega, h4⟩
    (by rw [he, Offset.add_add]; exact hc.inR hd)
  rw [he, Offset.add_add] at ex
  exact WP.cons ex (k _ (Upd.write _ _ _))

/-- `std t, off(n)` for `n = b + e` in the working space. -/
theorem sdr_ok (hc : Ctx b s) {n t : Reg} (hn : n ≠ .r0) {e off : Nat}
    (he : s.gpr n = b + BitVec.ofNat 64 e) (hd : e + off + 8 ≤ 4096) (h4 : off % 4 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 (e + off)) (s.gpr t)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  have ex := exec_store_d (s := s) (t := t) (n := n) (off := off) hn ⟨by omega, h4⟩
    (by rw [he, Offset.add_add]; exact hc.inW hd)
  rw [he, Offset.add_add] at ex
  exact WP.cons ex (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

end

section
variable {b : Addr}

theorem ACC_eq' : ACC = 952 := rfl

/-! ## A row -/

/-- After `j` steps of row `i` from `sr`: the doublewords `ACC[i, i + j)` and
the carry `r8` hold `acc[i, i + j) + X · Y_{<j}`, for `X` in `r4`. -/
structure StepInv (i : Nat) (Y : Nat → Nat) (sr : State) (j : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest [.r5, .r7, .r8, .r10] sr s
  frame : Frame [⟨b + BitVec.ofNat 64 (ACC + 8 * i), 8 * j⟩] sr.mem s.mem
  val : accW (ACC + 8 * i) s.mem b j + (2 ^ 64) ^ j * (s.gpr .r8).toNat =
    accW (ACC + 8 * i) sr.mem b j + (sr.gpr .r4).toNat * colsV Y j

theorem rowStep64_ok {y : Nat} (hy : y + 56 ≤ ACC) (hy4 : y % 4 = 0) {i : Nat} (hi : i < 7)
    {sr : State} (h9 : sr.gpr .r9 = b + BitVec.ofNat 64 (8 * i)) {j : Nat} (hj : j < 7) {s : State}
    (h : StepInv (b := b) i (ew sr.mem b y) sr j s) :
    WP isa (.block (rowStep64 y j)) s (StepInv (b := b) i (ew sr.mem b y) sr (j + 1)) := by
  have hA := ACC_eq'
  have hc := h.ctx
  have e9 : s.gpr .r9 = b + BitVec.ofNat 64 (8 * i) := by rw [h.rest.gpr _ (by decide), h9]
  have e4 : s.gpr .r4 = sr.gpr .r4 := h.rest.gpr _ (by decide)
  -- The operands, unchanged since `sr` outside the row's prefix.
  have eY : dw s.mem b (y + 8 * j) = dw sr.mem b (y + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have eA : dw s.mem b (ACC + 8 * i + 8 * j) = dw sr.mem b (ACC + 8 * i + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  unfold rowStep64
  refine ld0_ok hc (d := y + 8 * j) (by omega) (by omega) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => wp_mulhu fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc.of_rest ((u1.rest (ws := [.r5, .r7]) (by decide)).trans
    ((u2.rest (by decide)).trans (u3.rest (by decide)))) (by decide)
  refine ldr_ok hc3 (n := .r9) (e := 8 * i) (off := ACC + 8 * j) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), e9])
    (by omega) (by omega) fun s4 u4 => ?_
  refine wp_addc fun s5 u5 => wp_addze fun s6 u6 => wp_addc fun s7 u7 => wp_addze fun s8 u8 => ?_
  have hc8 : Ctx b s8 := hc3.of_rest ((u4.rest (ws := [.r5, .r7, .r8, .r10]) (by decide)).trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      (u8.rest (by decide)))))) (by decide)
  refine sdr_ok hc8 (n := .r9) (e := 8 * i) (off := ACC + 8 * j) (by decide)
    (by rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), e9])
    (by omega) (by omega) fun s9 u9 => WP.block_nil ?_
  -- The values.
  have hX := (sr.gpr .r4).isLt
  have hYl := dw_lt sr.mem b (y + 8 * j)
  generalize hXv : (sr.gpr .r4).toNat = X at *
  generalize hYv : dw sr.mem b (y + 8 * j) = Yj at *
  have g5 : (s1.gpr .r5).toNat = Yj := by rw [u1.gpr]; show dw s.mem b _ = _; rw [eY]
  have g4 : (s1.gpr .r4).toNat = X := by rw [u1.other _ (by decide), e4, hXv]
  have hP : X * Yj ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have elo : (s3.gpr .r7).toNat = X * Yj % 2 ^ 64 := by
    rw [u3.other _ (by decide), u2.gpr, BitVec.toNat_mul, g4, g5]
  have ehi : (s3.gpr .r5).toNat = X * Yj / 2 ^ 64 := by
    rw [u3.gpr, u2.other _ (by decide), u2.other _ (by decide), g4, g5, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)))]
  have hsplit : X * Yj % 2 ^ 64 + 2 ^ 64 * (X * Yj / 2 ^ 64) = X * Yj := Nat.mod_add_div _ _
  have ga : (s4.gpr .r10).toNat = dw sr.mem b (ACC + 8 * i + 8 * j) := by
    rw [u4.gpr, ← eA, u3.mem, u2.mem, u1.mem, show 8 * i + (ACC + 8 * j) = ACC + 8 * i + 8 * j by omega]
    rfl
  have gc : (s6.gpr .r8).toNat = (s.gpr .r8).toNat := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide)]
  have v5 := u5.val; have v6 := u6.val; have v7 := u7.val; have v8 := u8.val
  rw [u4.other _ (by decide), elo, ga] at v5
  rw [u5.other _ (by decide), u4.other _ (by decide), ehi] at v6
  rw [u6.other _ (by decide), gc] at v7
  rw [u7.other _ (by decide)] at v8
  have c5 := u5.ca; have c6 := u6.ca; have c7 := u7.ca; have c8 := u8.ca
  have hAl := dw_lt sr.mem b (ACC + 8 * i + 8 * j)
  have hCl := (s.gpr .r8).isLt
  have l5 := (s5.gpr .r7).isLt; have l6 := (s6.gpr .r5).isLt; have l7 := (s7.gpr .r7).isLt
  have l8 := (s8.gpr .r8).isLt
  -- The step's sum: the stored word and the carry.
  have hsum : (s7.gpr .r7).toNat + 2 ^ 64 * (s8.gpr .r8).toNat =
      X * Yj + dw sr.mem b (ACC + 8 * i + 8 * j) + (s.gpr .r8).toNat := by
    omega_arith
  have hm9 : s9.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * i + (ACC + 8 * j))) (s8.gpr .r7) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  rw [show 8 * i + (ACC + 8 * j) = ACC + 8 * i + 8 * j by omega] at hm9
  have hr9 : Rest [.r5, .r7, .r8, .r10] s s9 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans (u9.rest [.r5, .r7, .r8, .r10]))))))))
  refine ⟨hc8.of_rest (u9.rest []) (by decide), h.rest.trans hr9, ?_, ?_⟩
  · rw [hm9]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · have ew9 : accW (ACC + 8 * i) s9.mem b j = accW (ACC + 8 * i) s.mem b j :=
      accW_congr fun c hc' => by
        rw [hm9, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have es9 : dw s9.mem b (ACC + 8 * i + 8 * j) = (s7.gpr .r7).toNat := by
      rw [hm9, dw_write_self, u8.other _ (by decide)]
    have e8 : (s9.gpr .r8).toNat = (s8.gpr .r8).toNat := by rw [u9.gpr]
    have hv := h.val
    rw [hXv] at hv
    rw [accW, accW, colsV, ew9, es9, e8, hXv, show ((2 : Nat) ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ _ _]
    have hy' : ew sr.mem b y j = Yj := hYv
    rw [hy']
    generalize (2 ^ 64) ^ j = K at *
    generalize accW (ACC + 8 * i) s.mem b j = S at *
    generalize accW (ACC + 8 * i) sr.mem b j = S0 at *
    generalize colsV (ew sr.mem b y) j = CY at *
    generalize (s7.gpr .r7).toNat = L at *
    generalize (s8.gpr .r8).toNat = H at *
    generalize (s.gpr .r8).toNat = C at *
    generalize dw sr.mem b (ACC + 8 * i + 8 * j) = A at *
    -- S + K C = S0 + X CY, and L + 2⁶⁴ H = X Yj + A + C.
    have e1 : K * L + K * 2 ^ 64 * H = K * (X * Yj) + K * A + K * C := by
      rw [Nat.mul_assoc, ← Nat.mul_add, hsum, Nat.mul_add, Nat.mul_add]
    have e2 : X * (CY + K * Yj) = X * CY + K * (X * Yj) := by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm X K, Nat.mul_assoc]
    rw [e2]
    omega

/-- The loop invariant of the rows of `mul o x y` from `s0`, after `i` rows:
`ACC[0, i + 7)` holds the doublewords of `x_{<i} · y`. -/
structure RowInv64 (b : Addr) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob s0 s
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (8 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (7 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem
  val : accW ACC s.mem b (i + 7) = colsV (ew s0.mem b x) i * colsV (ew s0.mem b y) 7

theorem colsV_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by rw [colsV, colsV, colsV_congr (fun k hk => h k (by omega)), h n (by omega)]

theorem row64_ok {x y : Nat} (hx : x + 56 ≤ ACC) (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s0 : State} {i : Nat} (hi : i < 7) {s : State} (h : RowInv64 b x y s0 i s) :
    WP isa (.block (row64 x y)) s fun s' =>
      RowInv64 b x y s0 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (7 - (i + 1) ≠ 0) := by
  have hA := ACC_eq'
  -- An operand's doubleword is as it was at `s0`.
  have hop : ∀ (m : Mem), Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem m →
      ∀ z, z + 56 ≤ ACC → ∀ k < 7, dw m b (z + 8 * k) = dw s0.mem b (z + 8 * k) :=
    fun m hf z hz k hk => dw_frame hf fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  simp only [row64, List.cons_append, List.append_assoc]
  refine ldr_ok h.ctx (n := .r9) (e := 8 * i) (off := x) (by decide) h.r9 (by omega) hx4 fun s1 u1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.r4, .r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e4 : (s2.gpr .r4).toNat = ew s0.mem b x i := by
    rw [u2.other _ (by decide), u1.gpr, show 8 * i + x = x + 8 * i by omega]
    exact hop s.mem h.frame x hx i hi
  have e9 : s2.gpr .r9 = b + BitVec.ofNat 64 (8 * i) := by rw [hr2.gpr _ (by decide), h.r9]
  have hY : ∀ k < 7, ew s2.mem b y k = ew s0.mem b y k := fun k hk => by
    rw [hm2]; exact hop s.mem h.frame y hy k hk
  have h0 : StepInv (b := b) i (ew s2.mem b y) s2 0 s2 :=
    ⟨hc2, Rest.refl _ _, Frame.refl _ _, by simp [accW, colsV, u2.gpr]⟩
  rw [List.nil_append]
  refine WP.append (wp_range_flatMap (M := isa) (N := 7) (StepInv (b := b) i (ew s2.mem b y) s2)
    (fun j t hj ht => rowStep64_ok hy hy4 hi e9 hj ht) 7 (Nat.le_refl _) s2 h0) fun s3 h3 => ?_
  have hc3 := h3.ctx
  refine sdr_ok hc3 (n := .r9) (e := 8 * i) (off := ACC + 56) (by decide)
    (by rw [h3.rest.gpr _ (by decide), e9]) (by omega) (by omega) fun s4 u4 => ?_
  refine wp_addi (by decide) (by decide) fun s5 u5 => wp_subi (by decide) (by decide) fun s6 u6 =>
    WP.block_nil ?_
  have hm6 : s6.mem = s3.mem.writeW (b + BitVec.ofNat 64 (ACC + 8 * i + 8 * 7)) (s3.gpr .r8) := by
    rw [u6.mem, u5.mem, u4.mem, show 8 * i + (ACC + 56) = ACC + 8 * i + 8 * 7 by omega]
  have hr6 : Rest clob s s6 :=
    (hr2.mono (by decide)).trans ((h3.rest.mono (by decide)).trans ((u4.rest _).trans
      ((u5.rest (by decide)).trans (u6.rest (by decide)))))
  -- The frame of the row: `ACC[i, i + 8)`.
  have hf6 : Frame [⟨b + BitVec.ofNat 64 (ACC + 8 * i), 64⟩] s.mem s6.mem := by
    rw [hm6, ← hm2]
    exact (h3.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨⟨hc3.of_rest ((u4.rest [.r9, .r11]).trans ((u5.rest (ws := [.r9, .r11]) (by decide)).trans
      (u6.rest (by decide)))) (by decide), h.rest.trans hr6, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, u4.gpr, h3.rest.gpr _ (by decide), e9, Offset.add_add]
    congr 2
  · rw [u6.gpr, u5.other _ (by decide), u4.gpr, h3.rest.gpr _ (by decide), hr2.gpr _ (by decide),
      h.r11, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · exact h.frame.trans (hf6.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩)
  · -- The value.
    have hv := h.val
    have hv3 := h3.val
    rw [accW_add ACC s.mem b i 7] at hv
    rw [show i + 1 + 7 = i + 8 by omega, accW_add ACC s6.mem b i 8]
    have elow : accW ACC s6.mem b i = accW ACC s.mem b i := accW_congr fun c hc => by
      exact dw_frame hf6 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    have erow : accW (ACC + 8 * i) s6.mem b 8 =
        accW (ACC + 8 * i) s3.mem b 7 + (2 ^ 64) ^ 7 * (s3.gpr .r8).toNat := by
      have e : accW (ACC + 8 * i) (s3.mem.writeW (b + BitVec.ofNat 64 (ACC + 8 * i + 8 * 7))
          (s3.gpr .r8)) b 7 = accW (ACC + 8 * i) s3.mem b 7 :=
        accW_congr fun c hc => by rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]
      rw [accW, hm6, dw_write_self, e]
    rw [elow, erow, hv3, e4, colsV_congr hY, hm2,
      show colsV (ew s0.mem b x) (i + 1) = colsV (ew s0.mem b x) i + (2 ^ 64) ^ i * ew s0.mem b x i from rfl]
    generalize (2 ^ 64) ^ i = K at *
    generalize accW ACC s.mem b i = A at *
    generalize accW (ACC + 8 * i) s.mem b 7 = W at *
    generalize colsV (ew s0.mem b y) 7 = Y7 at *
    generalize colsV (ew s0.mem b x) i = CX at *
    generalize ew s0.mem b x i = X at *
    rw [Nat.mul_add, ← Nat.add_assoc, hv, Nat.add_mul, Nat.mul_assoc]
  · rw [u6.gpr, u5.other _ (by decide), u4.gpr, h3.rest.gpr _ (by decide), hr2.gpr _ (by decide),
      h.r11, ofNat_sub_one (by omega) (by omega), ofNat_ne_zero (by omega)]
    congr 1

end

/-! ## The product in registers -/

/-- The registers `mulR` changes before it restores them. -/
abbrev clobR : List Reg :=
  [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
    .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem pw_inj : ∀ j < 15, ∀ k < 15, pw j = pw k → j = k := by decide

theorem pw_facts : ∀ k < 15, pw k ≠ .r4 ∧ pw k ≠ .r5 ∧ pw k ≠ .r6 ∧ pw k ∈ clobR := by decide

theorem op_facts : ∀ i < 7, opA i ≠ .r4 ∧ opA i ≠ .r5 ∧ opB i ≠ .r4 ∧ opB i ≠ .r5 := by decide

/-- The operands' words that column `k` or a later one reads (`k ≤ i + 6`)
are in none of its accumulator's registers. -/
theorem live_facts' : ∀ k < 13, ∀ i < 7, i + 6 < k ∨
    ((opA i ≠ pw k ∧ opA i ≠ pw (k + 1) ∧ opA i ≠ pw (k + 2)) ∧
    (opB i ≠ pw k ∧ opB i ≠ pw (k + 1) ∧ opB i ≠ pw (k + 2))) := by decide

theorem live_facts {k : Nat} (hk : k < 13) {i : Nat} (hi : i < 7) (hl : k ≤ i + 6) :
    (opA i ≠ pw k ∧ opA i ≠ pw (k + 1) ∧ opA i ≠ pw (k + 2)) ∧
    (opB i ≠ pw k ∧ opB i ≠ pw (k + 1) ∧ opB i ≠ pw (k + 2)) :=
  (live_facts' k hk i hi).resolve_left (by omega)

theorem pairs_ok : ∀ k < 13, ∀ p ∈ pairs k, p.1 < 7 ∧ p.2 < 7 ∧ k ≤ p.1 + 6 ∧ k ≤ p.2 + 6 := by decide

theorem pairs_len : ∀ k < 13, (pairs k).length ≤ 7 := by decide

section
variable {b : Addr}

/-- From `s0`: what the terms of column `k` keep. -/
structure TermS (s0 : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobR s0 s
  mem : s.mem = s0.mem
  keep : ∀ r, r ≠ pw k → r ≠ pw (k + 1) → r ≠ pw (k + 2) → r ≠ .r4 → r ≠ .r5 → s.gpr r = s0.gpr r

/-- The product of the operands' words `p.1` and `p.2` in `s`. -/
def opProd (s : State) (p : Nat × Nat) : Nat := (s.gpr (opA p.1)).toNat * (s.gpr (opB p.2)).toNat

/-- A term `a_i b_j` of column `k`. -/
theorem termR_ok {s0 : State} {k : Nat} {p : Nat × Nat} (hk : k < 13)
    (hp : p.1 < 7 ∧ p.2 < 7 ∧ k ≤ p.1 + 6 ∧ k ≤ p.2 + 6) {s : State} (h : TermS (b := b) s0 k s) :
    WP isa (.block (termR k p)) s fun s' => TermS (b := b) s0 k s' ∧
      (v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opProd s0 p < 2 ^ 192 →
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + opProd s0 p) := by
  obtain ⟨hi, hj, hli, hlj⟩ := hp
  obtain ⟨p04, p05, -, p0c⟩ := pw_facts k (by omega)
  obtain ⟨p14, p15, -, p1c⟩ := pw_facts (k + 1) (by omega)
  obtain ⟨p24, p25, -, p2c⟩ := pw_facts (k + 2) (by omega)
  have h01 : pw k ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have h02 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have h12 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  obtain ⟨a4, a5, -, -⟩ := op_facts p.1 hi
  obtain ⟨-, -, b4, b5⟩ := op_facts p.2 hj
  obtain ⟨⟨a0, a1, a2⟩, -⟩ := live_facts hk hi hli
  obtain ⟨-, ⟨b0, b1, b2⟩⟩ := live_facts hk hj hlj
  have ka : s.gpr (opA p.1) = s0.gpr (opA p.1) := h.keep _ a0 a1 a2 a4 a5
  have kb : s.gpr (opB p.2) = s0.gpr (opB p.2) := h.keep _ b0 b1 b2 b4 b5
  simp only [termR]
  refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => ?_
  refine acc3_ok h01 h02 h12 p05 fun s3 hv3 hg3 hm3 hrd3 hwr3 hsp3 => WP.block_nil ?_
  have hA := (s.gpr (opA p.1)).isLt
  have hB := (s.gpr (opB p.2)).isLt
  have g1a : s1.gpr (opA p.1) = s.gpr (opA p.1) := u1.other _ a4
  have g1b : s1.gpr (opB p.2) = s.gpr (opB p.2) := u1.other _ b4
  have elo : (s2.gpr .r4).toNat = opProd s0 p % 2 ^ 64 := by
    rw [u2.other _ (by decide), u1.gpr, BitVec.toNat_mul, ka, kb]; rfl
  have ehi : (s2.gpr .r5).toNat = opProd s0 p / 2 ^ 64 := by
    rw [u2.gpr, g1a, g1b, ka, kb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · rfl
    · rw [← ka, ← kb]; exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt hA hB)
  have e : (s2.gpr .r4).toNat + 2 ^ 64 * (s2.gpr .r5).toNat = opProd s0 p := by
    rw [elo, ehi]; exact Nat.mod_add_div _ _
  have hv2 : v3 s2 (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) := by
    simp only [v3, u2.other _ p05, u2.other _ p15, u2.other _ p25, u1.other _ p04, u1.other _ p14,
      u1.other _ p24]
  have hr2 : Rest clobR s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hr3 : Rest clobR s2 s3 := ⟨fun r hr' => hg3 r (fun e => hr' (e ▸ p0c)) (fun e => hr' (e ▸ p1c))
    (fun e => hr' (e ▸ p2c)), hrd3, hwr3, hsp3⟩
  have hm : s3.mem = s.mem := by rw [hm3, u2.mem, u1.mem]
  refine ⟨⟨h.ctx.of_rest (hr2.trans hr3) (by decide), h.rest.trans (hr2.trans hr3), hm.trans h.mem,
    fun r n0 n1 n2 n4 n5 => ?_⟩, fun hb => ?_⟩
  · rw [hg3 r n0 n1 n2, u2.other _ n5, u1.other _ n4]; exact h.keep r n0 n1 n2 n4 n5
  · rw [hv3 (by rw [hv2, Nat.add_assoc, e]; exact hb), hv2, Nat.add_assoc, e]

/-- A column's terms, by induction on them. -/
theorem termsR_ok {s0 : State} {k : Nat} (hk : k < 13) :
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, p.1 < 7 ∧ p.2 < 7 ∧ k ≤ p.1 + 6 ∧ k ≤ p.2 + 6) →
      ∀ s, TermS (b := b) s0 k s →
      v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opProd s0) ps < 2 ^ 192 →
      WP isa (.block (ps.flatMap (termR k))) s fun s' => TermS (b := b) s0 k s' ∧
        v3 s' (pw k) (pw (k + 1)) (pw (k + 2)) = v3 s (pw k) (pw (k + 1)) (pw (k + 2)) + tsum (opProd s0) ps
  | [], _, s, h, _ => WP.block_nil ⟨h, by simp [tsum]⟩
  | p :: ps, hps, s, h, hb => by
    rw [List.flatMap_cons]
    rw [tsum_cons] at hb
    refine WP.append (termR_ok hk (hps p List.mem_cons_self) h) fun s1 ⟨h1, hv1⟩ => ?_
    have hv1 := hv1 (by omega)
    refine WP.mono (termsR_ok hk ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) s1 h1 (by omega))
      fun s2 ⟨h2, hv2⟩ => ⟨h2, ?_⟩
    rw [hv2, hv1, tsum_cons]; omega

/-- The value of the words `pw 0`, …, `pw (k - 1)`. -/
abbrev pwSum (s : State) (k : Nat) : Nat := colsV (fun j => (s.gpr (pw j)).toNat) k

/-- After `k` columns, from `s0`: the operands' words the later columns read
as they were, and `pw 0`, …, `pw (k - 1)` and the accumulator `pw k,
pw (k + 1)` the sum of the first `k` columns. -/
structure ColS (s0 : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clobR s0 s
  mem : s.mem = s0.mem
  ops : ∀ i < 7, k ≤ i + 6 → s.gpr (opA i) = s0.gpr (opA i) ∧ s.gpr (opB i) = s0.gpr (opB i)
  val : pwSum s k + (2 ^ 64) ^ k * ((s.gpr (pw k)).toNat + 2 ^ 64 * (s.gpr (pw (k + 1))).toNat) =
    colsV (fun c => tsum (opProd s0) (pairs c)) k

theorem tsum_lt7 {f : Nat × Nat → Nat} (hf : ∀ p, f p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 7) : tsum f ps < 7 * 2 ^ 128 := by
  have := tsum_le (ps := ps) fun p _ => hf p
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 7 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
    Nat.mul_le_mul_right _ hl
  omega

/-- Column `k`. -/
theorem colR_ok {s0 : State} {k : Nat} (hk : k < 13) {s : State} (h : ColS (b := b) s0 k s) :
    WP isa (.block (colR k)) s (ColS (b := b) s0 (k + 1)) := by
  obtain ⟨-, -, -, p2c⟩ := pw_facts (k + 2) (by omega)
  unfold colR
  refine wp_li (by decide) fun s1 u1 => ?_
  have hr1 : Rest clobR s s1 := u1.rest p2c
  have hRT : TermS (b := b) s1 k s1 := ⟨h.ctx.of_rest hr1 (by decide), Rest.refl _ _, rfl, fun _ _ _ _ _ _ => rfl⟩
  have hops : ∀ i < 7, k ≤ i + 6 → s1.gpr (opA i) = s0.gpr (opA i) ∧ s1.gpr (opB i) = s0.gpr (opB i) :=
    fun i hi hl => by
      obtain ⟨⟨-, -, a2⟩, ⟨-, -, b2⟩⟩ := live_facts hk hi hl
      exact ⟨by rw [u1.other _ a2]; exact (h.ops i hi hl).1, by rw [u1.other _ b2]; exact (h.ops i hi hl).2⟩
  have hF : ∀ p ∈ pairs k, opProd s1 p = opProd s0 p := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := pairs_ok k hk p hp
    simp only [opProd, (hops _ h1 h3).1, (hops _ h2 h4).2]
  have hts : tsum (opProd s1) (pairs k) = tsum (opProd s0) (pairs k) := by
    unfold tsum; congr 1; exact List.map_congr_left hF
  have hlt : tsum (opProd s1) (pairs k) < 7 * 2 ^ 128 :=
    tsum_lt7 (fun p => Nat.mul_le_mul (by have := (s1.gpr (opA p.1)).isLt; omega)
      (by have := (s1.gpr (opB p.2)).isLt; omega)) (pairs_len k hk)
  have g2 : s1.gpr (pw (k + 2)) = 0 := u1.gpr
  have h01 : pw k ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have h11 : pw (k + 1) ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
  have hv0 : v3 s1 (pw k) (pw (k + 1)) (pw (k + 2)) =
      (s.gpr (pw k)).toNat + 2 ^ 64 * (s.gpr (pw (k + 1))).toNat := by
    simp only [v3, g2, u1.other _ h01, u1.other _ h11]; rfl
  have hl := (s.gpr (pw k)).isLt
  have hh := (s.gpr (pw (k + 1))).isLt
  refine WP.mono (termsR_ok hk (pairs k) (fun p hp => pairs_ok k hk p hp) s1 hRT
    (by rw [hv0]; omega_arith)) fun s2 ⟨h2, hv2⟩ => ?_
  have hlow : ∀ j < k, s2.gpr (pw j) = s.gpr (pw j) := fun j hj => by
    have n0 : pw j ≠ pw k := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
    have n1 : pw j ≠ pw (k + 1) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
    have n2 : pw j ≠ pw (k + 2) := fun e => by have := pw_inj _ (by omega) _ (by omega) e; omega
    obtain ⟨j4, j5, -, -⟩ := pw_facts j (by omega)
    rw [h2.keep _ n0 n1 n2 j4 j5, u1.other _ n2]
  refine ⟨h2.ctx, h.rest.trans (hr1.trans h2.rest), h2.mem.trans (by rw [u1.mem, h.mem]),
    fun i hi hl => ?_, ?_⟩
  · obtain ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := live_facts hk hi (by omega)
    obtain ⟨a4, a5, b4, b5⟩ := op_facts i hi
    exact ⟨by rw [h2.keep _ a0 a1 a2 a4 a5]; exact (hops i hi (by omega)).1,
      by rw [h2.keep _ b0 b1 b2 b4 b5]; exact (hops i hi (by omega)).2⟩
  · have hv := h.val
    rw [show k + 1 + 1 = k + 2 by omega]
    simp only [pwSum, colsV]
    rw [colsV_congr (fun j hj => by rw [hlow j hj])]
    rw [← pwSum, ← hts]
    rw [hv0] at hv2
    unfold v3 at hv2
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K at *
    generalize pwSum s k = S at *
    generalize colsV (fun c => tsum (opProd s0) (pairs c)) k = C at *
    generalize tsum (opProd s1) (pairs k) = T at *
    generalize (s.gpr (pw k)).toNat = a at *
    generalize (s.gpr (pw (k + 1))).toNat = c at *
    generalize (s2.gpr (pw k)).toNat = a' at *
    generalize (s2.gpr (pw (k + 1))).toNat = c' at *
    generalize (s2.gpr (pw (k + 2))).toNat = d' at *
    generalize 2 ^ 64 = W at *
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, hv2, ← hv, Nat.mul_add K (a + W * c) T]
    omega

/-- The columns, by induction. -/
theorem colsR_ok {s0 : State} : ∀ n ≤ 13, ∀ s, ColS (b := b) s0 0 s →
    WP isa (.block ((List.range n).flatMap colR)) s (ColS (b := b) s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (colsR_ok n (by omega) s h) fun s1 h1 => colR_ok (by omega) h1

end

/-- The columns of a product of seven words sum to it. -/
theorem cols_mul (X Y : Nat → Nat) :
    colsV (fun c => tsum (fun p => X p.1 * Y p.2) (pairs c)) 13 = colsV X 7 * colsV Y 7 := by
  simp only [colsV]
  generalize 2 ^ 64 = B
  simp only [pairs, tsum, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  grind

theorem colsV_lt {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ 64) : ∀ n, colsV f n < (2 ^ 64) ^ n
  | 0 => by simp [colsV]
  | n + 1 => by
    have := colsV_lt hf n
    have := hf n
    rw [colsV, Nat.pow_succ]
    calc colsV f n + (2 ^ 64) ^ n * f n < (2 ^ 64) ^ n + (2 ^ 64) ^ n * f n := by omega
      _ = (2 ^ 64) ^ n * (f n + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ n * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)

section
variable {b : Addr}

/-- From `pw 0 = pw 1 = 0`: the fourteen words of the product of the
operands' words in `pw`. -/
theorem columns_ok {s0 : State} (hc : Ctx b s0) (h0 : s0.gpr (pw 0) = 0) (h1 : s0.gpr (pw 1) = 0) :
    WP isa (.block ((List.range 13).flatMap colR)) s0 fun s' => Ctx b s' ∧ Rest clobR s0 s' ∧
      s'.mem = s0.mem ∧
      pwSum s' 14 = colsV (fun i => (s0.gpr (opA i)).toNat) 7 * colsV (fun j => (s0.gpr (opB j)).toNat) 7 := by
  have hinit : ColS (b := b) s0 0 s0 := ⟨hc, Rest.refl _ _, rfl, fun _ _ _ => ⟨rfl, rfl⟩, by
    simp only [pwSum, colsV, Nat.pow_zero, Nat.one_mul, Nat.zero_add, h0, h1]; rfl⟩
  refine WP.mono (colsR_ok 13 (Nat.le_refl _) s0 hinit) fun s4 h4 => ⟨h4.ctx, h4.rest, h4.mem, ?_⟩
  have hv := h4.val
  have e : (fun c => tsum (opProd s0) (pairs c)) =
      (fun c => tsum (fun p => (s0.gpr (opA p.1)).toNat * (s0.gpr (opB p.2)).toNat) (pairs c)) := rfl
  rw [e, cols_mul (fun i => (s0.gpr (opA i)).toNat) (fun j => (s0.gpr (opB j)).toNat)] at hv
  have hlt : colsV (fun i => (s0.gpr (opA i)).toNat) 7 * colsV (fun j => (s0.gpr (opB j)).toNat) 7 <
      (2 ^ 64) ^ 14 := by
    have := colsV_lt (f := fun i => (s0.gpr (opA i)).toNat) (fun i => (s0.gpr (opA i)).isLt) 7
    have := colsV_lt (f := fun j => (s0.gpr (opB j)).toNat) (fun j => (s0.gpr (opB j)).isLt) 7
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (by assumption) (by assumption)) (by
      rw [← Nat.pow_add])
  have h14 := (s4.gpr (pw 14)).isLt
  have hp13 : pwSum s4 13 < (2 ^ 64) ^ 13 := colsV_lt (fun j => (s4.gpr (pw j)).isLt) 13
  rw [show pwSum s4 14 = pwSum s4 13 + (2 ^ 64) ^ 13 * (s4.gpr (pw 13)).toNat from rfl]
  rw [show (13 : Nat) + 1 = 14 from rfl] at hv
  generalize pwSum s4 13 = S at *
  generalize (s4.gpr (pw 13)).toNat = a at *
  generalize (s4.gpr (pw 14)).toNat = c at *
  generalize colsV (fun i => (s0.gpr (opA i)).toNat) 7 * colsV (fun j => (s0.gpr (opB j)).toNat) 7 = XY at *
  have : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact h
    · exfalso
      have : (2 ^ 64) ^ 13 * (2 ^ 64 * c) ≥ (2 ^ 64) ^ 14 := by
        rw [show (2 ^ 64) ^ 14 = (2 ^ 64) ^ 13 * 2 ^ 64 * 1 by rfl, Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
      omega
  subst this
  omega

end

end VG.Proof.X448.PPC64LE
