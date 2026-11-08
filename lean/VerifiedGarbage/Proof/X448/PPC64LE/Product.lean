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

end VG.Proof.X448.PPC64LE
