module

public import VerifiedGarbage.Proof.X448.RISCV64.R64.Carry
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.X448.Limbs32
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide

/-!
# X448 on RISC-V, 64-bit limbs: the reduction of a product

The product `L + 2⁴⁴⁸ H` at `ACC` (fourteen words) becomes the seven words
`T_k` of `L + H + (H - H mod 2²²⁴) + rot(H)` (`redT`), congruent to it modulo
`p` (`redT_mod`); `redStep k` computes word `k` with its carries
(`redStep_ok`, the invariant `RedInv`), and `reduce o` folds the carry out in
twice and stores the result (`reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (P)

/-- Word `k` of `L + H + (H - H mod 2²²⁴) + rot(H)`, for the product's words `Pw`. -/
def redT (Pw : Nat → Nat) (k : Nat) : Nat :=
  Pw k + Pw (7 + k) + (if 4 ≤ k then Pw (7 + k) else 0) +
    (if k = 3 then 2 ^ 32 * (Pw 10 / 2 ^ 32) else 0) +
    (Pw (7 + (k + 3) % 7) / 2 ^ 32 + 2 ^ 32 * (Pw (7 + (k + 4) % 7) % 2 ^ 32))

/-- `2⁴⁴⁸ H ≡ H + (H - H mod 2²²⁴) + rot(H)` modulo `p`, word by word. -/
theorem redT_mod (Pw : Nat → Nat) : colsV (redT Pw) 7 % P = colsV Pw 14 % P := by
  simp only [colsV, redT, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceEqDiff,
    ↓reduceIte]
  have e7 := Nat.mod_add_div (Pw 7) (2 ^ 32)
  have e8 := Nat.mod_add_div (Pw 8) (2 ^ 32)
  have e9 := Nat.mod_add_div (Pw 9) (2 ^ 32)
  have e10 := Nat.mod_add_div (Pw 10) (2 ^ 32)
  have e11 := Nat.mod_add_div (Pw 11) (2 ^ 32)
  have e12 := Nat.mod_add_div (Pw 12) (2 ^ 32)
  have e13 := Nat.mod_add_div (Pw 13) (2 ^ 32)
  generalize Pw 7 % 2 ^ 32 = l0 at *
  generalize Pw 8 % 2 ^ 32 = l1 at *
  generalize Pw 9 % 2 ^ 32 = l2 at *
  generalize Pw 10 % 2 ^ 32 = l3 at *
  generalize Pw 11 % 2 ^ 32 = l4 at *
  generalize Pw 12 % 2 ^ 32 = l5 at *
  generalize Pw 13 % 2 ^ 32 = l6 at *
  generalize Pw 7 / 2 ^ 32 = u0 at *
  generalize Pw 8 / 2 ^ 32 = u1 at *
  generalize Pw 9 / 2 ^ 32 = u2 at *
  generalize Pw 10 / 2 ^ 32 = u3 at *
  generalize Pw 11 / 2 ^ 32 = u4 at *
  generalize Pw 12 / 2 ^ 32 = u5 at *
  generalize Pw 13 / 2 ^ 32 = u6 at *
  rw [← e7, ← e8, ← e9, ← e10, ← e11, ← e12, ← e13]
  generalize Pw 0 = p0
  generalize Pw 1 = p1
  generalize Pw 2 = p2
  generalize Pw 3 = p3
  generalize Pw 4 = p4
  generalize Pw 5 = p5
  generalize Pw 6 = p6
  have key : ∀ A B M : Nat, B = A + P * M → A % P = B % P := fun A B M h => by
    rw [h, Nat.add_mul_mod_self_left]
  refine key _ _ ((l0 + 2 ^ 32 * u0) + 2 ^ 64 * (l1 + 2 ^ 32 * u1) + 2 ^ 128 * (l2 + 2 ^ 32 * u2) +
      2 ^ 192 * l3 + (2 ^ 224 + 1) * (u3 + 2 ^ 32 * (l4 + 2 ^ 32 * u4) + 2 ^ 96 * (l5 + 2 ^ 32 * u5) +
        2 ^ 160 * (l6 + 2 ^ 32 * u6))) ?_
  rw [VG.Proof.X448.Limbs32.P_eq]
  omega

variable {s : State}

/-- `r + v` into `r`, its carry added to `c`. -/
theorem addc_ok {r v c : Reg} (hrv : r ≠ v) (hr7 : r ≠ .a7) (hc7 : c ≠ .a7) (hcr : c ≠ r) :
    WP isa (.block [.add r r v, .sltu .a7 r v, .add c c .a7]) s fun s' =>
      ((s.gpr c).toNat < 2 ^ 63 → (s'.gpr r).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr r).toNat + (s.gpr v).toNat + 2 ^ 64 * (s.gpr c).toNat) ∧ Keeps [r, .a7, c] s s' := by
  rw [show ([.add r r v, .sltu .a7 r v, .add c c .a7] : List Instr) =
    [.add r r v, .sltu .a7 r v] ++ [.add c c .a7] from rfl]
  refine WP.append (addOut_ok hrv hr7) fun s1 ⟨e1, k1⟩ => WP.mono addSmall_ok fun s2 ⟨e2, k2⟩ =>
    ⟨fun hc => ?_, (k1.trans k2).mono fun x hx => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with (h | h) | h <;> simp only [h, true_or, or_true]⟩
  have hc1 : s1.gpr c = s.gpr c := k1.1 _ (by simp [hcr, hc7])
  have hr2 : s2.gpr r = s1.gpr r := k2.1 _ (by simp [Ne.symm hcr])
  have := (s1.gpr r).isLt
  have h7 : (s1.gpr .a7).toNat ≤ 1 := by have := (s.gpr r).isLt; have := (s.gpr v).isLt; omega
  rw [hc1] at e2
  rw [hr2, e2 (by omega)]
  omega

/-- The carry into word `k` of the reduction (none for word 0). -/
def cv (k : Nat) (s : State) : Nat := if k = 0 then 0 else (s.gpr (cr (k + 1))).toNat

/-- The words in `w 0`, `w 1`, …. -/
abbrev regsV (s : State) : Nat → Nat := fun c => (s.gpr (w c)).toNat

/-- Before word `k` of the reduction, from `sp` (the product at `ACC`): the
words below `k` and the carry the first `k` words of `redT`. -/
structure RedInv (b : Addr) (sp : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 sp s
  mem : s.mem = sp.mem
  val : colsV (regsV s) k + (2 ^ 64) ^ k * cv k s =
    colsV (redT fun i => dw sp.mem b (ACC + 8 * i)) k
  cy : cv k s ≤ 4

theorem red_regs : ∀ k < 7, w k ≠ .a7 ∧ w k ≠ .t0 ∧ cr k ≠ .a7 ∧ cr k ≠ .t0 ∧ cr k ≠ w k ∧
    cr (k + 1) ≠ w k ∧ cr (k + 1) ≠ cr k ∧ cr (k + 1) ≠ .a7 ∧ cr (k + 1) ≠ .t0 ∧ cr (k + 2) = cr k ∧
    w k ∈ clob64 ∧ cr k ∈ clob64 := by decide

theorem red_below' : ∀ k ∈ List.range 7, ∀ c ∈ List.range k,
    w c ≠ w k ∧ w c ≠ cr k ∧ w c ≠ .a7 ∧ w c ≠ .t0 := by decide

theorem red_below {k c : Nat} (hk : k < 7) (hc : c < k) :
    w c ≠ w k ∧ w c ≠ cr k ∧ w c ≠ .a7 ∧ w c ≠ .t0 :=
  red_below' k (List.mem_range.mpr hk) c (List.mem_range.mpr hc)

/-- What the middle of word `k` adds: `H_k` again for `k ≥ 4`, `H₃`'s upper half for `k = 3`. -/
def hmv (k h : Nat) : Nat := (if 4 ≤ k then h else 0) + (if k = 3 then 2 ^ 32 * (h / 2 ^ 32) else 0)

theorem mid_ok {k : Nat} (hk : k < 7) :
    WP isa (.block ((if 4 ≤ k then [.add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7]
        else []) ++
      (if k = 3 then [.shift .srl .d .a7 .a7 32, .shift .sll .d .a7 .a7 32, .add (w k) (w k) .a7,
        .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] else []))) s fun s' =>
      ((s.gpr (cr k)).toNat < 2 ^ 62 →
        (s'.gpr (w k)).toNat + 2 ^ 64 * (s'.gpr (cr k)).toNat =
          (s.gpr (w k)).toNat + 2 ^ 64 * (s.gpr (cr k)).toNat + hmv k (s.gpr .a7).toNat) ∧
      Keeps [w k, .a7, cr k] s s' := by
  obtain ⟨h7, h0, c7, c0, cw, -⟩ := red_regs k hk
  by_cases h4 : 4 ≤ k
  · rw [ite_eq_left h4, ite_eq_right (show ¬k = 3 by omega), List.append_nil]
    refine WP.mono (addc_ok (Ne.symm h7 |>.symm) h7 c7 cw) fun s' ⟨e, k'⟩ => ⟨fun hc => ?_, k'⟩
    rw [e (by omega), hmv, ite_eq_left h4, ite_eq_right (show ¬k = 3 by omega)]; omega
  · rw [ite_eq_right h4, List.nil_append]
    by_cases h3 : k = 3
    · subst h3
      rw [ite_eq_left rfl]
      refine wp_srl (by decide) fun s1 u1 => wp_sll (by decide) fun s2 u2 => ?_
      refine WP.mono (addc_ok (by decide) (by decide) (by decide) (by decide)) fun s' ⟨e, k'⟩ =>
        ⟨fun hc => ?_, ((Keeps.rest_mono_of_upd u1).trans ((Keeps.rest_mono_of_upd u2).trans k')).mono
          (by decide)⟩
      have ew : s2.gpr (w 3) = s.gpr (w 3) := by rw [u2.other _ (by decide), u1.other _ (by decide)]
      have ec : s2.gpr (cr 3) = s.gpr (cr 3) := by rw [u2.other _ (by decide), u1.other _ (by decide)]
      have e7 : (s2.gpr .a7).toNat = 2 ^ 32 * ((s.gpr .a7).toNat / 2 ^ 32) := by
        rw [u2.gpr, u1.gpr, toNat_shl, toNat_shr]
        have := (s.gpr .a7).isLt
        omega
      rw [ec] at e
      rw [e (by omega), ew, e7, hmv]
      simp only [h4, ite_false, ite_true, Nat.zero_add]
      omega
    · rw [ite_eq_right h3]
      refine WP.block_nil ⟨fun _ => ?_, Keeps.refl _ _⟩
      simp [hmv, h4, h3]

theorem colsV_congr {f g : Nat → Nat} : ∀ {k}, (∀ c < k, f c = g c) → colsV f k = colsV g k
  | 0, _ => rfl
  | k + 1, h => by rw [colsV, colsV, colsV_congr fun c hc => h c (by omega), h k (by omega)]

theorem hmv_eq (Pw : Nat → Nat) (k : Nat) :
    hmv k (Pw (7 + k)) = (if 4 ≤ k then Pw (7 + k) else 0) +
      (if k = 3 then 2 ^ 32 * (Pw 10 / 2 ^ 32) else 0) := by
  unfold hmv
  by_cases h3 : k = 3
  · subst h3; rfl
  · simp only [h3, ite_false]

section
variable {b : Addr}


/-- The end of word `k`: its value and carry make the invariant for `k + 1`. -/
theorem redFinish {sp : State} {k : Nat} (hk : k < 7) {s s' : State} (h : RedInv b sp k s)
    (hkp : Keeps [w k, .a7, .t0, cr k] s s')
    (hv : (s'.gpr (w k)).toNat + 2 ^ 64 * (s'.gpr (cr k)).toNat =
      redT (fun i => dw sp.mem b (ACC + 8 * i)) k + cv k s) :
    RedInv b sp (k + 1) s' := by
  obtain ⟨h7, h0, c7, c0, cw, dw', dc, d7, d0, c2, wc, cc⟩ := red_regs k hk
  have hr : Rest clob64 s s' := Rest.mono (Keeps.rest hkp) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [wc, by decide, by decide, cc]
  have hwc : ∀ c < k, s'.gpr (w c) = s.gpr (w c) := fun c hc => by
    obtain ⟨n1, n2, n3, n4⟩ := red_below hk hc
    exact hkp.1 _ (by simp [n1, n2, n3, n4])
  have hcv : cv (k + 1) s' = (s'.gpr (cr k)).toNat := by
    simp only [cv, show k + 1 ≠ 0 by omega, ite_false, show k + 1 + 1 = k + 2 by omega, c2]
  have hb := (s'.gpr (w k)).isLt
  have hT : redT (fun i => dw sp.mem b (ACC + 8 * i)) k < 4 * 2 ^ 64 := by
    have l := fun j => dw_lt sp.mem b (ACC + 8 * j)
    have := l k; have := l (7 + k); have := l 10
    have := l (7 + (k + 3) % 7); have := l (7 + (k + 4) % 7)
    simp only [redT]
    split <;> split <;> omega
  have hcy := h.cy
  refine ⟨h.ctx.of_rest hr (by decide), h.rest.trans hr, by rw [hkp.2.1, h.mem], ?_, ?_⟩
  · rw [hcv, colsV, colsV, colsV_congr (g := regsV s) fun c hc => by simp only [regsV, hwc c hc],
      ← h.val, Nat.pow_succ (n := 2 ^ 64)]
    simp only [regsV] at hv ⊢
    generalize (2 ^ 64) ^ k = K
    generalize colsV (fun c => (s.gpr (w c)).toNat) k = A
    generalize (s'.gpr (w k)).toNat = a at hv
    generalize (s'.gpr (cr k)).toNat = c at hv
    generalize cv k s = d at hv
    generalize redT (fun i => dw sp.mem b (ACC + 8 * i)) k = t at hv
    have : K * a + K * 2 ^ 64 * c = K * (t + d) := by rw [Nat.mul_assoc, ← Nat.mul_add, hv]
    rw [Nat.mul_add] at this
    omega
  · rw [hcv]; omega

theorem redStep_ok {sp : State} {k : Nat} (hk : k < 7) (h : RedInv b sp k s) :
    WP isa (.block (redStep k (cr (k + 1)) (cr k))) s (RedInv b sp (k + 1)) := by
  have hA := ACC_eq
  obtain ⟨h7, h0, c7, c0, cw, dw', dc, d7, d0, c2, wc, cc⟩ := red_regs k hk
  have hc := h.ctx
  have e : redStep k (cr (k + 1)) (cr k) = .load .d (w k) .a3 (ACC + 8 * k) ::
      .load .d .a7 .a3 (ACC + 56 + 8 * k) :: ([.add (w k) (w k) .a7, .sltu (cr k) (w k) .a7] ++
      (((if 4 ≤ k then [.add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] else []) ++
        (if k = 3 then [.shift .srl .d .a7 .a7 32, .shift .sll .d .a7 .a7 32, .add (w k) (w k) .a7,
          .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] else [])) ++
      (.load .d .a7 .a3 (ACC + 56 + 8 * ((k + 3) % 7)) :: .shift .srl .d .a7 .a7 32 ::
        .load .d .t0 .a3 (ACC + 56 + 8 * ((k + 4) % 7)) :: .shift .sll .d .t0 .t0 32 ::
        .logic .or .a7 .a7 .t0 :: ([.add (w k) (w k) .a7, .sltu .a7 (w k) .a7, .add (cr k) (cr k) .a7] ++
        (if 0 < k then [.add (w k) (w k) (cr (k + 1)), .sltu .a7 (w k) (cr (k + 1)),
          .add (cr k) (cr k) .a7] else []))))) := by
    simp only [redStep, List.cons_append, List.nil_append, List.append_assoc]
  rw [e]
  have hPw : ∀ j, j < 14 → ∀ (t : State), t.mem = sp.mem →
      (t.mem.readW (b + BitVec.ofNat 64 (ACC + 8 * j)) 64).toNat = dw sp.mem b (ACC + 8 * j) :=
    fun _ _ t ht => by rw [ht]; rfl
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest wc) (by decide)
  refine ld_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := clob64) (by decide)) (by decide)
  refine WP.append (addOut_ok h7 (Ne.symm cw)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (mid_ok hk) fun s4 ⟨e4, k4⟩ => ?_
  have m3 : ∀ r ∈ [w k, .a7, cr k], r ∈ clob64 := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [wc, by decide, cc]
  have m2 : ∀ r ∈ [w k, cr k], r ∈ clob64 := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [wc, cc]
  have hr4 : Rest clob64 s s4 := (u1.rest wc).trans ((u2.rest (by decide)).trans
    ((Rest.mono (Keeps.rest k3) m2).trans (Rest.mono (Keeps.rest k4) m3)))
  have hm4 : s4.mem = sp.mem := by rw [k4.2.1, k3.2.1, u2.mem, u1.mem, h.mem]
  have hc4 : Ctx b s4 := hc.of_rest hr4 (by decide)
  refine ld_ok hc4 (by omega) (by omega) fun s5 u5 => wp_srl (by decide) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc4.of_rest ((u5.rest (ws := clob64) (by decide)).trans
    (u6.rest (by decide))) (by decide)
  refine ld_ok hc6 (by omega) (by omega) fun s7 u7 => wp_sll (by decide) fun s8 u8 =>
    wp_or fun s9 u9 => ?_
  refine WP.append (addc_ok h7 h7 c7 cw) fun s10 ⟨e10, k10⟩ => ?_
  -- the values so far
  have v1 : (s1.gpr (w k)).toNat = dw sp.mem b (ACC + 8 * k) := by
    rw [u1.gpr]; exact hPw k (by omega) s h.mem
  have v2 : (s2.gpr .a7).toNat = dw sp.mem b (ACC + 8 * (7 + k)) := by
    rw [u2.gpr, show ACC + 56 + 8 * k = ACC + 8 * (7 + k) by omega]
    exact hPw _ (by omega) s1 (by rw [u1.mem, h.mem])
  rw [u2.other _ h7, v1, v2] at e3
  have a3 : s3.gpr .a7 = s2.gpr .a7 := k3.1 _ (by simp [Ne.symm h7, Ne.symm c7])
  have co2 : s2.gpr (cr k) = s1.gpr (cr k) := u2.other _ c7
  rw [a3, v2] at e4
  have e4 := e4 (by have := (s3.gpr (w k)).isLt; omega)
  have v5 : (s5.gpr .a7).toNat = dw sp.mem b (ACC + 8 * (7 + (k + 3) % 7)) := by
    rw [u5.gpr, show ACC + 56 + 8 * ((k + 3) % 7) = ACC + 8 * (7 + (k + 3) % 7) by omega]
    exact hPw _ (by omega) s4 hm4
  have v7 : (s7.gpr .t0).toNat = dw sp.mem b (ACC + 8 * (7 + (k + 4) % 7)) := by
    rw [u7.gpr, show ACC + 56 + 8 * ((k + 4) % 7) = ACC + 8 * (7 + (k + 4) % 7) by omega]
    exact hPw _ (by omega) s6 (by rw [u6.mem, u5.mem, hm4])
  have v9 : (s9.gpr .a7).toNat = dw sp.mem b (ACC + 8 * (7 + (k + 3) % 7)) / 2 ^ 32 +
      2 ^ 32 * (dw sp.mem b (ACC + 8 * (7 + (k + 4) % 7)) % 2 ^ 32) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), u7.other _ (by decide), u6.gpr, rot_or, ← v7, ← v5]
  have w9 : s9.gpr (w k) = s4.gpr (w k) := by
    rw [u9.other _ h7, u8.other _ h0, u7.other _ h0, u6.other _ h7, u5.other _ h7]
  have c9 : s9.gpr (cr k) = s4.gpr (cr k) := by
    rw [u9.other _ c7, u8.other _ c0, u7.other _ c0, u6.other _ c7, u5.other _ c7]
  rw [w9, c9, v9] at e10
  have hmb : hmv k (dw sp.mem b (ACC + 8 * (7 + k))) < 2 ^ 64 := by
    have := dw_lt sp.mem b (ACC + 8 * (7 + k))
    unfold hmv; split <;> split <;> omega
  have hco4 : (s4.gpr (cr k)).toNat ≤ 2 := by
    have := (s4.gpr (w k)).isLt; have := (s3.gpr (w k)).isLt
    have := dw_lt sp.mem b (ACC + 8 * k); have := dw_lt sp.mem b (ACC + 8 * (7 + k))
    omega
  have e10 := e10 (by omega)
  have kp10 : Keeps [w k, .a7, .t0, cr k] s s10 := by
    have := ((((((((((Keeps.rest_mono_of_upd u1).trans (Keeps.rest_mono_of_upd u2)).trans k3).trans
      k4).trans (Keeps.rest_mono_of_upd u5)).trans (Keeps.rest_mono_of_upd u6)).trans
      (Keeps.rest_mono_of_upd u7)).trans (Keeps.rest_mono_of_upd u8)).trans
      (Keeps.rest_mono_of_upd u9)).trans k10)
    refine this.mono fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    grind
  have hT := hmv_eq (fun i => dw sp.mem b (ACC + 8 * i)) k
  rw [hT] at e4
  by_cases k0 : k = 0
  · subst k0
    rw [ite_eq_right (Nat.lt_irrefl 0)]
    refine WP.block_nil (redFinish hk h kp10 ?_)
    simp only [cv, redT, Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte] at e4 ⊢
    omega
  · rw [ite_eq_left (Nat.pos_of_ne_zero k0)]
    refine WP.mono (addc_ok (Ne.symm dw') h7 c7 cw) fun s11 ⟨e11, k11⟩ => redFinish hk h
      ((kp10.trans k11).mono fun r hr => ?_) ?_
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      grind
    · have ci : s10.gpr (cr (k + 1)) = s.gpr (cr (k + 1)) := kp10.1 _ (by simp [dw', d7, d0, dc])
      rw [ci] at e11
      have hcy := h.cy
      simp only [cv, k0, ite_false] at hcy ⊢
      have hco10 : (s10.gpr (cr k)).toNat ≤ 3 := by
        have := (s10.gpr (w k)).isLt; have := (s4.gpr (w k)).isLt
        have := dw_lt sp.mem b (ACC + 8 * (7 + (k + 3) % 7))
        omega
      have e11 := e11 (by omega)
      simp only [redT]
      omega

theorem reds_ok {sp : State} : ∀ n ≤ 7, ∀ s, RedInv b sp 0 s →
    WP isa (.block ((List.range n).flatMap fun k => redStep k (cr (k + 1)) (cr k))) s (RedInv b sp n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (reds_ok n (by omega) s h) fun s1 h1 => redStep_ok (by omega) h1

/-- `w 0`, …, `w (n - 1)` stored at `[o]`. -/
theorem sts_ok {o : Nat} (ho : o + 56 ≤ 2048) (ho8 : o % 8 = 0) :
    ∀ n ≤ 7, ∀ s, Ctx b s →
      WP isa (.block ((List.range n).map fun i => .store .d (w i) .a3 (o + 8 * i))) s fun s' =>
        (∀ i < n, dw s'.mem b (o + 8 * i) = (s.gpr (w i)).toNat) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn, s, hc => by
    rw [List.range_succ, List.map_append]
    refine WP.append (sts_ok ho ho8 n (by omega) s hc) fun s1 ⟨h1, g1, r1, w1, p1, f1⟩ => ?_
    have hc1 : Ctx b s1 := ⟨by rw [g1, hc.a3], hc.al, by rw [w1]; exact hc.wr⟩
    refine sd_ok hc1 (by omega) (by omega) fun s2 u2 => WP.block_nil ⟨fun i hi => ?_,
      by rw [u2.gpr, g1], by rw [u2.rd, r1], by rw [u2.wr, w1], by rw [u2.sp, p1], ?_⟩
    · rw [u2.mem]
      by_cases hin : i = n
      · subst hin; rw [dw_write_self, g1]
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 i (by omega)
    · rw [u2.mem]
      exact f1.writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))

theorem colsV7 (f : Nat → Nat) : colsV f 7 = val7 f := by
  simp only [colsV, val7]
  generalize 2 ^ 64 = B
  grind

theorem B7_eq : ((2 : Nat) ^ 64) ^ 7 = 2 ^ 224 * 2 ^ 224 := by decide

/-- Two folds of a carry `c ≤ 4` leave a number congruent to `v₁ + 2⁴⁴⁸ c`. -/
theorem fold_twice {v1 v2 v3 c c2 c3 : Nat} (hv1 : v1 < 2 ^ 224 * 2 ^ 224) (hv2 : v2 < 2 ^ 224 * 2 ^ 224)
    (hv3 : v3 < 2 ^ 224 * 2 ^ 224) (hc : c ≤ 4)
    (e2 : v2 + 2 ^ 224 * 2 ^ 224 * c2 = v1 + c + 2 ^ 224 * c)
    (e3 : v3 + 2 ^ 224 * 2 ^ 224 * c3 = v2 + c2 + 2 ^ 224 * c2) :
    v3 % P = (v1 + 2 ^ 224 * 2 ^ 224 * c) % P := by
  have hc2 : c2 ≤ 1 := by omega
  have hc3 : c3 = 0 := by omega
  subst hc3
  rw [VG.Proof.X448.Limbs32.fold448, show v1 + (2 ^ 224 + 1) * c = v2 + 2 ^ 224 * 2 ^ 224 * c2 by omega,
    VG.Proof.X448.Limbs32.fold448]
  congr 1
  omega

/-- `reduce o`: the product at `ACC` reduced into `[o]`. -/
theorem reduce_ok {o : Nat} (ho : o + 56 ≤ ACC) (ho8 : o % 8 = 0) {sp : State} (hc : Ctx b sp) :
    WP isa (.block (reduce o)) sp fun s' => Ctx b s' ∧ Rest clob64 sp s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩] sp.mem s'.mem ∧
      Proof.X448.RISCV64.V s'.mem b o % P = accW sp.mem b 14 % P := by
  have hA := ACC_eq
  unfold reduce
  simp only [List.append_assoc]
  have h0 : RedInv b sp 0 sp := ⟨hc, Rest.refl _ _, rfl, by simp [colsV, cv], by simp [cv]⟩
  refine WP.append (reds_ok 7 (Nat.le_refl _) sp h0) fun s1 h1 => ?_
  have hcv : cv 7 s1 = (s1.gpr .a5).toNat := rfl
  have hv1 := h1.val
  rw [hcv, colsV7] at hv1
  have hcy := h1.cy
  rw [hcv] at hcy
  refine WP.append foldR_ok fun s2 ⟨e2, k2⟩ => ?_
  have e2 := e2 (by omega)
  refine WP.append foldR_ok fun s3 ⟨e3, k3⟩ => ?_
  have hc2 : (s2.gpr .a5).toNat ≤ 1 := by
    have := val7_lt (f := fun i => (s1.gpr (w i)).toNat) fun i _ => (s1.gpr (w i)).isLt
    have := val7_lt (f := fun i => (s2.gpr (w i)).toNat) fun i _ => (s2.gpr (w i)).isLt
    simp only [rw7] at e2
    omega
  have e3 := e3 (by omega)
  have hr3 : Rest clob64 sp s3 := h1.rest.trans (Rest.mono (Keeps.rest (k2.trans k3)) (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have hm3 : s3.mem = sp.mem := by rw [k3.2.1, k2.2.1, h1.mem]
  refine WP.mono (sts_ok (by omega) ho8 7 (Nat.le_refl _) s3 hc3) fun s4 ⟨h4, g4, r4, w4, p4, f4⟩ =>
    ⟨⟨by rw [g4, hc3.a3], hc3.al, by rw [w4]; exact hc3.wr⟩, hr3.trans ⟨fun r _ => by rw [g4], r4, w4, p4⟩,
      by rw [← hm3]; exact f4, ?_⟩
  have hV : Proof.X448.RISCV64.V s4.mem b o = rw7 s3 := by
    rw [V_eq]; exact val7_congr fun i hi => h4 i hi
  rw [hV]
  have hmod := redT_mod (fun i => dw sp.mem b (ACC + 8 * i))
  rw [← accW_eq] at hmod
  rw [← hmod, ← hv1]
  have l v := val7_lt (f := fun i => (State.gpr v (w i)).toNat) fun i _ => (v.gpr (w i)).isLt
  simp only [rw7, B7_eq] at e2 e3 ⊢
  rw [B7_eq] at l
  exact fold_twice (l s1) (l s2) (l s3) hcy e2 e3

end

end VG.Proof.X448.RISCV64.R64
