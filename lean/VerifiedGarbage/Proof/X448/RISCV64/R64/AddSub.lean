module

public import VerifiedGarbage.Proof.X448.RISCV64.R64.Reduce
import VerifiedGarbage.Proof.X448.Limbs32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide

/-!
# X448 on RISC-V, 64-bit limbs: sums and differences

`add o x y` stores at `o` a number congruent to `[x] + [y]` (`add_ok`): the
words of the sum with carries (`addStep_ok`, the invariant `AddInv`), the
carry folded in twice; `sub o x y` one congruent to `[x] - [y]` (`sub_ok`):
the words of the difference with borrows (`subStep_ok`, `SubInv`), the
borrow taken out twice (`unfold_twice`).
-/

-- separate module: its proofs (about 2.5 s) cost more than its imports, and its importer's
-- changes need not re-check them

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64
open VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (P)
open VG.Proof.X448.RISCV64 (V)

theorem as_regs : ∀ k < 7, w k ≠ .a7 ∧ w k ≠ .a5 ∧ w k ≠ .a6 ∧ w k ∈ clob64 := by decide

theorem as_below' : ∀ k ∈ List.range 7, ∀ c ∈ List.range k,
    w c ≠ w k ∧ w c ≠ .a5 ∧ w c ≠ .a6 ∧ w c ≠ .a7 := by decide

theorem as_below {k c : Nat} (hk : k < 7) (hc : c < k) :
    w c ≠ w k ∧ w c ≠ .a5 ∧ w c ≠ .a6 ∧ w c ≠ .a7 :=
  as_below' k (List.mem_range.mpr hk) c (List.mem_range.mpr hc)

/-- Two borrows `c ≤ 1` taken out leave a number congruent to `x - y`. -/
theorem unfold_twice {v0 v1 v2 X Y c c1 c2 : Nat} (hv0 : v0 < 2 ^ 224 * 2 ^ 224)
    (hv1 : v1 < 2 ^ 224 * 2 ^ 224) (hv2 : v2 < 2 ^ 224 * 2 ^ 224) (hc : c ≤ 1)
    (e0 : v0 + Y = X + 2 ^ 224 * 2 ^ 224 * c)
    (e1 : v1 + c + 2 ^ 224 * c = v0 + 2 ^ 224 * 2 ^ 224 * c1)
    (e2 : v2 + c1 + 2 ^ 224 * c1 = v1 + 2 ^ 224 * 2 ^ 224 * c2) :
    (v2 + Y) % P = X % P := by
  have hP := VG.Proof.X448.Limbs32.pow448_eq
  have hc1 : c1 ≤ 1 := by omega
  have hc2 : c2 = 0 := by omega
  subst hc2
  have : v2 + Y = X + P * (c + c1) := by
    rw [Nat.mul_add]
    generalize 2 ^ 224 * 2 ^ 224 = K at *
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with rfl | rfl <;> omega
  rw [this, Nat.add_mul_mod_self_left]

section
variable {b : Addr}

/-- After `k` words of `[x] + [y]`, from `s0`. -/
structure AddInv (b : Addr) (s0 : State) (x y : Nat) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  mem : s.mem = s0.mem
  val : colsV (regsV s) k + (2 ^ 64) ^ k * (s.gpr .a5).toNat =
    colsV (fun i => dw s0.mem b (x + 8 * i)) k + colsV (fun i => dw s0.mem b (y + 8 * i)) k
  cy : (s.gpr .a5).toNat ≤ 1

/-- The end of a word of a sum or a difference: the invariant's value, with
the words below `k` kept. -/
theorem asFinish {s s' : State} {k : Nat} (hk : k < 7)
    (hkp : Keeps [w k, .a5, .a6, .a7] s s') :
    colsV (regsV s') (k + 1) = colsV (regsV s) k + (2 ^ 64) ^ k * (s'.gpr (w k)).toNat := by
  rw [colsV, colsV_congr (g := regsV s) fun c hc => by
    obtain ⟨n1, n2, n3, n4⟩ := as_below hk hc
    simp only [regsV]; rw [hkp.1 _ (by simp [n1, n2, n3, n4])]]

/-- Word 0 of `[x] + [y]`. -/
theorem addStep0_ok {x y : Nat} (hx : x + 56 ≤ 2048) (hx8 : x % 8 = 0) (hy : y + 56 ≤ 2048)
    (hy8 : y % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (addStep x y 0)) s (AddInv b s x y 1) := by
  simp only [addStep, ite_true]
  refine ld_ok hc (by omega) hx8 fun s1 u1 => ?_
  refine ld_ok (hc.of_rest (u1.rest (ws := clob64) (by decide)) (by decide)) (by omega) hy8
    fun s2 u2 => ?_
  refine WP.mono (addOut_ok (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  have hr : Rest clob64 s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    (Rest.mono (Keeps.rest k3) (by decide)))
  have hm : s3.mem = s.mem := by rw [k3.2.1, u2.mem, u1.mem]
  have v1 : (s2.gpr (w 0)).toNat = dw s.mem b (x + 8 * 0) := by
    rw [u2.other _ (by decide), u1.gpr]; rfl
  have v2 : (s2.gpr .a7).toNat = dw s.mem b (y + 8 * 0) := by rw [u2.gpr, u1.mem]; rfl
  rw [v1, v2] at e3
  refine ⟨hc.of_rest hr (by decide), hr, hm, ?_, ?_⟩
  · simp only [colsV, regsV, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one]; omega
  · have := (s3.gpr (w 0)).isLt
    have := dw_lt s.mem b (x + 8 * 0); have := dw_lt s.mem b (y + 8 * 0)
    omega

/-- Word `k > 0` of `[x] + [y]`. -/
theorem addStepS_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ 2048) (hx8 : x % 8 = 0)
    (hy : y + 56 ≤ 2048) (hy8 : y % 8 = 0) {k : Nat} (hk : k < 7) (hk0 : k ≠ 0) {s : State}
    (h : AddInv b s0 x y k s) :
    WP isa (.block (addStep x y k)) s (AddInv b s0 x y (k + 1)) := by
  obtain ⟨h7, h5, h6, wc⟩ := as_regs k hk
  have hc := h.ctx
  simp only [addStep, hk0, ite_false]
  rw [show ∀ (a b c d e f g : Instr), [a, b, c, d, e, f, g] = a :: b :: ([c, d] ++ ([e, f] ++ [g]))
    from fun _ _ _ _ _ _ _ => rfl]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
  refine ld_ok (hc.of_rest (u1.rest wc) (by decide)) (by omega) (by omega) fun s2 u2 => ?_
  refine WP.append (addOut_ok h7 h6) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (addOut_ok h5 h7) fun s4 ⟨e4, k4⟩ => ?_
  refine WP.mono addSmall_ok fun s5 ⟨e5, k5⟩ => ?_
  have kp : Keeps [w k, .a5, .a6, .a7] s s5 :=
    (((((Keeps.rest_mono_of_upd u1).trans (Keeps.rest_mono_of_upd u2)).trans k3).trans k4).trans
      k5).mono fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        grind
  have hr : Rest clob64 s s5 := Rest.mono (Keeps.rest kp) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [wc, by decide, by decide, by decide]
  have v1 : (s2.gpr (w k)).toNat = dw s0.mem b (x + 8 * k) := by
    rw [u2.other _ h7, u1.gpr, h.mem]; rfl
  have v2 : (s2.gpr .a7).toNat = dw s0.mem b (y + 8 * k) := by rw [u2.gpr, u1.mem, h.mem]; rfl
  rw [v1, v2] at e3
  have c3 : s3.gpr .a5 = s.gpr .a5 := by
    rw [k3.1 _ (by simp [Ne.symm h5]), u2.other _ (by decide), u1.other _ (Ne.symm h5)]
  have a3 : s4.gpr .a6 = s3.gpr .a6 := k4.1 _ (by simp [Ne.symm h6])
  rw [c3] at e4
  rw [a3] at e5
  have w5 : s5.gpr (w k) = s4.gpr (w k) := k5.1 _ (by simp [h5])
  have hcy := h.cy
  have := (s3.gpr (w k)).isLt; have := (s4.gpr (w k)).isLt
  have := dw_lt s0.mem b (x + 8 * k); have := dw_lt s0.mem b (y + 8 * k)
  have e5 := e5 (by omega)
  refine ⟨hc.of_rest hr (by decide), h.rest.trans hr, by rw [kp.2.1, h.mem], ?_, by omega⟩
  rw [asFinish hk kp, colsV, colsV, w5, Nat.pow_succ (n := 2 ^ 64)]
  have hv := h.val
  generalize (2 ^ 64) ^ k = K at *
  have : K * (s4.gpr (w k)).toNat + K * 2 ^ 64 * (s5.gpr .a5).toNat =
      K * (dw s0.mem b (x + 8 * k) + dw s0.mem b (y + 8 * k)) + K * (s.gpr .a5).toNat := by
    rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e5]; congr 1; omega
  rw [Nat.mul_add] at this
  omega

/-- The words of `[x] + [y]`. -/
theorem addSteps_ok {x y : Nat} (hx : x + 56 ≤ 2048) (hx8 : x % 8 = 0) (hy : y + 56 ≤ 2048)
    (hy8 : y % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    ∀ n, 1 ≤ n → n ≤ 7 → WP isa (.block ((List.range n).flatMap (addStep x y))) s0 (AddInv b s0 x y n)
  | 0, h, _ => absurd h (by decide)
  | 1, _, _ => by simpa using addStep0_ok hx hx8 hy hy8 hc
  | n + 2, _, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (addSteps_ok hx hx8 hy hy8 hc (n + 1) (by omega) (by omega)) fun s1 h1 =>
      addStepS_ok hx hx8 hy hy8 (by omega) (by omega) h1

/-- After `k` words of `[x] - [y]`, from `s0`. -/
structure SubInv (b : Addr) (s0 : State) (x y : Nat) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob64 s0 s
  mem : s.mem = s0.mem
  val : colsV (regsV s) k + colsV (fun i => dw s0.mem b (y + 8 * i)) k =
    colsV (fun i => dw s0.mem b (x + 8 * i)) k + (2 ^ 64) ^ k * (s.gpr .a5).toNat
  cy : (s.gpr .a5).toNat ≤ 1

/-- Word 0 of `[x] - [y]`. -/
theorem subStep0_ok {x y : Nat} (hx : x + 56 ≤ 2048) (hx8 : x % 8 = 0) (hy : y + 56 ≤ 2048)
    (hy8 : y % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (subStep x y 0)) s (SubInv b s x y 1) := by
  simp only [subStep, ite_true]
  refine ld_ok hc (by omega) hx8 fun s1 u1 => ?_
  refine ld_ok (hc.of_rest (u1.rest (ws := clob64) (by decide)) (by decide)) (by omega) hy8
    fun s2 u2 => ?_
  refine WP.mono (subOut_ok (by decide) (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  have hr : Rest clob64 s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    (Rest.mono (Keeps.rest k3) (by decide)))
  have hm : s3.mem = s.mem := by rw [k3.2.1, u2.mem, u1.mem]
  have v1 : (s2.gpr (w 0)).toNat = dw s.mem b (x + 8 * 0) := by
    rw [u2.other _ (by decide), u1.gpr]; rfl
  have v2 : (s2.gpr .a7).toNat = dw s.mem b (y + 8 * 0) := by rw [u2.gpr, u1.mem]; rfl
  rw [v1, v2] at e3
  refine ⟨hc.of_rest hr (by decide), hr, hm, ?_, ?_⟩
  · simp only [colsV, regsV, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one]; omega
  · have := (s3.gpr (w 0)).isLt
    have := dw_lt s.mem b (x + 8 * 0); have := dw_lt s.mem b (y + 8 * 0)
    omega

/-- Word `k > 0` of `[x] - [y]`. -/
theorem subStepS_ok {s0 : State} {x y : Nat} (hx : x + 56 ≤ 2048) (hx8 : x % 8 = 0)
    (hy : y + 56 ≤ 2048) (hy8 : y % 8 = 0) {k : Nat} (hk : k < 7) (hk0 : k ≠ 0) {s : State}
    (h : SubInv b s0 x y k s) :
    WP isa (.block (subStep x y k)) s (SubInv b s0 x y (k + 1)) := by
  obtain ⟨h7, h5, h6, wc⟩ := as_regs k hk
  have hc := h.ctx
  simp only [subStep, hk0, ite_false]
  rw [show ∀ (a b c d e f g : Instr), [a, b, c, d, e, f, g] = a :: b :: ([c, d] ++ ([e, f] ++ [g]))
    from fun _ _ _ _ _ _ _ => rfl]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => ?_
  refine ld_ok (hc.of_rest (u1.rest wc) (by decide)) (by omega) (by omega) fun s2 u2 => ?_
  refine WP.append (subOut_ok h6 (by decide)) fun s3 ⟨e3, k3⟩ => ?_
  refine WP.append (subOut_ok h7 (by decide)) fun s4 ⟨e4, k4⟩ => ?_
  refine WP.mono addSmall_ok fun s5 ⟨e5, k5⟩ => ?_
  have kp : Keeps [w k, .a5, .a6, .a7] s s5 :=
    (((((Keeps.rest_mono_of_upd u1).trans (Keeps.rest_mono_of_upd u2)).trans k3).trans k4).trans
      k5).mono fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        grind
  have hr : Rest clob64 s s5 := Rest.mono (Keeps.rest kp) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [wc, by decide, by decide, by decide]
  have v1 : (s2.gpr (w k)).toNat = dw s0.mem b (x + 8 * k) := by
    rw [u2.other _ h7, u1.gpr, h.mem]; rfl
  have v2 : (s2.gpr .a7).toNat = dw s0.mem b (y + 8 * k) := by rw [u2.gpr, u1.mem, h.mem]; rfl
  rw [v1, v2] at e3
  have c3 : s3.gpr .a5 = s.gpr .a5 := by
    rw [k3.1 _ (by simp [Ne.symm h5]), u2.other _ (by decide), u1.other _ (Ne.symm h5)]
  have a3 : s4.gpr .a6 = s3.gpr .a6 := k4.1 _ (by simp [Ne.symm h6])
  rw [c3] at e4
  rw [a3] at e5
  have w5 : s5.gpr (w k) = s4.gpr (w k) := k5.1 _ (by simp [h5])
  have hcy := h.cy
  have := (s3.gpr (w k)).isLt; have := (s4.gpr (w k)).isLt
  have := dw_lt s0.mem b (x + 8 * k); have := dw_lt s0.mem b (y + 8 * k)
  have hb : (s3.gpr .a6).toNat + (s4.gpr .a7).toNat ≤ 1 := by omega
  have e5 := e5 (by omega)
  refine ⟨hc.of_rest hr (by decide), h.rest.trans hr, by rw [kp.2.1, h.mem], ?_, by omega⟩
  rw [asFinish hk kp, colsV, colsV, w5, Nat.pow_succ (n := 2 ^ 64)]
  have hv := h.val
  generalize (2 ^ 64) ^ k = K at *
  have : K * (s4.gpr (w k)).toNat + K * dw s0.mem b (y + 8 * k) + K * (s.gpr .a5).toNat =
      K * dw s0.mem b (x + 8 * k) + K * 2 ^ 64 * (s5.gpr .a5).toNat := by
    rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e5]; congr 1; omega
  omega

/-- The words of `[x] - [y]`. -/
theorem subSteps_ok {x y : Nat} (hx : x + 56 ≤ 2048) (hx8 : x % 8 = 0) (hy : y + 56 ≤ 2048)
    (hy8 : y % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    ∀ n, 1 ≤ n → n ≤ 7 → WP isa (.block ((List.range n).flatMap (subStep x y))) s0 (SubInv b s0 x y n)
  | 0, h, _ => absurd h (by decide)
  | 1, _, _ => by simpa using subStep0_ok hx hx8 hy hy8 hc
  | n + 2, _, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (subSteps_ok hx hx8 hy hy8 hc (n + 1) (by omega) (by omega)) fun s1 h1 =>
      subStepS_ok hx hx8 hy hy8 (by omega) (by omega) h1

theorem add_ok {o x y : Nat} (ho : o + 56 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048)
    (ho8 : o % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest clob64 s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x + V s.mem b y) % P := by
  unfold add
  simp only [List.append_assoc]
  refine WP.append (addSteps_ok hx hx8 hy hy8 hc 7 (by decide) (Nat.le_refl _)) fun s1 h1 => ?_
  refine WP.append foldR_ok fun s2 ⟨e2, k2⟩ => ?_
  have hcy := h1.cy
  have e2 := e2 (by omega)
  refine WP.append foldR_ok fun s3 ⟨e3, k3⟩ => ?_
  have l v := val7_lt (f := fun i => (State.gpr v (w i)).toNat) fun i _ => (v.gpr (w i)).isLt
  rw [B7_eq] at l
  simp only [rw7, B7_eq] at e2 e3
  have hc2 : (s2.gpr .a5).toNat ≤ 1 := by have := l s1; have := l s2; omega
  have e3 := e3 (by omega)
  have hr3 : Rest clob64 s s3 := h1.rest.trans (Rest.mono (Keeps.rest (k2.trans k3)) (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have hm3 : s3.mem = s.mem := by rw [k3.2.1, k2.2.1, h1.mem]
  refine WP.mono (sts_ok ho ho8 7 (Nat.le_refl _) s3 hc3) fun s4 ⟨h4, g4, r4, w4, p4, f4⟩ =>
    ⟨hr3.trans ⟨fun r _ => by rw [g4], r4, w4, p4⟩, by rw [← hm3]; exact f4, ?_⟩
  have hV : V s4.mem b o = val7 fun i => (s3.gpr (w i)).toNat := by
    rw [V_eq]; exact val7_congr fun i hi => h4 i hi
  have hv := h1.val
  rw [colsV7, colsV7, colsV7, B7_eq] at hv
  rw [hV, fold_twice (l s1) (l s2) (l s3) (by omega) e2 e3, V_eq, V_eq]
  exact congrArg (· % P) hv

theorem sub_ok {o x y : Nat} (ho : o + 56 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048)
    (ho8 : o % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob64 s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      (V s'.mem b o + V s.mem b y) % P = V s.mem b x % P := by
  unfold sub
  simp only [List.append_assoc]
  refine WP.append (subSteps_ok hx hx8 hy hy8 hc 7 (by decide) (Nat.le_refl _)) fun s1 h1 => ?_
  refine WP.append unfoldR_ok fun s2 ⟨e2, k2⟩ => ?_
  have hcy := h1.cy
  have e2 := e2 (by omega)
  refine WP.append unfoldR_ok fun s3 ⟨e3, k3⟩ => ?_
  have l v := val7_lt (f := fun i => (State.gpr v (w i)).toNat) fun i _ => (v.gpr (w i)).isLt
  rw [B7_eq] at l
  simp only [rw7, B7_eq] at e2 e3
  have hc2 : (s2.gpr .a5).toNat ≤ 1 := by have := l s1; have := l s2; omega
  have e3 := e3 (by omega)
  have hr3 : Rest clob64 s s3 := h1.rest.trans (Rest.mono (Keeps.rest (k2.trans k3)) (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have hm3 : s3.mem = s.mem := by rw [k3.2.1, k2.2.1, h1.mem]
  refine WP.mono (sts_ok ho ho8 7 (Nat.le_refl _) s3 hc3) fun s4 ⟨h4, g4, r4, w4, p4, f4⟩ =>
    ⟨hr3.trans ⟨fun r _ => by rw [g4], r4, w4, p4⟩, by rw [← hm3]; exact f4, ?_⟩
  have hV : V s4.mem b o = val7 fun i => (s3.gpr (w i)).toNat := by
    rw [V_eq]; exact val7_congr fun i hi => h4 i hi
  have hv := h1.val
  rw [colsV7, colsV7, colsV7, B7_eq] at hv
  rw [hV, V_eq, V_eq]
  exact unfold_twice (l s1) (l s2) (l s3) hcy hv e2 e3

end

end VG.Proof.X448.RISCV64.R64
