module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: a row of the multiplication

`mulRowD M src` adds `r2 · [src]` (`D` digits, `r2` a digit) to the window of
`D + 2` digits at `r0` (`mulRowD_ok`), when the sum fits it: a word of
`[src]` (two digits, `macD_ok`) an iteration, the carry then into the
window's last two digits.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_mul wp_movw op2_imm op2_reg op2_lsr
  dpVal toNat_add_lt toNat_shr)

/-- Digit `h` of the word in `r7`, times `r2`, plus the carry `r3`, added to
the window's digit at `[r10 + 4h]`. -/
theorem macD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {K h : Nat} (hh : h < 2)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (h10 : s.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 K)
    (hK : K + 4 * h + 4 ≤ size) (hu : (s.gpr .r2).toNat < 2 ^ 16) (hc : (s.gpr .r3).toNat < 2 ^ 16)
    (ht : w32 s.mem base (K + 4 * h) < 2 ^ 16) :
    WP isa (.block (macD h)) s fun u =>
      u.mem = s.mem.writeW (off base (K + 4 * h)) (BitVec.ofNat 32
        (((s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h + w32 s.mem base (K + 4 * h) + (s.gpr .r3).toNat) % 2 ^ 16)) ∧
      (u.gpr .r3).toNat =
        ((s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h + w32 s.mem base (K + 4 * h) + (s.gpr .r3).toNat) / 2 ^ 16 ∧
      Rest [.r3, .r4, .r5] s u := by
  have hd := hdig_lt (s.gpr .r7).toNat h
  have hx := step_lt hu hd ht hc
  have hmul : (s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h < 2 ^ 32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hu) (Nat.le_of_lt_succ hd); omega
  simp only [macD]
  refine wp_half hh h6 fun s₁ u₁ => ?_
  have w₁ := hs.of_upd u₁ (by decide)
  have e10 : s₁.gpr .r10 = s₁.gpr .r12 + BitVec.ofNat 32 K := by
    simp only [u₁.get, reduceCtorEq, ↓reduceIte]; exact h10
  refine wp_ldr (by omega) (w₁.ea e10 (by omega)) (w₁.read (by omega)) fun s₂ u₂ => wp_mla fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have w₅ := (((w₁.of_upd u₂ (by decide)).of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)
  refine wp_str (by omega) (w₅.ea (by simp only [u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; exact e10)
    (by omega)) (w₅.write (by omega)) fun s₆ m₆ => wp_mov (op2_lsr (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have ew : w32 s.mem base (K + 4 * h) = (s.mem.readW (off base (K + 4 * h)) 32).toNat := rfl
  have v4 : (s₄.gpr .r5).toNat =
      (s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h + w32 s.mem base (K + 4 * h) + (s.gpr .r3).toNat := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal]
    rw [u₁.mem]
    have hm : (s.gpr .r2 * BitVec.ofNat 32 (hdig (s.gpr .r7).toNat h)).toNat =
        (s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h := by
      rw [BitVec.toNat_mul, toNat_ofNat_dig, Nat.mod_eq_of_lt hmul]
    refine (toNat_add_eq (toNat_add_eq hm rfl ?_) rfl ?_).trans ?_ <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [u₇.mem, m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    congr 1
    rw [u₅.gpr, dpVal, show s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 by
      simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h6]
    exact and_mask_ofNat v4
  · rw [u₇.gpr, toNat_shr, m₆.gpr, u₅.other .r5 (by decide), v4]
  · exact (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
      ((u₅.rest (by simp)).trans ((m₆.rest _).trans (u₇.rest (by simp))))

/-- The low digits of a number, two on. -/
theorem pval_two (m : Mem) (base : Addr) (d j : Nat) :
    pval m base d (2 * j + 2) = pval m base d (2 * j) + hdig (w32 m base (d + 4 * j)) 0 * 2 ^ (32 * j) +
      hdig (w32 m base (d + 4 * j)) 1 * (2 ^ 16 * 2 ^ (32 * j)) := by
  rw [show 2 * j + 2 = 2 * j + 1 + 1 by omega, pval, pval]
  simp only [pdig, show (2 * j + 1) / 2 = j by omega, show 2 * j / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega,
    show 2 * j % 2 = 0 by omega, show 16 * (2 * j) = 32 * j by omega, show 16 * (2 * j + 1) = 16 + 32 * j by omega,
    Nat.pow_add]

/-- An iteration of a row, as numbers. -/
theorem mac_step {D c T V P u d0 d1 t0 t1 : Nat} (h : D + c * P = T + u * V) :
    D + (u * d0 + t0 + c) % 2 ^ 16 * P + (u * d1 + t1 + (u * d0 + t0 + c) / 2 ^ 16) % 2 ^ 16 * (2 ^ 16 * P) +
      (u * d1 + t1 + (u * d0 + t0 + c) / 2 ^ 16) / 2 ^ 16 * (2 ^ 32 * P) =
      T + t0 * P + t1 * (2 ^ 16 * P) + u * (V + d0 * P + d1 * (2 ^ 16 * P)) := by
  have e0 := Nat.mod_add_div (u * d0 + t0 + c) (2 ^ 16)
  have e1 := Nat.mod_add_div (u * d1 + t1 + (u * d0 + t0 + c) / 2 ^ 16) (2 ^ 16)
  generalize (u * d0 + t0 + c) % 2 ^ 16 = a0 at *
  generalize (u * d0 + t0 + c) / 2 ^ 16 = q0 at *
  generalize (u * d1 + t1 + q0) % 2 ^ 16 = a1 at *
  generalize (u * d1 + t1 + q0) / 2 ^ 16 = q1 at *
  grind

/-- The carry into the window's last two digits, as numbers. -/
theorem carry_val {Du c P Ds V tD tD1 : Nat} (h : Du + c * P = Ds + V) :
    Du + (tD + c) % 2 ^ 16 * P + (tD1 + (tD + c) / 2 ^ 16) * (2 ^ 16 * P) =
      Ds + tD * P + tD1 * (2 ^ 16 * P) + V := by
  have e := Nat.mod_add_div (tD + c) (2 ^ 16)
  generalize (tD + c) % 2 ^ 16 = a at *
  generalize (tD + c) / 2 ^ 16 = q at *
  grind

/-- The invariant of a row's loop after `j` words of `[src]`. -/
structure RowInv (s : State) (base : Addr) (size w src : Nat) (j : Nat) (u : State) : Prop where
  ws : Ws u base size
  rest : Rest [.r3, .r4, .r5, .r7, .r8, .r9, .r10] s u
  r3 : (u.gpr .r3).toNat < 2 ^ 16
  r10 : u.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 w + BitVec.ofNat 32 (8 * j)
  val : dval u.mem base w (2 * j) + (u.gpr .r3).toNat * 2 ^ (32 * j) =
    dval s.mem base w (2 * j) + (s.gpr .r2).toNat * pval s.mem base src (2 * j)
  digs : Digs u.mem base w (2 * j)
  out : Outside base w (8 * j) s.mem u.mem

theorem RowInv.fupd {s : State} {base : Addr} {size w src j : Nat} {u u' : State}
    (h : RowInv s base size w src j u) (f : Fupd u u') : RowInv s base size w src j u' :=
  ⟨h.ws.of_fupd f, h.rest.trans (f.rest _), by rw [f.gpr]; exact h.r3, by rw [f.gpr]; exact h.r10,
    by rw [f.gpr, f.mem]; exact h.val, by rw [f.mem]; exact h.digs, by rw [f.mem]; exact h.out⟩

/-- The window at `r0 = r12 + w` `+= r2 · [src]` (`D` digits), when the sum
fits its `D + 2` digits. -/
theorem mulRowD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src w : Nat}
    (hn : 0 < M.n) (h0 : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 w) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hu : (s.gpr .r2).toNat < 2 ^ 16) (hsrc : src + 4 * words M ≤ size) (h16 : src + 4 * words M < 2 ^ 16)
    (hw : w + 4 * digits M + 8 ≤ size) (hsep : src + 4 * words M ≤ w ∨ w + 4 * digits M + 8 ≤ src)
    (hd : Digs s.mem base w (digits M + 2))
    (hlt : dval s.mem base w (digits M + 2) + (s.gpr .r2).toNat * pval s.mem base src (digits M) <
      2 ^ (16 * (digits M + 2))) :
    WP isa (mulRowD M src) s fun u => Ws u base size ∧ Outside base w (4 * digits M + 8) s.mem u.mem ∧
      dval u.mem base w (digits M + 2) = dval s.mem base w (digits M + 2) +
        (s.gpr .r2).toNat * pval s.mem base src (digits M) ∧
      Digs u.mem base w (digits M + 2) ∧ Rest [.r3, .r4, .r5, .r7, .r8, .r9, .r10] s u := by
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega
  rw [hD] at hw hsep hd hlt ⊢
  rw [hW] at hsrc h16 hsep
  have hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega
  unfold mulRowD
  rw [hW]
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_ptr (d := .r8) (by decide) (by omega) fun s₃ u₃ => wp_ptr (d := .r9) (by decide) (by omega) fun t u₄ =>
    WP.block_nil ?_)
  have R : Rest [.r3, .r4, .r5, .r7, .r8, .r9, .r10] s t := (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    (u₃.rest (by decide))).trans (u₄.rest (by decide))
  have mt : t.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have I0 : RowInv s base size w src 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; decide
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, h0]
      exact (BitVec.add_zero _).symm
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; rfl
    · rw [mt]; exact Outside.refl _ _ _ _
  have p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 src := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 src + BitVec.ofNat 32 (4 * W) := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
  clear u₁ u₂ u₃ u₄ mt R
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 src) (step := 4) (k := W)
    (RowInv s base size w src) (by decide) hW0 (by omega) (fun _ _ _ h f => h.fupd f) I0 p8 p9 ?_
    fun u I _ => ?_)
  · intro j hj u I pu p9u
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    have e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    have xs : w32 u.mem base (src + 4 * j + 0) = w32 s.mem base (src + 4 * j) := I.out.w32 (by omega) (by omega)
    have x0 : w32 u.mem base (w + 8 * j) = w32 s.mem base (w + 8 * j) := I.out.w32 (by omega) (by omega)
    have x1 : w32 u.mem base (w + 8 * j + 4) = w32 s.mem base (w + 8 * j + 4) := I.out.w32 (by omega) (by omega)
    have t0 : w32 s.mem base (w + 8 * j) < 2 ^ 16 := by
      have := hd (2 * j) (by omega); rwa [show w + 4 * (2 * j) = w + 8 * j by omega] at this
    have t1 : w32 s.mem base (w + 8 * j + 4) < 2 ^ 16 := by
      have := hd (2 * j + 1) (by omega); rwa [show w + 4 * (2 * j + 1) = w + 8 * j + 4 by omega] at this
    have g6 : u.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [I.rest.gpr _ (by decide)]; exact h6
    have g2 : u.gpr .r2 = s.gpr .r2 := I.rest.gpr _ (by decide)
    refine wp_ldr (by decide) (I.ws.ea (K := src + 4 * j) (at_ptr pu e12) (by omega))
      (I.ws.read (d := src + 4 * j + 0) (n := 4) (by omega)) fun u₁ v₁ => ?_
    have w₁ := I.ws.of_upd v₁ (by decide)
    have e10 : u₁.gpr .r10 = u₁.gpr .r12 + BitVec.ofNat 32 (w + 8 * j) := by
      rw [v₁.other .r10 (by decide), v₁.other .r12 (by decide)]; exact at_ptr I.r10 e12
    refine VG.Proof.X25519.Arm.WP.append (macD_ok w₁ (h := 0) (by decide) (by rw [v₁.other .r6 (by decide)]; exact g6)
      e10 (by omega) (by rw [v₁.other .r2 (by decide), g2]; exact hu) (by rw [v₁.other .r3 (by decide)]; exact I.r3)
      (by rw [v₁.mem, Nat.mul_zero, Nat.add_zero, x0]; exact t0)) fun u₂ ⟨M₂, C₂, R₂⟩ => ?_
    have w₂ := w₁.of_rest R₂ (by decide)
    have hd0 := hdig_lt (u₁.gpr .r7).toNat 0
    have := I.r3
    have hx := step_lt (u := (u₁.gpr .r2).toNat) (by rw [v₁.other .r2 (by decide), g2]; exact hu) hd0
      (t := w32 u₁.mem base (w + 8 * j + 4 * 0)) (by rw [v₁.mem, Nat.mul_zero, Nat.add_zero, x0]; exact t0)
      (c := (u₁.gpr .r3).toNat) (by rw [v₁.other .r3 (by decide)]; exact I.r3)
    refine VG.Proof.X25519.Arm.WP.append (macD_ok w₂ (K := w + 8 * j) (h := 1) (by decide)
      (by rw [R₂.gpr _ (by decide), v₁.other .r6 (by decide)]; exact g6)
      (by rw [R₂.gpr _ (by decide), R₂.gpr _ (by decide)]; exact e10) (by omega)
      (by rw [R₂.gpr _ (by decide), v₁.other .r2 (by decide), g2]; exact hu)
      (by rw [C₂]; exact Nat.div_lt_of_lt_mul (by omega))
      (by rw [M₂, Nat.mul_one, w32_write_ne (size := size) hnw (by omega) (by omega) (by omega), v₁.mem, x1]; exact t1))
      fun u₃ ⟨M₃, C₃, R₃⟩ => ?_
    refine wp_bump (by decide) fun u₄ v₄ => wp_bump (by decide) fun u₅ v₅ => WP.block_nil ?_
    rw [R₂.gpr .r2 (by decide), R₂.gpr .r7 (by decide), C₂, M₂, Nat.mul_one, Nat.mul_zero, Nat.add_zero,
      w32_write_ne (size := size) hnw (by omega) (by omega) (by omega)] at M₃ C₃
    have r7₁ : (u₁.gpr .r7).toNat = w32 s.mem base (src + 4 * j) := by rw [v₁.gpr]; exact xs
    rw [v₁.mem, x0, x1, v₁.other .r2 (by decide), v₁.other .r3 (by decide), g2, r7₁] at M₃ C₃
    have m₅ : u₅.mem = u₃.mem := by rw [v₅.mem, v₄.mem]
    obtain ⟨d0, d1, O⟩ := pair_writes (m := u.mem) (base := base) (Q := w + 8 * j) (by omega) _ _
    rw [← M₃] at d0 d1 O
    rw [toNat_ofNat_mod16] at d0 d1
    have c₅ : u₅.gpr .r3 = u₃.gpr .r3 := by simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
    have hy0 := hdig_lt (w32 s.mem base (src + 4 * j)) 0
    have hy1 := hdig_lt (w32 s.mem base (src + 4 * j)) 1
    have hx2 := step_lt hu hy1 t1 (c := ((s.gpr .r2).toNat * hdig (w32 s.mem base (src + 4 * j)) 0 +
      w32 s.mem base (w + 8 * j) + (u.gpr .r3).toNat) / 2 ^ 16) (Nat.div_lt_of_lt_mul (by
        have := step_lt hu hy0 t0 I.r3; omega))
    refine ⟨⟨(((w₂.of_rest R₃ (by decide)).of_upd v₄ (by decide)).of_upd v₅ (by decide)),
      I.rest.trans ((((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans
        ((v₄.rest (by decide)).trans (v₅.rest (by decide)))), ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [c₅, C₃]; exact Nat.div_lt_of_lt_mul (by omega)
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r10 (by decide), R₂.gpr .r10 (by decide), v₁.other .r10 (by decide)]
      rw [I.r10, Offset.add_add, Offset.add_add, Offset.add_add, show 8 * (j + 1) = 8 * j + 8 by omega]
    · rw [m₅, c₅, C₃, show 2 * (j + 1) = 2 * j + 2 by omega, dval_two, d0, d1, O.dval (by omega) (by omega),
        show 32 * (j + 1) = 32 + 32 * j by omega, Nat.pow_add, pval_two, dval_two]
      exact mac_step I.val
    · rw [m₅, show 2 * (j + 1) = 2 * j + 2 by omega]
      exact digs_two (by omega) O I.digs (by rw [d0]; omega) (by rw [d1]; omega)
    · rw [m₅]
      exact (I.out.mono (by omega) (by omega)).trans (O.mono (by omega) (by omega))
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r8 (by decide), R₂.gpr .r8 (by decide), v₁.other .r8 (by decide)]
      exact ptr_step pu
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r9 (by decide), R₂.gpr .r9 (by decide), v₁.other .r9 (by decide)]
      exact p9u
  · have e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    have e10 : u.gpr .r10 = u.gpr .r12 + BitVec.ofNat 32 (w + 8 * W) := at_ptr I.r10 e12
    have x0 : w32 u.mem base (w + 8 * W) = w32 s.mem base (w + 8 * W) := I.out.w32 (by omega) (by omega)
    have x1 : w32 u.mem base (w + 8 * W + 4) = w32 s.mem base (w + 8 * W + 4) := I.out.w32 (by omega) (by omega)
    have t0 : w32 s.mem base (w + 8 * W) < 2 ^ 16 := by
      have := hd (2 * W) (by omega); rwa [show w + 4 * (2 * W) = w + 8 * W by omega] at this
    have t1 : w32 s.mem base (w + 8 * W + 4) < 2 ^ 16 := by
      have := hd (2 * W + 1) (by omega); rwa [show w + 4 * (2 * W + 1) = w + 8 * W + 4 by omega] at this
    have g6 : u.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [I.rest.gpr _ (by decide)]; exact h6
    have := I.r3
    refine wp_ldr (by decide) (I.ws.ea (d := 0) e10 (by omega)) (I.ws.read (d := w + 8 * W + 0) (n := 4) (by omega))
      fun u₁ v₁ => wp_dp (op2_reg _ _) fun u₂ v₂ => wp_dp (op2_reg _ _) fun u₃ v₃ => ?_
    have w₃ := ((I.ws.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)
    have e10₃ : u₃.gpr .r10 = u₃.gpr .r12 + BitVec.ofNat 32 (w + 8 * W) := by
      simp only [v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact e10
    refine wp_str (by decide) (w₃.ea (d := 0) e10₃ (by omega)) (w₃.write (d := w + 8 * W + 0) (n := 4) (by omega))
      fun u₄ m₄ => ?_
    have w₄ := w₃.of_mupd m₄
    have e10₄ : u₄.gpr .r10 = u₄.gpr .r12 + BitVec.ofNat 32 (w + 8 * W) := by rw [m₄.gpr]; exact e10₃
    refine wp_ldr (by decide) (w₄.ea (d := 4) e10₄ (by omega)) (w₄.read (d := w + 8 * W + 4) (n := 4) (by omega))
      fun u₅ v₅ => wp_dp (op2_lsr (by decide)) fun u₆ v₆ => ?_
    have w₆ := (w₄.of_upd v₅ (by decide)).of_upd v₆ (by decide)
    refine wp_str (by decide) (w₆.ea (d := 4)
      (by simp only [v₆.get, v₅.get, m₄.gpr, reduceCtorEq, ↓reduceIte]; exact e10₃) (by omega))
      (w₆.write (d := w + 8 * W + 4) (n := 4) (by omega)) fun u₇ m₇ => WP.block_nil ?_
    have ew : (u.mem.readW (off base (w + 8 * W)) 32).toNat = w32 s.mem base (w + 8 * W) := x0
    have r5₂ : (u₂.gpr .r5).toNat = w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat := by
      simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte, dpVal, Nat.add_zero]
      rw [toNat_add_lt (by rw [ew]; omega), ew]
    have st₁ : u₄.mem = u.mem.writeW (off base (w + 8 * W))
        (BitVec.ofNat 32 ((w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat) % 2 ^ 16)) := by
      rw [m₄.mem, v₃.mem, v₂.mem, v₁.mem, Nat.add_zero]
      congr 1
      rw [v₃.gpr, dpVal, show u₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 by
        simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact g6]
      exact and_mask_ofNat r5₂
    have r7₆ : (u₆.gpr .r7).toNat = w32 s.mem base (w + 8 * W + 4) +
        (w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat) / 2 ^ 16 := by
      have r55 : u₅.gpr .r5 = u₂.gpr .r5 := by simp only [v₅.get, m₄.gpr, v₃.get, reduceCtorEq, ↓reduceIte]
      have r75 : (u₅.gpr .r7).toNat = w32 s.mem base (w + 8 * W + 4) := by
        rw [v₅.gpr, st₁, ← x1]
        exact w32_write_ne (size := size) hnw (by omega) (by omega) (by omega) _
      rw [v₆.gpr, dpVal, toNat_add_lt (by rw [r75, toNat_shr, r55, r5₂]; omega), r75, toNat_shr, r55, r5₂]
    have st : u₇.mem = (u.mem.writeW (off base (w + 8 * W))
        (BitVec.ofNat 32 ((w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat) % 2 ^ 16))).writeW
          (off base (w + 8 * W + 4)) (u₆.gpr .r7) := by
      rw [m₇.mem, v₆.mem, v₅.mem, st₁]
    obtain ⟨d0, d1, O⟩ := pair_writes (m := u.mem) (base := base) (Q := w + 8 * W) (by omega) _ _
    rw [← st] at d0 d1 O
    rw [toNat_ofNat_mod16] at d0
    rw [r7₆] at d1
    have V : dval u₇.mem base w (2 * W + 2) = dval s.mem base w (2 * W + 2) +
        (s.gpr .r2).toNat * pval s.mem base src (2 * W) := by
      rw [dval_two, d0, d1, O.dval (by omega) (by omega), dval_two, carry_val I.val]
    have hP : 0 < 2 ^ (32 * W) := Nat.two_pow_pos _
    refine ⟨w₆.of_mupd m₇, ?_, V, ?_, ?_⟩
    · exact (I.out.mono (by omega) (by omega)).trans (O.mono (by omega) (by omega))
    · refine digs_two (by omega) O I.digs (by rw [d0]; omega) ?_
      have hl := hlt
      rw [← V, dval_two, show 16 * (2 * W + 2) = 32 + 32 * W by omega, Nat.pow_add] at hl
      have : w32 u₇.mem base (w + 8 * W + 4) * 2 ^ 16 * 2 ^ (32 * W) < 2 ^ 32 * 2 ^ (32 * W) := by
        rw [Nat.mul_assoc]; omega
      have := Nat.lt_of_mul_lt_mul_right this
      omega
    · exact I.rest.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
        ((v₃.rest (by decide)).trans (m₄.rest _))).trans
        (((v₅.rest (by decide)).trans (v₆.rest (by decide))).trans (m₇.rest _)))

end VG.Proof.Mont.Arm.Dyn
