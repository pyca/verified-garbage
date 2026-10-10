import VerifiedGarbage.Proof.Weierstrass.X86.MontBase
import VerifiedGarbage.Proof.Mont.X86.Row

/-!
# Montgomery arithmetic as functions on x86 (32-bit): a row

A row adds `ecx · Y` to the window of the accumulator at `[ebp + acc]`, for
the `N` words `y_j` of `Y` at `ys j` (`[esi + 4j]`, or immediates): its steps
(`rowSteps_ok`) add it to the window's low `N` words, the carry word in
`ebx`, which the carry adds to words `N` and `N + 1` (`carryUpB_ok`), or to
word `N` with word `N + 1` its carry out, unread (`carryUp1_ok`): `rowG_ok`,
`rowG1_ok`. Row 0 writes the window (`rowZ_ok`), not yet written.
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- The value of the words `y 0 … y (k - 1)`, little-endian. -/
def yVal (y : Nat → BitVec 32) : Nat → Nat
  | 0 => 0
  | k + 1 => yVal y k + 2 ^ (32 * k) * (y k).toNat

theorem yVal_lt (y : Nat → BitVec 32) : ∀ k, yVal y k < 2 ^ (32 * k)
  | 0 => by simp [yVal]
  | k + 1 => by
    have := yVal_lt y k
    have := (y k).isLt
    rw [yVal, pow32_add, show 32 * 1 = 32 from rfl]
    have : 2 ^ (32 * k) * (y k).toNat ≤ 2 ^ (32 * k) * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ (by omega_arith)
    have : 2 ^ (32 * k) * (2 ^ 32 - 1) + 2 ^ (32 * k) = 2 ^ (32 * k) * 2 ^ 32 := by
      rw [Nat.mul_sub_one]; have : 2 ^ (32 * k) ≤ 2 ^ (32 * k) * 2 ^ 32 := Nat.le_mul_of_pos_right _ (by decide)
      omega_arith
    omega_arith

theorem val32_one (m : Mem) (base : Addr) (d : Nat) : val32 m base d 1 = w32 m base d := by
  simp [val32]

/-- The words at a pointer are its number. -/
theorem yVal_val32 (m : Mem) (base : Addr) (p : Nat) :
    ∀ k, yVal (fun j => m.readW (off base (p + 4 * j)) 32) k = val32 m base p k
  | 0 => rfl
  | k + 1 => by rw [yVal, yVal_val32 m base p k, val32_succ]

/-- What a row keeps that the words of its multiplicand may depend on. -/
structure RowKeep (base : Addr) (acc len : Nat) (s t : State) : Prop where
  esi : t.gpr .esi = s.gpr .esi
  ebp : t.gpr .ebp = s.gpr .ebp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : Outside base acc len s.mem t.mem

theorem RowKeep.of {base : Addr} {acc len : Nat} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (h1 : .esi ∉ rs) (h2 : .ebp ∉ rs) (ho : Outside base acc len s.mem t.mem) : RowKeep base acc len s t :=
  ⟨h.1 _ h1, h.1 _ h2, h.2.1, h.2.2, ho⟩

theorem RowKeep.trans {base : Addr} {acc len : Nat} {s t u : State} (h₁ : RowKeep base acc len s t)
    (h₂ : RowKeep base acc len t u) : RowKeep base acc len s u :=
  ⟨h₂.esi.trans h₁.esi, h₂.ebp.trans h₁.ebp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.out.trans h₂.out⟩

/-- The words of a multiplicand: `ys j` reads `y j` in any state the row
reaches. -/
def YsOk (ys : Nat → Src) (y : Nat → BitVec 32) (base : Addr) (acc len N : Nat) (s : State) : Prop :=
  ∀ j < N, ∀ t, RowKeep base acc len s t → readSrc t (ys j) = some (y j)

/-- The steps `0 … k - 1` of a row. -/
def rowSteps (ys : Nat → Src) (acc : Nat) : Nat → List Instr
  | 0 => []
  | 1 => step0G (ys 0) acc
  | k + 2 => rowSteps ys acc (k + 1) ++ stepG (ys (k + 1)) acc (k + 1)

theorem rowSteps_eq (ys : Nat → Src) (acc : Nat) :
    ∀ k, step0G (ys 0) acc ++ stepsG ys acc k = rowSteps ys acc (k + 1)
  | 0 => by simp [stepsG, rowSteps]
  | k + 1 => by rw [stepsG, ← List.append_assoc, rowSteps_eq ys acc k]; rfl

variable {s : State} {base : Addr} {size : Nat}

/-- The window's low `k` words `+= ecx · Y`, the carry word to `ebx`. -/
theorem rowSteps_ok (hb : Bx s base size) {ys : Nat → Src} {y : Nat → BitVec 32} {acc len N : Nat}
    (hY : YsOk ys y base acc len N s) (hlen : ∀ k ≤ N, 4 * k ≤ len) :
    ∀ k, 1 ≤ k → k ≤ N → acc + 4 * k ≤ size →
    WP isa (.block (rowSteps ys acc k)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧
      val32 u.mem base acc k + 2 ^ (32 * k) * (u.gpr .ebx).toNat =
        val32 s.mem base acc k + (s.gpr .ecx).toNat * yVal y k ∧
      Keeps [.eax, .ebx, .edx] s u
  | 0, h, _, _ => absurd h (by decide)
  | 1, _, hN, hacc => by
    have hn := hb.nowrap
    refine WP.mono (step0G_ok hb (hY 0 (by omega_arith) s ⟨rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩)
      (acc := acc) (by omega_arith)) fun u ⟨m, b, K⟩ => ?_
    have W := writeW32_outside s.mem base (d := acc)
      (BitVec.ofNat 32 ((s.gpr .ecx).toNat * (y 0).toNat + w32 s.mem base acc)) (by omega_arith)
    rw [← m] at W
    refine ⟨W, ?_, K⟩
    rw [val32_one, val32_one, show yVal y 1 = (y 0).toNat by simp [yVal], m, w32_write_self,
      BitVec.toNat_ofNat, b, show 32 * 1 = 32 from rfl]
    have hx := Nat.div_add_mod ((s.gpr .ecx).toNat * (y 0).toNat + w32 s.mem base acc) (2 ^ 32)
    omega_arith
  | k + 2, _, hN, hacc => by
    have hn := hb.nowrap
    rw [rowSteps]
    refine WP.block_append (WP.mono (rowSteps_ok hb hY hlen (k + 1) (by omega_arith) (by omega_arith) (by omega_arith))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    have hy := hY (k + 1) (by omega_arith) s₁ (RowKeep.of K₁ (by decide) (by decide)
      (O₁.mono (Nat.le_refl _) (by have := hlen (k + 1) (by omega_arith); omega_arith)))
    refine WP.mono (stepG_ok hb₁ hy (acc := acc) (j := k + 1) (by omega_arith)) fun u ⟨m₂, b₂, K₂⟩ => ?_
    have ecx₁ : s₁.gpr .ecx = s.gpr .ecx := K₁.1 _ (by decide)
    have tk : w32 s₁.mem base (acc + 4 * (k + 1)) = w32 s.mem base (acc + 4 * (k + 1)) :=
      O₁.w32 (by omega_arith) (by omega_arith)
    rw [ecx₁, tk] at m₂ b₂
    have W := writeW32_outside s₁.mem base (d := acc + 4 * (k + 1))
      (BitVec.ofNat 32 ((s.gpr .ecx).toNat * (y (k + 1)).toNat + (s₁.gpr .ebx).toNat +
        w32 s.mem base (acc + 4 * (k + 1)))) (by omega_arith)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_, K₁.trans K₂⟩
    have hlow : val32 u.mem base acc (k + 1) = val32 s₁.mem base acc (k + 1) := W.val32 (by omega_arith) (by omega_arith)
    have htop : w32 u.mem base (acc + 4 * (k + 1)) = ((s.gpr .ecx).toNat * (y (k + 1)).toNat +
        (s₁.gpr .ebx).toNat + w32 s.mem base (acc + 4 * (k + 1))) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    rw [val32_succ u.mem base acc (k + 1), val32_succ s.mem base acc (k + 1), hlow, htop, b₂,
      pow32_succ (k + 1), yVal]
    generalize hxd : (s.gpr .ecx).toNat * (y (k + 1)).toNat + (s₁.gpr .ebx).toNat +
      w32 s.mem base (acc + 4 * (k + 1)) = x at *
    have hx := Nat.div_add_mod x (2 ^ 32)
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

/-- The carry word `ebx` added to the window's words `N` and `N + 1`, when
the sum fits them. -/
theorem carryUpB_ok (hb : Bx s base size) {acc N : Nat} (hN : acc + 4 * N + 8 ≤ size)
    (hlt : val32 s.mem base (acc + 4 * N) 2 + (s.gpr .ebx).toNat < 2 ^ 64) :
    WP isa (.block (carryUp acc N)) s fun u =>
      Outside base (acc + 4 * N) 8 s.mem u.mem ∧
      val32 u.mem base (acc + 4 * N) 2 = val32 s.mem base (acc + 4 * N) 2 + (s.gpr .ebx).toNat ∧
      Keeps [.eax] s u := by
  have hn := hb.nowrap
  simp only [carryUp]
  refine wp_movS (readSrc_bp hb (d := acc + 4 * N) (by omega_arith)) fun s₁ u₁ cf₁ => ?_
  refine wp_addS rfl fun s₂ u₂ c₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := u₁.keeps.widen u₂.keeps
  have hb₂ := hb.of_keeps k₂ (by decide)
  refine wp_storeS (hb₂.ea (d := acc + 4 * N) (by omega_arith)) (hb₂.write (n := 4) (by omega_arith))
    fun s₃ m₃ => ?_
  have k₃ : Keeps [.eax] s s₃ := k₂.trans (m₃.keeps _)
  have hb₃ := hb.of_keeps k₃ (by decide)
  refine wp_movS (readSrc_bp hb₃ (d := acc + 4 * N + 4) (by omega_arith)) fun s₄ u₄ cf₄ => ?_
  refine wp_adcS rfl (by rw [cf₄, m₃.cf]; exact c₂) fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax] s s₅ := (k₃.widen u₄.keeps).widen u₅.keeps
  have hb₅ := hb.of_keeps k₅ (by decide)
  refine wp_storeS (hb₅.ea (d := acc + 4 * N + 4) (by omega_arith)) (hb₅.write (n := 4) (by omega_arith))
    fun s₆ m₆ => WP.block_nil ?_
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hm₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  rw [hm₂] at m₃
  rw [hm₅, m₃.mem] at m₆
  have W₀ := writeW32_outside s.mem base (d := acc + 4 * N) (s₂.gpr .eax) (by omega_arith)
  have W₁ := writeW32_outside (s.mem.writeW (off base (acc + 4 * N)) (s₂.gpr .eax)) base
    (d := acc + 4 * N + 4) (s₅.gpr .eax) (by omega_arith)
  rw [← m₆.mem] at W₁
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega_arith)).trans (W₁.mono (by omega_arith) (by omega_arith)), ?_,
    k₅.trans (m₆.keeps _)⟩
  have a₂ : s₂.gpr .eax = s.mem.readW (off base (acc + 4 * N)) 32 + s.gpr .ebx := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide)]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  have a₅ : s₅.gpr .eax = s₃.mem.readW (off base (acc + 4 * N + 4)) 32 +
      (BitVec.ofBool (decide (2 ^ 32 ≤ (s₁.gpr .eax).toNat + (s₁.gpr .ebx).toNat))).setWidth 32 := by
    rw [u₅.gpr, u₄.gpr, h0]
  have t₁ : w32 s₃.mem base (acc + 4 * N + 4) = w32 s.mem base (acc + 4 * N + 4) := by
    rw [m₃.mem]; exact w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith) _
  rw [u₁.gpr, u₁.other _ (by decide), m₃.mem] at a₅
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [m₆.mem, w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self, w32_write_self,
    a₂, a₅, BitVec.toNat_add, BitVec.toNat_add, ofBool_toNat]
  simp only [val32, Nat.mul_zero, Nat.add_zero] at hlt
  rw [m₃.mem] at t₁
  simp only [w32] at t₁ hlt ⊢
  rw [t₁]
  have := (s.mem.readW (off base (acc + 4 * N)) 32).isLt
  have := (s.gpr .ebx).isLt
  by_cases hc : 2 ^ 32 ≤ (s.mem.readW (off base (acc + 4 * N)) 32).toNat + (s.gpr .ebx).toNat <;>
    simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The carry word `ebx` added to the window's word `N`, whose carry out is
word `N + 1` (its old value unread). -/
theorem carryUp1_ok (hb : Bx s base size) {acc N : Nat} (hN : acc + 4 * N + 8 ≤ size) :
    WP isa (.block (carryUp1 acc N)) s fun u =>
      Outside base (acc + 4 * N) 8 s.mem u.mem ∧
      val32 u.mem base (acc + 4 * N) 2 = w32 s.mem base (acc + 4 * N) + (s.gpr .ebx).toNat ∧
      Keeps [.eax] s u := by
  have hn := hb.nowrap
  simp only [carryUp1]
  refine wp_movS (readSrc_bp hb (d := acc + 4 * N) (by omega_arith)) fun s₁ u₁ cf₁ => ?_
  refine wp_addS rfl fun s₂ u₂ c₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := u₁.keeps.widen u₂.keeps
  have hb₂ := hb.of_keeps k₂ (by decide)
  refine wp_storeS (hb₂.ea (d := acc + 4 * N) (by omega_arith)) (hb₂.write (n := 4) (by omega_arith))
    fun s₃ m₃ => ?_
  refine wp_movS rfl fun s₄ u₄ cf₄ => ?_
  refine wp_adcS rfl (by rw [cf₄, m₃.cf]; exact c₂) fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax] s s₅ := ((k₂.trans (m₃.keeps _)).widen u₄.keeps).widen u₅.keeps
  have hb₅ := hb.of_keeps k₅ (by decide)
  refine wp_storeS (hb₅.ea (d := acc + 4 * N + 4) (by omega_arith)) (hb₅.write (n := 4) (by omega_arith))
    fun s₆ m₆ => WP.block_nil ?_
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hm₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  rw [hm₂] at m₃
  rw [hm₅, m₃.mem] at m₆
  have W₀ := writeW32_outside s.mem base (d := acc + 4 * N) (s₂.gpr .eax) (by omega_arith)
  have W₁ := writeW32_outside (s.mem.writeW (off base (acc + 4 * N)) (s₂.gpr .eax)) base
    (d := acc + 4 * N + 4) (s₅.gpr .eax) (by omega_arith)
  rw [← m₆.mem] at W₁
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega_arith)).trans (W₁.mono (by omega_arith) (by omega_arith)), ?_,
    k₅.trans (m₆.keeps _)⟩
  have a₂ : s₂.gpr .eax = s.mem.readW (off base (acc + 4 * N)) 32 + s.gpr .ebx := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide)]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  have a₅ : s₅.gpr .eax = 0 + 0 +
      (BitVec.ofBool (decide (2 ^ 32 ≤ (s₁.gpr .eax).toNat + (s₁.gpr .ebx).toNat))).setWidth 32 := by
    rw [u₅.gpr, u₄.gpr]
  rw [u₁.gpr, u₁.other _ (by decide)] at a₅
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [m₆.mem, w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self, w32_write_self,
    a₂, a₅, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, ofBool_toNat]
  simp only [w32]
  have := (s.mem.readW (off base (acc + 4 * N)) 32).isLt
  have := (s.gpr .ebx).isLt
  have z : (0 : BitVec 32).toNat = 0 := rfl
  rw [z]
  by_cases hc : 2 ^ 32 ≤ (s.mem.readW (off base (acc + 4 * N)) 32).toNat + (s.gpr .ebx).toNat <;>
    simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- A row: the window `+= ecx · Y` (`N` words of `Y`), when the sum fits its
`N + 2` words. -/
theorem rowG_ok (hb : Bx s base size) {ys : Nat → Src} {y : Nat → BitVec 32} {acc N : Nat} (hN0 : 0 < N)
    (hY : YsOk ys y base acc (4 * N + 8) N s) (hacc : acc + 4 * N + 8 ≤ size)
    (hlt : val32 s.mem base acc (N + 2) + (s.gpr .ecx).toNat * yVal y N < 2 ^ (32 * (N + 2))) :
    WP isa (.block (rowG ys acc N (carryUp acc N))) s fun u =>
      Outside base acc (4 * N + 8) s.mem u.mem ∧
      val32 u.mem base acc (N + 2) = val32 s.mem base acc (N + 2) + (s.gpr .ecx).toNat * yVal y N ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hn := hb.nowrap
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega_arith⟩
  rw [rowG, Nat.add_sub_cancel, rowSteps_eq]
  refine WP.block_append (WP.mono (rowSteps_ok hb hY (fun k hk => by omega_arith) (k + 1) (by omega_arith) (Nat.le_refl _)
    (by omega_arith)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  have hhi : val32 s₁.mem base (acc + 4 * (k + 1)) 2 = val32 s.mem base (acc + 4 * (k + 1)) 2 :=
    O₁.val32 (by omega_arith) (by omega_arith)
  have hsplit : val32 s.mem base acc (k + 1 + 2) = val32 s.mem base acc (k + 1) +
      2 ^ (32 * (k + 1)) * val32 s.mem base (acc + 4 * (k + 1)) 2 := val32_append _ _ _ _ _
  rw [pow32_add, show 32 * 2 = 64 by rfl] at hlt
  have hP : 0 < 2 ^ (32 * (k + 1)) := Nat.two_pow_pos _
  have hlt₁ : val32 s₁.mem base (acc + 4 * (k + 1)) 2 + (s₁.gpr .ebx).toNat < 2 ^ 64 := by
    rw [hhi]
    rw [hsplit] at hlt
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * (k + 1))) ?_
    rw [Nat.mul_add]
    omega_arith
  refine WP.mono (carryUpB_ok hb₁ (by omega_arith) hlt₁) fun u ⟨O₂, V₂, K₂⟩ =>
    ⟨?_, ?_, K₁.trans (K₂.mono (by simp))⟩
  · exact (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))
  · rw [val32_append u.mem base acc (k + 1) 2, V₂, O₂.val32 (d := acc) (k := k + 1) (by omega_arith) (by omega_arith),
      hhi, hsplit, Nat.mul_add]
    omega_arith

/-- A row whose window's word `N + 1` is not yet written: the window's
`N + 1` words plus `ecx · Y`, in its `N + 2` words. -/
theorem rowG1_ok (hb : Bx s base size) {ys : Nat → Src} {y : Nat → BitVec 32} {acc N : Nat} (hN0 : 0 < N)
    (hY : YsOk ys y base acc (4 * N + 8) N s) (hacc : acc + 4 * N + 8 ≤ size) :
    WP isa (.block (rowG ys acc N (carryUp1 acc N))) s fun u =>
      Outside base acc (4 * N + 8) s.mem u.mem ∧
      val32 u.mem base acc (N + 2) = val32 s.mem base acc (N + 1) + (s.gpr .ecx).toNat * yVal y N ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hn := hb.nowrap
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega_arith⟩
  rw [rowG, Nat.add_sub_cancel, rowSteps_eq]
  refine WP.block_append (WP.mono (rowSteps_ok hb hY (fun k hk => by omega_arith) (k + 1) (by omega_arith) (Nat.le_refl _)
    (by omega_arith)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  refine WP.mono (carryUp1_ok hb₁ (by omega_arith)) fun u ⟨O₂, V₂, K₂⟩ =>
    ⟨?_, ?_, K₁.trans (K₂.mono (by simp))⟩
  · exact (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))
  · have htop : w32 s₁.mem base (acc + 4 * (k + 1)) = w32 s.mem base (acc + 4 * (k + 1)) :=
      O₁.w32 (by omega_arith) (by omega_arith)
    rw [val32_append u.mem base acc (k + 1) 2, V₂, O₂.val32 (d := acc) (k := k + 1) (by omega_arith) (by omega_arith),
      htop, val32_succ s.mem base acc (k + 1), Nat.mul_add]
    omega_arith

/-! ## Row 0 -/

/-- A step of row 0: `[ebp + acc + 4j] = ecx · y + ebx` (the window not
read), the carry word to `ebx`. -/
theorem stepZ_ok (hb : Bx s base size) {y : BitVec 32} {acc j : Nat}
    (hy : readSrc s (.mem (at_ .esi (4 * j))) = some y) (ht : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (stepZ acc j)) s fun u =>
      u.mem = s.mem.writeW (off base (acc + 4 * j)) (BitVec.ofNat 32
        ((s.gpr .ecx).toNat * y.toNat + (s.gpr .ebx).toNat)) ∧
      (u.gpr .ebx).toNat = ((s.gpr .ecx).toNat * y.toNat + (s.gpr .ebx).toNat) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] s u := by
  simp only [stepZ]
  refine wp_movS hy fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  have k₄ : Keeps [.eax, .edx] s s₄ :=
    ((u₁.keeps.mono (by decide)).widen m₂.keeps).widen u₃.keeps |>.widen u₄.keeps
  have hb₄ := hb.of_keeps k₄ (by decide)
  refine wp_storeS (hb₄.ea (d := acc + 4 * j) (by omega_arith)) (hb₄.write ht) fun s₅ m₅ => ?_
  refine wp_movS rfl fun s₆ u₆ _ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂.mem, u₁.mem]
  have ecx₁ : s₁.gpr .ecx = s.gpr .ecx := u₁.other _ (by decide)
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [u₁.gpr, ecx₁] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = s.gpr .ebx := by rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
  have hpost := step0_regs y (s.gpr .ecx) (s.gpr .ebx) _ rfl
  have hx : s₄.gpr .eax = BitVec.ofNat 32 ((s.gpr .ecx).toNat * y.toNat + (s.gpr .ebx).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [u₄.other _ (by decide), u₃.gpr, eax₂, ebx₂, hpost.1, BitVec.toNat_ofNat]
  have dx : s₄.gpr .edx = BitVec.ofNat 32 (y.toNat * (s.gpr .ecx).toNat / 2 ^ 32) + 0 +
      (BitVec.ofBool (decide (2 ^ 32 ≤ (BitVec.ofNat 32 (y.toNat * (s.gpr .ecx).toNat)).toNat +
        (s.gpr .ebx).toNat))).setWidth 32 := by
    rw [u₄.gpr, u₃.other _ (by decide), edx₂, ← eax₂, ← ebx₂]
  refine ⟨by rw [u₆.mem, m₅.mem, m₄, hx], by rw [u₆.gpr, m₅.gpr, dx, hpost.2], fun r hr => ?_,
    by rw [u₆.rd, m₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd], by rw [u₆.wr, m₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  rw [u₆.other _ h2, m₅.gpr, u₄.other _ h3, u₃.other _ h1, m₂.other _ h1 h3, u₁.other _ h1]

/-- The steps `0 … k - 1` of row 0. -/
def rowStepsZ (acc : Nat) : Nat → List Instr
  | 0 => []
  | 1 => [.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .store (bp acc) .eax, .mov .ebx (.reg .edx)]
  | k + 2 => rowStepsZ acc (k + 1) ++ stepZ acc (k + 1)

theorem rowStepsZ_eq (acc : Nat) :
    ∀ k, ([.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .store (bp acc) .eax, .mov .ebx (.reg .edx)] : List Instr) ++
      stepsZ acc k = rowStepsZ acc (k + 1)
  | 0 => by simp [stepsZ, rowStepsZ]
  | k + 1 => by rw [stepsZ, ← List.append_assoc, rowStepsZ_eq acc k]; rfl

/-- Row 0's steps: the window's low `k` words `= ecx · Y`, the carry word to `ebx`. -/
theorem rowStepsZ_ok (hb : Bx s base size) {y : Nat → BitVec 32} {acc len N : Nat}
    (hY : YsOk bWord y base acc len N s) (hlen : ∀ k ≤ N, 4 * k ≤ len) :
    ∀ k, 1 ≤ k → k ≤ N → acc + 4 * k ≤ size →
    WP isa (.block (rowStepsZ acc k)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧
      val32 u.mem base acc k + 2 ^ (32 * k) * (u.gpr .ebx).toNat = (s.gpr .ecx).toNat * yVal y k ∧
      Keeps [.eax, .ebx, .edx] s u
  | 0, h, _, _ => absurd h (by decide)
  | 1, _, hN, hacc => by
    have hn := hb.nowrap
    have hy : readSrc s (.mem (at_ .esi 0)) = some (y 0) :=
      hY 0 (by omega_arith) s ⟨rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩
    simp only [rowStepsZ]
    refine wp_movS hy fun s₁ u₁ _ => ?_
    refine wp_mul fun s₂ m₂ => ?_
    have k₂ : Keeps [.eax, .edx] s s₂ := (u₁.keeps.mono (by decide)).widen m₂.keeps
    have hb₂ := hb.of_keeps k₂ (by decide)
    refine wp_storeS (hb₂.ea (d := acc) (by omega_arith)) (hb₂.write (n := 4) (by omega_arith)) fun s₃ m₃ => ?_
    refine wp_movS rfl fun s₄ u₄ _ => WP.block_nil ?_
    have mem₂ : s₂.mem = s.mem := by rw [m₂.mem, u₁.mem]
    have W := writeW32_outside s.mem base (d := acc) (s₂.gpr .eax) (by omega_arith)
    have hm : s₄.mem = s.mem.writeW (off base acc) (s₂.gpr .eax) := by rw [u₄.mem, m₃.mem, mem₂]
    rw [← hm] at W
    refine ⟨W, ?_, ((k₂.mono (by decide)).trans (m₃.keeps _)).widen u₄.keeps⟩
    have eax₂ := m₂.eax
    have edx₂ := m₂.edx
    rw [u₁.gpr, u₁.other .ecx (by decide)] at eax₂ edx₂
    obtain ⟨hw, hq⟩ := mul_words (y 0) (s.gpr .ecx)
    rw [val32_one, show yVal y 1 = (y 0).toNat by simp [yVal], hm, w32_write_self, eax₂, u₄.gpr, m₃.gpr,
      edx₂, show 32 * 1 = 32 from rfl, Nat.mul_comm (s.gpr .ecx).toNat]
    exact hw
  | k + 2, _, hN, hacc => by
    have hn := hb.nowrap
    rw [rowStepsZ]
    refine WP.block_append (WP.mono (rowStepsZ_ok hb hY hlen (k + 1) (by omega_arith) (by omega_arith) (by omega_arith))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    have hy := hY (k + 1) (by omega_arith) s₁ (RowKeep.of K₁ (by decide) (by decide)
      (O₁.mono (Nat.le_refl _) (by have := hlen (k + 1) (by omega_arith); omega_arith)))
    refine WP.mono (stepZ_ok hb₁ hy (acc := acc) (j := k + 1) (by omega_arith)) fun u ⟨m₂, b₂, K₂⟩ => ?_
    have ecx₁ : s₁.gpr .ecx = s.gpr .ecx := K₁.1 _ (by decide)
    rw [ecx₁] at m₂ b₂
    have W := writeW32_outside s₁.mem base (d := acc + 4 * (k + 1))
      (BitVec.ofNat 32 ((s.gpr .ecx).toNat * (y (k + 1)).toNat + (s₁.gpr .ebx).toNat)) (by omega_arith)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_, K₁.trans K₂⟩
    have hlow : val32 u.mem base acc (k + 1) = val32 s₁.mem base acc (k + 1) := W.val32 (by omega_arith) (by omega_arith)
    have htop : w32 u.mem base (acc + 4 * (k + 1)) = ((s.gpr .ecx).toNat * (y (k + 1)).toNat +
        (s₁.gpr .ebx).toNat) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    rw [val32_succ u.mem base acc (k + 1), hlow, htop, b₂, pow32_succ (k + 1), yVal]
    generalize hxd : (s.gpr .ecx).toNat * (y (k + 1)).toNat + (s₁.gpr .ebx).toNat = x at *
    have hx := Nat.div_add_mod x (2 ^ 32)
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

/-- Row 0's product: the window's `N + 2` words `= ecx · Y`. -/
theorem rowZ_ok (hb : Bx s base size) {y : Nat → BitVec 32} {acc N : Nat} (hN0 : 0 < N)
    (hY : YsOk bWord y base acc (4 * N + 8) N s) (hacc : acc + 4 * N + 8 ≤ size) :
    WP isa (.block (rowZ acc N)) s fun u =>
      Outside base acc (4 * N + 8) s.mem u.mem ∧
      val32 u.mem base acc (N + 2) = (s.gpr .ecx).toNat * yVal y N ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hn := hb.nowrap
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega_arith⟩
  rw [rowZ, Nat.add_sub_cancel, rowStepsZ_eq]
  refine WP.block_append (WP.mono (rowStepsZ_ok hb hY (fun k hk => by omega_arith) (k + 1) (by omega_arith)
    (Nat.le_refl _) (by omega_arith)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  refine wp_storeS (hb₁.ea (d := acc + 4 * (k + 1)) (by omega_arith)) (hb₁.write (n := 4) (by omega_arith))
    fun s₂ m₂ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  have hb₃ := hb₁.of_keeps ((m₂.keeps [.eax]).widen u₃.keeps) (by decide)
  refine wp_storeS (hb₃.ea (d := acc + 4 * (k + 1) + 4) (by omega_arith)) (hb₃.write (n := 4) (by omega_arith))
    fun s₄ m₄ => WP.block_nil ?_
  have W₁ := writeW32_outside s₁.mem base (d := acc + 4 * (k + 1)) (s₁.gpr .ebx) (by omega_arith)
  have W₂ := writeW32_outside (s₁.mem.writeW (off base (acc + 4 * (k + 1))) (s₁.gpr .ebx)) base
    (d := acc + 4 * (k + 1) + 4) (s₃.gpr .eax) (by omega_arith)
  have hm : s₄.mem = (s₁.mem.writeW (off base (acc + 4 * (k + 1))) (s₁.gpr .ebx)).writeW
      (off base (acc + 4 * (k + 1) + 4)) (s₃.gpr .eax) := by
    rw [m₄.mem, u₃.mem, m₂.mem]
  rw [← hm] at W₂
  refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans ((W₁.mono (by omega_arith) (by omega_arith)).trans
    (W₂.mono (by omega_arith) (by omega_arith))), ?_, (K₁.trans ((m₂.keeps _).widen u₃.keeps)).trans (m₄.keeps _)⟩
  have hlo : val32 s₄.mem base acc (k + 1) = val32 s₁.mem base acc (k + 1) := by
    rw [W₂.val32 (by omega_arith) (by omega_arith), W₁.val32 (by omega_arith) (by omega_arith)]
  have hhi : val32 s₄.mem base (acc + 4 * (k + 1)) 2 = (s₁.gpr .ebx).toNat := by
    simp only [val32, Nat.mul_zero, Nat.add_zero]
    rw [hm, w32_write_self, w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self, u₃.gpr]
    rfl
  rw [val32_append s₄.mem base acc (k + 1) 2, hlo, hhi, V₁]

end VG.Proof.Weierstrass.X86.Mont
