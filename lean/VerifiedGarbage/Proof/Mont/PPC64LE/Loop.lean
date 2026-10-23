module

import VerifiedGarbage.Proof.Mont.PPC64LE.Row
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Montgomery arithmetic on PPC64LE: the loop of the multiplication

An iteration of the loop (`row`), at `r7 = r3 + acc + 4k`, adds `u [b]` (for
digit `k` of `[a]`) and then `q m` to the window of `D + 2` digits there,
which holds `T < 2m` (the digit above it being zero): `q = t₀ m' mod 2³²`
makes the sum's low digit zero, so the window one digit up holds
`(T + u B + q m) / 2³²`, below `2m` again (`row_ok`). The loop runs it `D`
times (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- `t₀ + (t₀ m' mod 2³²) m ≡ 0 (mod 2³²)` when `m m' ≡ -1`. -/
theorem mont_low32 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 32 = 0) :
    (t0 + t0 * minv % 2 ^ 32 * m) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 32), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2³²`. -/
theorem minv32_inv {M : Mod} {m : Nat} (h : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0 := by
  rw [minv32, BitVec.toNat_setWidth, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * M.minv.toNat + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩), h]

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T u B q m : Nat} (hT : T < 2 * m) (hu : u < 2 ^ 32) (hB : B < m) (hq : q < 2 ^ 32) :
    T + u * B + q * m < 2 ^ 32 * (2 * m) := by
  have h1 : u * B ≤ (2 ^ 32 - 1) * B := Nat.mul_le_mul_right _ (by omega)
  have h2 : q * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 ^ 32 - 1) * B ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The low digit of a window. -/
theorem val32_low (m : Mem) (base : Addr) (d k : Nat) : val32 m base d (k + 1) % 2 ^ 32 = w32 m base d := by
  rw [val32_succ', Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (w32_lt _ _ _)

/-- The window one digit up, when the low digit is zero and the digit above
the window is zero. -/
theorem val32_shift {m : Mem} {base : Addr} {d k : Nat} (h0 : w32 m base d = 0)
    (htop : w32 m base (d + 4 * k) = 0) :
    2 ^ 32 * val32 m base (d + 4) k = val32 m base d k := by
  have e1 := val32_succ m base d k
  have e2 := val32_succ' m base d k
  rw [htop] at e1
  rw [h0] at e2
  omega

/-- `lis`, `ori` of a 32-bit constant: its low 32 bits. -/
theorem wp_movImm {s : State} {d : Reg} {x : BitVec 32} {is : List Instr} {Q : State → Prop}
    (k : ∀ v : BitVec 64, v.toNat % 2 ^ 32 = x.toNat → WP isa (.block is) (s.write d v) Q) :
    WP isa (.block (movImm d x ++ is)) s Q := by
  simp only [movImm, List.cons_append, List.nil_append]
  refine wp_step exec_lis (wp_step exec_ori ?_)
  rw [write_write]
  refine k _ ?_
  have := congrArg BitVec.toNat (lis_ori x)
  rw [BitVec.toNat_setWidth] at this
  rw [← this]
  simp only [write_gpr, ite_true]

/-! ## An iteration -/

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus (`D`
digits) in the working space and apart from the accumulator (`2D + 2`
digits at `acc`). -/
structure MulLay (D size acc a b mo : Nat) : Prop where
  acc_le : acc + 4 * (2 * D + 2) ≤ size
  a_le : a + 4 * D ≤ size
  b_le : b + 4 * D ≤ size
  mo_le : mo + 4 * D ≤ size
  sa : a + 4 * D ≤ acc ∨ acc + 4 * (2 * D + 2) ≤ a
  sb : b + 4 * D ≤ acc ∨ acc + 4 * (2 * D + 2) ≤ b
  smo : mo + 4 * D ≤ acc ∨ acc + 4 * (2 * D + 2) ≤ mo

/-- The registers the loop writes. -/
def clob : List Reg := [.r0, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The invariant of the loop, before the iteration for digit `k` of `[a]`:
the window of `D + 2` digits at `acc + 4k` holds `T < 2m` with
`2^(32 k) T ≡ A B`, for the low `k` digits `A` of `[a]`; the digits above
it are zero; `r5` points to digit `k`, `r7` to the window, and `r8` counts
the digits left. -/
structure LoopInv (base : Addr) (D acc a b m k : Nat) (s t : State) : Prop where
  r3 : At t base .r3 0
  r5 : At t base .r5 (a + 4 * k)
  r6 : At t base .r6 b
  r7 : At t base .r7 (acc + 4 * k)
  r8 : t.gpr .r8 = BitVec.ofNat 64 (D - k)
  out : Outside base acc (4 * (2 * D + 2)) s.mem t.mem
  kp : Kp clob s t
  zeros : ∀ l, k + D + 2 ≤ l → l < 2 * D + 2 → w32 t.mem base (acc + 4 * l) = 0
  lt : val32 t.mem base (acc + 4 * k) (D + 2) < 2 * m
  cong : ∃ U, 2 ^ (32 * k) * val32 t.mem base (acc + 4 * k) (D + 2) =
    val32 s.mem base a k * val32 s.mem base b D + U * m

theorem kp_clob {s t : State} (h : Kp clob s t) {r : Reg} (hr : r ∉ clob := by decide) : t.gpr r = s.gpr r :=
  h.gpr r hr

/-- `T + u B < 2^(32 (D + 2))` for `T < 2m`, `B < m < 2^(32 D)`. -/
theorem sum_lt {T u B m D : Nat} (hT : T < (2 ^ 32 + 1) * m) (hu : u < 2 ^ 32) (hB : B ≤ m)
    (hm : m < 2 ^ (32 * D)) : T + u * B < 2 ^ (32 * (D + 2)) := by
  have h1 : u * B ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul (by omega) hB
  have h2 : (2 ^ 32 + 1) * m + (2 ^ 32 - 1) * m ≤ 2 ^ 33 * m := by omega
  have h3 : 2 ^ 33 * m < 2 ^ 33 * 2 ^ (32 * D) := Nat.mul_lt_mul_of_pos_left hm (by decide)
  have h4 : 2 ^ 33 * 2 ^ (32 * D) ≤ 2 ^ (32 * (D + 2)) := by
    rw [show 32 * (D + 2) = 33 + (32 * D + 31) by omega, Nat.pow_add, Nat.pow_add]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  omega

/-- An iteration of the loop. -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {D acc a b m k : Nat}
    (hD : digits M = D) (hL : MulLay D size acc a b M.mo) (hk : k < D)
    (hm : val32 s.mem base M.mo D = m) (hinv : (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b D < m) {t : State} (I : LoopInv base D acc a b m k s t) :
    WP isa (.block (row M)) t fun u => LoopInv base D acc a b m (k + 1) s u := by
  have hn := hs.nowrap
  have hs15 := hs.small
  obtain ⟨acc_le, a_le, b_le, mo_le, sa, sb, smo⟩ := hL
  have ht := I.kp.ws hs
  have hm0 : m < 2 ^ (32 * D) := by rw [← hm]; exact val32_lt _ _ _ _
  have hmt : val32 t.mem base M.mo D = m := by rw [I.out.val32 (by omega) (by omega), hm]
  have hbt : val32 t.mem base b D = val32 s.mem base b D := I.out.val32 (by omega) (by omega)
  have hat : w32 t.mem base (a + 4 * k + 0) = w32 s.mem base (a + 4 * k) := I.out.w32 (by omega) (by omega)
  simp only [row, hD, List.cons_append, List.nil_append, List.append_assoc]
  -- u
  refine wp_step (lwz_ok ht I.r5 (by decide) (d := 0) (by omega)) ?_
  rw [hat]
  generalize hu : w32 s.mem base (a + 4 * k) = u
  have hu32 : u < 2 ^ 32 := hu ▸ w32_lt _ _ _
  have hlt₁ : val32 t.mem base (acc + 4 * k) (D + 2) + u * val32 t.mem base (b + 0) D < 2 ^ (32 * (D + 2)) := by
    simp only [Nat.add_zero]; rw [hbt]; exact sum_lt (by have := I.lt; omega) hu32 (by omega) hm0
  refine wp_append (WP.mono (mulRow_ok (ht.write _ _) (I.r6.write _) (I.r7.write _) (rs := .r6) (src := 0)
    (by decide) (by omega) (by omega) (by omega)
    (by simp only [write_gpr, ite_true]; rw [toNat_ofNat_lt (by omega)]; exact hu32)
    (by simp only [write_gpr, ite_true, write_mem]; rw [toNat_ofNat_lt (by omega)]; exact hlt₁))
    fun t₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [write_gpr, ite_true, write_mem] at O₂ V₂
  rw [toNat_ofNat_lt (by omega)] at V₂
  simp only [Nat.add_zero] at V₂
  rw [hbt] at V₂
  have K₁₂ : Kp [.r9, .r10, .r11, .r12] t t₂ := (Kp.write t _ (by decide)).trans (K₂.mono (by decide))
  have ht₂ := K₁₂.ws ht
  have h7₂ : At t₂ base .r7 (acc + 4 * k) := K₁₂.at I.r7
  -- q
  refine wp_step (lwz_ok ht₂ h7₂ (by decide) (d := 0) (by omega)) ?_
  refine wp_movImm fun v hv => ?_
  refine wp_step exec_mul ?_
  refine wp_step (exec_rotr_w (by decide)) ?_
  simp only [write_gpr, ite_true, reduceCtorEq, ite_false, Nat.add_zero]
  generalize hT1 : val32 t.mem base (acc + 4 * k) (D + 2) + u * val32 s.mem base b D = T1 at V₂
  have ht0 : w32 t₂.mem base (acc + 4 * k) = T1 % 2 ^ 32 := by rw [← V₂, val32_low]
  rw [ht0]
  generalize hq : (((BitVec.ofNat 64 (T1 % 2 ^ 32) * v).setWidth 32).rotateRight 0).setWidth 64 = qv
  have hqv : qv.toNat = T1 % 2 ^ 32 * (minv32 M).toNat % 2 ^ 32 := by
    rw [← hq, BitVec.toNat_setWidth, rotr0, BitVec.toNat_setWidth, BitVec.toNat_mul,
      toNat_ofNat_lt (by have := Nat.mod_lt T1 (show 0 < 2 ^ 32 by decide); omega),
      Nat.mod_mod_of_dvd _ (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩),
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), Nat.mul_mod, hv, Nat.mod_mod]
  have hq32 : qv.toNat < 2 ^ 32 := by rw [hqv]; exact Nat.mod_lt _ (by decide)
  have hT1lt : T1 < (2 ^ 32 + 1) * m := by
    have := I.lt
    have : u * val32 s.mem base b D ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h3₂ : At t₂ base .r3 0 := K₁₂.at I.r3
  have hmt₂ : val32 t₂.mem base (0 + M.mo) D = m := by
    rw [Nat.zero_add, O₂.val32 (by omega) (by omega), hmt]
  have hlt₂ : T1 + qv.toNat * m < 2 ^ (32 * (D + 2)) := sum_lt hT1lt hq32 (Nat.le_refl _) hm0
  refine wp_append (WP.mono (mulRow_ok ((((ht₂.write _ _).write _ _).write _ _).write _ _)
    ((((h3₂.write _).write _).write _).write _) ((((h7₂.write _).write _).write _).write _) (rs := .r3)
    (src := M.mo) (K := 0) (D := D) (by decide) (by omega) (by omega) (by omega)
    (by simp only [write_gpr, ite_true]; exact hq32)
    (by simp only [write_gpr, ite_true, write_mem]; rw [hmt₂, V₂]; exact hlt₂))
    fun t₇ ⟨O₇, V₇, K₇⟩ => ?_)
  simp only [write_gpr, ite_true, write_mem] at O₇ V₇
  rw [hmt₂, V₂] at V₇
  have K₂₇ : Kp [.r0, .r9, .r10, .r11, .r12] t₂ t₇ :=
    (((((Kp.write t₂ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (K₇.mono (by decide)))
  have K₀₇ : Kp [.r0, .r9, .r10, .r11, .r12] t t₇ := (K₁₂.mono (by decide)).trans K₂₇
  -- The pointers and the count.
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
  have g5 : t₇.gpr .r5 = off base (a + 4 * k) := by rw [K₀₇.g]; exact I.r5
  have g7 : t₇.gpr .r7 = off base (acc + 4 * k) := by rw [K₀₇.g]; exact I.r7
  have g8 : t₇.gpr .r8 = BitVec.ofNat 64 (D - k) := by rw [K₀₇.g]; exact I.r8
  -- The window's low digit is zero, and the one above it too.
  have hz : w32 t₇.mem base (acc + 4 * k) = 0 := by
    rw [← val32_low t₇.mem base _ (D + 1), V₇, hqv]
    have h := mont_low32 (T1 % 2 ^ 32) (minv32 M).toNat m hinv
    generalize T1 % 2 ^ 32 * (minv32 M).toNat % 2 ^ 32 * m = X at h ⊢
    omega
  have htop : w32 t₇.mem base (acc + 4 * k + 4 * (D + 2)) = 0 := by
    rw [O₇.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega),
      show acc + 4 * k + 4 * (D + 2) = acc + 4 * (k + D + 2) by omega]
    exact I.zeros _ (Nat.le_refl _) (by omega)
  have hsh := val32_shift hz htop
  have hT2 : val32 t₇.mem base (acc + 4 * (k + 1)) (D + 2) < 2 * m := by
    have := row_lt I.lt hu32 hB hq32
    rw [show acc + 4 * (k + 1) = acc + 4 * k + 4 by omega]
    rw [V₇, ← hT1] at hsh
    omega
  have e4 : ∀ x, off base x + BitVec.ofNat 64 4 = off base (x + 4) := fun x => off_add base x 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [K₀₇.g]; exact I.r3
  · simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [g5, e4, show a + 4 * k + 4 = a + 4 * (k + 1) by omega]
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [K₀₇.g]; exact I.r6
  · simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [g7, e4, show acc + 4 * k + 4 = acc + 4 * (k + 1) by omega]
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [g8]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : D < 2 ^ 15 := by omega
    omega
  · exact I.out.trans ((O₂.mono (by omega) (by omega)).trans (O₇.mono (by omega) (by omega)))
  · exact I.kp.trans ((K₀₇.mono (by decide)).trans (((Kp.write _ _ (by decide)).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))))
  · intro l hl1 hl2
    simp only [write_mem]
    rw [O₇.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega)]
    exact I.zeros l (by omega) hl2
  · exact hT2
  · obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + qv.toNat * 2 ^ (32 * k), ?_⟩
    simp only [write_mem]
    have hA : val32 s.mem base a (k + 1) = val32 s.mem base a k + 2 ^ (32 * k) * u := by
      rw [val32_succ, hu]
    rw [V₇, ← hT1] at hsh
    rw [hA, show acc + 4 * (k + 1) = acc + 4 * k + 4 by omega, show 32 * (k + 1) = 32 * k + 32 by omega,
      Nat.pow_add, Nat.mul_assoc, hsh, Nat.mul_add, Nat.mul_add, hU]
    grind

end VG.Proof.Mont.PPC64LE

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

theorem eval_nonzero_ofNat {s : State} {r : Reg} {x : Nat} (h : s.gpr r = BitVec.ofNat 64 x) (hx : x < 2 ^ 64) :
    isa.eval (.nonzero .d r) s = some (decide (x ≠ 0)) := by
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, h, Option.some.injEq]
  by_cases hx0 : x = 0
  · subst hx0; rfl
  · have : BitVec.ofNat 64 x ≠ 0 := fun e => hx0 (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this)
    exact (bne_iff_ne.mpr this).trans (decide_eq_true hx0).symm

/-- The loop of `mul`: from the invariant at digit 0 to the invariant at `D`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {D acc a b m : Nat}
    (hD : digits M = D) (hL : MulLay D size acc a b M.mo) (hD0 : 0 < D)
    (hm : val32 s.mem base M.mo D = m) (hinv : (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b D < m) {t : State} (h0 : LoopInv base D acc a b m 0 s t) :
    WP isa (.loop (.block (row M)) (.nonzero .d .r8)) t fun u => LoopInv base D acc a b m D s u := by
  have hD15 : D < 2 ^ 15 := by have := hs.small; have := hL.acc_le; omega
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = D - k ∧ k < D ∧ LoopInv base D acc a b m k s t') ?_ D t ⟨0, rfl, hD0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (row_ok hs hD hL hk hm hinv hB I) fun u I' => ?_
  have he := eval_nonzero_ofNat I'.r8 (x := D - (k + 1)) (by omega)
  by_cases hk1 : k + 1 = D
  · exact .inl ⟨by rw [he]; simp [hk1], hk1 ▸ I'⟩
  · exact .inr ⟨by rw [he]; simp; omega, D - (k + 1), by omega, k + 1, rfl, by omega, I'⟩

end VG.Proof.Mont.PPC64LE
