module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound

/-!
# The RSA public-key operation on PPC64LE: the power

`power` scans the public exponent `e` from its first set bit (`skip_ok`),
starting from `a = x R mod n`; each later bit squares `a` and, if set,
multiplies it by `x R mod n` (`bitStep_ok`), but the last, whose
multiplication by `x` or 1 also converts out of Montgomery form
(`lastBit_ok`). `power_ok` composes them.

Throughout, `r24` holds the bits of `e` not yet scanned at its top: after
`q` shifts, `c 2⁶⁴ + r24 = v 2³¹ 2^q` for the number `c` of the bits
scanned, where `v` is `e` (below `2^33`), and `a ≡ x^c R (mod n)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE

/-- Array `j`'s number. -/
abbrev V (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (slot w j) (2 * w)

/-- What the Montgomery multiplications need, with `N` the modulus in
array 0. -/
structure Ctx (s : State) (B : Addr) (Z w N : Nat) : Prop where
  scr : Scr s B Z
  w2 : 2 ≤ w
  w31 : w < 2 ^ 31
  hZ : slot w 8 ≤ Z
  r10 : s.gpr .r10 = off B (slot w 0)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (s.gpr .r12).toNat < 2 ^ 32
  inv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  n : V s.mem B w 0 = N

theorem Ctx.sl {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {j : Nat} (hj : j < 8) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_le hj) h.hZ

/-- An array apart from those in `js` keeps its number. -/
theorem Ctx.vj {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {m m' : Mem} {js : List Nat}
    {j : Nat} (hj : j < 8) (hjs : ∀ k ∈ js, k ≠ j) (o : Outs B (js.map fun k => (slot w k, 8 * (w + 2))) m m') :
    V m' B w j = V m B w j := by
  have hnw := h.scr.nowrap
  have := h.sl hj
  refine o.val32 (fun r hr => ?_) (by omega)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
  have := slot_sep (w := w) (Ne.symm (hjs k hk))
  omega

/-- The context after code that writes only arrays 1–7 and none of `r10`,
`r11`, `r12`, `r29`. -/
theorem Ctx.of {s t : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ [Reg.r10, .r11, .r12, .r29], r ∉ rs) (o : Outs B (powRs w) s.mem t.mem) : Ctx t B Z w N := by
  have hnw := h.scr.nowrap
  have hrs' := fun r hr => k.gpr r (hrs r hr)
  have a0 : ∀ r ∈ powRs w, slot w 0 + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w 0 := fun r hr => by
    simp only [powRs, List.mem_map] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    have : k ≠ 0 := by revert k; decide
    have := slot_sep (w := w) (Ne.symm this)
    omega
  have s0 := h.sl (j := 0) (by decide)
  refine ⟨h.scr.congr k.wr, h.w2, h.w31, h.hZ, (hrs' .r10 (by decide)).trans h.r10,
    (hrs' .r29 (by decide)).trans h.r29, (hrs' .r11 (by decide)).trans h.r11,
    by rw [hrs' .r12 (by decide)]; exact h.r12, ?_, ?_⟩
  · rw [hrs' .r12 (by decide), Outs.w32 o (fun r hr => by have := a0 r hr; omega) (by omega)]
    exact h.inv
  · rw [← h.n]
    exact o.val32 (fun r hr => by have := a0 r hr; omega) (by omega)

theorem outs_pow {w : Nat} {m m' : Mem} {B : Addr} {js : List Nat}
    (h : Outs B (js.map fun k => (slot w k, 8 * (w + 2))) m m')
    (hjs : ∀ j ∈ js, j ∈ [1, 2, 3, 4, 5, 6, 7] := by decide) : Outs B (powRs w) m m' :=
  h.mono fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨k, hjs k hk, rfl⟩

/-- A Montgomery multiplication in the context. -/
theorem Ctx.mont {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {o a b : Nat} (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (ho1 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hB : V s.mem B w b < N) :
    WP isa (montOp o a b) s fun t =>
      (Ctx t B Z w N ∧ V t.mem B w o < N ∧
        V t.mem B w o * 2 ^ (64 * w) % N = V s.mem B w a * V s.mem B w b % N ∧
        (∀ j < 8, j ≠ 2 → j ≠ 3 → j ≠ o → V t.mem B w j = V s.mem B w j) ∧
        Outs B (powRs w) s.mem t.mem) ∧ Keep montRegs s t := by
  refine WP.mono (montOp_ok h.scr ho ha hb ho2 ho3 ha2 hb2 h.w2 h.w31 h.hZ h.r10 h.r29 h.r11 h.r12 h.inv
    (by rw [show val32 s.mem B (slot w 0) (2 * w) = N from h.n]; exact hB)) fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  have o' : Outs B ([2, 3, o].map fun k => (slot w k, 8 * (w + 2))) s.mem t.mem := out
  have op : Outs B (powRs w) s.mem t.mem := outs_pow (js := [2, 3, o]) o' (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp <;> omega)
  rw [show val32 s.mem B (slot w 0) (2 * w) = N from h.n] at hlt he
  exact ⟨⟨h.of k (by decide) op, hlt, he,
    fun j hj h2 h3 hjo => h.vj hj (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) o', op⟩, k⟩

/-! ## The leading zeros -/

theorem pow_step (a i : Nat) : a * 2 ^ (i + 1) = 2 * (a * 2 ^ i) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]

/-- A step of `skip`: the top bit of `r24` shifted out, `r25` counted down,
and `r3` 0 if the bit was set, else `r25`. -/
theorem skipBody_ok {t : State} {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (h25 : t.gpr .r25 = BitVec.ofNat 64 n) :
    WP isa (.block [.lsr .d .r3 .r24 63, .lsl .r24 .r24 1, .subi .r25 .r25 1, .subi .r3 .r3 1,
        .logic .and .r3 .r3 .r25]) t fun t' =>
      (t'.gpr .r24 = t.gpr .r24 <<< 1 ∧ t'.gpr .r25 = BitVec.ofNat 64 (n - 1) ∧
        t'.gpr .r3 = (if 2 ^ 63 ≤ (t.gpr .r24).toNat then 0 else BitVec.ofNat 64 (n - 1)) ∧ t'.mem = t.mem) ∧
      Keep [.r3, .r24, .r25] t t' := by
  refine WP.keep _ ?_ (by decide)
  prun [top_bit, h25]
  have e : BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [e]
  refine ⟨rfl, ?_⟩
  split
  · simp
  · rw [show BitVec.ofNat 64 0 - 1#64 = BitVec.allOnes 64 by decide, BitVec.allOnes_and]

theorem r24_shift (x : BitVec 64) :
    (x <<< 1).toNat + (if 2 ^ 63 ≤ x.toNat then 1 else 0) * 2 ^ 64 = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := x.isLt
  split <;> omega

/-- `skip`: from `r24 = v 2³¹`, `r25 = 32 - i` after `i + 1` shifts, the last of them out of `e`'s first set bit if `v` is not 0. -/
theorem skip_ok {s : State} {v : Nat} (h24 : (s.gpr .r24).toNat = v * 2 ^ 31) :
    WP isa skip s fun t =>
      (∃ i ≤ 32, t.gpr .r25 = BitVec.ofNat 64 (32 - i) ∧
        (0 < v → 2 ^ 64 + (t.gpr .r24).toNat = v * 2 ^ 31 * 2 ^ (i + 1)) ∧ t.mem = s.mem) ∧
      Keep [.r3, .r24, .r25] s t := by
  unfold skip
  refine WP.seq (WP.mono (WP.keep [.r25] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 33 ∧ t.mem = s.mem)
    (by prun) (by decide)) fun s₁ ⟨⟨h25, m1⟩, k1⟩ => ?_)
  let Inv : Nat → State → Prop := fun n t => ∃ i, n = 33 - i ∧ i ≤ 32 ∧ t.gpr .r25 = BitVec.ofNat 64 (33 - i) ∧
    (t.gpr .r24).toNat = v * 2 ^ 31 * 2 ^ i ∧ t.mem = s.mem ∧ Keep [.r3, .r24, .r25] s t
  refine WP.loop Inv (fun n t ⟨i, hn, hi, t25, t24, tm, kt⟩ => ?_) 33 s₁
    ⟨0, rfl, by omega, h25, by rw [k1.gpr .r24 (by decide), h24]; simp, m1, k1.mono⟩
  refine WP.mono (skipBody_ok (n := 33 - i) (by omega) (by omega) t25) fun t' ⟨⟨a24, a25, a3, am⟩, k'⟩ => ?_
  have hsh := r24_shift (t.gpr .r24)
  rw [← a24] at hsh
  have hlt := (t'.gpr .r24).isLt
  have hlt' := (t.gpr .r24).isLt
  have kt' : Keep [.r3, .r24, .r25] s t' := (kt.trans k').mono
  by_cases hb : 2 ^ 63 ≤ (t.gpr .r24).toNat
  · -- The first set bit: the loop ends.
    simp only [hb, ↓reduceIte] at a3 hsh
    refine .inl ⟨by rw [eval_nonzero, a3]; rfl, ⟨i, hi, by rw [a25]; congr 1; omega, fun _ => ?_, am.trans tm⟩, kt'⟩
    rw [pow_step, ← t24]
    omega
  · simp only [hb, ↓reduceIte, Nat.zero_mul, Nat.add_zero] at a3 hsh
    by_cases hz : i = 32
    · -- No set bit: `v = 0`.
      subst hz
      refine .inl ⟨by rw [eval_nonzero, a3]; rfl, ⟨32, by omega, by rw [a25], fun hv0 => ?_, am.trans tm⟩, kt'⟩
      exfalso
      have : v * 2 ^ 31 * 2 ^ 32 < 2 ^ 63 := by rw [← t24]; omega
      have : 2 ^ 63 ≤ v * 2 ^ 31 * 2 ^ 32 := by
        rw [show (2 : Nat) ^ 63 = 1 * 2 ^ 31 * 2 ^ 32 from rfl]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hv0)
      omega
    · refine .inr ⟨?_, 33 - (i + 1), by omega, i + 1, rfl, by omega, by rw [a25]; congr 1, ?_,
        am.trans tm, kt'⟩
      · rw [eval_nonzero, a3, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        congr 1
        simp only [ne_eq, decide_eq_true_eq]
        omega
      · rw [pow_step, ← t24]
        omega

/-! ## The scan -/

/-- The mask of all ones and the bases of arrays 6, 6 and 5, for `initA`. -/
theorem initBlock_ok {t : State} {B : Addr} {w : Nat} (h10 : t.gpr .r10 = off B (slot w 0))
    (h29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (([.li .r0 1, .li .r3 0, .sub .r20 .r3 .r0] : List Instr) ++ base .r8 6 ++ base .r9 6 ++
        base .r5 5)) t fun t' =>
      (t'.gpr .r20 = BitVec.allOnes 64 ∧
        t'.gpr .r8 = off B (slot w 6) ∧ t'.gpr .r9 = off B (slot w 6) ∧ t'.gpr .r5 = off B (slot w 5) ∧
        t'.mem = t.mem) ∧
      Keep [.r0, .r3, .r20, .r8, .r9, .r5] t t' := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r3, .r20] (Q := fun t₁ =>
      t₁.gpr .r20 = BitVec.allOnes 64 ∧ t₁.mem = t.mem)
    (by prun; decide) (by decide)) fun t₁ ⟨⟨a20, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r8) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 6) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r9) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 6) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (base_ok (rd := .r5) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 5) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ⟨⟨?_, ?_, ?_, a5, ?_⟩, (k13.trans k4).mono⟩
  · rw [k4.gpr .r20 (by decide), k3.gpr .r20 (by decide), k2.gpr .r20 (by decide), a20]
  · rw [k4.gpr .r8 (by decide), k3.gpr .r8 (by decide), a8]
  · rw [k4.gpr .r9 (by decide), a9]
  · rw [m4, m3, m2, m1]

/-- The registers `initA` writes. -/
def initRegs : List Reg := [.r0, .r3, .r20, .r8, .r9, .r5, .r14, .r15, .r16, .r17]

/-- The registers `bitStep` writes. -/
def bitRegs : List Reg := montRegs ++ [.r3, .r24]

/-- `initA`: array 6 into array 5. -/
theorem initA_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) :
    WP isa initA s fun t =>
      (Ctx t B Z w N ∧ V t.mem B w 5 = V s.mem B w 6 ∧
        (∀ j < 8, j ≠ 5 → V t.mem B w j = V s.mem B w j) ∧ Outs B (powRs w) s.mem t.mem) ∧
      Keep initRegs s t := by
  have hnw := h.scr.nowrap
  unfold initA
  refine WP.seq (WP.mono (initBlock_ok h.r10 h.r29) fun s₁ ⟨⟨a20, a8, a9, a5, m1⟩, k1⟩ => ?_)
  have s5 := h.sl (j := 5) (by decide)
  have s6 := h.sl (j := 6) (by decide)
  have d56 := slot_sep (w := w) (show (5 : Nat) ≠ 6 by decide)
  refine WP.mono (selectAcc_ok (b := true) (n := 2 * w) (dA := slot w 6) (dT := slot w 6) (dO := slot w 5)
    (h.scr.congr k1.wr) a8 a9 a5 ((k1.gpr _ (by decide)).trans h.r11) (by rw [a20]; decide)
    (by have := h.w2; omega)
    (by have := h.w31; omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, out, k2⟩ => ?_
  rw [m1] at hv out
  have o : Outs B ([5].map fun k => (slot w k, 8 * (w + 2))) s.mem t.mem :=
    Outs.of_outside (o := slot w 5) (n := 8 * (w + 2)) (out.mono (Nat.le_refl _) (by omega)) (by simp)
  have op : Outs B (powRs w) s.mem t.mem := outs_pow o
  have k12 : Keep initRegs s t := (k1.trans k2).mono
  exact ⟨⟨h.of k12 (by decide) op, hv,
    fun j hj hj5 => h.vj hj (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) o, op⟩, k12⟩

/-- `bitStep`: `S R ≡ a² (mod n)`, `P R ≡ S (x R) (mod n)` and `a := P` if the
top bit of `r24` is set, else `S`. -/
theorem bitStep_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) (hA : V s.mem B w 5 < N)
    (hX : V s.mem B w 6 < N) :
    WP isa bitStep s fun t =>
      (Ctx t B Z w N ∧ V t.mem B w 5 < N ∧
        (∃ S, S * 2 ^ (64 * w) % N = V s.mem B w 5 * V s.mem B w 5 % N ∧
          if 2 ^ 63 ≤ (s.gpr .r24).toNat then V t.mem B w 5 * 2 ^ (64 * w) % N = S * V s.mem B w 6 % N
          else V t.mem B w 5 = S) ∧
        (∀ j < 8, j ≠ 2 → j ≠ 3 → j ≠ 5 → V t.mem B w j = V s.mem B w j) ∧
        Outs B (powRs w) s.mem t.mem ∧ t.gpr .r24 = s.gpr .r24 <<< 1) ∧ Keep bitRegs s t := by
  unfold bitStep
  refine WP.seq (WP.mono (h.mont (o := 5) (a := 5) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hA) fun s₁ ⟨⟨c1, lt1, e1, v1, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.r3, .r24] (Q := fun t => t.gpr .r3 = s₁.gpr .r24 >>> 63 ∧
      t.gpr .r24 = s₁.gpr .r24 <<< 1 ∧ t.mem = s₁.mem) (by prun) (by decide)) fun s₂ ⟨⟨a3, a24, m2⟩, k2⟩ => ?_)
  have e24 : s₁.gpr .r24 = s.gpr .r24 := k1.gpr .r24 (by decide)
  rw [e24, top_bit] at a3
  rw [e24] at a24
  have k12 := k1.trans k2
  have c2 : Ctx s₂ B Z w N := c1.of k2 (by decide) (by rw [m2]; exact Outs.refl _ _ _)
  have X1 : V s₁.mem B w 6 = V s.mem B w 6 := v1 6 (by decide) (by decide) (by decide) (by decide)
  refine WP.ite (decide (2 ^ 63 ≤ (s.gpr .r24).toNat)) (by
    rw [eval_nonzero, a3, ne_zero_iff]; split <;> rename_i hb <;> simp [hb]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.mono (c2.mont (o := 5) (a := 5) (b := 6) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [m2, X1]; exact hX))
      fun t ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ⟨⟨c3, lt3, ⟨_, e1, by simp only [hb, ↓reduceIte]; rw [e3, m2, X1]⟩,
        fun j hj h2 h3 h5 => by rw [v3 j hj h2 h3 h5, m2, v1 j hj h2 h3 h5], ?_, ?_⟩, (k12.trans k3).mono⟩
    · rw [m2] at o3; exact o1.trans o3
    · rw [k3.gpr .r24 (by decide), a24]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨⟨c2, by rw [m2]; exact lt1, ⟨_, e1, by simp only [hb, ↓reduceIte]; rw [m2]⟩,
      fun j hj h2 h3 h5 => by rw [m2, v1 j hj h2 h3 h5], by rw [m2]; exact o1, a24⟩, k12.mono⟩

/-- `lastBit`: `S R ≡ a² (mod n)`, then the result `y` in array 4 with
`y R ≡ x S (mod n)` if the top bit of `r24` is set, else `y R ≡ S`. -/
theorem lastBit_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) (hA : V s.mem B w 5 < N)
    (h7 : V s.mem B w 7 = 1) :
    WP isa lastBit s fun t =>
      (∃ S, S * 2 ^ (64 * w) % N = V s.mem B w 5 * V s.mem B w 5 % N ∧
        V t.mem B w 4 * 2 ^ (64 * w) % N =
          (if 2 ^ 63 ≤ (s.gpr .r24).toNat then V s.mem B w 4 else 1) * S % N) ∧
        V t.mem B w 4 < N ∧ Outs B (powRs w) s.mem t.mem ∧ Keep powRegs s t := by
  unfold lastBit
  refine WP.seq (WP.mono (h.mont (o := 5) (a := 5) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hA) fun s₁ ⟨⟨c1, lt1, e1, v1, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = s₁.gpr .r24 >>> 63 ∧ t.mem = s₁.mem)
    (by prun) (by decide)) fun s₂ ⟨⟨a3, m2⟩, k2⟩ => ?_)
  have e24 : s₁.gpr .r24 = s.gpr .r24 := k1.gpr .r24 (by decide)
  rw [e24, top_bit] at a3
  have k12 := k1.trans k2
  have c2 : Ctx s₂ B Z w N := c1.of k2 (by decide) (by rw [m2]; exact Outs.refl _ _ _)
  have X1 : V s₁.mem B w 4 = V s.mem B w 4 := v1 4 (by decide) (by decide) (by decide) (by decide)
  have S1 : V s₁.mem B w 7 = 1 := by rw [v1 7 (by decide) (by decide) (by decide) (by decide), h7]
  refine WP.ite (decide (2 ^ 63 ≤ (s.gpr .r24).toNat)) (by
    rw [eval_nonzero, a3, ne_zero_iff]; split <;> rename_i hb <;> simp [hb]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.mono (c2.mont (o := 4) (a := 4) (b := 5) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [m2]; exact lt1))
      fun t ⟨⟨_, lt3, e3, _, o3⟩, k3⟩ => ⟨⟨_, e1, by rw [e3, m2, X1]; simp only [hb, ↓reduceIte]⟩, lt3,
        by rw [m2] at o3; exact o1.trans o3, (k12.trans k3).mono⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (c2.mont (o := 4) (a := 7) (b := 5) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [m2]; exact lt1))
      fun t ⟨⟨_, lt3, e3, _, o3⟩, k3⟩ => ⟨⟨_, e1, by rw [e3, m2, S1]; simp only [hb, ↓reduceIte]⟩, lt3,
        by rw [m2] at o3; exact o1.trans o3, (k12.trans k3).mono⟩

/-! ## The power -/

theorem shl31_toNat (E : Nat) : (BitVec.ofNat 64 E <<< 31).toNat = E % 2 ^ 33 * 2 ^ 31 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

/-- The last bit: `y R ≡ x^b S` with `S R ≡ a²` and `a ≡ x^c R`. -/
theorem last_step {A S Y X c R N : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hS : S * R % N = A * A % N) (b : Bool) (hY : Y * R % N = (if b then X else 1) * S % N) :
    Y % N = X ^ (2 * c + if b then 1 else 0) % N := by
  have hS' := sq_step hR hA hS
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hY, Nat.mul_mod, hS', ← Nat.mul_mod]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul, Nat.add_zero]
  · simp only [↓reduceIte]
    congr 1
    rw [Nat.pow_succ]
    grind

theorem shift_arith {c t r r' : Nat} (hr : r' + t * 2 ^ 64 = 2 * r) :
    (2 * c + t) * 2 ^ 64 + r' = 2 * (c * 2 ^ 64 + r) := by
  omega

/-- A bit of the scan: `c` and `a ≡ x^c R` for the bits after `q` shifts. -/
theorem bit_step {A S A' X XM c R N r r' v q : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hXM : XM % N = X * R % N) (hS : S * R % N = A * A % N) (b : Bool)
    (hA' : if b then A' * R % N = S * XM % N else A' = S) (hc : c * 2 ^ 64 + r = v * 2 ^ 31 * 2 ^ q)
    (hr : r' + (if b then 1 else 0) * 2 ^ 64 = 2 * r) :
    (2 * c + if b then 1 else 0) * 2 ^ 64 + r' = v * 2 ^ 31 * 2 ^ (q + 1) ∧
      A' % N = X ^ (2 * c + if b then 1 else 0) * R % N := by
  have hS' := sq_step hR hA hS
  refine ⟨by rw [pow_step (v * 2 ^ 31) q, ← hc]; exact shift_arith hr, ?_⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hA' ⊢
    rw [hA', Nat.add_zero]; exact hS'
  · simp only [↓reduceIte] at hA' ⊢
    exact mul_step hR hS' hXM hA'

/-- `power`: `x^(E mod 2^33) mod n` into array 4, for the input `x` in array 4,
`E 2^31` in `r24` and something below `n` in array 1: if it is `R² mod n`
and `E mod 2^33` is not 0. -/
theorem power_ok {s : State} {B : Addr} {Z w E : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1)
    (hRRlt : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w))
    (h24 : s.gpr .r24 = BitVec.ofNat 64 E <<< 31) :
    WP isa power s fun t =>
      ((0 < E % 2 ^ 33 →
          val32 s.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) →
          val32 t.mem B (slot w 4) (2 * w) =
            val32 s.mem B (slot w 4) (2 * w) ^ (E % 2 ^ 33) % val32 s.mem B (slot w 0) (2 * w)) ∧
        Outs B (powRs w) s.mem t.mem) ∧ Keep powRegs s t := by
  have hnw := hs.nowrap
  have h0 : Ctx s B Z w (val32 s.mem B (slot w 0) (2 * w)) := ⟨hs, hw2, hw', hZ, h10, h29, h11, h12, hinv, rfl⟩
  generalize hNd : val32 s.mem B (slot w 0) (2 * w) = N at hN hodd hRRlt h0 ⊢
  generalize hR : 2 ^ (64 * w) = R
  have hcop : Nat.Coprime R N := by rw [← hR]; exact VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega
  generalize hXd : val32 s.mem B (slot w 4) (2 * w) = X
  generalize hRRd : val32 s.mem B (slot w 1) (2 * w) = RRv at hRRlt ⊢
  generalize hv : E % 2 ^ 33 = v
  have h24' : (s.gpr .r24).toNat = v * 2 ^ 31 := by rw [h24, shl31_toNat, hv]
  unfold power
  -- 1 in array 7.
  refine WP.seq (WP.mono (oneP_ok hs (by omega) hw' hZ h10 h29 h11) fun s₁ ⟨⟨h7, out1⟩, k1⟩ => ?_)
  have o1 : Outs B ([7].map fun k => (slot w k, 8 * (w + 2))) s.mem s₁.mem :=
    Outs.of_outside (o := slot w 7) (n := 8 * (w + 2)) (out1.mono (Nat.le_refl _) (by omega)) (by simp)
  have c1 := h0.of k1 (by decide) (outs_pow o1)
  have R1 : V s₁.mem B w 1 = RRv := (h0.vj (by decide) (by decide) o1).trans hRRd
  have X1 : V s₁.mem B w 4 = X := (h0.vj (by decide) (by decide) o1).trans hXd
  -- `x R mod n` into array 6.
  refine WP.seq (WP.mono (c1.mont (o := 6) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R1]; exact hRRlt))
    fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [X1, R1, hR] at e2
  have XM : RRv = R * R % N → V s₂.mem B w 6 % N = X * R % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hcop ?_
    rw [e2, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have X2 : V s₂.mem B w 4 = X := (v2 4 (by decide) (by decide) (by decide) (by decide)).trans X1
  have S2 : V s₂.mem B w 7 = 1 := (v2 7 (by decide) (by decide) (by decide) (by decide)).trans h7
  have O2 : Outs B (powRs w) s.mem s₂.mem := (outs_pow o1).trans o2
  have k12 := k1.trans k2
  generalize hXMd : V s₂.mem B w 6 = XMv at lt2 XM
  -- The leading zeros.
  refine WP.seq (WP.mono (skip_ok (s := s₂) (v := v)
    (by rw [k2.gpr .r24 (by decide), k1.gpr .r24 (by decide)]; exact h24'))
    fun s₃ ⟨⟨i, hi, h25, hfound, m3⟩, k3⟩ => ?_)
  have c3 := c2.of k3 (by decide) (by rw [m3]; exact Outs.refl _ _ _)
  -- `a := x R mod n`.
  refine WP.seq (WP.mono (initA_ok c3) fun s₄ ⟨⟨c4, a4, v4, o4⟩, k4⟩ => ?_)
  rw [m3] at a4 v4 o4
  have k14 := (k12.trans k3).trans k4
  -- What holds after `q` shifts of `r24`.
  let Inv : Nat → State → Prop := fun q t =>
    Ctx t B Z w N ∧ Outs B (powRs w) s.mem t.mem ∧ V t.mem B w 6 = XMv ∧ V t.mem B w 7 = 1 ∧
      V t.mem B w 4 = X ∧ V t.mem B w 5 < N ∧ Keep powRegs s t ∧
      (0 < v → RRv = R * R % N →
        ∃ c, c * 2 ^ 64 + (t.gpr .r24).toNat = v * 2 ^ 31 * 2 ^ q ∧ V t.mem B w 5 % N = X ^ c * R % N)
  have I4 : Inv (i + 1) s₄ := ⟨c4, O2.trans o4, by rw [v4 6 (by decide) (by decide)]; exact hXMd,
    by rw [v4 7 (by decide) (by decide), S2], by rw [v4 4 (by decide) (by decide), X2],
    by rw [a4, hXMd]; exact lt2, k14.mono, fun hv0 hE => ⟨1, by
      rw [k4.gpr .r24 (by decide), Nat.one_mul]; exact hfound hv0, by rw [a4, hXMd, Nat.pow_one]; exact XM hE⟩⟩
  have h25' : s₄.gpr .r25 = BitVec.ofNat 64 (32 - i) := (k4.gpr .r25 (by decide)).trans h25
  -- The rest of the bits.
  have last : ∀ t, Inv 32 t → WP isa lastBit t fun u =>
      ((0 < v → RRv = R * R % N → V u.mem B w 4 = X ^ v % N) ∧ Outs B (powRs w) s.mem u.mem) ∧
        Keep powRegs s u := by
    intro t ⟨ct, ot, _, t7, t4, tA, kt, hc⟩
    refine WP.mono (lastBit_ok ct tA t7) fun u ⟨⟨S, eS, eY⟩, uY, ou, ku⟩ =>
      ⟨⟨fun hv0 hE => ?_, ot.trans ou⟩, (kt.trans ku).mono⟩
    obtain ⟨c, hc, hcA⟩ := hc hv0 hE
    rw [t4, hR] at eY
    rw [hR] at eS
    have hY := last_step hcop hcA eS (decide (2 ^ 63 ≤ (t.gpr .r24).toNat)) (by
      rw [eY]; simp only [decide_eq_true_eq])
    have hlt := (t.gpr .r24).isLt
    have hb : 2 * c + (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0) = v := by
      simp only [decide_eq_true_eq]
      rw [show v * 2 ^ 31 * 2 ^ 32 = v * 2 ^ 63 by rw [Nat.mul_assoc]] at hc
      split <;> omega
    rw [hb] at hY
    rw [← hY, Nat.mod_eq_of_lt uY]
  unfold bits
  refine WP.ite (decide (32 - i ≠ 0)) (by rw [eval_nonzero, h25', ne_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]) (fun hp => ?_) (fun hp => ?_)
  · simp only [ne_eq, decide_eq_true_eq] at hp
    refine WP.seq (WP.mono (subi_ok s₄ .r25 (by decide)) fun s₅ e5 => ?_)
    subst e5
    have h25'' : (s₄.write .r25 (s₄.gpr .r25 - BitVec.ofNat 64 1)).gpr .r25 = BitVec.ofNat 64 (31 - i) := by
      gsimp
      rw [h25']
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have I5 : Inv (i + 1) (s₄.write .r25 (s₄.gpr .r25 - BitVec.ofNat 64 1)) := by
      obtain ⟨ct, ot, t6, t7, t4, tA, kt, hc⟩ := I4
      exact ⟨ct.of (Keep.write _ _ _) (by decide) (by rw [mem_write]; exact Outs.refl _ _ _), by rw [mem_write]; exact ot,
        by rw [mem_write]; exact t6, by rw [mem_write]; exact t7, by rw [mem_write]; exact t4,
        by rw [mem_write]; exact tA, (kt.trans (Keep.write _ _ _)).mono,
        by gsimp; exact hc⟩
    refine WP.seq (WP.mono (?_ : WP isa _ _ (Inv 32)) fun t ht => last t ht)
    refine WP.ite (decide (31 - i ≠ 0)) (by rw [eval_nonzero, h25'', ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]) (fun hq => ?_) (fun hq => ?_)
    · simp only [ne_eq, decide_eq_true_eq] at hq
      refine WP.mono (wp_countdown (cnt := .r25) (N := 31 - i) (by omega) (by omega) (fun j t => Inv (i + 1 + j) t)
        (fun j _ t ⟨ct, ot, t6, t7, t4, tA, kt, hc⟩ _ => ?_) I5 h25'') fun t ht => by
          rwa [show i + 1 + (31 - i) = 32 by omega] at ht
      refine WP.seq (WP.mono (bitStep_ok ct tA (by rw [t6]; exact lt2))
        fun t₁ ⟨⟨c1', lt1', ⟨S, eS, eA⟩, v1', o1', a24⟩, k1'⟩ => ?_)
      refine WP.mono (subi_ok t₁ .r25 (by decide)) fun t₂ e => ?_
      subst e
      refine ⟨⟨c1'.of (Keep.write _ _ _) (by decide) (by rw [mem_write]; exact Outs.refl _ _ _),
        by rw [mem_write]; exact ot.trans o1', by rw [mem_write, v1' 6 (by decide) (by decide) (by decide) (by decide), t6],
        by rw [mem_write, v1' 7 (by decide) (by decide) (by decide) (by decide), t7],
        by rw [mem_write, v1' 4 (by decide) (by decide) (by decide) (by decide), t4],
        by rw [mem_write]; exact lt1', ((kt.trans k1').trans (Keep.write _ _ _)).mono, fun hv0 hE => ?_⟩,
        by gsimp; rw [k1'.gpr .r25 (by decide)]⟩
      obtain ⟨c, hc, hcA⟩ := hc hv0 hE
      rw [hR] at eS eA
      rw [t6] at eA
      have hsh := r24_shift (t.gpr .r24)
      rw [← a24] at hsh
      obtain ⟨hc', hA'⟩ := bit_step (b := decide (2 ^ 63 ≤ (t.gpr .r24).toNat)) hcop hcA (XM hE)
        eS (by simp only [decide_eq_true_eq]; exact eA) hc (by simp only [decide_eq_true_eq]; exact hsh)
      refine ⟨_, ?_, by rw [mem_write]; exact hA'⟩
      gsimp
      rw [show i + 1 + (j + 1) = i + 1 + j + 1 by omega]
      exact hc'
    · simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hq
      refine WP.block_nil ?_
      rw [show (32 : Nat) = i + 1 by omega]
      exact I5
  · simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hp
    -- `e = 1`: out of Montgomery form.
    obtain ⟨ct, ot, _, t7, _, tA, kt, _⟩ := I4
    refine WP.mono (ct.mont (o := 4) (a := 7) (b := 5) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) tA) fun u ⟨⟨_, uY, eY, _, ou⟩, ku⟩ =>
      ⟨⟨fun hv0 hE => ?_, ot.trans ou⟩, (kt.trans ku).mono⟩
    have hf := hfound hv0
    have hlt := (s₃.gpr .r24).isLt
    have hv1 : v = 1 := by
      rw [show i = 32 by omega, show v * 2 ^ 31 * 2 ^ (32 + 1) = v * 2 ^ 64 by rw [Nat.mul_assoc]] at hf
      omega
    subst hv1
    rw [t7, Nat.one_mul, hR, a4, hXMd] at eY
    refine (Nat.mod_eq_of_lt uY).symm.trans ?_
    exact VG.Proof.Bignum.mont_cancel hcop (by rw [eY, XM hE, Nat.pow_one])

end VG.Proof.Bignum.PPC64LE.Pub
