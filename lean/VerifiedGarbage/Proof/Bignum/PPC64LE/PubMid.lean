module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSan
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.PPC64LE.PubScan`, which only this module used -/

section

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
  refine o.val32 (fun r hr => ?_) (by omega_using [hnw, this])
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
  have := slot_sep (w := w) (Ne.symm (hjs k hk))
  omega_using [this]

/-- The context after code that writes only arrays 1–7 and none of `r10`,
`r11`, `r12`, `r29`. -/
theorem Ctx.of {s t : State} {B : Addr} {Z w N : Nat} (h : Ctx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ [Reg.r10, .r11, .r12, .r29], r ∉ rs) (o : Outs B (powRs w) s.mem t.mem) : Ctx t B Z w N := by
  have hnw := h.scr.nowrap
  obtain hrs' := fun r hr => k.gpr r (hrs r hr)
  obtain a0 : ∀ r ∈ powRs w, slot w 0 + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w 0 := fun r hr => by
    simp only [powRs, List.mem_map] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    have : k ≠ 0 := by revert k; decide
    have := slot_sep (w := w) (Ne.symm this)
    omega_using [this]
  obtain s0 := h.sl (j := 0) (by decide)
  refine ⟨h.scr.congr k.wr, h.w2, h.w31, h.hZ, (hrs' .r10 (by decide)).trans h.r10,
    (hrs' .r29 (by decide)).trans h.r29, (hrs' .r11 (by decide)).trans h.r11,
    by rw [hrs' .r12 (by decide)]; exact h.r12, ?_, ?_⟩
  · rw [hrs' .r12 (by decide), Outs.w32 o (fun r hr => by have := a0 r hr; omega_using [this]) (by omega_using [hnw, s0])]
    exact h.inv
  · rw [← h.n]
    exact o.val32 (fun r hr => by have := a0 r hr; omega_using [this]) (by omega_using [hnw, s0])

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
  obtain op : Outs B (powRs w) s.mem t.mem := outs_pow (js := [2, 3, o]) o' (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp <;> omega_using [ho, ho1])
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
  obtain e : BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
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
  split <;> omega_arith

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
    ⟨0, rfl, by omega_using [], h25, by rw [k1.gpr .r24 (by decide), h24]; simp, m1, k1.mono⟩
  refine WP.mono (skipBody_ok (n := 33 - i) (by omega_using [hi]) (by omega_using []) t25) fun t' ⟨⟨a24, a25, a3, am⟩, k'⟩ => ?_
  obtain hsh := r24_shift (t.gpr .r24)
  rw [← a24] at hsh
  obtain hlt := (t'.gpr .r24).isLt
  obtain hlt' := (t.gpr .r24).isLt
  obtain kt' : Keep [.r3, .r24, .r25] s t' := (kt.trans k').mono
  by_cases hb : 2 ^ 63 ≤ (t.gpr .r24).toNat
  · -- The first set bit: the loop ends.
    simp only [hb, ↓reduceIte] at a3 hsh
    refine .inl ⟨by rw [eval_nonzero, a3]; rfl, ⟨i, hi, by rw [a25]; congr 1; omega_using [], fun _ => ?_, am.trans tm⟩, kt'⟩
    rw [pow_step, ← t24]
    omega_using [hsh]
  · simp only [hb, ↓reduceIte, Nat.zero_mul, Nat.add_zero] at a3 hsh
    by_cases hz : i = 32
    · -- No set bit: `v = 0`.
      subst hz
      refine .inl ⟨by rw [eval_nonzero, a3]; rfl, ⟨32, by omega_using [], by rw [a25], fun hv0 => ?_, am.trans tm⟩, kt'⟩
      exfalso
      have : v * 2 ^ 31 * 2 ^ 32 < 2 ^ 63 := by rw [← t24]; omega_using [hb]
      have : 2 ^ 63 ≤ v * 2 ^ 31 * 2 ^ 32 := by
        rw [show (2 : Nat) ^ 63 = 1 * 2 ^ 31 * 2 ^ 32 from rfl]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hv0)
      omega_arith
    · refine .inr ⟨?_, 33 - (i + 1), by omega_using [hn, hi], i + 1, rfl, by omega_using [hi, hz], by rw [a25]; congr 1, ?_,
        am.trans tm, kt'⟩
      · rw [eval_nonzero, a3, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
        congr 1
        simp only [ne_eq, decide_eq_true_eq]
        omega_using [hi, hz]
      · rw [pow_step, ← t24]
        omega_using [hsh]

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
  obtain k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r9) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 6) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
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
  obtain s5 := h.sl (j := 5) (by decide)
  obtain s6 := h.sl (j := 6) (by decide)
  obtain d56 := slot_sep (w := w) (show (5 : Nat) ≠ 6 by decide)
  refine WP.mono (selectAcc_ok (b := true) (n := 2 * w) (dA := slot w 6) (dT := slot w 6) (dO := slot w 5)
    (h.scr.congr k1.wr) a8 a9 a5 ((k1.gpr _ (by decide)).trans h.r11) (by rw [a20]; decide)
    (by have := h.w2; omega_using [this])
    (by have := h.w31; omega_using [this]) (by omega_using [s6]) (by omega_using [s6]) (by omega_using [s5]) (by omega_using [d56]) (by omega_using [d56]))
    fun t ⟨hv, out, k2⟩ => ?_
  rw [m1] at hv out
  obtain o : Outs B ([5].map fun k => (slot w k, 8 * (w + 2))) s.mem t.mem :=
    Outs.of_outside (o := slot w 5) (n := 8 * (w + 2)) (out.mono (Nat.le_refl _) (by omega_using [])) (by simp)
  obtain op : Outs B (powRs w) s.mem t.mem := outs_pow o
  obtain k12 : Keep initRegs s t := (k1.trans k2).mono
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
  obtain e24 : s₁.gpr .r24 = s.gpr .r24 := k1.gpr .r24 (by decide)
  rw [e24, top_bit] at a3
  rw [e24] at a24
  obtain k12 := k1.trans k2
  obtain c2 : Ctx s₂ B Z w N := c1.of k2 (by decide) (by rw [m2]; exact Outs.refl _ _ _)
  obtain X1 : V s₁.mem B w 6 = V s.mem B w 6 := v1 6 (by decide) (by decide) (by decide) (by decide)
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
  obtain e24 : s₁.gpr .r24 = s.gpr .r24 := k1.gpr .r24 (by decide)
  rw [e24, top_bit] at a3
  obtain k12 := k1.trans k2
  obtain c2 : Ctx s₂ B Z w N := c1.of k2 (by decide) (by rw [m2]; exact Outs.refl _ _ _)
  obtain X1 : V s₁.mem B w 4 = V s.mem B w 4 := v1 4 (by decide) (by decide) (by decide) (by decide)
  obtain S1 : V s₁.mem B w 7 = 1 := by rw [v1 7 (by decide) (by decide) (by decide) (by decide), h7]
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
  omega_using []

/-- The last bit: `y R ≡ x^b S` with `S R ≡ a²` and `a ≡ x^c R`. -/
theorem last_step {A S Y X c R N : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hS : S * R % N = A * A % N) (b : Bool) (hY : Y * R % N = (if b then X else 1) * S % N) :
    Y % N = X ^ (2 * c + if b then 1 else 0) % N := by
  obtain hS' := sq_step hR hA hS
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
  omega_using [hr]

/-- A bit of the scan: `c` and `a ≡ x^c R` for the bits after `q` shifts. -/
theorem bit_step {A S A' X XM c R N r r' v q : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hXM : XM % N = X * R % N) (hS : S * R % N = A * A % N) (b : Bool)
    (hA' : if b then A' * R % N = S * XM % N else A' = S) (hc : c * 2 ^ 64 + r = v * 2 ^ 31 * 2 ^ q)
    (hr : r' + (if b then 1 else 0) * 2 ^ 64 = 2 * r) :
    (2 * c + if b then 1 else 0) * 2 ^ 64 + r' = v * 2 ^ 31 * 2 ^ (q + 1) ∧
      A' % N = X ^ (2 * c + if b then 1 else 0) * R % N := by
  obtain hS' := sq_step hR hA hS
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
  have hN0 : 0 < N := by omega_using [hN]
  generalize hXd : val32 s.mem B (slot w 4) (2 * w) = X
  generalize hRRd : val32 s.mem B (slot w 1) (2 * w) = RRv at hRRlt ⊢
  generalize hv : E % 2 ^ 33 = v
  have h24' : (s.gpr .r24).toNat = v * 2 ^ 31 := by rw [h24, shl31_toNat, hv]
  unfold power
  -- 1 in array 7.
  refine WP.seq (WP.mono (oneP_ok hs (by omega_using [hw2]) hw' hZ h10 h29 h11) fun s₁ ⟨⟨h7, out1⟩, k1⟩ => ?_)
  have o1 : Outs B ([7].map fun k => (slot w k, 8 * (w + 2))) s.mem s₁.mem :=
    Outs.of_outside (o := slot w 7) (n := 8 * (w + 2)) (out1.mono (Nat.le_refl _) (by omega_using [])) (by simp)
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
      split <;> omega_arith
    rw [hb] at hY
    rw [← hY, Nat.mod_eq_of_lt uY]
  unfold bits
  refine WP.ite (decide (32 - i ≠ 0)) (by rw [eval_nonzero, h25', ne_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [])]) (fun hp => ?_) (fun hp => ?_)
  · simp only [ne_eq, decide_eq_true_eq] at hp
    refine WP.seq (WP.mono (subi_ok s₄ .r25 (by decide)) fun s₅ e5 => ?_)
    subst e5
    have h25'' : (s₄.write .r25 (s₄.gpr .r25 - BitVec.ofNat 64 1)).gpr .r25 = BitVec.ofNat 64 (31 - i) := by
      gsimp
      rw [h25']
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [hp]
    have I5 : Inv (i + 1) (s₄.write .r25 (s₄.gpr .r25 - BitVec.ofNat 64 1)) := by
      obtain ⟨ct, ot, t6, t7, t4, tA, kt, hc⟩ := I4
      exact ⟨ct.of (Keep.write _ _ _) (by decide) (by rw [mem_write]; exact Outs.refl _ _ _), by rw [mem_write]; exact ot,
        by rw [mem_write]; exact t6, by rw [mem_write]; exact t7, by rw [mem_write]; exact t4,
        by rw [mem_write]; exact tA, (kt.trans (Keep.write _ _ _)).mono,
        by gsimp; exact hc⟩
    refine WP.seq (WP.mono (?_ : WP isa _ _ (Inv 32)) fun t ht => last t ht)
    refine WP.ite (decide (31 - i ≠ 0)) (by rw [eval_nonzero, h25'', ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [])]) (fun hq => ?_) (fun hq => ?_)
    · simp only [ne_eq, decide_eq_true_eq] at hq
      refine WP.mono (wp_countdown (cnt := .r25) (N := 31 - i) (by omega_using []) (by omega_using [hq]) (fun j t => Inv (i + 1 + j) t)
        (fun j _ t ⟨ct, ot, t6, t7, t4, tA, kt, hc⟩ _ => ?_) I5 h25'') fun t ht => by
          rwa [show i + 1 + (31 - i) = 32 by omega_using [hp]] at ht
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
      rw [show i + 1 + (j + 1) = i + 1 + j + 1 by omega_using []]
      exact hc'
    · simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hq
      refine WP.block_nil ?_
      rw [show (32 : Nat) = i + 1 by omega_using [hp, hq]]
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
      rw [show i = 32 by omega_using [hi, hp], show v * 2 ^ 31 * 2 ^ (32 + 1) = v * 2 ^ 64 by rw [Nat.mul_assoc]] at hf
      omega_using [hf]
    subst hv1
    rw [t7, Nat.one_mul, hR, a4, hXMd] at eY
    refine (Nat.mod_eq_of_lt uY).symm.trans ?_
    exact VG.Proof.Bignum.mont_cancel hcop (by rw [eY, XM hE, Nat.pow_one])

end VG.Proof.Bignum.PPC64LE.Pub

end

end


/-!
# The RSA public-key operation on PPC64LE: from `setup` to the output

`mid_ok`: from the state after `setup` (`Mid`), everything up to restoring
the registers: the result and the return value, with only the arrays and
`out` changed.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

theorem exponentValid_sat (v : Nat) : Spec.Rsa.exponentValid (sat v) = Spec.Rsa.exponentValid v := by
  unfold sat
  by_cases h : v < 2 ^ 33
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right (by omega_arith)]
    obtain h2 : (decide (v < 2 ^ 33)) = false := decide_eq_false h
    simp only [Spec.Rsa.exponentValid, h2, Bool.and_false]
    decide

/-- `k` bytes reversed from the low bytes of a number of `2 w` digits below
`256^k`: its I2OSP. -/
theorem out_bytes {m m' : Mem} {O B : Addr} {d k w v : Nat} (hkw : k ≤ 8 * w)
    (hv : Mont.val32 m B d (2 * w) = v) (hvk : v < 256 ^ k)
    (h : ∀ i < k, m' (off O i) = m (off B (d + (k - 1 - i)))) :
    Spec.Rsa.bytesAt m' O k = Spec.Rsa.i2osp v k := by
  rw [reversed_i2osp m m' (off B d) O k fun j hj => by rw [h j hj, off, off, Offset.add_add]]
  congr 1
  obtain e := read_eq_val32 m B (2 * w) d
  rw [hv] at e
  rw [read_prefix_value m (off B d) (show k ≤ 4 * (2 * w) by omega_arith) (by rw [e, ← pow256_eq]; exact hvk), e]

theorem zero_bytes {m' : Mem} {O : Addr} {k : Nat} (h : ∀ i < k, m' (off O i) = 0) :
    Spec.Rsa.bytesAt m' O k = List.replicate k 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  exact h i h1

theorem bytes_apart {m m' : Mem} {B X : Addr} {Z o n k : Nat} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off X i ≠ x) : Spec.Rsa.bytesAt m' X k = Spec.Rsa.bytesAt m X k := by
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  show m' (off X i) = m (off X i)
  refine h _ (Or.inr ?_)
  have := hsep i hi (off X i)
  by_contra hc
  exact this (by omega) rfl

theorem mask_and_prop (a : Bool) (p : Prop) [Decidable p] :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if a then 1 else 0)) &&&
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if p then 1 else 0)) =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 (if (a && decide p) then 1 else 0) := by
  by_cases hp : p <;> simp only [hp, decide_true, decide_false] <;> cases a <;> decide

/-- Memory changed only at offsets `[d, d + L)` of `S`, then at `O`'s first
`k` bytes. -/
theorem frame_two {S O : Addr} {d L k : Nat} {m m₁ m' : Mem} (h₁ : Outside S d L m m₁)
    (h₂ : Outside O 0 k m₁ m') (hdL : d + L ≤ 2 ^ 64) : Frame [⟨off S d, L⟩, ⟨O, k⟩] m m' := by
  intro x hx
  obtain a := hx _ (List.mem_cons_self ..)
  obtain b := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [Region.Contains] at a b
  rw [h₂ x (Or.inr (by simp only [ofs]; omega_arith))]
  refine h₁ x ?_
  have := Offset.lt_iff x S (d := d) (n := L) hdL
  simp only [ofs]
  by_contra hc
  exact a (by have := this.mpr ⟨by omega, by omega⟩; simp only [off]; omega_using [this])

/-- The public data of a run: `out` and `k`, `pre`, `e` and its length, the
input, and the working space and its size in bytes. -/
structure PD where
  O : Addr
  k : Nat
  P : Addr
  E : Addr
  L : Nat
  X : Addr
  S : Addr
  Z : Nat

/-- The words of a number of `k` bytes. -/
abbrev PD.w (d : PD) : Nat := (d.k + 7) / 8

/-- What holds after `setup`. -/
structure Mid (d : PD) (s : State) : Prop where
  scr : Scr s d.S d.Z
  out : Scr s d.O d.k
  k64 : 64 ≤ d.k
  k1024 : d.k ≤ 1024
  hZ : slot d.w 8 ≤ d.Z
  L1 : 1 ≤ d.L
  Lk : d.L ≤ d.k
  nwP : d.P.toNat + 16 * d.w ≤ 2 ^ 64
  sepP : ∀ x, ofs d.P x < 16 * d.w → d.Z ≤ ofs d.S x
  sepO : ∀ x, ofs d.O x < d.k → d.Z ≤ ofs d.S x
  sepE : ∀ i < d.L, ∀ x, ofs d.S x < d.Z → off d.E i ≠ x
  sepX : ∀ i < d.k, ∀ x, ofs d.S x < d.Z → off d.X i ≠ x
  rdP : ∀ i < 2 * d.w, InRegions (s.rd ++ s.wr) (off d.P (8 * i)) 8
  rdE : ∀ i < d.L, InRegions (s.rd ++ s.wr) (off d.E i) 1
  rdX : ∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.X i) 1
  r5 : s.gpr .r5 = off d.P 0
  r7 : s.gpr .r7 = off d.E 0
  r8 : s.gpr .r8 = BitVec.ofNat 64 d.L
  r9 : s.gpr .r9 = d.X
  r23 : s.gpr .r23 = d.S
  r27 : s.gpr .r27 = off d.O 0
  r28 : s.gpr .r28 = BitVec.ofNat 64 d.k
  r10 : s.gpr .r10 = off d.S (slot d.w 0)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * d.w)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (d.w + 2))

/-- The registers from `readE` to `output`. -/
def midRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24,
    .r25, .r26]

/-- What holds after `output`: the result, with only the arrays and `out`
changed. -/
def MidPost (d : PD) (s t : State) : Prop :=
  (∀ nB : List Byte, nB.length = d.k →
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem d.P (2 * d.w)) →
    Spec.Rsa.written t.mem d.O d.k ((t.gpr .r3).setWidth 32)
      (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem d.E d.L) (Spec.Rsa.bytesAt s.mem d.X d.k))) ∧
    Frame [⟨off d.S (slot d.w 0), 8 * (8 * (d.w + 2))⟩, ⟨d.O, d.k⟩] s.mem t.mem ∧ Keep midRegs s t

/-- `e`'s number, saturated. -/
abbrev PD.ev (d : PD) (m : Mem) : Nat := sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m d.E d.L))

/-- The input's number. -/
abbrev PD.x (d : PD) (m : Mem) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt m d.X d.k)

/-- What holds after `sanitize`, from `s` after `setup`. -/
structure M5 (d : PD) (s t : State) : Prop where
  keep : Keep midRegs s t
  r24 : t.gpr .r24 = BitVec.ofNat 64 (d.ev s.mem) <<< 31
  r26 : t.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid (d.ev s.mem) then 1 else 0)
  r10 : t.gpr .r10 = off d.S (slot d.w 0)
  odd : wv t.mem d.S (slot d.w 0) d.w % 2 = 1
  ge2 : 2 ≤ wv t.mem d.S (slot d.w 0) d.w
  low : (word t.mem d.S (slot d.w 0)).toNat % 2 = 1
  rr : wv t.mem d.S (slot d.w 1) d.w < wv t.mem d.S (slot d.w 0) d.w
  valid : wv s.mem d.P 0 d.w % 2 = 1 → 2 ^ (64 * (d.w - 1)) ≤ wv s.mem d.P 0 d.w →
    wv t.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w ∧
      (wv s.mem d.P (8 * d.w) d.w < wv s.mem d.P 0 d.w → wv t.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w)
  top : word t.mem d.S (slot d.w 4 + 8 * d.w) = 0
  x : wv t.mem d.S (slot d.w 4) d.w = d.x s.mem
  frame : Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s.mem t.mem

theorem mid5_ok {d : PD} {s : State} {c : Prog isa} {Q : State → Prop} (h : Mid d s)
    (hQ : ∀ t, M5 d s t → WP isa c t Q) :
    WP isa (.seq readE (.seq (.block checkE) (.seq copyPre (.seq loadX (.seq sanitize c))))) s Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hw8 : 8 ≤ d.w := by have := h.k64; omega_arith
  obtain hw' : d.w < 2 ^ 31 := by have := h.k1024; omega_arith
  obtain hkw : d.k ≤ 8 * d.w := by omega_arith
  obtain e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  -- `e`.
  refine WP.seq (WP.mono (readE_ok (E := d.E) (L := d.L) h.r7 h.r8 h.L1 (by have := h.Lk; have := h.k1024; omega_arith)
    h.rdE) fun s₁ ⟨⟨a24, m1⟩, k1⟩ => ?_)
  obtain hev2 : d.ev s.mem ≤ 2 ^ 33 := by unfold PD.ev sat; omega_arith
  refine WP.seq (WP.mono (checkE_ok a24 hev2) fun s₂ ⟨⟨a26, a24', m2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  obtain m12 : s₂.mem = s.mem := m2.trans m1
  -- `pre` into arrays 0 and 1.
  refine WP.seq (WP.mono (copyPre_ok (h.scr.congr k12.wr) h.nwP (by rw [k12.rd, k12.wr]; exact h.rdP)
    ((k12.gpr _ (by decide)).trans h.r5) ((k12.gpr _ (by decide)).trans h.r10)
    ((k12.gpr _ (by decide)).trans h.r29) ((k12.gpr _ (by decide)).trans h.r11) (by omega_arith) hw' hZ h.sepP)
    fun s₃ ⟨⟨c0, c1, out3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  rw [m12] at c0 c1 out3
  obtain N3 : wv s₃.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w :=
    wv_congr2 fun i hi => by rw [Nat.zero_add]; exact c0 i hi
  obtain R3 : wv s₃.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w := wv_congr2 fun i hi => c1 i hi
  -- The input into array 4.
  refine WP.seq (WP.mono (loadX_ok (h.scr.congr k13.wr) ((k13.gpr _ (by decide)).trans h.r23)
    ((k13.gpr _ (by decide)).trans h.r9) ((k13.gpr _ (by decide)).trans h.r28)
    ((k13.gpr _ (by decide)).trans h.r10) ((k13.gpr _ (by decide)).trans h.r29)
    ((k13.gpr _ (by decide)).trans h.r11) (by omega_arith) hkw hw' hZ (by rw [k13.rd, k13.wr]; exact h.rdX) h.sepX)
    fun s₄ ⟨⟨x4, z4, out4, a10⟩, k4⟩ => ?_)
  rw [bytes_apart out3 (by omega_arith) h.sepX] at x4
  obtain k14 := k13.trans k4
  obtain N4 : wv s₄.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w := by
    rw [out4.wv (Or.inl (by omega_arith)) (by omega_arith), N3]
  obtain R4 : wv s₄.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w := by
    rw [out4.wv (Or.inl (by omega_arith)) (by omega_arith), R3]
  -- `n` and `R² mod n` made safe.
  refine WP.seq (WP.mono (sanitize_ok (h.scr.congr k14.wr) (by omega_arith) hw' hZ a10
    ((k14.gpr _ (by decide)).trans h.r29) ((k14.gpr _ (by decide)).trans h.r11))
    fun s₅ ⟨⟨n5o, n5g, n5w, r5l, n5v, out5⟩, k5⟩ => hQ s₅ ⟨(k14.trans k5).mono, ?_, ?_,
      (k5.gpr _ (by decide)).trans a10, ?_, ?_, n5w, ?_, ?_, by rw [out5.word (by omega_arith) (by omega_arith)]; exact z4, ?_,
      ((out3.mono (Nat.le_refl _) (by omega_arith)).trans (out4.mono (by omega_arith) (by omega_arith))).trans
        (out5.mono (Nat.le_refl _) (by omega_arith))⟩)
  · rw [k5.gpr .r24 (by decide), k4.gpr .r24 (by decide), k3.gpr .r24 (by decide)]; exact a24'
  · rw [k5.gpr .r26 (by decide), k4.gpr .r26 (by decide), k3.gpr .r26 (by decide)]; exact a26
  · rw [← Pre.val32_eq_wv]; exact n5o
  · rw [← Pre.val32_eq_wv]; exact n5g
  · rw [← Pre.val32_eq_wv, ← Pre.val32_eq_wv]; exact r5l
  · simp only [Pre.val32_eq_wv, N4, R4] at n5v
    exact n5v
  · rw [out5.wv (Or.inr (by omega_arith)) (by omega_arith), ← Pre.val32_eq_wv]; exact x4

/-- What holds after `power`, from `s` after `setup`, with `N` the modulus
used. -/
structure M8 (d : PD) (s u : State) (N : Nat) : Prop where
  keep : Keep midRegs s u
  r10 : u.gpr .r10 = off d.S (slot d.w 0)
  r26 : u.gpr .r26 = BitVec.ofNat 64 0 -
    BitVec.ofNat 64 (if (Spec.Rsa.exponentValid (d.ev s.mem) && decide (d.x s.mem < N)) then 1 else 0)
  res : wv s.mem d.P 0 d.w % 2 = 1 → 2 ^ (64 * (d.w - 1)) ≤ wv s.mem d.P 0 d.w →
    wv s.mem d.P (8 * d.w) d.w = 2 ^ (64 * d.w) * 2 ^ (64 * d.w) % wv s.mem d.P 0 d.w →
    N = wv s.mem d.P 0 d.w ∧ (Spec.Rsa.exponentValid (d.ev s.mem) = true →
      wv u.mem d.S (slot d.w 4) d.w = d.x s.mem ^ (d.ev s.mem % 2 ^ 33) % N)
  frame : Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s.mem u.mem

/-- What holds after `checkX`, from `t` after `sanitize`. -/
def M7 (d : PD) (t s₇ : State) : Prop :=
  ∃ s₆ : State, ((s₆.gpr .r12).toNat < 2 ^ 32 ∧
      (Mont.w32 t.mem d.S (slot d.w 0) * (s₆.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧ s₆.mem = t.mem) ∧
    Keep [.r0, .r3, .r4, .r12] t s₆ ∧
    (s₇.gpr .r26 = s₆.gpr .r26 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64
        (if Mont.val32 s₆.mem d.S (slot d.w 4) (2 * d.w) < Mont.val32 s₆.mem d.S (slot d.w 0) (2 * d.w) then 1
          else 0)) ∧
      Mont.Outside d.S (slot d.w 3) (8 * d.w) s₆.mem s₇.mem) ∧
    Keep [.r0, .r3, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r26] s₆ s₇

theorem mid7_ok {d : PD} {s t : State} (h : Mid d s) (h5 : M5 d s t) :
    WP isa (.seq (.block minv) checkX) t (M7 d t) := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hw8 : 8 ≤ d.w := by have := h.k64; omega_arith
  obtain hw' : d.w < 2 ^ 31 := by have := h.k1024; omega_arith
  obtain e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  have k5 := h5.keep
  obtain hs₅ := h.scr.congr k5.wr
  -- `-n⁻¹ mod 2³²`.
  refine WP.seq (WP.mono (minv_ok hs₅ h5.r10 (by omega_arith) h5.low) fun s₆ ⟨⟨i12, iinv, m6⟩, k6⟩ => ?_)
  obtain k56 := k5.trans k6
  -- Whether the input is below `n`.
  exact WP.mono (checkX_ok (h.scr.congr k56.wr) (by omega_arith) hw' hZ ((k6.gpr _ (by decide)).trans h5.r10)
    ((k56.gpr _ (by decide)).trans h.r29) ((k56.gpr _ (by decide)).trans h.r11)
    (by rw [m6]; exact h5.top)) fun s₇ ⟨⟨c26, out7⟩, k7⟩ => ⟨s₆, ⟨i12, iinv, m6⟩, k6, ⟨c26, out7⟩, k7⟩

/-- From `setup` to the checks. -/
theorem prep_ok {d : PD} {s : State} (h : Mid d s) :
    WP isa prep s fun u => ∃ t, M5 d s t ∧ M7 d t u :=
  mid5_ok h fun t h5 => WP.mono (mid7_ok h h5) fun _ h7 => ⟨t, h5, h7⟩

theorem mid8_ok {d : PD} {s t s₇ : State} {Q : State → Prop} (h : Mid d s) (h5 : M5 d s t)
    (h7 : M7 d t s₇) (hQ : ∀ u N, M8 d s u N → Q u) : WP isa power s₇ Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hw8 : 8 ≤ d.w := by have := h.k64; omega_arith
  obtain hw' : d.w < 2 ^ 31 := by have := h.k1024; omega_arith
  obtain e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  have k5 := h5.keep
  obtain ⟨s₆, ⟨i12, iinv, m6⟩, k6, ⟨c26, out7⟩, k7⟩ := h7
  obtain k56 := k5.trans k6
  obtain k57 := k56.trans k7
  obtain out7' : Outside d.S (slot d.w 3) (8 * d.w) t.mem s₇.mem := by
    rw [← m6]; exact fun x hx => out7 x hx
  simp only [Pre.val32_eq_wv] at c26
  rw [m6] at c26
  obtain N7 : wv s₇.mem d.S (slot d.w 0) d.w = wv t.mem d.S (slot d.w 0) d.w :=
    out7'.wv (Or.inl (by omega_arith)) (by omega_arith)
  obtain R7 : wv s₇.mem d.S (slot d.w 1) d.w = wv t.mem d.S (slot d.w 1) d.w :=
    out7'.wv (Or.inl (by omega_arith)) (by omega_arith)
  obtain X7 : wv s₇.mem d.S (slot d.w 4) d.w = wv t.mem d.S (slot d.w 4) d.w :=
    out7'.wv (Or.inr (by omega_arith)) (by omega_arith)
  obtain W7 : Mont.w32 s₇.mem d.S (slot d.w 0) = Mont.w32 t.mem d.S (slot d.w 0) := by
    rw [Mont.Outside.w32 out7 (Or.inl (by omega_arith)) (by omega_arith), m6]
  -- `x^e mod n` into array 4.
  refine WP.mono (power_ok (E := d.ev s.mem) (h.scr.congr k57.wr) (by omega_arith) hw' hZ
    ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans h5.r10)) ((k57.gpr _ (by decide)).trans h.r29)
    ((k57.gpr _ (by decide)).trans h.r11) (by rw [k7.gpr .r12 (by decide)]; exact i12)
    (by rw [k7.gpr .r12 (by decide), W7]; exact iinv)
    (by rw [Pre.val32_eq_wv, N7]; exact h5.ge2) (by rw [Pre.val32_eq_wv, N7]; exact h5.odd)
    (by rw [Pre.val32_eq_wv, Pre.val32_eq_wv, N7, R7]; exact h5.rr)
    (by rw [k7.gpr .r24 (by decide), k6.gpr .r24 (by decide)]; exact h5.r24)) fun s₈ ⟨⟨p8, out8⟩, k8⟩ => ?_
  simp only [Pre.val32_eq_wv, N7, R7, X7, h5.x] at p8
  refine hQ s₈ (wv t.mem d.S (slot d.w 0) d.w) ⟨(k57.trans k8).mono,
    (k8.gpr _ (by decide)).trans ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans h5.r10)), ?_,
    fun hodd htop hRR => ?_, ?_⟩
  · rw [k8.gpr .r26 (by decide), c26, k6.gpr .r26 (by decide), h5.r26, h5.x, mask_and_prop]
  · obtain ⟨N5, RR5⟩ := h5.valid hodd htop
    obtain hRl : wv s.mem d.P (8 * d.w) d.w < wv s.mem d.P 0 d.w := by
      rw [hRR]; exact Nat.mod_lt _ (by omega_arith)
    refine ⟨N5, fun he => p8 ?_ ?_⟩
    · simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at he
      omega
    · rw [RR5 hRl, N5, hRR]
  · have o8 : Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s₇.mem s₈.mem := fun x hx => out8 x fun r hr => by
      obtain e2 := e 2; have e5 := e 5; have e6 := e 6; have e7 := e 7
      simp only [powRs, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨j, hj, rfl⟩ := hr
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Mont.ofs, ofs] at hx ⊢ <;> omega_arith
    exact (h5.frame.trans (out7'.mono (by omega_arith) (by omega_arith))).trans o8

theorem midOut_ok {d : PD} {s u : State} {N : Nat} {Q : State → Prop} (h : Mid d s) (h8 : M8 d s u N)
    (hQ : ∀ t, MidPost d s t → WP isa (.block PublicChecked.restore) t Q) :
    WP isa (.seq output (.block PublicChecked.restore)) u Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hkw : d.k ≤ 8 * d.w := by omega_arith
  have e0 : slot d.w 0 = hdrBytes + 0 * (8 * (d.w + 2)) := rfl
  have e8 : slot d.w 8 = hdrBytes + 8 * (8 * (d.w + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have k8 := h8.keep
  refine WP.seq (WP.mono (output_ok (h.scr.congr k8.wr) (h.out.congr k8.wr) h8.r10
    ((k8.gpr _ (by decide)).trans h.r29) ((k8.gpr _ (by decide)).trans h.r28)
    ((k8.gpr _ (by decide)).trans h.r27) h8.r26 (by have := h.k64; omega_arith) hkw h.hZ h.sepO)
    fun t ⟨⟨ob, outt, t3⟩, kt⟩ => hQ t ⟨?_, frame_two h8.frame outt (by have := h.k1024; omega_arith),
      (k8.trans kt).mono⟩)
  intro nB hl hpp
  obtain ⟨hv, hn, hr⟩ := pre_of_some hl h.k64 hpp
  obtain ⟨hodd, hn1, htop⟩ := valid_facts hv h.k64
  rw [← hn] at hodd htop hn1
  obtain ⟨hN, res⟩ := h8.res hodd htop
    (by rw [hr, hn, ← Nat.pow_add, show 64 * d.w + 64 * d.w = 128 * d.w by omega_arith])
  rw [hN, hn] at res ob t3
  obtain hE := exponentValid_sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L))
  obtain hnk : Spec.Rsa.os2ip nB < 256 ^ d.k := by rw [← hl]; exact os2ip_lt nB
  unfold Spec.Rsa.publicOpChecked Spec.Rsa.publicOp Spec.Rsa.encrypt
  rw [← hE, hl]
  by_cases hb : (Spec.Rsa.exponentValid (d.ev s.mem) && decide (d.x s.mem < Spec.Rsa.os2ip nB)) = true
  · obtain ⟨he, hx⟩ : Spec.Rsa.exponentValid (d.ev s.mem) = true ∧ d.x s.mem < Spec.Rsa.os2ip nB := by
      simpa using hb
    obtain hlt : d.ev s.mem < 2 ^ 33 := by
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at he; exact he.2
    obtain hev : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L)) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L) := by
      unfold PD.ev sat at hlt; unfold sat; omega_arith
    replace res := res he
    simp only [PD.ev, PD.x] at he hx res
    simp only [he, hv, hx, ↓reduceIte, Option.map_some]
    refine ⟨by rw [t3, hb]; rfl, ?_⟩
    rw [VG.Proof.Bignum.powMod_eq]
    rw [hev, Nat.mod_eq_of_lt (a := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L)) (b := 2 ^ 33)
      (by rw [← hev]; exact hlt)] at res
    exact out_bytes hkw (by rw [Pre.val32_eq_wv]; exact res)
      (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hnk) fun i hi => by rw [ob i hi]; simp only [hb, ↓reduceIte]
  · have hnone : (if Spec.Rsa.exponentValid (d.ev s.mem) = true then
        (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) d.k = true then
          Option.map (fun x => Spec.Rsa.i2osp x d.k)
            (if d.x s.mem < Spec.Rsa.os2ip nB then
              some (Spec.Rsa.powMod (d.x s.mem) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L))
                (Spec.Rsa.os2ip nB))
            else none)
        else none)
      else none) = none := by
      by_cases he : Spec.Rsa.exponentValid (d.ev s.mem) = true
      · have hx : ¬ d.x s.mem < Spec.Rsa.os2ip nB := fun hx => hb (by simp [he, hx])
        simp only [he, hv, hx, ↓reduceIte, Option.map_none]
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
    simp only [PD.ev, PD.x] at hnone
    rw [hnone]
    refine ⟨by rw [t3]; simp only [hb]; rfl,
      zero_bytes fun i hi => by rw [ob i hi]; simp only [hb, Bool.false_eq_true, ↓reduceIte]⟩

/-- From `setup` to the output. -/
theorem mid_ok {d : PD} {s : State} {Q : State → Prop} (h : Mid d s)
    (hQ : ∀ t, MidPost d s t → WP isa (.block PublicChecked.restore) t Q) :
    WP isa (.seq prep (.seq power (.seq output (.block PublicChecked.restore)))) s Q :=
  WP.seq (WP.mono (prep_ok h) fun _ ⟨_, h5, h7⟩ => WP.seq (mid8_ok h h5 h7 fun _ _ h8 => midOut_ok h h8 hQ))

end VG.Proof.Bignum.PPC64LE.Pub
