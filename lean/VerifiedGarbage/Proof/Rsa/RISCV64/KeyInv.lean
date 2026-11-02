module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Inverse
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `inverse` on RISC-V

As PPC64LE's unbatched inverse (`Proof/Rsa/PPC64LE/Inv{Parts,U,Step,Loop}.lean`),
in words of 64 bits:

* `subModP_ok`: `subModP o a b` computes `subMod m a b` for `a, b < m`, and
  `halfModP_ok`: a step's end computes `halfMod m` of `[aT3]`, with the
  negated modulus `2^(64 w) - m` in `aNM` and zero in `aZero`;
* `invU_ok`: a step's `u` and `v`; `invStep_ok`: a step is
  `KeyMath.invStep`;
* `inverse_ok`: `K` iterations of two steps, `K` in `s7`, are
  `invIter m (2 K)`; `inverse_done`: from `(a, m, 1, 0)` with
  `a m < 2^(2 K)`, array 1 ends as `gcd(a, m)` and array 3 as `x < m` with
  `x a ≡ gcd(a, m) (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (seqs sub3 sel bitOf stBorrow andS half subModP inverse aM aNM aZero aT1 aT2
  aT3 aT4 sOdd sB sC)
open VG.Proof.Rsa (subMod halfMod subMod_impl halfMod_impl invU_arith borrow_iff invStep_arith invIter InvI
  invI_start')

theorem wp_seqs_cons {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (c :: l)) s Q ↔ WP isa c s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem wp_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s : State}
    {Q : State → Prop} :
    WP isa (seqs (l₁ ++ l₂)) s Q ↔ WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) := by
  induction l₁ generalizing s with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · exact wp_seqs_cons h₂
    · rw [List.cons_append, wp_seqs_cons (by simp), wp_seqs_cons (by simp)]
      exact ⟨fun h => WP.mono h fun t ht => (ih (by simp)).mp ht,
        fun h => WP.mono h fun t ht => (ih (by simp)).mpr ht⟩

/-- Index side conditions. -/
macro "idx" : tactic => `(tactic| ((try simp only [aM, aNM, aZero, aT1, aT2, aT3, aT4, sOdd, sB, sC,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-! ## Differences and halvings modulo `m` -/

/-- `subModP o a b`: `[o] = [a] - [b] mod m`. -/
theorem subModP_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 2048) (ho : o < N) (ha : a < N) (hb : b < N)
    (hoT1 : o ≠ aT1) (hoT4 : o ≠ aT4) (haT1 : a ≠ aT1) (hbT1 : b ≠ aT1) :
    WP isa (seqs (subModP o a b)) s fun t => Ws t B Z w N ∧
      Frame B w [aT1, aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (64 * w) → num s.mem B w aZero = 0 →
        num s.mem B w a < num s.mem B w aM → num s.mem B w b < num s.mem B w aM →
        num t.mem B w o = subMod (num s.mem B w aM) (num s.mem B w a) (num s.mem B w b)) ∧
      Keep opRegs s t := by
  have hsB : sB + 8 ≤ hdr := by decide
  simp only [aT1, aT4] at hoT1 hoT4 haT1 hbT1
  unfold subModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h (by idx) ha hb hN (by idx) (by idx)) fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (stBorrow_ok h1 hsB (by decide)) fun t2 ⟨h2, k2, s2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h2 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsB (by decide)
    (by rw [s2]; exact b1)) fun t3 ⟨h3, k3, v3, r3⟩ => ?_
  refine WP.mono (sub3_ok h3 ho (by idx) (by idx) hN hoT1 hoT4) fun t ⟨h4, k4, v4, b4, r4⟩ => ?_
  refine ⟨h4, Frame.join (k1.join k2 (js := [aT1, aT4, o]) (ds := [sB]))
      (k3.join k4 (js := [aT1, aT4, o]) (ds := [sB])),
    fun hNM hZ ha' hb' => ?_, Keep.trans' r1 (Keep.trans' (Keep.mono r2 (by decide)) (Keep.trans' r3 r4))⟩
  have P := h.wpos
  have fz := h.fit64 (j := aZero) (by idx)
  have fn := h.fit64 (j := aNM) (by idx)
  have fT1 := h.fit64 (j := aT1) (by idx)
  have z3 : num t2.mem B w aZero = 0 := by
    rw [k2.num (by simp) (by decide) fz, k1.num (by idx) (by simp) fz, hZ]
  have n3 : num t2.mem B w aNM = num s.mem B w aNM := by
    rw [k2.num (by simp) (by decide) fn, k1.num (by idx) (by simp) fn]
  have t13 : num t3.mem B w aT1 = num t1.mem B w aT1 := by
    rw [k3.num (by idx) (by simp) fT1, k2.num (by simp) (by decide) fT1]
  rw [t13] at v4
  rw [s2, z3, n3] at v3
  refine subMod_impl (P := 2 ^ (64 * w)) (by omega_arith) hb' v1 (wordsVal_lt _ _ _ _) b1 ?_ v4
    (wordsVal_lt _ _ _ _) b4
  rw [v3]
  split <;> omega_arith

/-- The halving of `[aT3]` modulo `m` into `[o]`. -/
def halfModP (o : Nat) : List (Prog isa) := [
  .block (bitOf sB aT3), sel aT4 aZero aNM sB, sub3 o aT3 aT4,
  .block [.load .d .t5 .s11 sB, .logic .xor .t4 .t4 .t5], half o]

/-- The exclusive or of two bits. -/
theorem xor_bits {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ^^^ y).toNat = (x.toNat + y.toNat) % 2 := by
  rw [BitVec.toNat_xor]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega_arith) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega_arith) with f | f <;> rw [e, f] <;> decide

theorem halfModP_ok {s : State} {B : Addr} {Z w N o : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 2048) (ho : o < N) (hoT3 : o ≠ aT3) (hoT4 : o ≠ aT4) :
    WP isa (seqs (halfModP o)) s fun t => Ws t B Z w N ∧ Frame B w [aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (64 * w) → num s.mem B w aZero = 0 →
        num t.mem B w o = halfMod (num s.mem B w aM) (num s.mem B w aT3)) ∧
      Keep opRegs s t := by
  have hsB : sB + 8 ≤ hdr := by decide
  simp only [aT3, aT4] at hoT3 hoT4
  unfold halfModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by idx) hN hsB (by decide)) fun t1 ⟨h1, k1, s1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have b1 : slot t1.mem B sB ≤ 1 := by rw [s1]; omega_arith
  refine WP.mono (sel_ok h1 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsB (by decide) b1)
    fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 ho (by idx) (by idx) hN hoT3 hoT4) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hz := h3.hdr_le
  have nw := h3.nowrap
  have sB3 : slot t3.mem B sB = slot t1.mem B sB := by
    rw [k3.slot hsB (by simp), k2.slot hsB (by simp)]
  have hx : WP isa (.block [.load .d .t5 .s11 sB, .logic .xor .t4 .t4 .t5]) t3 fun t4 =>
      (t4.gpr .t4 = t3.gpr .t4 ^^^ word t3.mem B sB ∧ t4.mem = t3.mem) ∧ Keep [.t4, .t5] t3 t4 := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h3.s11, h3.scr.ld (d := sB) (n := 8) (by simp only [hdr_eq] at hsB hz ⊢; omega_arith),
      h3.scr.al8 (d := sB) (by simp only [hdr_eq] at hsB hz ⊢; omega_arith) (by decide),
      show sB < 2048 by decide, add_ofNat_zero']
  refine WP.mono hx fun t4 ⟨⟨u4, m4⟩, k4⟩ => ?_
  have h5 : Ws t4 B Z w N := h3.of_keep k4
  have c4 : (t4.gpr .t4).toNat = ((t3.gpr .t4).toNat + num s.mem B w aT3 % 2) % 2 := by
    have e : (word t3.mem B sB).toNat = num s.mem B w aT3 % 2 := by
      change slot t3.mem B sB = _; rw [sB3, s1]
    rw [u4, xor_bits b3 (by rw [e]; omega_arith), e]
  refine WP.mono (half_ok h5 ho hN (by rw [c4]; omega_arith)) fun t ⟨h6, k6, v6, _, r6⟩ => ?_
  rw [m4] at k6 v6
  refine ⟨h6, (k1.join k2 (js := [aT4, o]) (ds := [sB])).join (k3.join k6 (js := [aT4, o]) (ds := [sB]))
      (js := [aT4, o]) (ds := [sB]), fun hNM hZ => ?_,
    Keep.trans' r1 (Keep.trans' r2 (Keep.trans' r3 (Keep.trans' (Keep.mono k4 (by decide)) r6)))⟩
  have f3 := h.fit64 (j := aT3) (by idx)
  have fz := h.fit64 (j := aZero) (by idx)
  have fn := h.fit64 (j := aNM) (by idx)
  have x2 : num t2.mem B w aT3 = num s.mem B w aT3 := by
    rw [k2.num (by idx) (by simp) f3, k1.num (by simp) (by decide) f3]
  have z1 : num t1.mem B w aZero = 0 := by rw [k1.num (by simp) (by decide) fz, hZ]
  have n1 : num t1.mem B w aNM = num s.mem B w aNM := k1.num (by simp) (by decide) fn
  rw [x2] at v3
  rw [s1, z1, n1] at v2
  rw [v6, c4]
  refine halfMod_impl (P := 2 ^ (64 * w)) (by omega_arith) (wordsVal_lt _ _ _ _) ?_ v3 (wordsVal_lt _ _ _ _)
    b3 rfl
  rw [v2]; split <;> omega_arith

/-! ## A step -/

/-- The first part of a step from the bank at `A` to the bank at `D`: `u`, `v`, and the masks. -/
def invU (A D : Nat) : List (Prog isa) := [
  .block (bitOf sOdd A),
  sub3 aT1 A (A + 1),
  .block (stBorrow sB ++ andS sC sOdd sB),
  sub3 aT2 (A + 1) A,
  sel (D + 1) (A + 1) A sC,
  sel aT3 aT1 aT2 sC,
  sel D A aT3 sOdd,
  .block [.li .t4 0],
  half D]

theorem invU_ok {s : State} {B : Addr} {Z w N A D : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 2048) (hb : (A = 0 ∧ D = 4) ∨ (A = 4 ∧ D = 0)) :
    WP isa (seqs (invU A D)) s fun t => Ws t B Z w N ∧
      Frame B w [D, D + 1, aT1, aT2, aT3] [sOdd, sB, sC] s.mem t.mem ∧
      slot t.mem B sOdd = num s.mem B w A % 2 ∧
      slot t.mem B sC = (if num s.mem B w A % 2 = 1 ∧ num s.mem B w A < num s.mem B w (A + 1) then 1 else 0) ∧
      num t.mem B w (D + 1) = (if num s.mem B w A % 2 = 1 ∧ num s.mem B w A < num s.mem B w (A + 1)
        then num s.mem B w A else num s.mem B w (A + 1)) ∧
      num t.mem B w D = (if num s.mem B w A % 2 = 1 then
        (if num s.mem B w A < num s.mem B w (A + 1) then (num s.mem B w (A + 1) - num s.mem B w A) / 2
          else (num s.mem B w A - num s.mem B w (A + 1)) / 2) else num s.mem B w A / 2) ∧
      Keep opRegs s t := by
  have hsOdd : sOdd + 8 ≤ hdr := by decide
  have hsB : sB + 8 ≤ hdr := by decide
  have hsC : sC + 8 ≤ hdr := by decide
  have fA := h.fit64 (j := A) (by idx)
  have fA1 := h.fit64 (j := A + 1) (by idx)
  have fT1 := h.fit64 (j := aT1) (by idx)
  have fT2 := h.fit64 (j := aT2) (by idx)
  have fD1 := h.fit64 (j := D + 1) (by idx)
  generalize hu : num s.mem B w A = u
  generalize hv : num s.mem B w (A + 1) = v
  unfold invU
  -- 1: the low bit of `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by idx) hN hsOdd (by decide)) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  rw [hu] at o1
  have u1 : num t1.mem B w A = u := by rw [k1.num (by simp) (by decide) fA, hu]
  have v1 : num t1.mem B w (A + 1) = v := by rw [k1.num (by simp) (by decide) fA1, hv]
  -- 2: `u - v`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (by idx) (by idx) (by idx) hN (by idx) (by idx)) fun t2 ⟨h2, k2, d2, b2, r2⟩ => ?_
  rw [u1, v1] at d2
  -- 3: the masks.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff]
  refine WP.mono (stBorrow_ok h2 hsB (by decide)) fun t3' ⟨h3', k3', sB3, r3'⟩ => ?_
  have o3 : slot t3'.mem B sOdd = u % 2 := by
    rw [k3'.slot hsOdd (by decide), k2.slot hsOdd (by simp), o1]
  refine WP.mono (andS_ok h3' hsC (by decide) hsOdd (by decide) hsB (by decide) (by rw [o3]; omega_arith)
    (by rw [sB3]; exact b2)) fun t3 ⟨h3, k3, c3, r3⟩ => ?_
  rw [o3, sB3] at c3
  have lt : (t2.gpr .t4).toNat = 1 ↔ u < v := by
    have := borrow_iff d2 (wordsVal_lt _ _ _ _) b2; omega_arith
  have c3' : slot t3.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [c3]
    rcases Nat.mod_two_eq_zero_or_one u with f | f
    · simp [f]
    · by_cases g : u < v
      · simp [f, g, lt.mpr g]
      · have : (t2.gpr .t4).toNat ≠ 1 := fun e => g (lt.mp e)
        simp only [f, g, and_false, ↓reduceIte, Nat.one_mul]
        omega_arith
  have K3 : Frame B w [] [sB, sC] t2.mem t3.mem := k3'.join k3
  have o3' : slot t3.mem B sOdd = u % 2 := by rw [k3.slot hsOdd (by decide), o3]
  have u3 : num t3.mem B w A = u := by
    rw [K3.num (by simp) (by decide) fA, k2.num (by idx) (by simp) fA, u1]
  have v3 : num t3.mem B w (A + 1) = v := by
    rw [K3.num (by simp) (by decide) fA1, k2.num (by idx) (by simp) fA1, v1]
  -- 4: `v - u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by idx) (by idx) (by idx) hN (by idx) (by idx)) fun t4 ⟨h4, k4, d4, b4, r4⟩ => ?_
  rw [u3, v3] at d4
  have cs4 : slot t4.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [k4.slot hsC (by simp), c3']
  have cb4 : slot t4.mem B sC ≤ 1 := by rw [cs4]; split <;> omega_arith
  -- 5: `v'`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h4 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsC (by decide) cb4)
    fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  rw [k4.num (by idx) (by simp) fA1, k4.num (by idx) (by simp) fA, u3, v3, cs4] at e5
  -- 6: `|u - v|`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h5 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsC (by decide)
    (by rw [k5.slot hsC (by simp)]; exact cb4)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [k5.slot hsC (by simp), cs4, k5.num (by idx) (by simp) fT1, k5.num (by idx) (by simp) fT2,
    k4.num (by idx) (by simp) fT1, K3.num (by simp) (by decide) fT1] at e6
  -- 7: `u'` before the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have od6 : slot t6.mem B sOdd = u % 2 := by
    rw [k6.slot hsOdd (by simp), k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), o3']
  refine WP.mono (sel_ok h6 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsOdd (by decide)
    (by rw [od6]; omega_arith)) fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [od6, e6, k6.num (by idx) (by simp) fA, k5.num (by idx) (by simp) fA, k4.num (by idx) (by simp) fA, u3] at e7
  -- 8, 9: the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hz : WP isa (.block [.li .t4 0]) t7 fun t8 =>
      (t8.gpr .t4 = 0 ∧ t8.mem = t7.mem) ∧ Keep [.t4] t7 t8 := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono hz fun t8 ⟨⟨u9, u8⟩, k8⟩ => ?_
  have h8 := h7.of_keep k8
  refine WP.mono (half_ok h8 (by idx) hN (by rw [u9]; decide)) fun t ⟨h9, k9, e9, _, r9⟩ => ?_
  rw [u9, u8] at e9
  rw [u8] at k9
  refine ⟨h9, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
      (k7.mono.trans k9.mono))))))
  · rw [k9.slot hsOdd (by simp), k7.slot hsOdd (by simp), od6]
  · rw [k9.slot hsC (by simp), k7.slot hsC (by simp), k6.slot hsC (by simp), k5.slot hsC (by simp), cs4]
  · rw [k9.num (by idx) (by simp) fD1, k7.num (by idx) (by simp) fD1, k6.num (by idx) (by simp) fD1, e5]
    by_cases c : u % 2 = 1 ∧ u < v <;> simp [c]
  · rw [e9, e7, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    exact invU_arith d2 b2 (wordsVal_lt _ _ _ _) d4 b4 (wordsVal_lt _ _ _ _)
  · exact Keep.trans' r1 (Keep.trans' r2 (Keep.trans' (Keep.mono r3' (by decide)) (Keep.trans' r3
      (Keep.trans' r4 (Keep.trans' r5 (Keep.trans' r6 (Keep.trans' r7 (Keep.trans' (Keep.mono k8 (by decide))
        r9))))))))

/-- The bank at `j`: `(u, v, x₁, x₂)`. -/
def bank (m : Mem) (B : Addr) (w j : Nat) : Nat × Nat × Nat × Nat :=
  (num m B w j, num m B w (j + 1), num m B w (j + 2), num m B w (j + 3))

/-- The selections of `x₁` and `x₂`. -/
def invX (A D : Nat) : List (Prog isa) :=
  [sel (D + 3) (A + 3) (A + 2) sC, sel aT1 aT3 aT2 sC, sel aT3 (A + 2) aT1 sOdd]

theorem invStep_eq (A D : Nat) : VG.Impl.Rsa.RISCV64.Keys.invStep A D =
    seqs (invU A D ++ (subModP aT3 (A + 2) (A + 3) ++ (subModP aT2 (A + 3) (A + 2) ++
      (invX A D ++ halfModP (D + 2))))) := rfl

theorem invStep_ok {s : State} {B : Addr} {Z w N A D : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 2048) (hb : (A = 0 ∧ D = 4) ∨ (A = 4 ∧ D = 0)) :
    WP isa (VG.Impl.Rsa.RISCV64.Keys.invStep A D) s fun t => Ws t B Z w N ∧
      Frame B w [D, D + 1, D + 2, D + 3, aT1, aT2, aT3, aT4] [sOdd, sB, sC] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (64 * w) → num s.mem B w aZero = 0 →
        num s.mem B w (A + 2) < num s.mem B w aM → num s.mem B w (A + 3) < num s.mem B w aM →
        bank t.mem B w D = VG.Proof.Rsa.invStep (num s.mem B w aM) (bank s.mem B w A)) ∧
      Keep opRegs s t := by
  have hsOdd : sOdd + 8 ≤ hdr := by decide
  have hsC : sC + 8 ≤ hdr := by decide
  have fA2 := h.fit64 (j := A + 2) (by idx)
  have fA3 := h.fit64 (j := A + 3) (by idx)
  have fM := h.fit64 (j := aM) (by idx)
  have fNM := h.fit64 (j := aNM) (by idx)
  have fZ := h.fit64 (j := aZero) (by idx)
  have fT2 := h.fit64 (j := aT2) (by idx)
  have fT3 := h.fit64 (j := aT3) (by idx)
  have fD := h.fit64 (j := D) (by idx)
  have fD1 := h.fit64 (j := D + 1) (by idx)
  have fD3 := h.fit64 (j := D + 3) (by idx)
  rw [invStep_eq, wp_seqs_append (by unfold invU; exact List.cons_ne_nil _ _)
    (by unfold subModP; exact List.cons_ne_nil _ _)]
  refine WP.mono (invU_ok h hN15 hN hb) fun t1 ⟨h1, k1, o1, c1, v1, u1, r1⟩ => ?_
  rw [wp_seqs_append (by unfold subModP; exact List.cons_ne_nil _ _)
    (by unfold subModP; exact List.cons_ne_nil _ _)]
  refine WP.mono (subModP_ok h1 hN15 hN (by idx) (by idx) (by idx) (by idx) (by idx) (by idx) (by idx))
    fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [wp_seqs_append (by unfold subModP; exact List.cons_ne_nil _ _)
    (by unfold invX; exact List.cons_ne_nil _ _)]
  refine WP.mono (subModP_ok h2 hN15 hN (by idx) (by idx) (by idx) (by idx) (by idx) (by idx) (by idx))
    fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [wp_seqs_append (by unfold invX; exact List.cons_ne_nil _ _)
    (by unfold halfModP; exact List.cons_ne_nil _ _)]
  unfold invX
  have cs3 : slot t3.mem B sC = slot t1.mem B sC := by
    rw [k3.slot hsC (by decide), k2.slot hsC (by decide)]
  have cb3 : slot t3.mem B sC ≤ 1 := by rw [cs3, c1]; split <;> omega_arith
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h3 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsC (by decide) cb3)
    fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h4 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsC (by decide)
    (by rw [k4.slot hsC (by simp)]; exact cb3)) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  have od5 : slot t5.mem B sOdd = slot t1.mem B sOdd := by
    rw [k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), k3.slot hsOdd (by decide), k2.slot hsOdd (by decide)]
  refine WP.mono (sel_ok h5 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsOdd (by decide)
    (by rw [od5, o1]; omega_arith)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine WP.mono (halfModP_ok h6 hN15 hN (by idx) (by idx) (by idx)) fun t ⟨h7, k7, e7, r7⟩ => ?_
  refine ⟨h7, k1.mono.trans (k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
    k7.mono))))), fun hNM hZ l2 l3 => ?_, Keep.trans' r1 (Keep.trans' r2 (Keep.trans' r3 (Keep.trans' r4
      (Keep.trans' r5 (Keep.trans' r6 r7)))))⟩
  -- What each step left that the others keep.
  have m1 : num t1.mem B w aM = num s.mem B w aM := k1.num (by idx) (by decide) fM
  have nm1 : num t1.mem B w aNM = num s.mem B w aNM := k1.num (by idx) (by decide) fNM
  have z1 : num t1.mem B w aZero = num s.mem B w aZero := k1.num (by idx) (by decide) fZ
  have x1 : num t1.mem B w (A + 2) = num s.mem B w (A + 2) := k1.num (by idx) (by decide) fA2
  have x2 : num t1.mem B w (A + 3) = num s.mem B w (A + 3) := k1.num (by idx) (by decide) fA3
  have m2 : num t2.mem B w aM = num s.mem B w aM := by rw [k2.num (by idx) (by decide) fM, m1]
  have nm2 : num t2.mem B w aNM = num s.mem B w aNM := by rw [k2.num (by idx) (by decide) fNM, nm1]
  have z2 : num t2.mem B w aZero = num s.mem B w aZero := by rw [k2.num (by idx) (by decide) fZ, z1]
  have x12 : num t2.mem B w (A + 2) = num s.mem B w (A + 2) := by rw [k2.num (by idx) (by decide) fA2, x1]
  have x22 : num t2.mem B w (A + 3) = num s.mem B w (A + 3) := by rw [k2.num (by idx) (by decide) fA3, x2]
  have E1 := e2 (by rw [nm1, m1]; exact hNM) (by rw [z1]; exact hZ) (by rw [x1, m1]; exact l2)
    (by rw [x2, m1]; exact l3)
  have E2 := e3 (by rw [nm2, m2]; exact hNM) (by rw [z2]; exact hZ) (by rw [x22, m2]; exact l3)
    (by rw [x12, m2]; exact l2)
  rw [m1, x1, x2] at E1
  rw [m2, x12, x22] at E2
  -- The state at `t6`, and the halving.
  have m6 : num t6.mem B w aM = num s.mem B w aM := by
    rw [k6.num (by idx) (by simp) fM, k5.num (by idx) (by simp) fM, k4.num (by idx) (by simp) fM,
      k3.num (by idx) (by decide) fM, m2]
  have nm6 : num t6.mem B w aNM = num s.mem B w aNM := by
    rw [k6.num (by idx) (by simp) fNM, k5.num (by idx) (by simp) fNM, k4.num (by idx) (by simp) fNM,
      k3.num (by idx) (by decide) fNM, nm2]
  have z6 : num t6.mem B w aZero = num s.mem B w aZero := by
    rw [k6.num (by idx) (by simp) fZ, k5.num (by idx) (by simp) fZ, k4.num (by idx) (by simp) fZ,
      k3.num (by idx) (by decide) fZ, z2]
  have H := e7 (by rw [nm6, m6]; exact hNM) (by rw [z6]; exact hZ)
  rw [m6, e6, od5, o1, k5.num (by idx) (by simp) fA2, k4.num (by idx) (by simp) fA2,
    k3.num (by idx) (by decide) fA2, x12, e5, k4.slot hsC (by simp), cs3, c1, k4.num (by idx) (by simp) fT3,
    k4.num (by idx) (by simp) fT2, k3.num (by idx) (by decide) fT3, E1, E2] at H
  have U : num t.mem B w D = num t1.mem B w D := by
    rw [k7.num (by idx) (by decide) fD, k6.num (by idx) (by simp) fD, k5.num (by idx) (by simp) fD,
      k4.num (by idx) (by simp) fD, k3.num (by idx) (by decide) fD, k2.num (by idx) (by decide) fD]
  have V : num t.mem B w (D + 1) = num t1.mem B w (D + 1) := by
    rw [k7.num (by idx) (by decide) fD1, k6.num (by idx) (by simp) fD1, k5.num (by idx) (by simp) fD1,
      k4.num (by idx) (by simp) fD1, k3.num (by idx) (by decide) fD1, k2.num (by idx) (by decide) fD1]
  have X2 : num t.mem B w (D + 3) = num t4.mem B w (D + 3) := by
    rw [k7.num (by idx) (by decide) fD3, k6.num (by idx) (by simp) fD3, k5.num (by idx) (by simp) fD3]
  rw [e4, cs3, c1, k3.num (by idx) (by decide) fA3, k3.num (by idx) (by decide) fA2, x12, x22] at X2
  rw [bank, bank, U, V, X2, u1, v1, H]
  exact invStep_arith

/-! ## The loop -/

/-- The arrays and header words `inverse` writes. -/
abbrev invArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4]
abbrev invSlots : List Nat := [sOdd, sB, sC]

/-- The registers `inverse` changes. -/
abbrev invRegs : List Reg := .s7 :: opRegs

/-- The state after `i` iterations, from `s0`. -/
structure InvLoopI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Frame B w invArrs invSlots s0.mem t.mem
  regs : Keep invRegs s0 t
  value : num s0.mem B w aNM + num s0.mem B w aM = 2 ^ (64 * w) → num s0.mem B w aZero = 0 →
    num s0.mem B w aM % 2 = 1 → 1 < num s0.mem B w aM →
    bank s0.mem B w 0 = (num s0.mem B w 0, num s0.mem B w aM, 1, 0) →
    bank t.mem B w 0 = invIter (num s0.mem B w aM) (2 * i) (bank s0.mem B w 0)

theorem inverseBody_ok {s0 t : State} {B : Addr} {Z w N i : Nat} (hN15 : 15 ≤ N) (hN : N ≤ 2048)
    (inv : InvLoopI s0 B Z w N i t) :
    WP isa (.seq (VG.Impl.Rsa.RISCV64.Keys.invStep 0 4) (.seq (VG.Impl.Rsa.RISCV64.Keys.invStep 4 0)
        (.block [.addi .s7 .s7 (-1)]))) t fun u =>
      InvLoopI s0 B Z w N (i + 1) u ∧ u.gpr .s7 = t.gpr .s7 - BitVec.ofNat 64 1 := by
  have h := inv.ws
  have fM := h.fit64 (j := aM) (by idx)
  have fNM := h.fit64 (j := aNM) (by idx)
  have fZ := h.fit64 (j := aZero) (by idx)
  have keepM : ∀ {m m' : Mem} {js ds : List Nat}, Frame B w js ds m m' →
      (∀ k ∈ js, k ≠ aM ∧ k ≠ aNM ∧ k ≠ aZero) → (∀ d ∈ ds, d + 8 ≤ hdr) →
        num m' B w aM = num m B w aM ∧ num m' B w aNM = num m B w aNM ∧
        num m' B w aZero = num m B w aZero := fun k hk hd =>
    ⟨k.num (fun x hx => (hk x hx).1) hd fM, k.num (fun x hx => (hk x hx).2.1) hd fNM,
      k.num (fun x hx => (hk x hx).2.2) hd fZ⟩
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h hN15 hN (.inl ⟨rfl, rfl⟩)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h1 hN15 hN (.inr ⟨rfl, rfl⟩)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have hs : WP isa (.block [.addi .s7 .s7 (-1)]) t2 fun u =>
      (u.gpr .s7 = t2.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t2.mem) ∧ Keep [.s7] t2 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun
  refine WP.mono hs fun u ⟨⟨u7, m2⟩, k3⟩ => ?_
  have r7 : t2.gpr .s7 = t.gpr .s7 := (r2.gpr (by decide)).trans (r1.gpr (by decide))
  refine ⟨⟨h2.of_keep k3, ?_, ?_, ?_⟩, by rw [u7, r7]⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact Keep.trans' inv.regs (Keep.mono ((r1.trans r2).trans k3) (by decide))
  · intro hNM hZ hodd h1M hst
    have prev := inv.value hNM hZ hodd h1M hst
    obtain ⟨m0, n0, z0⟩ := keepM inv.keep (by idx) (by decide)
    obtain ⟨m1, n1, z1⟩ := keepM k1 (by idx) (by decide)
    have I := VG.Proof.Rsa.invIter_inv hodd (invI_start' (a := num s0.mem B w 0) hodd h1M) (2 * i)
    rw [← hst, ← prev] at I
    have s1 := e1 (by rw [n0, m0]; exact hNM) (by rw [z0]; exact hZ)
      (by rw [m0]; exact I.x₁_lt) (by rw [m0]; exact I.x₂_lt)
    rw [m0] at s1
    have I1 := VG.Proof.Rsa.invStep_inv hodd I
    rw [← s1] at I1
    have s2 := e2 (by rw [n1, m1, n0, m0]; exact hNM) (by rw [z1, z0]; exact hZ)
      (by rw [m1, m0]; exact I1.x₁_lt) (by rw [m1, m0]; exact I1.x₂_lt)
    rw [m1, m0, s1, prev] at s2
    rw [m2, s2, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    rfl

/-- `inverse`: `K` iterations of two steps, `K` in `s7`. -/
theorem inverse_ok {s : State} {B : Addr} {Z w N K : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N)
    (hN : N ≤ 2048) (h7 : s.gpr .s7 = BitVec.ofNat 64 K) (hK : 0 < K) (hK' : K < 2 ^ 64) :
    WP isa inverse s fun t => Ws t B Z w N ∧ Frame B w invArrs invSlots s.mem t.mem ∧
      Keep invRegs s t ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (64 * w) → num s.mem B w aZero = 0 →
        num s.mem B w aM % 2 = 1 → 1 < num s.mem B w aM →
        bank s.mem B w 0 = (num s.mem B w 0, num s.mem B w aM, 1, 0) →
        bank t.mem B w 0 = invIter (num s.mem B w aM) (2 * K) (bank s.mem B w 0)) := by
  have start : InvLoopI s B Z w N 0 s :=
    ⟨h, Frame.refl _ _ _ _ _, Keep.refl _ _, fun _ _ _ _ _ => rfl⟩
  refine WP.mono (wp_countdown (body := .seq (VG.Impl.Rsa.RISCV64.Keys.invStep 0 4)
      (.seq (VG.Impl.Rsa.RISCV64.Keys.invStep 4 0) (.block [.addi .s7 .s7 (-1)])))
    (cnt := .s7) (N := K) hK' hK (InvLoopI s B Z w N)
    (fun i _ t inv _ => inverseBody_ok hN15 hN inv) start h7) fun t inv => ?_
  exact ⟨inv.ws, inv.keep, inv.regs, inv.value⟩

/-- From `(a, m, 1, 0)` with `a m < 2^(2 K)`: `gcd(a, m)` in array 1 and the inverse in array 3. -/
theorem inverse_done {mem : Mem} {B : Addr} {w K : Nat} {t : Mem} (hodd : num mem B w aM % 2 = 1)
    (h1M : 1 < num mem B w aM) (hlt : num mem B w 0 * num mem B w aM < 2 ^ (2 * K))
    (hst : bank mem B w 0 = (num mem B w 0, num mem B w aM, 1, 0))
    (v : bank t B w 0 = invIter (num mem B w aM) (2 * K) (bank mem B w 0)) :
    num t B w 1 = Nat.gcd (num mem B w 0) (num mem B w aM) ∧
      (num mem B w aM : Int) ∣ (num t B w 3 : Int) * num mem B w 0 - num t B w 1 ∧
      num t B w 3 < num mem B w aM := by
  rw [hst] at v
  have hm : 1 % num mem B w aM = 1 := Nat.mod_eq_of_lt h1M
  have D := VG.Proof.Rsa.invIter_done (a := num mem B w 0) (K := 2 * K) hodd hlt
  rw [hm] at D
  dsimp only at D
  rw [← v] at D
  exact ⟨D.2.1, D.2.2.1, D.2.2.2⟩

end VG.Proof.Rsa.RISCV64.Keys
