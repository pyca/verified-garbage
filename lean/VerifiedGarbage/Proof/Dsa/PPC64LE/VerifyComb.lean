module

import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
import VerifiedGarbage.Proof.Dsa.PPC64LE.Comb.Pow
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Basic
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr

/-!
# DSA verification on PPC64LE: `g^u1 y^u2 mod p`

`combine_ok`: into the P space (p in array 0, `R² mod p` in array 24), g and y
into arrays 4 and 5, `R² mod p` into array 1, the joint table `g^i y^j R mod
p` for `i, j < 4` in arrays 8–23 (`jointTable_ok`), the joint windows of the
exponents `u1` and `u2`, the buffer's first and second `q_len` octets
(`jointLoop_ok`), and `g^u1 y^u2 mod p` to the buffer's first `p_len`
octets. The Q space is kept. As RISC-V's (`Proof/Dsa/RISCV64/VerifyComb.lean`),
over the four-bit windows' working space (`Proof/Bignum/PPC64LE/Win*.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-! ## The joint power `g^u1 y^u2 mod p`

`jointTable` builds `T_(i + 4 j) = g^i y^j R mod p` for `i, j < 4` in arrays
8–23 (`jointTable_ok`), each entry the Montgomery product of two before it
(`montStep`); a joint window is two squares and `a := a T_(d1 + 4 d2)` for
two bits of each exponent (`jointWindow_ok`); a byte of each is four windows
(`jointByte_ok`); and the power is the bytes in turn (`jointLoop_ok`). -/

section Joint
open VG.Impl.Bignum.PPC64LE.PublicChecked (montOp)

/-- A Montgomery product of products of powers of `G` and `Y` in Montgomery form. -/
theorem mont_pow2 {o a b G Y i j k l R N : Nat} (hR : Nat.Coprime R N) (ha : a % N = G ^ i * Y ^ j * R % N)
    (hb : b % N = G ^ k * Y ^ l * R % N) (h : o * R % N = a * b % N) :
    o % N = G ^ (i + k) * Y ^ (j + l) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [h, Nat.mul_mod, ha, hb, ← Nat.mul_mod, Nat.pow_add, Nat.pow_add]
  congr 1
  ac_rfl

/-- Entry `k` of the joint table is `G^e1 Y^e2 R mod N`, if `R² mod N` is right. -/
def JGood (m : Mem) (B : Addr) (w N G Y RR k e1 e2 : Nat) : Prop :=
  Win.A m B w (8 + k) < N ∧ (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N →
    Win.A m B w (8 + k) % N = G ^ e1 * Y ^ e2 * 2 ^ (64 * w) % N)

/-- While the joint table is built: `R² mod N` in array 1, `G` and `Y` in
arrays 4 and 5, 1 in array 7, and the entries `done`. -/
structure JInv (m : Mem) (B : Addr) (w N G Y RR : Nat) (done : List (Nat × Nat × Nat)) : Prop where
  rr : Win.A m B w 1 = RR
  g : Win.A m B w 4 = G
  y : Win.A m B w 5 = Y
  one : Win.A m B w 7 = 1
  good : ∀ q ∈ done, JGood m B w N G Y RR q.1 q.2.1 q.2.2

/-- Every key of `done` is below 16 and none is `k`. -/
def Fresh (done : List (Nat × Nat × Nat)) (k : Nat) : Bool :=
  decide (k < 16) && done.all fun q => decide (q.1 < 16 ∧ q.1 ≠ k)

theorem JInv.after {m m' : Mem} {B : Addr} {w N G Y RR : Nat} {done : List (Nat × Nat × Nat)} {o : Nat}
    (h : JInv m B w N G Y RR done) (ho : o ≠ 1 ∧ o ≠ 4 ∧ o ≠ 5 ∧ o ≠ 7) (hf : ∀ q ∈ done, 8 + q.1 ≠ o ∧ q.1 < 16)
    (hv : ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ o → Win.A m' B w j = Win.A m B w j) :
    JInv m' B w N G Y RR done := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [hv 1 (by decide) (by decide) (by decide) (by omega)]; exact h.rr
  · rw [hv 4 (by decide) (by decide) (by decide) (by omega)]; exact h.g
  · rw [hv 5 (by decide) (by decide) (by decide) (by omega)]; exact h.y
  · rw [hv 7 (by decide) (by decide) (by decide) (by omega)]; exact h.one
  · have := hf q hq
    unfold JGood
    rw [hv (8 + q.1) (by omega) (by omega) (by omega) this.1]
    exact h.good q hq

/-- `T_k := T_k1 T_k2`, for entries `(k1, i1, j1)` and `(k2, i2, j2)` of `done`. -/
theorem montStep {s : State} {B : Addr} {Z w N G Y RR : Nat} {done : List (Nat × Nat × Nat)}
    (h : Win.WCtx s B Z w N) (hodd : N % 2 = 1) (hj : JInv s.mem B w N G Y RR done) {k k1 k2 i1 j1 i2 j2 : Nat}
    (hk : Fresh done k = true) (h1 : (k1, i1, j1) ∈ done) (h2 : (k2, i2, j2) ∈ done) :
    WP isa (montOp (8 + k) (8 + k1) (8 + k2)) s fun t =>
      (Win.WCtx t B Z w N ∧ Outs B (Win.win w) s.mem t.mem ∧
        JInv t.mem B w N G Y RR ((k, i1 + i2, j1 + j2) :: done)) ∧ Keep Pub.montRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  simp only [Fresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk
  obtain ⟨hk16, hall⟩ := hk
  have f1 := hall _ h1; have f2 := hall _ h2
  refine WP.mono (h.mont (o := 8 + k) (a := 8 + k1) (b := 8 + k2) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (hj.good _ h2).1) fun t ⟨⟨ct, lt, e, v, o⟩, kt⟩ =>
    ⟨⟨ct, o, ?_⟩, kt⟩
  have hj' := hj.after (m' := t.mem) (o := 8 + k) (by omega)
    (fun q hq => ⟨by have := (hall q hq).2; omega, (hall q hq).1⟩) v
  refine ⟨hj'.rr, hj'.g, hj'.y, hj'.one, fun q hq => ?_⟩
  rcases List.mem_cons.1 hq with rfl | hq
  · exact ⟨lt, fun hE => mont_pow2 hR ((hj.good _ h1).2 hE) ((hj.good _ h2).2 hE) e⟩
  · exact hj'.good q hq

/-- The table's entries, from `jointTable`'s order. -/
def jDone : List (Nat × Nat × Nat) :=
  [(15, 3, 3), (14, 2, 3), (13, 1, 3), (12, 0, 3), (11, 3, 2), (10, 2, 2), (9, 1, 2), (8, 0, 2),
   (7, 3, 1), (6, 2, 1), (5, 1, 1), (3, 3, 0), (2, 2, 0), (4, 0, 1), (1, 1, 0), (0, 0, 0)]

/-- The registers the joint table writes. -/
def jtRegs : List Reg := Pub.montRegs ++ Win.copyRegs ++ [.r0, .r14, .r17]

/-- `montStep`, with what the steps before it changed. -/
theorem montStepAcc {s₀ s : State} {B : Addr} {Z w N G Y RR : Nat} {done : List (Nat × Nat × Nat)}
    (h : Win.WCtx s B Z w N) (hodd : N % 2 = 1) (O : Outs B (Win.win w) s₀.mem s.mem) (K : Keep jtRegs s₀ s)
    (hj : JInv s.mem B w N G Y RR done) {k k1 k2 i1 j1 i2 j2 : Nat}
    (hk : Fresh done k = true) (h1 : (k1, i1, j1) ∈ done) (h2 : (k2, i2, j2) ∈ done) :
    WP isa (montOp (8 + k) (8 + k1) (8 + k2)) s fun t =>
      Win.WCtx t B Z w N ∧ Outs B (Win.win w) s₀.mem t.mem ∧
        JInv t.mem B w N G Y RR ((k, i1 + i2, j1 + j2) :: done) ∧ Keep jtRegs s₀ t :=
  WP.mono (montStep h hodd hj hk h1 h2) fun _ ⟨⟨c, o, J⟩, k⟩ => ⟨c, O.trans o, J, (K.trans k).mono (by decide)⟩

/-- `jointTable`. -/
theorem jointTable_ok {s : State} {B : Addr} {Z w N : Nat} (h : Win.WCtx s B Z w N) (hN : 2 ≤ N) (hodd : N % 2 = 1)
    (hRR : Win.A s.mem B w 1 < N) :
    WP isa jointTable s fun t =>
      (Win.WCtx t B Z w N ∧ Outs B (Win.win w) s.mem t.mem ∧ Win.A t.mem B w 7 = 1 ∧
        Win.A t.mem B w 6 = Win.A t.mem B w 8 ∧
        JInv t.mem B w N (Win.A s.mem B w 4) (Win.A s.mem B w 5) (Win.A s.mem B w 1) jDone) ∧
        Keep jtRegs s t := by
  have hn := h.nw
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hG : Win.A s.mem B w 4 = G
  generalize hY : Win.A s.mem B w 5 = Y
  generalize hRRd : Win.A s.mem B w 1 = RR at hRR
  unfold jointTable
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.scr (by have := h.w2; omega_arith) h.w31
    (Nat.le_trans (by unfold slot; omega_arith) h.hZ) h.r10 h.r29 h.r11) fun s₁ ⟨⟨h7, out1⟩, k1⟩ => ?_)
  replace h7 : Win.A s₁.mem B w 7 = 1 := h7
  have o1 : Outside B (slot w 7) (8 * (w + 2)) s.mem s₁.mem := out1.mono (Nat.le_refl _) (by omega_arith)
  have c1 := h.of k1 (by decide) (Win.win_of_out o1 (by decide) (by decide))
  have R1 : Win.A s₁.mem B w 1 = RR := by rw [Win.arr_out o1 (by decide) (by decide) hn, hRRd]
  have G1 : Win.A s₁.mem B w 4 = G := by rw [Win.arr_out o1 (by decide) (by decide) hn, hG]
  have Y1 : Win.A s₁.mem B w 5 = Y := by rw [Win.arr_out o1 (by decide) (by decide) hn, hY]
  -- `T_0 = R mod N`.
  refine WP.seq (WP.mono (c1.mont (o := 8) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h7]; omega_arith)) fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [h7, Nat.mul_one, R1] at e2
  have J2 : JInv s₂.mem B w N G Y RR [(0, 0, 0)] :=
    ⟨by rw [v2 1 (by decide) (by decide) (by decide) (by decide), R1],
      by rw [v2 4 (by decide) (by decide) (by decide) (by decide), G1],
      by rw [v2 5 (by decide) (by decide) (by decide) (by decide), Y1],
      by rw [v2 7 (by decide) (by decide) (by decide) (by decide), h7],
      fun q hq => by
        rw [List.mem_singleton.1 hq]
        show JGood s₂.mem B w N G Y RR 0 0 0
        exact ⟨lt2, fun hE => by
          simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul]
          exact VG.Proof.Bignum.mont_cancel hR (by rw [e2, hE, Nat.mod_mod])⟩⟩
  -- `T_1 = G R mod N` and `T_4 = Y R mod N`.
  refine WP.seq (WP.mono (c2.mont (o := 9) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [J2.rr]; exact hRR))
    fun s₃ ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ?_)
  rw [J2.g, J2.rr] at e3
  have J3' := J2.after (m' := s₃.mem) (o := 9) (by decide) (by decide) v3
  have J3 : JInv s₃.mem B w N G Y RR [(1, 1, 0), (0, 0, 0)] :=
    ⟨J3'.rr, J3'.g, J3'.y, J3'.one, fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · show JGood s₃.mem B w N G Y RR 1 1 0
        exact ⟨lt3, fun hE => VG.Proof.Bignum.mont_cancel hR (by
          rw [e3, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.pow_zero, Nat.mul_one,
            Nat.mul_assoc])⟩
      · exact J3'.good q hq⟩
  refine WP.seq (WP.mono (c3.mont (o := 12) (a := 5) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [J3.rr]; exact hRR))
    fun s₄ ⟨⟨c4, lt4, e4, v4, o4⟩, k4⟩ => ?_)
  rw [J3.y, J3.rr] at e4
  have J4' := J3.after (m' := s₄.mem) (o := 12) (by decide) (by decide) v4
  have J4 : JInv s₄.mem B w N G Y RR [(4, 0, 1), (1, 1, 0), (0, 0, 0)] :=
    ⟨J4'.rr, J4'.g, J4'.y, J4'.one, fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · show JGood s₄.mem B w N G Y RR 4 0 1
        exact ⟨lt4, fun hE => VG.Proof.Bignum.mont_cancel hR (by
          rw [e4, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.pow_zero, Nat.one_mul,
            Nat.mul_assoc])⟩
      · exact J4'.good q hq⟩
  have O4 : Outs B (Win.win w) s.mem s₄.mem :=
    (((Win.win_of_out o1 (by decide) (by decide)).trans o2).trans o3).trans o4
  have K4' : Keep jtRegs s s₄ := (((k1.trans k2).trans k3).trans k4).mono (by decide)
  -- The other entries.
  refine WP.seq (WP.mono (montStepAcc (k := 2) (k1 := 1) (i1 := 1) (j1 := 0) (k2 := 1) (i2 := 1)
    (j2 := 0) c4 hodd O4 K4' J4 (by decide) (by decide) (by decide)) fun s5 ⟨c5, O5, J5, K5⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 3) (k1 := 2) (i1 := 2) (j1 := 0) (k2 := 1) (i2 := 1)
    (j2 := 0) c5 hodd O5 K5 J5 (by decide) (by decide) (by decide)) fun s6 ⟨c6, O6, J6, K6⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 5) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 1) (i2 := 1)
    (j2 := 0) c6 hodd O6 K6 J6 (by decide) (by decide) (by decide)) fun s7 ⟨c7, O7, J7, K7⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 6) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 2) (i2 := 2)
    (j2 := 0) c7 hodd O7 K7 J7 (by decide) (by decide) (by decide)) fun s8 ⟨c8, O8, J8, K8⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 7) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 3) (i2 := 3)
    (j2 := 0) c8 hodd O8 K8 J8 (by decide) (by decide) (by decide)) fun s9 ⟨c9, O9, J9, K9⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 8) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 4) (i2 := 0)
    (j2 := 1) c9 hodd O9 K9 J9 (by decide) (by decide) (by decide)) fun s10 ⟨c10, O10, J10, K10⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 9) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 1) (i2 := 1)
    (j2 := 0) c10 hodd O10 K10 J10 (by decide) (by decide) (by decide)) fun s11 ⟨c11, O11, J11, K11⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 10) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 2) (i2 := 2)
    (j2 := 0) c11 hodd O11 K11 J11 (by decide) (by decide) (by decide)) fun s12 ⟨c12, O12, J12, K12⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 11) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 3) (i2 := 3)
    (j2 := 0) c12 hodd O12 K12 J12 (by decide) (by decide) (by decide)) fun s13 ⟨c13, O13, J13, K13⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 12) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 4) (i2 := 0)
    (j2 := 1) c13 hodd O13 K13 J13 (by decide) (by decide) (by decide)) fun s14 ⟨c14, O14, J14, K14⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 13) (k1 := 12) (i1 := 0) (j1 := 3) (k2 := 1) (i2 := 1)
    (j2 := 0) c14 hodd O14 K14 J14 (by decide) (by decide) (by decide)) fun s15 ⟨c15, O15, J15, K15⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 14) (k1 := 12) (i1 := 0) (j1 := 3) (k2 := 2) (i2 := 2)
    (j2 := 0) c15 hodd O15 K15 J15 (by decide) (by decide) (by decide)) fun s16 ⟨c16, O16, J16, K16⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 15) (k1 := 12) (i1 := 0) (j1 := 3) (k2 := 3) (i2 := 3)
    (j2 := 0) c16 hodd O16 K16 J16 (by decide) (by decide) (by decide)) fun s17 ⟨c17, O17, J17, K17⟩ => ?_)
  -- `a := T_0`.
  refine WP.mono (Win.copy_ok c17 (o := 6) (a := 8) (by decide) (by decide) (by decide)) fun t ⟨⟨ta, to⟩, kt⟩ => ?_
  have hv : ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 6 → Win.A t.mem B w j = Win.A s17.mem B w j :=
    fun j hj _ _ h6 => Win.arr_out to hj h6 hn
  have Jt := J17.after (m' := t.mem) (o := 6) (by decide) (by decide) hv
  refine ⟨⟨c17.of kt (by decide) (Win.win_of_out to (by decide) (by decide)), ?_, Jt.one,
    by rw [ta, hv 8 (by decide) (by decide) (by decide) (by decide)], Jt⟩, ?_⟩
  · exact O17.trans (Win.win_of_out to (by decide) (by decide))
  · exact (K17.trans kt).mono (by decide)

theorem jDone_mem {i j : Nat} (hi : i < 4) (hj : j < 4) : (i + 4 * j, i, j) ∈ jDone := by
  have key : ∀ i < 4, ∀ j < 4, (i + 4 * j, i, j) ∈ jDone := by decide
  exact key i hi j hj

theorem jDone_lt {m : Mem} {B : Addr} {w N G Y RR : Nat} (h : JInv m B w N G Y RR jDone) :
    ∀ k < 16, Win.A m B w (8 + k) < N := fun k hk => by
  have := (h.good _ (jDone_mem (i := k % 4) (j := k / 4) (Nat.mod_lt _ (by decide)) (by omega))).1
  rwa [show k % 4 + 4 * (k / 4) = k by omega] at this

/-- The digit of a joint window: `r24`'s top two bits, and its bits 54–55
times 4. -/
theorem digit_eq (x : BitVec 64) :
    x >>> 62 + (x <<< 8 >>> 62 <<< 2) = BitVec.ofNat 64 (x.toNat / 2 ^ 62 + 4 * (x.toNat / 2 ^ 54 % 4)) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have e1 : x.toNat * 2 ^ 8 % 2 ^ 64 / 2 ^ 62 = x.toNat / 2 ^ 54 % 4 := by
    have h1 : x.toNat * 2 ^ 8 % 2 ^ 64 = x.toNat % 2 ^ 56 * 2 ^ 8 := by omega
    rw [h1, show (2 : Nat) ^ 62 = 2 ^ 54 * 2 ^ 8 by rw [← Nat.pow_add],
      Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 8), show (2 : Nat) ^ 56 = 2 ^ 54 * 4 by rw [show 4 = 2 ^ 2 from rfl,
        ← Nat.pow_add], Nat.mod_mul_right_div_self]
  rw [e1]
  omega_arith

/-- A square of `a` in the context, for powers of `G` and `Y`. -/
theorem sq2_ok {s : State} {B : Addr} {Z w N : Nat} (h : Win.WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : Win.A s.mem B w 6 < N) {G Y c1 c2 : Nat} :
    WP isa (montOp 6 6 6) s fun t =>
      (Win.WCtx t B Z w N ∧ Outs B (Win.win w) s.mem t.mem ∧ Win.Fix B w s.mem t.mem ∧ Win.A t.mem B w 6 < N ∧
        (Win.A s.mem B w 6 % N = G ^ c1 * Y ^ c2 * 2 ^ (64 * w) % N →
          Win.A t.mem B w 6 % N = G ^ (c1 + c1) * Y ^ (c2 + c2) * 2 ^ (64 * w) % N)) ∧ Keep Pub.montRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  exact WP.mono (h.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ha) fun t ⟨⟨ct, lt, e, v, o⟩, k⟩ =>
    ⟨⟨ct, o, fun j hj h2 h3 _ h6 => v j hj h2 h3 h6, lt, fun hA => mont_pow2 hR hA hA e⟩, k⟩

/-- The registers a joint window writes. -/
def jwRegs : List Reg := Pub.montRegs ++ Win.selectRegs ++ [.r3, .r18, .r24]

/-- `jointWindow`: two squares, then `a := a T_(d1 + 4 d2)`, for `d1` the top
two bits of `r24` and `d2` its bits 54–55. -/
theorem jointWindow_ok {s : State} {B : Addr} {Z w N : Nat} (h : Win.WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : Win.A s.mem B w 6 < N) (htab : ∀ k < 16, Win.A s.mem B w (8 + k) < N) {G Y c1 c2 : Nat} :
    WP isa jointWindow s fun t =>
      (Win.WCtx t B Z w N ∧ Outs B (Win.win w) s.mem t.mem ∧ Win.Fix B w s.mem t.mem ∧ Win.A t.mem B w 6 < N ∧
        t.gpr .r24 = s.gpr .r24 <<< 2 ∧
        (Win.A s.mem B w 6 % N = G ^ c1 * Y ^ c2 * 2 ^ (64 * w) % N →
          (∀ i < 4, ∀ j < 4, Win.A s.mem B w (8 + (i + 4 * j)) % N = G ^ i * Y ^ j * 2 ^ (64 * w) % N) →
          Win.A t.mem B w 6 % N = G ^ (4 * c1 + (s.gpr .r24).toNat / 2 ^ 62) *
            Y ^ (4 * c2 + (s.gpr .r24).toNat / 2 ^ 54 % 4) * 2 ^ (64 * w) % N)) ∧ Keep jwRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold jointWindow
  refine WP.seq (WP.mono (sq2_ok h hodd ha (G := G) (Y := Y) (c1 := c1) (c2 := c2))
    fun s₁ ⟨⟨cs1, o1, f1, l1, e1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (sq2_ok cs1 hodd l1 (G := G) (Y := Y) (c1 := c1 + c1) (c2 := c2 + c2))
    fun s₂ ⟨⟨cs2, o2, f2, l2, e2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have f12 := f1.trans f2
  have hx := (s.gpr .r24).isLt
  have hd1 : (s.gpr .r24).toNat / 2 ^ 62 < 4 := by omega_arith
  have hd2 : (s.gpr .r24).toNat / 2 ^ 54 % 4 < 4 := Nat.mod_lt _ (by decide)
  have hd : (s.gpr .r24).toNat / 2 ^ 62 + 4 * ((s.gpr .r24).toNat / 2 ^ 54 % 4) < 16 := by omega
  refine WP.seq (WP.mono (WP.keep [.r18, .r3] (Q := fun t =>
      t.gpr .r18 = BitVec.ofNat 64 ((s.gpr .r24).toNat / 2 ^ 62 + 4 * ((s.gpr .r24).toNat / 2 ^ 54 % 4)) ∧
        t.mem = s₂.mem)
    (by prun [k12.gpr .r24 (by decide)]; rw [digit_eq]) (by decide)) fun s₃ ⟨⟨a18, m3⟩, k3⟩ => ?_)
  have cs3 := cs2.regs k3 (by decide) m3
  refine WP.seq (WP.mono (Win.select_ok cs3 a18 hd) fun s₄ ⟨⟨a5, v4, cs4, o4⟩, k4⟩ => ?_)
  have A6 : Win.A s₄.mem B w 6 = Win.A s₂.mem B w 6 := by rw [v4 6 (by decide) (by decide) (by decide), m3]
  rw [m3, f12 _ (by omega) (by omega) (by omega) (by omega) (by omega)] at a5
  refine WP.seq (WP.mono (cs4.mont (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [a5]; exact htab _ hd))
    fun s₅ ⟨⟨cs5, l5, e5, v5, o5⟩, k5⟩ => ?_)
  refine WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = s₅.gpr .r24 <<< 2 ∧ t.mem = s₅.mem)
    (by prun) (by decide)) fun t ⟨⟨a24, mt⟩, kt⟩ =>
      ⟨⟨cs5.regs kt (by decide) mt, ?_, ?_, by rw [mt]; exact l5, ?_, ?_⟩, ?_⟩
  · rw [mt]
    exact ((o1.trans o2).trans (by rw [← m3]; exact o4)).trans o5
  · intro j hj h2 h3 h5 h6
    rw [mt, v5 j hj h2 h3 h6, v4 j hj h3 h5, m3]
    exact f12 j hj h2 h3 h5 h6
  · rw [a24, k5.gpr .r24 (by decide), k4.gpr .r24 (by decide), k3.gpr .r24 (by decide), k12.gpr .r24 (by decide)]
  · intro hA hT
    rw [mt]
    rw [A6] at e5
    have := mont_pow2 hR (e2 (e1 hA)) (by rw [a5]; exact hT _ hd1 _ hd2) e5
    rw [this, show c1 + c1 + (c1 + c1) + (s.gpr .r24).toNat / 2 ^ 62 = 4 * c1 + (s.gpr .r24).toNat / 2 ^ 62 by omega,
      show c2 + c2 + (c2 + c2) + (s.gpr .r24).toNat / 2 ^ 54 % 4 = 4 * c2 + (s.gpr .r24).toNat / 2 ^ 54 % 4 by omega]
  · exact ((((k12.trans k3).trans k4).trans k5).trans kt).mono (by decide)

/-- A byte's four 2-bit digits, most significant first, after `c`. -/
theorem byte_digits (c b : Nat) :
    4 * (4 * (4 * (4 * c + b / 64) + b / 16 % 4) + b / 4 % 4) + b % 4 = 256 * c + b := by
  omega

/-- The word of a byte pair: `b1` at the top, `b2` below it. -/
theorem pair_eq {b1 b2 : Nat} (h1 : b1 < 256) (h2 : b2 < 256) :
    (BitVec.ofNat 64 b1 <<< 56 + BitVec.ofNat 64 b2 <<< 48).toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48 := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem digits0 {x b1 b2 : Nat} (hx : x = b1 * 2 ^ 56 + b2 * 2 ^ 48) (h2 : b2 < 256) :
    x / 2 ^ 62 = b1 / 64 ∧ x / 2 ^ 54 % 4 = b2 / 64 := by subst hx; omega_arith

theorem digits1 {v : BitVec 64} {b1 b2 : Nat} (hx : v.toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48)
    (h2 : b2 < 256) : (v <<< 2).toNat / 2 ^ 62 = b1 / 16 % 4 ∧ (v <<< 2).toNat / 2 ^ 54 % 4 = b2 / 16 % 4 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx]; omega_arith

theorem digits2 {v : BitVec 64} {b1 b2 : Nat} (hx : v.toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48)
    (h2 : b2 < 256) : (v <<< 2 <<< 2).toNat / 2 ^ 62 = b1 / 4 % 4 ∧ (v <<< 2 <<< 2).toNat / 2 ^ 54 % 4 = b2 / 4 % 4 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx]; omega_arith

theorem digits3 {v : BitVec 64} {b1 b2 : Nat} (hx : v.toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48)
    (h2 : b2 < 256) :
    (v <<< 2 <<< 2 <<< 2).toNat / 2 ^ 62 = b1 % 4 ∧ (v <<< 2 <<< 2 <<< 2).toNat / 2 ^ 54 % 4 = b2 % 4 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, hx]; omega_arith

/-- The registers the joint loop writes. -/
def jlRegs : List Reg := jtRegs ++ jwRegs ++ [.r0, .r24, .r25, .r30, .r31]

/-- After the joint table (`t₀`), with `c1` and `c2` of the exponents scanned. -/
structure JRun (s₀ t₀ u : State) (B : Addr) (Z w N G Y RR c1 c2 : Nat) : Prop where
  ctx : Win.WCtx u B Z w N
  out : Outs B (Win.win w) s₀.mem u.mem
  fix : Win.Fix B w t₀.mem u.mem
  lt : Win.A u.mem B w 6 < N
  pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → Win.A u.mem B w 6 % N = G ^ c1 * Y ^ c2 * 2 ^ (64 * w) % N
  keep : Keep jlRegs s₀ u

/-- The two bytes of a joint step into `r24`. -/
theorem lbz2_ok {u : State} {D E : Addr} {i : Nat} (h30 : u.gpr .r30 = off D i) (h25 : u.gpr .r25 = off E i)
    (hrd1 : InRegions (u.rd ++ u.wr) (off D i) 1) (hrd2 : InRegions (u.rd ++ u.wr) (off E i) 1) :
    WP isa (.block [.lbz .r24 .r30 0, .lsl .r24 .r24 56, .lbz .r0 .r25 0, .lsl .r0 .r0 48, .add .r24 .r24 .r0,
        .addi .r30 .r30 1, .addi .r25 .r25 1]) u fun t =>
      (t.gpr .r24 = BitVec.ofNat 64 (u.mem (off D i)).toNat <<< 56 +
          BitVec.ofNat 64 (u.mem (off E i)).toNat <<< 48 ∧
        t.gpr .r30 = off D (i + 1) ∧ t.gpr .r25 = off E (i + 1) ∧ t.mem = u.mem) ∧
        Keep [.r24, .r0, .r30, .r25] u t := by
  refine WP.keep _ ?_ (by decide)
  prun [h30, h25, exec_lbz' (show Reg.r30 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    exec_lbz' (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd1, hrd2, read_byte64]

/-- The table's entries, from what the windows keep of it. -/
theorem jtab_of {t₀ : State} {m : Mem} {B : Addr} {w N G Y RR : Nat} (htab : JInv t₀.mem B w N G Y RR jDone)
    (hf : Win.Fix B w t₀.mem m) :
    (∀ k < 16, Win.A m B w (8 + k) < N) ∧ (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N →
      ∀ i < 4, ∀ j < 4, Win.A m B w (8 + (i + 4 * j)) % N = G ^ i * Y ^ j * 2 ^ (64 * w) % N) := by
  refine ⟨fun k hk => ?_, fun hE i hi j hj => ?_⟩
  · rw [hf (8 + k) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact jDone_lt htab k hk
  · rw [hf (8 + (i + 4 * j)) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact (htab.good _ (jDone_mem hi hj)).2 hE

theorem jw_jl {r : Reg} (h : r ∈ jwRegs) : r ∈ jlRegs :=
  List.mem_append_left _ (List.mem_append_right _ h)

/-- `jointByte`: the four joint windows of the bytes `b1` at `r30` and `b2` at
`r25`, `c1 := 256 c1 + b1` and `c2 := 256 c2 + b2`. -/
theorem jointByte_ok {s₀ t₀ u : State} {B D E : Addr} {Z w N G Y RR c1 c2 i : Nat} (hodd : N % 2 = 1)
    (htab : JInv t₀.mem B w N G Y RR jDone) (h : JRun s₀ t₀ u B Z w N G Y RR c1 c2)
    (h30 : u.gpr .r30 = off D i) (h25 : u.gpr .r25 = off E i)
    (hrd1 : InRegions (u.rd ++ u.wr) (off D i) 1) (hrd2 : InRegions (u.rd ++ u.wr) (off E i) 1) :
    WP isa jointByte u fun t =>
      JRun s₀ t₀ t B Z w N G Y RR (256 * c1 + (u.mem (off D i)).toNat) (256 * c2 + (u.mem (off E i)).toNat) ∧
        Outs B (Win.win w) u.mem t.mem ∧ t.gpr .r30 = off D (i + 1) ∧ t.gpr .r25 = off E (i + 1) ∧
        t.gpr .r31 = u.gpr .r31 := by
  generalize hb1 : (u.mem (off D i)).toNat = b1
  generalize hb2 : (u.mem (off E i)).toNat = b2
  have h1 : b1 < 256 := by rw [← hb1]; exact (u.mem (off D i)).isLt
  have h2 : b2 < 256 := by rw [← hb2]; exact (u.mem (off E i)).isLt
  unfold jointByte
  refine WP.seq (WP.mono (lbz2_ok h30 h25 hrd1 hrd2) fun u₁ ⟨⟨a24, a30, a25, m1⟩, k1⟩ => ?_)
  rw [hb1, hb2] at a24
  have hv : (u₁.gpr .r24).toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48 := by rw [a24]; exact pair_eq h1 h2
  have c1' := h.ctx.regs k1 (by decide) m1
  have f1 : Win.Fix B w t₀.mem u₁.mem := by rw [m1]; exact h.fix
  have d0 := digits0 hv h2
  refine WP.seq (WP.mono (jointWindow_ok c1' hodd (by rw [m1]; exact h.lt) (jtab_of htab f1).1
    (G := G) (Y := Y) (c1 := c1) (c2 := c2)) fun u₂ ⟨⟨c2', o2, f2, l2, s2, e2⟩, k2⟩ => ?_)
  rw [d0.1, d0.2] at e2
  have d1 := digits1 hv h2
  rw [← s2] at d1
  refine WP.seq (WP.mono (jointWindow_ok c2' hodd l2 (jtab_of htab (f1.trans f2)).1
    (G := G) (Y := Y) (c1 := 4 * c1 + b1 / 64) (c2 := 4 * c2 + b2 / 64)) fun u₃ ⟨⟨c3', o3, f3, l3, s3, e3⟩, k3⟩ => ?_)
  rw [d1.1, d1.2] at e3
  have d2 := digits2 hv h2
  rw [← s2, ← s3] at d2
  refine WP.seq (WP.mono (jointWindow_ok c3' hodd l3 (jtab_of htab ((f1.trans f2).trans f3)).1
    (G := G) (Y := Y) (c1 := 4 * (4 * c1 + b1 / 64) + b1 / 16 % 4) (c2 := 4 * (4 * c2 + b2 / 64) + b2 / 16 % 4))
    fun u₄ ⟨⟨c4', o4, f4, l4, s4, e4⟩, k4⟩ => ?_)
  rw [d2.1, d2.2] at e4
  have d3 := digits3 hv h2
  rw [← s2, ← s3, ← s4] at d3
  refine WP.mono (jointWindow_ok c4' hodd l4 (jtab_of htab (((f1.trans f2).trans f3).trans f4)).1
    (G := G) (Y := Y) (c1 := 4 * (4 * (4 * c1 + b1 / 64) + b1 / 16 % 4) + b1 / 4 % 4)
    (c2 := 4 * (4 * (4 * c2 + b2 / 64) + b2 / 16 % 4) + b2 / 4 % 4))
    fun t ⟨⟨c5', o5, f5, l5, _, e5⟩, k5⟩ => ⟨⟨c5', ?_, ?_, l5, fun hE => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [m1] at o2; exact (((h.out.trans o2).trans o3).trans o4).trans o5
  · exact f1.trans (f2.trans (f3.trans (f4.trans f5)))
  · rw [d3.1, d3.2] at e5
    have T : ∀ {m : Mem}, Win.Fix B w t₀.mem m →
        ∀ i < 4, ∀ j < 4, Win.A m B w (8 + (i + 4 * j)) % N = G ^ i * Y ^ j * 2 ^ (64 * w) % N :=
      fun hf => (jtab_of htab hf).2 hE
    have p1 := e2 (by rw [m1]; exact h.pw hE) (T f1)
    have p2 := e3 p1 (T (f1.trans f2))
    have p3 := e4 p2 (T ((f1.trans f2).trans f3))
    have p4 := e5 p3 (T (((f1.trans f2).trans f3).trans f4))
    exact p4.trans (by rw [byte_digits, byte_digits])
  · exact (((((h.keep.trans k1).trans k2).trans k3).trans k4).trans k5).mono fun r hr => by
      simp only [List.mem_append] at hr
      rcases hr with ((((hr | hr) | hr) | hr) | hr) | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      all_goals exact jw_jl hr
  · rw [m1] at o2; exact ((o2.trans o3).trans o4).trans o5
  · rw [k5.gpr .r30 (by decide), k4.gpr .r30 (by decide), k3.gpr .r30 (by decide), k2.gpr .r30 (by decide), a30]
  · rw [k5.gpr .r25 (by decide), k4.gpr .r25 (by decide), k3.gpr .r25 (by decide), k2.gpr .r25 (by decide), a25]
  · rw [k5.gpr .r31 (by decide), k4.gpr .r31 (by decide), k3.gpr .r31 (by decide), k2.gpr .r31 (by decide),
      k1.gpr .r31 (by decide)]

/-- The joint loop: `c1` and `c2` become `U1` and `U2`, the `L ≥ 1` bytes at
`D` (`r30`) and `E` (`r25`), counted in `r31`, apart from the working space. -/
theorem jointLoop_ok {s t₀ : State} {B D E : Addr} {Z w N G Y RR L : Nat} (hodd : N % 2 = 1)
    (htab : JInv t₀.mem B w N G Y RR jDone) (h : JRun s t₀ t₀ B Z w N G Y RR 0 0)
    (h30 : t₀.gpr .r30 = off D 0) (h25 : t₀.gpr .r25 = off E 0) (h31 : t₀.gpr .r31 = BitVec.ofNat 64 L)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (off D i) 1 ∧ InRegions (t₀.rd ++ t₀.wr) (off E i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x ∧ off E i ≠ x) :
    WP isa (.loop (.seq jointByte (.block [.subi .r31 .r31 1])) (.nonzero .d .r31)) t₀ fun u =>
      JRun s t₀ u B Z w N G Y RR (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem D L))
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem E L)) := by
  have hn := h.ctx.nw
  have hZ := h.ctx.hZ
  have hmem : ∀ {u : State}, Outs B (Win.win w) t₀.mem u.mem → ∀ i < L,
      u.mem (off D i) = t₀.mem (off D i) ∧ u.mem (off E i) = t₀.mem (off E i) := by
    intro u hu i hi
    have hl := Win.slot_lt (w := w) (show 1 < 24 by decide)
    have e24 : slot w 24 = slot w 1 + 23 * (8 * (w + 2)) := by unfold slot; omega_arith
    refine ⟨hu _ fun r hr => ?_, hu _ fun r hr => ?_⟩ <;> rw [Win.win, List.mem_singleton] at hr <;> subst hr <;>
      right <;> by_contra hc
    · exact (hsep i hi (off D i) (by simp only [Mont.ofs, ofs] at hc ⊢; omega_arith)).1 rfl
    · exact (hsep i hi (off E i) (by simp only [Mont.ofs, ofs] at hc ⊢; omega_arith)).2 rfl
  let Inv : Nat → State → Prop := fun i u =>
    JRun s t₀ u B Z w N G Y RR (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem D i))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem E i)) ∧ Outs B (Win.win w) t₀.mem u.mem ∧
      u.gpr .r30 = off D i ∧ u.gpr .r25 = off E i
  refine WP.mono (wp_countdown (cnt := .r31) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨hu, ou, u30, u25⟩ _ => ?_) ⟨by simpa [Spec.Rsa.bytesAt, Spec.Rsa.os2ip] using h,
      Outs.refl _ _ _, h30, h25⟩ h31) fun u ⟨hu, _⟩ => hu
  have hrd' : InRegions (u.rd ++ u.wr) (off D i) 1 ∧ InRegions (u.rd ++ u.wr) (off E i) 1 := by
    rw [hu.keep.rd, hu.keep.wr, ← h.keep.rd, ← h.keep.wr]; exact hrd i hi
  refine WP.seq (WP.mono (jointByte_ok hodd htab hu u30 u25 hrd'.1 hrd'.2)
    fun u₁ ⟨hu₁, o₁, a30, a25, a31⟩ => ?_)
  refine WP.mono (subi_ok u₁ .r31 (by decide)) fun u₂ e => ?_
  subst e
  have ou₁ : Outs B (Win.win w) t₀.mem u₁.mem := ou.trans o₁
  refine ⟨⟨⟨hu₁.ctx.regs (Keep.write _ _ _) (by decide) (by rw [mem_write]), by rw [mem_write]; exact hu₁.out,
      by rw [mem_write]; exact hu₁.fix, by rw [mem_write]; exact hu₁.lt, fun hE => ?_,
      (hu₁.keep.trans (Keep.write _ _ _)).mono (by decide)⟩, by rw [mem_write]; exact ou₁, by gsimp; exact a30,
      by gsimp; exact a25⟩, by gsimp; rw [a31]⟩
  rw [mem_write, hu₁.pw hE, (hmem ou i hi).1, (hmem ou i hi).2, Pub.bytesAt_succ, Pub.bytesAt_succ,
    VG.Proof.Rsa.os2ip_snoc, VG.Proof.Rsa.os2ip_snoc]

end Joint

/-! ## Frames of `combine` -/

/-- A change in the P space's arrays keeps the Q space. -/
theorem comb_pbody_keepQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  intro x hx
  have hlt := (x - L.Q).isLt
  have hq : ofs L.Q x < 1600 := by simp only [ofs] at hx ⊢; omega_arith
  have := (Offset.lt_iff x L.S (d := L.qOff) (n := 1600) (by simp only [Lay.bOff] at hb; omega_arith)).mp hq
  have : 256 ≤ L.qOff := by simp only [Lay.qOff, Lay.slot_eq]; omega_arith
  exact h x (Or.inr (by simp only [ofs] at this ⊢; omega_arith))

/-- A change in the buffer keeps the Q space. -/
theorem combBufKeepQ {L : Lay} {m m' : Mem} {n : Nat} (h : Outside L.Buf 0 n m m') (hn : n ≤ 2 ^ 64 - 1600) :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hlt := (x - L.Q).isLt
  have hq : ofs L.Q x < 1600 := by simp only [ofs] at hx ⊢; omega_arith
  refine h x (Or.inr ?_)
  rw [buf_eq]
  simp only [ofs, off] at hq ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- The buffer's bytes are past the P space, as `storeBE` needs. -/
theorem combBufPastP {L : Lay} (hL : L.Ok) : ∀ x, ofs L.Buf x < L.pl → L.qOff ≤ ofs L.S x := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  intro x hx
  have := (Offset.lt_iff x L.S (d := L.bOff) (n := L.pl) (by omega_arith)).mp hx
  simp only [Lay.bOff] at this
  simp only [ofs]
  omega_arith


/-! ## `combine` -/

/-- A change in the four-bit windows' arrays of the P space. -/
theorem parr_win {L : Lay} {m m' : Mem} (h : Outs L.S (Win.win L.wp) m m') : PArr L m m' :=
  outs_within h fun r hr => by
    rw [Win.win, List.mem_singleton] at hr
    subst hr
    simp only [Lay.qOff, Lay.slot_eq]
    omega

/-- The registers `combine` writes. -/
def combRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22,
    .r23, .r24, .r25, .r29, .r30, .r31]

/-- `combine`: `g^u1 y^u2 mod p` to the buffer's first `p_len` octets. -/
theorem combine_ok {s : State} {L : Lay} {key sig dig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (3 * L.pl + L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa combine s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) =
          gOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) % p *
            (yOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf L.ql) L.ql) % p) % p ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧ Keep combRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hpl := hL.pl
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega_arith
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e4 := Lay.slot_eq L.wp 4
  have e5 := Lay.slot_eq L.wp 5; have e8 := Lay.slot_eq L.wp 8; have e24 := Lay.slot_eq L.wp 24
  have e28 := Lay.slot_eq L.wp 28
  have hR := VG.Proof.Bignum.coprime_pow2 hpo (64 * L.wp)
  unfold combine
  -- Into the P space; g's octets.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterP_ok hL hs hr) fun s₁ ⟨⟨in1, m1⟩, k1⟩ => ?_
  refine WP.mono (ptrG_ok (hr.keep k1)) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have en2 := in1.env.keep k2 (by decide)
  -- g into array 4.
  have hg := (hk.keep k12.rd k12.wr).sub (o := L.pl + L.ql) (k := L.pl) (by omega_arith)
  refine WP.seq (WP.mono (loadArr_ok en2 (j := 4) (by decide) a12 a6 (by omega_arith) (by omega_arith) hg.rd
      (fun i hi x hx => hg.sep i hi x (by omega_arith))) fun s₃ ⟨⟨v4, _, o3, a10⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  have en3 := env_keep10 en2 k3 (by decide) a10
  -- y's octets, into array 5.
  refine WP.seq (WP.mono (ptrY_ok (hr.keep (k12.trans k3))) fun s₄ ⟨⟨b12, b6, m4⟩, k4⟩ => ?_)
  have k14 := (k12.trans k3).trans k4
  have en4 := en3.keep k4 (by decide)
  have hy := (hk.keep k14.rd k14.wr).sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega_arith)
  refine WP.seq (WP.mono (loadArr_ok en4 (j := 5) (by decide) b12 b6 (by omega_arith) (by omega_arith) hy.rd
      (fun i hi x hx => hy.sep i hi x (by omega_arith))) fun s₅ ⟨⟨v5, _, o5, a10'⟩, k5⟩ => ?_)
  rw [m4] at v5 o5
  have en5 := env_keep10 en4 k5 (by decide) a10'
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (copy_ok en5 (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₆ ⟨⟨v1, o6⟩, k6⟩ => ?_)
  have en6 := en5.keep k6 (by decide)
  have k16 := (k14.trans k5).trans k6
  have pa6 : PArr L s.mem s₆.mem :=
    ((o3.mono (by omega_arith) (by omega_arith)).trans (o5.mono (by omega_arith) (by omega_arith))).trans
      (o6.mono (by omega_arith) (by omega_arith))
  -- The exponents' pointers and length, and `-p⁻¹`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrBuf_ok hL (hr.keep k16)) fun s₇ ⟨⟨c12, c6, m7⟩, k7⟩ => ?_
  refine WP.mono (WP.keep [.r30, .r25, .r31] (Q := fun t => t.gpr .r30 = off L.Buf 0 ∧
      t.gpr .r25 = off L.Buf L.ql ∧ t.gpr .r31 = BitVec.ofNat 64 L.ql ∧ t.mem = s₇.mem)
    (by prun [c12, c6, off, BitVec.add_zero]) (by decide)) fun s₈ ⟨⟨d30, d25, d31, m8⟩, k8⟩ => ?_
  have k68 := k7.trans k8
  have hm8 : s₈.mem = s₆.mem := by rw [m8, m7]
  have g10 : s₈.gpr .r10 = off L.S (slot L.wp 0) := (k68.gpr .r10 (by decide)).trans en6.h10
  have p8 : val32 s₈.mem L.S (slot L.wp 0) (2 * L.wp) = p := by
    rw [hm8, Outside.val32 pa6 (by omega_arith) (by omega_arith)]; exact hp0
  have hlow : (word s₈.mem L.S (slot L.wp 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₈.mem L.S (slot L.wp 0)
    have h2 : val32 s₈.mem L.S (slot L.wp 0) (2 * L.wp - 1 + 1) =
        w32 s₈.mem L.S (slot L.wp 0) + 2 ^ 32 * val32 s₈.mem L.S (slot L.wp 0 + 4) (2 * L.wp - 1) := rfl
    rw [Nat.sub_add_cancel (by omega_arith : 1 ≤ 2 * L.wp), p8] at h2
    omega_arith
  refine WP.mono (Pub.minv_ok (en6.hs.congr k68.wr) g10 (by omega_arith) hlow)
    fun s₉ ⟨⟨r12lt, r12inv, m9⟩, k9⟩ => ?_
  have k69 := k68.trans k9
  have hm9 : s₉.mem = s₆.mem := by rw [m9, hm8]
  have A0 : Win.A s₉.mem L.S L.wp 0 = p := by rw [m9]; exact p8
  have A1 : Win.A s₉.mem L.S L.wp 1 = 2 ^ (128 * L.wp) % p := by
    show val32 s₉.mem L.S (slot L.wp 1) (2 * L.wp) = _
    rw [hm9]
    show arr s₆.mem L.S L.wp 1 = _
    rw [v1, arr, Outside.val32 o5 (by omega_arith) (by omega_arith), Outside.val32 o3 (by omega_arith) (by omega_arith)]
    exact hrr
  have A4 : Win.A s₉.mem L.S L.wp 4 = gOf s.mem L key := by
    show val32 s₉.mem L.S (slot L.wp 4) (2 * L.wp) = _
    rw [hm9, Outside.val32 o6 (by omega_arith) (by omega_arith), Outside.val32 o5 (by omega_arith) (by omega_arith)]
    exact v4
  have A5 : Win.A s₉.mem L.S L.wp 5 = yOf s.mem L key := by
    show val32 s₉.mem L.S (slot L.wp 5) (2 * L.wp) = _
    rw [hm9, Outside.val32 o6 (by omega_arith) (by omega_arith), v5]
    unfold yOf
    rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega_arith)).bytes
      (Body.ofP hL o3 (by omega_arith) (by omega_arith)) hZ]
    rfl
  have c9 : Win.WCtx s₉ L.S L.qOff L.wp p :=
    ⟨en6.hs.congr k69.wr, by omega_arith, by omega_arith, by omega_arith,
      (k9.gpr .r10 (by decide)).trans g10, (k69.gpr .r29 (by decide)).trans en6.h29,
      (k69.gpr .r11 (by decide)).trans en6.h11, r12lt, by rw [m9]; exact r12inv, A0⟩
  -- The joint table.
  refine WP.seq (WP.mono (jointTable_ok c9 hp hpo (by rw [A1]; exact Nat.mod_lt _ (by omega_arith)))
    fun s₁₀ ⟨⟨c10, o10, t7, a6t, J⟩, k10⟩ => ?_)
  rw [A1, A4, A5] at J
  have g0 := J.good _ (show (0, 0, 0) ∈ jDone by decide)
  have r0 : JRun s₁₀ s₁₀ s₁₀ L.S L.qOff L.wp p (gOf s.mem L key) (yOf s.mem L key) (2 ^ (128 * L.wp) % p) 0 0 :=
    ⟨c10, Outs.refl _ _ _, fun _ _ _ _ _ _ => rfl, by rw [a6t]; exact g0.1, fun hE => by rw [a6t]; exact g0.2 hE,
      Keep.refl _ _⟩
  have k610 := k69.trans k10
  have K10 := k16.trans k610
  have pa10 : PArr L s.mem s₁₀.mem := pa6.trans (by rw [← hm9]; exact parr_win o10)
  -- The joint windows.
  refine WP.seq (WP.mono (jointLoop_ok (L := L.ql) (D := off L.Buf 0) (E := off L.Buf L.ql) hpo J r0
      (by rw [k10.gpr .r30 (by decide), k9.gpr .r30 (by decide), d30]; exact (BitVec.add_zero _).symm)
      (by rw [k10.gpr .r25 (by decide), k9.gpr .r25 (by decide), d25]; exact (BitVec.add_zero _).symm)
      (by rw [k10.gpr .r31 (by decide), k9.gpr .r31 (by decide), d31]) (by omega_arith) (by omega_arith)
      (fun i hi => by
        rw [K10.rd, K10.wr]
        exact ⟨combBufRd hL hs (o := 0) (k := L.ql) (by omega_arith) i hi,
          combBufRd hL hs (o := L.ql) (k := L.ql) (by omega_arith) i hi⟩)
      (fun i hi x hx => ⟨combBufSepP hL (o := 0) (k := L.ql) (by omega_arith) i hi x hx,
        combBufSepP hL (o := L.ql) (k := L.ql) (by omega_arith) i hi x hx⟩))
    fun u hu => ?_)
  rw [combBufBytes hL pa10 (by omega_arith) (o := 0) (k := L.ql) (by omega_arith),
    combBufBytes hL pa10 (by omega_arith) (o := L.ql) (k := L.ql) (by omega_arith)] at hu
  have K1u := (((((k2.trans k3).trans k4).trans k5).trans k6).trans k610).trans hu.keep
  have u23 : u.gpr .r23 = L.S := (K1u.gpr .r23 (by decide)).trans in1.h23
  -- The space again in `r31`.
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = L.S ∧ t.mem = u.mem)
    (by prun [u23, BitVec.add_zero]) (by decide)) fun u₁ ⟨⟨f31, mu1⟩, ku1⟩ => ?_)
  have cu1 := hu.ctx.regs ku1 (by decide) mu1
  have t7' : Win.A u₁.mem L.S L.wp 7 = 1 := by
    rw [mu1, hu.fix 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact t7
  -- Out of Montgomery form.
  refine WP.seq (WP.mono (cu1.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t7']; omega_arith))
    fun u₂ ⟨⟨cu2, lt4, e4, _, o4⟩, k4'⟩ => ?_)
  rw [t7', Nat.mul_one, mu1] at e4
  have hE : 2 ^ (128 * L.wp) % p = 2 ^ (64 * L.wp) * 2 ^ (64 * L.wp) % p := by
    rw [← Nat.pow_add, show 64 * L.wp + 64 * L.wp = 128 * L.wp by omega_arith]
  have hb0 : off L.Buf 0 = L.Buf := BitVec.add_zero _
  have V : Win.A u₂.mem L.S L.wp 4 = gOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf 0) L.ql) *
      yOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf L.ql) L.ql) % p :=
    (Nat.mod_eq_of_lt lt4).symm.trans (VG.Proof.Bignum.mont_cancel hR (by rw [e4, hu.pw hE]))
  rw [hb0] at V
  have Ku2 := (ku1.trans k4')
  have env2 : Env u₂ L.S L.qOff L.wp :=
    env_keep31 en6 ((k610.trans hu.keep).trans Ku2) (by decide) ((k4'.gpr .r31 (by decide)).trans f31)
  have K2 := K1u.trans Ku2
  have hr2 : Regs u₂ L key sig dig := hr.keep (k1.trans K2)
  have pa2 : PArr L s.mem u₂.mem := (pa10.trans (parr_win hu.out)).trans (by rw [← mu1]; exact parr_win o4)
  -- To the buffer.
  refine WP.seq (WP.mono (show WP isa (.block (bufBase .r12 .r0 ++ getP .r6)) u₂ fun t =>
      (t.gpr .r12 = L.Buf ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = u₂.mem) ∧ Keep [.r12, .r0, .r6] u₂ t by
      rw [WP.block_append_iff]
      exact WP.mono (bufBase_ok hL hr2 (by decide)) fun v ⟨⟨a, mv⟩, kv⟩ =>
        WP.mono (getP_ok (hr2.keep kv) .r6) fun v' ⟨⟨b, mv'⟩, kv'⟩ =>
          ⟨⟨(kv'.gpr .r12 (by decide)).trans a, b, mv'.trans mv⟩, (kv.trans kv').mono (by decide)⟩)
    fun u₃ ⟨⟨c12', c6', m3'⟩, k3'⟩ => ?_)
  have K3 := (k1.trans K2).trans k3'
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) (env2.keep k3' (by decide)) (by decide)
    (ScrL.bufN (hs.congr K3.wr) hL (by omega_arith)) c12' c6' (by omega_arith) (by omega_arith) (combBufPastP hL))
    fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [m3'] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← p8, ← hw8, show 8 * (8 * L.wp) = 32 * (2 * L.wp) by omega_arith]; exact val32_lt _ _ _ _
  have Kt := K3.trans kt
  refine ⟨⟨?_, ⟨env2.keep (k3'.trans kt) (by decide), (Kt.gpr .r21 (by decide)).trans hr.r21,
      (((ku1.trans k4').trans (k3'.trans kt)).gpr .r23 (by decide)).trans u23⟩,
    (pa2.pbody.body hL).trans (Body.ofBuf hL ot (by omega_arith)),
    (comb_pbody_keepQ hL pa2.pbody).trans (combBufKeepQ ot (by omega_arith))⟩, ?_⟩
  · rw [vt, read_low (w := L.wp) _ _ (by omega_arith)
      (by show Win.A u₂.mem L.S L.wp 4 < _; rw [V]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hplt)]
    show Win.A u₂.mem L.S L.wp 4 = _
    rw [V]
    exact Nat.mul_mod _ _ _
  · exact (((((((((((((((k1.mono (rs' := combRegs) (by decide))).trans' (k2.mono (by decide))).trans'
      (k3.mono (by decide))).trans' (k4.mono (by decide))).trans' (k5.mono (by decide))).trans'
      (k6.mono (by decide))).trans' (k7.mono (by decide))).trans' (k8.mono (by decide))).trans'
      (k9.mono (by decide))).trans' (k10.mono (by decide))).trans' (hu.keep.mono (by decide))).trans'
      (ku1.mono (by decide))).trans' (k4'.mono (by decide))).trans' (k3'.mono (by decide))).trans'
      (kt.mono (by decide))

end VG.Proof.Dsa.PPC64LE
