module

public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLoops
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The word loops of the batched inverse on RISC-V

Over `n` words of 64 bits at byte offsets of the working space (`Scr s B Z`),
multiples of 8, pointers in `t0`–`t2` and the count in `t3`, as
`KeyLoops.lean`'s (whose `subLoop_ok`, `selLoop_ok`, `copyLoop_ok` and
`zeroLoop_ok` the inverse also uses):

* `macLoop_ok`: `[o] := [a] + k [b]`, `k` in `a5`, the carry in and out in
  `t4`;
* `shrLoop_ok`: `[o] := [a] >> 59`, reading one word more;
* `linLoop_ok`: `[o] := u [a] + v [b]` for signed `u`, `v` in `a5`, `a7`, the
  signed accumulator in `t4` and `a4`.

The output may be an input, or come before it, or be apart from it
(`Ahead`): a word is read before any word at or after it is written.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.InvBatch (macBody shrBody linBody linTerm)
open VG.Proof.Rsa.RISCV64.Loops (loopRegs Ahead out_step)

/-! ## `mac` -/

/-- A word of `a + k b + c`: the low word and the carry. -/
theorem mac_arith (k b a c : BitVec 64) :
    let lo := k * b + a
    let c1 : BitVec 64 := if lo < a then 1 else 0
    let s := lo + c
    let c2 : BitVec 64 := if s < c then 1 else 0
    s.toNat + 2 ^ 64 * (BitVec.ofNat 64 ((k.toNat * b.toNat) / 2 ^ 64) + c1 + c2).toNat =
      a.toNat + k.toNat * b.toNat + c.toNat := by
  intro lo c1 s c2
  have hk := k.isLt; have hb := b.isLt; have ha := a.isLt; have hc := c.isLt
  have hkb : k.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have vlo : lo.toNat = (k.toNat * b.toNat % 2 ^ 64 + a.toNat) % 2 ^ 64 := by
    simp only [lo, BitVec.toNat_add, BitVec.toNat_mul]
  have vs : s.toNat = (lo.toNat + c.toNat) % 2 ^ 64 := by simp only [s, BitVec.toNat_add]
  have vc1 : c1.toNat = (k.toNat * b.toNat % 2 ^ 64 + a.toNat) / 2 ^ 64 := by
    simp only [c1, BitVec.lt_def]; split <;> simp <;> omega
  have vc2 : c2.toNat = (lo.toNat + c.toNat) / 2 ^ 64 := by
    simp only [c2, BitVec.lt_def]; split <;> simp <;> omega
  have vhi : (BitVec.ofNat 64 ((k.toNat * b.toNat) / 2 ^ 64) + c1 + c2).toNat =
      k.toNat * b.toNat / 2 ^ 64 + c1.toNat + c2.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : k.toNat * b.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by omega
    rw [vc1, vc2, vlo]
    omega
  rw [vhi, vs, vc1, vc2, vlo]
  generalize k.toNat * b.toNat = P at hkb ⊢
  omega

/-- `[o] := [a] + k [b]` over `n` words (`countLoop .t3 macBody`), from the
carry `c` in `t4`: the sum and the carry out. -/
theorem macLoop_ok {s : State} {B : Addr} {Z dO dA dM n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dM)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hA8 : dA % 8 = 0) (hM8 : dM % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * n ≤ Z) (hM : dM + 8 * n ≤ Z)
    (aA : Ahead dO dA n) (aM : Ahead dO dM n) :
    WP isa (countLoop .t3 macBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat =
        wordsVal s.mem B dA n + (s.gpr .a5).toNat * wordsVal s.mem B dM n + (s.gpr .t4).toNat ∧
      t.gpr .t0 = off B (dO + 8 * n) ∧ Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dA + 8 * i) ∧ t.gpr .t2 = off B (dM + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat =
        wordsVal s.mem B dA i + (s.gpr .a5).toNat * wordsVal s.mem B dM i + (s.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (macBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨j0, _, _, jout, jeq, jk⟩ => ⟨jeq, j0, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have k5 : t.gpr .a5 = s.gpr .a5 := jk.gpr (by decide)
  have hst := (show WP isa (.block (macBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let bw := word t.mem B (dM + 8 * i)
      let aw := word t.mem B (dA + 8 * i)
      let lo := t.gpr .a5 * bw + aw
      let c1 : BitVec 64 := if lo < aw then 1 else 0
      let sw := lo + t.gpr .t4
      let c2 : BitVec 64 := if sw < t.gpr .t4 then 1 else 0
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dA + 8 * i + 8) ∧
        t'.gpr .t2 = off B (dM + 8 * i + 8) ∧
        t'.gpr .t4 = BitVec.ofNat 64 ((t.gpr .a5).toNat * bw.toNat / 2 ^ 64) + c1 + c2 ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) sw) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [macBody, j0, j1, j2,
      hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith), hs'.ld (show dM + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dM + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    all_goals done)
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l4, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l2, show dM + 8 * i + 8 = dM + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wm : word t.mem B (dM + 8 * i) = word s.mem B (dM + 8 * i) :=
      jout.word (by have := aM.outside hi; omega_arith) (by omega_arith)
    have k := mac_arith (t.gpr .a5) (word t.mem B (dM + 8 * i)) (word t.mem B (dA + 8 * i)) (t.gpr .t4)
    simp only at k
    rw [lm, l4, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dM i,
      wordsVal_succ_top s.mem B dA i, Nat.mul_succ, Nat.pow_add, ← wa, ← wm, ← k5]
    rw [← k5] at jeq
    grind

/-! ## `shr` -/

/-- A word of the shift by 59: the top five bits of `x` and the low 59 of `y`. -/
theorem shr_arith (x y : BitVec 64) :
    (x >>> 59 + y <<< 5).toNat = x.toNat / 2 ^ 59 + 2 ^ 5 * (y.toNat % 2 ^ 59) := by
  have h1 : (x >>> 59).toNat = x.toNat / 2 ^ 59 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (y <<< 5).toNat = 2 ^ 5 * (y.toNat % 2 ^ 59) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := y.isLt
    omega_arith
  rw [BitVec.toNat_add, h1, h2]
  have := x.isLt
  have : x.toNat / 2 ^ 59 < 2 ^ 5 := Nat.div_lt_of_lt_mul (by omega)
  omega_arith

/-- The shift's invariant, a word on: `R + 2^(64 i) ⌊a / 2^59⌋ = ⌊A / 2^59⌋`
for `A` the first `i + 1` words, with `a` the last of them. -/
theorem shr_inv_step {R A a y i : Nat}
    (h : R + 2 ^ (64 * i) * (a / 2 ^ 59) = (A + 2 ^ (64 * i) * a) / 2 ^ 59) :
    R + 2 ^ (64 * i) * (a / 2 ^ 59 + 2 ^ 5 * (y % 2 ^ 59)) + 2 ^ (64 * (i + 1)) * (y / 2 ^ 59) =
      (A + 2 ^ (64 * i) * a + 2 ^ (64 * (i + 1)) * y) / 2 ^ 59 := by
  have e : 2 ^ (64 * (i + 1)) = 2 ^ 59 * (2 ^ (64 * i) * 2 ^ 5) := by
    rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 from rfl]; ac_rfl
  have hR : (A + 2 ^ (64 * i) * a + 2 ^ 59 * (2 ^ (64 * i) * 2 ^ 5) * y) / 2 ^ 59 =
      (A + 2 ^ (64 * i) * a) / 2 ^ 59 + 2 ^ (64 * i) * 2 ^ 5 * y := by
    rw [Nat.mul_assoc (2 ^ 59), Nat.add_mul_div_left _ _ (Nat.two_pow_pos 59)]
  rw [e, hR, ← h]
  have hy := Nat.mod_add_div y (2 ^ 59)
  have k : 2 ^ (64 * i) * 2 ^ 5 * y = 2 ^ (64 * i) * (2 ^ 5 * (y % 2 ^ 59)) +
      2 ^ 59 * (2 ^ (64 * i) * 2 ^ 5) * (y / 2 ^ 59) := by
    have : 2 ^ (64 * i) * 2 ^ 5 * y = 2 ^ (64 * i) * 2 ^ 5 * (y % 2 ^ 59 + 2 ^ 59 * (y / 2 ^ 59)) := by rw [hy]
    rw [this, Nat.mul_add]; ac_rfl
  rw [Nat.mul_add, k]
  omega

/-- `[o] := [a] >> 59` over `n` words (`countLoop .t3 shrBody`), reading
`n + 1`: the first `n` words of `⌊[a] / 2^59⌋`, and the last word's top bits. -/
theorem shrLoop_ok {s : State} {B : Addr} {Z dO dA n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hA8 : dA % 8 = 0) (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * (n + 1) ≤ Z)
    (aA : Ahead dO dA (n + 1)) :
    WP isa (countLoop .t3 shrBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * ((word s.mem B (dA + 8 * n)).toNat / 2 ^ 59) =
        wordsVal s.mem B dA (n + 1) / 2 ^ 59 ∧
      t.gpr .t0 = off B (dO + 8 * n) ∧ t.gpr .t1 = off B (dA + 8 * n) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dA + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * ((word s.mem B (dA + 8 * i)).toNat / 2 ^ 59) =
        wordsVal s.mem B dA (i + 1) / 2 ^ 59 ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (shrBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨j0, j1, jout, jeq, jk⟩ => ⟨jeq, j0, j1, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst := (show WP isa (.block (shrBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dA + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dA + 8 * i) >>> 59 + word t.mem B (dA + 8 * i + 8) <<< 5)) ∧
      Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [shrBody, j0, j1, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dA + 8 * i + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside (show i < n + 1 by omega); omega_arith) (by omega_arith)
    have wb : word t.mem B (dA + 8 * i + 8) = word s.mem B (dA + 8 * (i + 1)) := by
      rw [show dA + 8 * (i + 1) = dA + 8 * i + 8 by omega_arith]
      exact jout.word (by have := aA.outside (show i + 1 < n + 1 by omega); omega_arith) (by omega_arith)
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wb, shr_arith,
      wordsVal_succ_top s.mem B dA (i + 1)]
    rw [wordsVal_succ_top s.mem B dA i] at jeq ⊢
    rw [show dA + 8 * (i + 1) = dA + 8 * i + 8 by omega_arith]
    exact shr_inv_step jeq

/-! ## `lin` -/

/-- A signed coefficient times an unsigned word: `mul`'s low word and
`mulhu`'s high word less the word where the coefficient is negative. -/
theorem smul_split (c x : BitVec 64) :
    ((c * x).toNat : Int) + 2 ^ 64 * ((c.toNat * x.toNat / 2 ^ 64 : Nat) - ((c.sshiftRight 63 &&& x).toNat : Int)) =
      c.toInt * x.toNat := by
  rw [BitVec.toNat_mul, BitVec.toInt_eq_toNat_cond]
  cases hm : c.msb
  · have hu : c.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide c; rw [hm] at this; simp at this; omega
    have h0 : c >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, h0, BitVec.zero_and, ite_eq_left (by omega)]
    rw [← Int.natCast_mul]
    generalize c.toNat * x.toNat = P
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Int.natCast_zero, Int.sub_zero]
    omega
  · have hu : 2 ^ 63 ≤ c.toNat := by
      have := BitVec.msb_eq_decide c; rw [hm] at this; simp at this; omega
    have h0 : (~~~c) >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, h0, BitVec.not_zero, BitVec.allOnes_and,
      ite_eq_right (by omega), Int.sub_mul, ← Int.natCast_mul]
    generalize c.toNat * x.toNat = P
    omega

/-- The signed accumulator of `lin`: the low word unsigned, the high signed. -/
def acc (lo hi : BitVec 64) : Int := lo.toNat + 2 ^ 64 * hi.toInt

/-- `linTerm`: the accumulator plus a signed coefficient times a word, when
the sum fits. -/
theorem lin_term (c x t4 a4 : BitVec 64)
    (h1 : -2 ^ 127 ≤ acc t4 a4 + c.toInt * x.toNat) (h2 : acc t4 a4 + c.toInt * x.toNat < 2 ^ 127) :
    acc (t4 + c * x)
        (a4 + (if t4 + c * x < c * x then (1 : BitVec 64) else 0) + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) -
          (c.sshiftRight 63 &&& x)) =
      acc t4 a4 + c.toInt * x.toNat := by
  have hs := smul_split c x
  unfold acc at *
  rw [← hs] at h1 h2 ⊢
  have hc := c.isLt; have hx := x.isLt
  have hP : c.toNat * x.toNat / 2 ^ 64 < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_lt_of_le hc (Nat.le_of_lt hx) (by decide : 0 < 2 ^ 64)
    exact Nat.div_lt_of_lt_mul this
  have hL := (c * x).isLt
  have hM := (c.sshiftRight 63 &&& x).isLt
  have ht := t4.isLt; have ha := a4.isLt
  have vcy : (if t4 + c * x < c * x then (1 : BitVec 64) else 0).toNat = (t4.toNat + (c * x).toNat) / 2 ^ 64 := by
    have e : (t4 + c * x).toNat = (t4.toNat + (c * x).toNat) % 2 ^ 64 := BitVec.toNat_add _ _
    by_cases hlt : t4 + c * x < c * x
    · rw [ite_eq_left hlt]; rw [BitVec.lt_def, e] at hlt
      generalize (c * x).toNat = L at *; simp; omega
    · rw [ite_eq_right hlt]; rw [BitVec.lt_def, e] at hlt
      generalize (c * x).toNat = L at *; simp; omega
  generalize (if t4 + c * x < c * x then (1 : BitVec 64) else 0) = cy at vcy ⊢
  have na : (a4 + cy + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) - (c.sshiftRight 63 &&& x)).toNat =
      (2 ^ 64 - (c.sshiftRight 63 &&& x).toNat +
        ((a4.toNat + cy.toNat) % 2 ^ 64 + c.toNat * x.toNat / 2 ^ 64 % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
  generalize a4 + cy + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) - (c.sshiftRight 63 &&& x) = a4' at na ⊢
  have ia := BitVec.toInt_eq_toNat_cond a4
  have ia' := BitVec.toInt_eq_toNat_cond a4'
  rw [BitVec.toNat_add]
  rw [vcy] at na
  generalize c.toNat * x.toNat / 2 ^ 64 = H at *
  generalize (c * x).toNat = L at *
  generalize (c.sshiftRight 63 &&& x).toNat = M at *
  generalize t4.toNat = T at *
  generalize a4.toNat = A at *
  generalize a4'.toNat = A' at *
  split at ia <;> split at ia' <;> omega

/-- The accumulator shifted down a word: the high word's value. -/
theorem acc_shift (a : BitVec 64) : acc a (a.sshiftRight 63) = a.toInt := by
  unfold acc
  rw [BitVec.toInt_eq_toNat_cond a]
  cases hm : a.msb
  · have hu : a.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide a; rw [hm] at this; simp at this; omega
    have h0 : a >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, h0, ite_eq_left (by omega)]; simp
  · have hu : 2 ^ 63 ≤ a.toNat := by
      have := BitVec.msb_eq_decide a; rw [hm] at this; simp at this; omega
    have h0 : (~~~a) >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, h0, BitVec.not_zero, ite_eq_right (by omega)]
    simp
    omega

/-- A coefficient of at most `2^61` times a word. -/
theorem smul_bound (c x : BitVec 64) (h1 : -2 ^ 61 ≤ c.toInt) (h2 : c.toInt ≤ 2 ^ 61) :
    -2 ^ 125 ≤ c.toInt * x.toNat ∧ c.toInt * x.toNat ≤ 2 ^ 125 := by
  have hx0 : (0 : Int) ≤ x.toNat := Int.natCast_nonneg _
  have hx1 : (x.toNat : Int) ≤ 2 ^ 64 := by have := x.isLt; omega
  have a := Int.mul_le_mul_of_nonneg_right h2 hx0
  have b := Int.mul_le_mul_of_nonneg_right h1 hx0
  omega

/-- `lin`'s invariant, a word on. -/
theorem lin_inv_step {W Ai Bi x1 x2 k : Nat} {u v a S0 : Int} {lo hi : BitVec 64}
    (jeq : (W : Int) + 2 ^ k * a = u * Ai + v * Bi + S0) (e2 : acc lo hi = a + u * x1 + v * x2) :
    ((W + 2 ^ k * lo.toNat : Nat) : Int) + 2 ^ (k + 64) * hi.toInt =
      u * ((Ai + 2 ^ k * x1 : Nat) : Int) + v * ((Bi + 2 ^ k * x2 : Nat) : Int) + S0 := by
  unfold acc at e2
  rw [Int.pow_add]
  push_cast
  generalize (2 : Int) ^ k = M at *
  have := congrArg (M * ·) e2
  grind

/-- `[o] := u [a] + v [b]` over `n` words (`countLoop .t3 linBody`), for
signed `u`, `v` (in `a5`, `a7`) of at most `2^61`, from the signed
accumulator in `t4` and `a4`: the words and the accumulator out. -/
theorem linLoop_ok {s : State} {B : Addr} {Z dO dA dM n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dM)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hA8 : dA % 8 = 0) (hM8 : dM % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * n ≤ Z) (hM : dM + 8 * n ≤ Z)
    (aA : Ahead dO dA n) (aM : Ahead dO dM n)
    (hu1 : -2 ^ 61 ≤ (s.gpr .a5).toInt) (hu2 : (s.gpr .a5).toInt ≤ 2 ^ 61)
    (hv1 : -2 ^ 61 ≤ (s.gpr .a7).toInt) (hv2 : (s.gpr .a7).toInt ≤ 2 ^ 61)
    (hc1 : -2 ^ 63 ≤ acc (s.gpr .t4) (s.gpr .a4)) (hc2 : acc (s.gpr .t4) (s.gpr .a4) < 2 ^ 63) :
    WP isa (countLoop .t3 linBody) s fun t =>
      (wordsVal t.mem B dO n : Int) + 2 ^ (64 * n) * acc (t.gpr .t4) (t.gpr .a4) =
        (s.gpr .a5).toInt * wordsVal s.mem B dA n + (s.gpr .a7).toInt * wordsVal s.mem B dM n +
          acc (s.gpr .t4) (s.gpr .a4) ∧
      -2 ^ 63 ≤ acc (t.gpr .t4) (t.gpr .a4) ∧ acc (t.gpr .t4) (t.gpr .a4) < 2 ^ 63 ∧
      t.gpr .t0 = off B (dO + 8 * n) ∧ Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dA + 8 * i) ∧ t.gpr .t2 = off B (dM + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      ((wordsVal t.mem B dO i : Int) + 2 ^ (64 * i) * acc (t.gpr .t4) (t.gpr .a4) =
        (s.gpr .a5).toInt * wordsVal s.mem B dA i + (s.gpr .a7).toInt * wordsVal s.mem B dM i +
          acc (s.gpr .t4) (s.gpr .a4)) ∧
      -2 ^ 63 ≤ acc (t.gpr .t4) (t.gpr .a4) ∧ acc (t.gpr .t4) (t.gpr .a4) < 2 ^ 63 ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (linBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, jout, jeq, jb1, jb2, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], hc1, hc2,
      Keep.refl _ _⟩ h3)
    fun t ⟨j0, _, _, jout, jeq, jb1, jb2, jk⟩ => ⟨jeq, jb1, jb2, j0, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have k5 : t.gpr .a5 = s.gpr .a5 := jk.gpr (by decide)
  have k7 : t.gpr .a7 = s.gpr .a7 := jk.gpr (by decide)
  have hst := (show WP isa (.block (linBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let x1 := word t.mem B (dA + 8 * i)
      let x2 := word t.mem B (dM + 8 * i)
      let u := t.gpr .a5
      let v := t.gpr .a7
      let t4a := t.gpr .t4 + u * x1
      let a4a := t.gpr .a4 + (if t4a < u * x1 then (1 : BitVec 64) else 0) +
        BitVec.ofNat 64 (u.toNat * x1.toNat / 2 ^ 64) - (u.sshiftRight 63 &&& x1)
      let t4b := t4a + v * x2
      let a4b := a4a + (if t4b < v * x2 then (1 : BitVec 64) else 0) +
        BitVec.ofNat 64 (v.toNat * x2.toNat / 2 ^ 64) - (v.sshiftRight 63 &&& x2)
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dA + 8 * i + 8) ∧
        t'.gpr .t2 = off B (dM + 8 * i + 8) ∧
        t'.gpr .t4 = a4b ∧ t'.gpr .a4 = a4b.sshiftRight 63 ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) t4b) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [linBody, linTerm, j0, j1, j2, BitVec.add_zero,
      hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith), hs'.ld (show dM + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dM + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    all_goals done)
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l4, la, l3, lm⟩, lk⟩ => ?_
  have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
    jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
  have wm : word t.mem B (dM + 8 * i) = word s.mem B (dM + 8 * i) :=
    jout.word (by have := aM.outside hi; omega_arith) (by omega_arith)
  have b1 := smul_bound (t.gpr .a5) (word t.mem B (dA + 8 * i)) (k5 ▸ hu1) (k5 ▸ hu2)
  have b2 := smul_bound (t.gpr .a7) (word t.mem B (dM + 8 * i)) (k7 ▸ hv1) (k7 ▸ hv2)
  have e1 := lin_term (t.gpr .a5) (word t.mem B (dA + 8 * i)) (t.gpr .t4) (t.gpr .a4) (by omega) (by omega)
  have e2 := lin_term (t.gpr .a7) (word t.mem B (dM + 8 * i)) _ _ (by rw [e1]; omega) (by rw [e1]; omega)
  rw [e1] at e2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l2, show dM + 8 * i + 8 = dM + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  rotate_left 1
  · rw [l4, la, acc_shift]; exact BitVec.le_toInt _
  · rw [l4, la, acc_shift]; exact BitVec.toInt_lt
  · rw [l4, la, acc_shift, lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dM i,
      wordsVal_succ_top s.mem B dA i, Nat.mul_succ, ← wa, ← wm, ← k5, ← k7]
    rw [← k5, ← k7] at jeq
    exact lin_inv_step jeq e2

end VG.Proof.Rsa.RISCV64.InvBatch
