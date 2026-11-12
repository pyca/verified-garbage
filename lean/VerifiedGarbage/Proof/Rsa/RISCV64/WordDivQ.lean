module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
import VerifiedGarbage.Proof.Bignum.WordStepLazy
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the quotient, which only `recover_primes_det` needs, out of `KeyWordDiv`, which
-- `check_key` and `crt_values` import

/-!
# Division by words with the quotient, on RISC-V

`WordDiv.divCore a r m t (some (dig, q))`: the remainder as `divCore_ok`
gives it, and the quotient, from the steps' digits:

* `storeQ_ok`: a step's digit `q̂` (`s1`) stored at word `j` of `[dig]`, whose
  first `j + 1` words then read, most significant first, `qa 2^63 + q̂`
  (`digVal`) for `qa` those of the `j` before;
* `PreR2Lazy.stepsQ_ok` then gives `X = qa n + r`, `r < 2 n`, for `qa`
  the digits of the `S` steps, and `finish_ok` `g = [r ≥ n]`, so that the
  quotient is `qa + g`;
* `combine_ok`: `[q] := qa + g`, adding the digits from the least significant
  (`lowSum`), with their carries, 63 bits a digit (`orIn_val`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs)
open VG.Impl.Rsa.RISCV64.WordDiv (prep divInit chunk steps storeQ digInit combBody combine divCore)
open VG.Impl.Bignum.RISCV64.Precompute (step finish)
open VG.Impl.Bignum.RISCV64 (countLoop)

/-! ## The digits -/

/-- The first `j` words at `d`, digits of weight `2^63` apart, the first the
most significant. -/
def digVal (m : Mem) (B : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => digVal m B d j * 2 ^ 63 + (word m B (d + 8 * j)).toNat

theorem digVal_congr {m m' : Mem} {B : Addr} {d : Nat} :
    ∀ j, (∀ i < j, word m' B (d + 8 * i) = word m B (d + 8 * i)) → digVal m' B d j = digVal m B d j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [digVal]
    rw [digVal_congr j fun i hi => h i (by omega), h j (by omega)]

/-- The digits from `k` on below the most significant `S - k`: the last `k`,
least significant first. -/
def lowSum (m : Mem) (B : Addr) (d S : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => lowSum m B d S k + (word m B (d + 8 * (S - 1 - k))).toNat * 2 ^ (63 * k)

theorem digVal_low (m : Mem) (B : Addr) (d S : Nat) :
    ∀ k ≤ S, digVal m B d S = digVal m B d (S - k) * 2 ^ (63 * k) + lowSum m B d S k
  | 0, _ => by simp [lowSum]
  | k + 1, hk => by
    rw [digVal_low m B d S k (by omega), lowSum]
    have e : S - k = (S - (k + 1)) + 1 := by omega
    rw [e, digVal, show S - (k + 1) = S - 1 - k by omega, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add,
      show 63 + 63 * k = 63 * (k + 1) by omega]
    omega

theorem digVal_lowSum (m : Mem) (B : Addr) (d S : Nat) : digVal m B d S = lowSum m B d S S := by
  have := digVal_low m B d S S (Nat.le_refl _)
  rw [Nat.sub_self] at this
  simpa [digVal] using this

theorem wdq_off_add8 (B : Addr) (d : Nat) : off B d + BitVec.ofNat 64 8 = off B (d + 8) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- `storeQ`: the digit in `s1` stored at word `j` of the digits, `t2` the next word. -/
theorem storeQ_ok {u : State} {B : Addr} {Z dD j : Nat} (hs : Scr u B Z) (h2 : u.gpr .t2 = off B (dD + 8 * j))
    (hD8 : dD % 8 = 0) (hZ : dD + 8 * j + 8 ≤ Z) :
    WP isa (.block storeQ) u fun u' => (u'.gpr .t2 = off B (dD + 8 * (j + 1)) ∧
      u'.mem = u.mem.writeW (off B (dD + 8 * j)) (u.gpr .s1)) ∧ Keep [.t2] u u' := by
  have hnw := hs.nowrap
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold storeQ
  brun [h2, BitVec.add_zero, exec_addi_nat (show 8 < 2048 by decide), hs.st (show dD + 8 * j + 8 ≤ Z by omega),
    hs.al8 (show dD + 8 * j + 8 ≤ Z by omega) (by omega)]
  rw [show dD + 8 * j + 8 = dD + 8 * (j + 1) by omega]

theorem digVal_store {m : Mem} {B : Addr} {dD j : Nat} (v : BitVec 64) (fit : dD + 8 * j + 8 ≤ 2 ^ 64) :
    digVal (m.writeW (off B (dD + 8 * j)) v) B dD (j + 1) = digVal m B dD j * 2 ^ 63 + v.toNat := by
  simp only [digVal]
  rw [word_writeW_self, digVal_congr j fun i hi =>
    (writeW_outside m B (d := dD + 8 * j) v fit).word (by omega) (by omega)]

/-! ## A digit or-ed in -/

/-- A digit `e` or-ed in at bit `64 J + b` of `K ≥ J + 2` words below
`2^(64 J + b)`: into word `J` shifted up by `b`, and word `J + 1` by what is left. -/
theorem orIn_val (m : Mem) (B : Addr) {d K J b : Nat} (e : BitVec 64) (hJ : J + 2 ≤ K) (hb : b < 64)
    (hlt : wordsVal m B d K < 2 ^ (64 * J + b)) (fit : d + 8 * K ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B (d + 8 * J)) (word m B (d + 8 * J) ||| (e <<< b))).writeW (off B (d + 8 * J + 8))
      (word (m.writeW (off B (d + 8 * J)) (word m B (d + 8 * J) ||| (e <<< b))) B (d + 8 * J + 8) |||
        ((e >>> 1) >>> (63 - b)))) B d K = wordsVal m B d K + e.toNat * 2 ^ (64 * J + b) := by
  -- `K = J + 1 + 1 + R` words: the low `J`, word `J`, word `J + 1`, the rest.
  obtain ⟨R, rfl⟩ : ∃ R, K = J + 2 + R := ⟨K - (J + 2), by omega⟩
  have split : ∀ m' : Mem, wordsVal m' B d (J + 2 + R) = wordsVal m' B d J +
      2 ^ (64 * J) * ((word m' B (d + 8 * J)).toNat + 2 ^ 64 * ((word m' B (d + 8 * J + 8)).toNat +
        2 ^ 64 * wordsVal m' B (d + 8 * J + 16) R)) := fun m' => by
    rw [show J + 2 + R = J + (1 + (1 + R)) by omega, wordsVal_append, wordsVal_append m' B (d + 8 * J) 1 (1 + R),
      wordsVal_append m' B (d + 8 * J + 8 * 1) 1 R, show d + 8 * J + 8 * 1 = d + 8 * J + 8 by omega,
      show d + 8 * J + 8 + 8 * 1 = d + 8 * J + 16 by omega]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  have o1 := writeW_outside m B (d := d + 8 * J) (word m B (d + 8 * J) ||| (e <<< b)) (by omega)
  generalize hm1 : m.writeW (off B (d + 8 * J)) (word m B (d + 8 * J) ||| (e <<< b)) = m1 at o1 ⊢
  have o2 := writeW_outside m1 B (d := d + 8 * J + 8) (word m1 B (d + 8 * J + 8) ||| ((e >>> 1) >>> (63 - b)))
    (by omega)
  rw [split, split m]
  -- The words of `m`: those above `J` zero, word `J` below `2^b`.
  have hm := split m
  have hw0 := (word m B (d + 8 * J)).isLt
  have hlo := wordsVal_lt m B d J
  generalize word m B (d + 8 * J) = W0 at hm hw0 hm1
  generalize hW1 : word m B (d + 8 * J + 8) = W1 at hm
  generalize hRr : wordsVal m B (d + 8 * J + 16) R = Rr at hm
  generalize hL : wordsVal m B d J = L at hm hlo ⊢
  have hpow : 2 ^ (64 * J + b) = 2 ^ (64 * J) * 2 ^ b := Nat.pow_add _ _ _
  rw [hpow] at hlt
  rw [hm] at hlt
  have hW0 : W0.toNat < 2 ^ b := by
    by_contra c
    have : 2 ^ (64 * J) * 2 ^ b ≤ 2 ^ (64 * J) * W0.toNat := Nat.mul_le_mul_left _ (by omega)
    have := Nat.le_add_right (2 ^ (64 * J) * W0.toNat) (2 ^ (64 * J) * (2 ^ 64 * (W1.toNat + 2 ^ 64 * Rr)))
    rw [← Nat.mul_add] at this
    omega
  have hhi : W1.toNat + 2 ^ 64 * Rr = 0 := by
    by_contra c
    have : 2 ^ (64 * J) * 2 ^ 64 ≤ 2 ^ (64 * J) * (2 ^ 64 * (W1.toNat + 2 ^ 64 * Rr)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    have h64 : 2 ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ (64 * J) * 2 ^ b ≤ 2 ^ (64 * J) * 2 ^ 64 := Nat.mul_le_mul_left _ h64
    rw [Nat.mul_add] at hlt
    omega
  have hW1' : W1.toNat = 0 := by omega
  have hRr' : Rr = 0 := by
    have := Nat.two_pow_pos 64
    rcases Nat.eq_zero_or_pos Rr with h | h
    · exact h
    · exfalso; have := Nat.le_mul_of_pos_right (2 ^ 64) h; omega
  -- The words of `m2`.
  have w0 : (word (m1.writeW (off B (d + 8 * J + 8)) (word m1 B (d + 8 * J + 8) ||| ((e >>> 1) >>> (63 - b))))
      B (d + 8 * J)).toNat = W0.toNat + e.toNat % 2 ^ (64 - b) * 2 ^ b := by
    rw [o2.word (by omega) (by omega), ← hm1, word_writeW_self, BitVec.toNat_or, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, show (2 : Nat) ^ 64 = 2 ^ (64 - b) * 2 ^ b by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_mod_mul_right, Nat.or_comm, Nat.mul_comm (e.toNat % _), ← Nat.two_pow_add_eq_or_of_lt hW0]
    omega
  have w1 : (word (m1.writeW (off B (d + 8 * J + 8)) (word m1 B (d + 8 * J + 8) ||| ((e >>> 1) >>> (63 - b))))
      B (d + 8 * J + 8)).toNat = e.toNat / 2 ^ (64 - b) := by
    rw [word_writeW_self, ← hm1, (writeW_outside m B (d := d + 8 * J) _ (by omega)).word (by omega) (by omega), hW1,
      BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 1 + (63 - b) = 64 - b by omega]
    rw [show W1.toNat = 0 from hW1', Nat.zero_or]
  have wR : wordsVal (m1.writeW (off B (d + 8 * J + 8)) (word m1 B (d + 8 * J + 8) ||| ((e >>> 1) >>> (63 - b))))
      B (d + 8 * J + 16) R = 0 := by
    rw [o2.wordsVal (by omega) (by omega), ← hm1, (writeW_outside m B (d := d + 8 * J) _ (by omega)).wordsVal
      (by omega) (by omega), hRr, hRr']
  have wL : wordsVal (m1.writeW (off B (d + 8 * J + 8)) (word m1 B (d + 8 * J + 8) ||| ((e >>> 1) >>> (63 - b))))
      B d J = L := by
    rw [o2.wordsVal (by omega) (by omega), ← hm1, (writeW_outside m B (d := d + 8 * J) _ (by omega)).wordsVal
      (by omega) (by omega), hL]
  rw [w0, w1, wR, wL, hW1', hRr']
  -- `e 2^b = (e mod 2^(64 - b)) 2^b + 2^64 ⌊e / 2^(64 - b)⌋`.
  have e64 : e.toNat * 2 ^ b = e.toNat % 2 ^ (64 - b) * 2 ^ b + 2 ^ 64 * (e.toNat / 2 ^ (64 - b)) := by
    have := Nat.mod_add_div e.toNat (2 ^ (64 - b))
    rw [show (2 : Nat) ^ 64 = 2 ^ (64 - b) * 2 ^ b by rw [← Nat.pow_add]; congr 1; omega]
    calc e.toNat * 2 ^ b = (e.toNat % 2 ^ (64 - b) + 2 ^ (64 - b) * (e.toNat / 2 ^ (64 - b))) * 2 ^ b := by
          rw [this]
      _ = _ := by rw [Nat.add_mul, Nat.mul_right_comm (2 ^ (64 - b))]
  rw [hpow, Nat.mul_left_comm e.toNat, e64]
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
  omega

/-! ## The sum of the digits -/

/-- The registers `combine` writes. -/
abbrev combRegs : List Reg := [.a0, .a1, .a2, .a3, .s0, .s1, .t1, .t2, .t3, .t4, .t5, .t6]

/-- What `combine` keeps after `k` digits: the pointers, the bit offset `63 k`,
the carry `c` (`s0`) and the previous digit's top bit `h` (`s1`), and `[q]`'s
`K` words `E < 2^(63 k)` with `E + 2^(63 k) (c + h) = lowSum k + g`. -/
def CbInv (s : State) (B : Addr) (dQ K dD S g : Nat) (k : Nat) (t : State) : Prop :=
  t.gpr .a2 = off B dQ ∧ t.gpr .t1 = BitVec.ofNat 64 (63 * k) ∧ t.gpr .t2 = off B (dD + 8 * S - 8 * (k + 1)) ∧
    (t.gpr .s0).toNat ≤ 1 ∧ (t.gpr .s1).toNat ≤ 1 ∧ wordsVal t.mem B dQ K < 2 ^ (63 * k) ∧
    wordsVal t.mem B dQ K + 2 ^ (63 * k) * ((t.gpr .s0).toNat + (t.gpr .s1).toNat) = lowSum s.mem B dD S k + g ∧
    Outside B dQ (8 * K) s.mem t.mem ∧ Keep combRegs s t

/-- A digit's low 63 bits, by shifts. -/
theorem lo63 (x : BitVec 64) : ((x <<< 1) >>> 1).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by decide)]

theorem hi63 (x : BitVec 64) : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem combBody_ok {s : State} {B : Addr} {Z dQ K dD S g k : Nat} (hs : Scr s B Z) (hk : k < S)
    (hS : S < 2 ^ 14) (hK : 63 * (S - 1) / 64 + 2 ≤ K) (hQ8 : dQ % 8 = 0) (hD8 : dD % 8 = 0) (hD : 8 ≤ dD)
    (hQZ : dQ + 8 * K ≤ Z) (hDZ : dD + 8 * S ≤ Z) (dQD : dQ + 8 * K ≤ dD ∨ dD + 8 * S ≤ dQ)
    {t : State} (hI : CbInv s B dQ K dD S g k t) :
    WP isa (.block (combBody ++ ([.addi .a1 .a1 (-1)] : List Instr))) t fun t' =>
      CbInv s B dQ K dD S g (k + 1) t' ∧ t'.gpr .a1 = t.gpr .a1 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j2, j1, jt2, jc, jh, jlt, jv, jout, jk⟩ := hI
  have hs' := hs.congr jk.2.2
  have e2 : dD + 8 * S - 8 * (k + 1) = dD + 8 * (S - 1 - k) := by omega
  rw [e2] at jt2
  -- The digit, and where it goes: word `J` of `[q]`, bit `b`.
  have wd : word t.mem B (dD + 8 * (S - 1 - k)) = word s.mem B (dD + 8 * (S - 1 - k)) :=
    jout.word (by omega) (by omega)
  generalize hd : word s.mem B (dD + 8 * (S - 1 - k)) = d at wd
  have rd : t.mem.readW (off B (dD + 8 * (S - 1 - k))) 64 = d := wd
  have ho : 63 * k < 2 ^ 20 := by omega
  obtain ⟨sh1, sh2⟩ := shifts_val (63 * k) (by omega)
  have ea := ea_word B (d := dQ) ho
  generalize hJ : 63 * k / 64 = J at ea
  generalize hb : 63 * k % 64 = b at sh1 sh2
  have hJb : 64 * J + b = 63 * k := by omega
  have hJK : J + 2 ≤ K := by
    have : 63 * k ≤ 63 * (S - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 63 * k / 64 ≤ 63 * (S - 1) / 64 := Nat.div_le_div_right this
    omega
  generalize hc : t.gpr .s0 = c at jc jv
  generalize hh : t.gpr .s1 = h at jh jv
  generalize hV : (d <<< 1) >>> 1 + h + c = V
  generalize hsb : BitVec.ofNat 64 (63 * k) &&& BitVec.ofNat 64 63 = sb at sh1 sh2
  have j5 : t.gpr .a1 = t.gpr .a1 := rfl
  refine WP.mono (WP.keep [.a0, .a1, .a3, .s0, .s1, .t1, .t2, .t3, .t4, .t5, .t6] (Q := fun t' =>
      t'.gpr .t1 = BitVec.ofNat 64 (63 * k) + BitVec.ofNat 64 63 ∧
      t'.gpr .t2 = off B (dD + 8 * (S - 1 - k) - 8) ∧ t'.gpr .s0 = V >>> 63 ∧ t'.gpr .s1 = d >>> 63 ∧
      t'.gpr .a1 = t.gpr .a1 - BitVec.ofNat 64 1 ∧
      t'.mem = (t.mem.writeW (off B (dQ + 8 * J)) (word t.mem B (dQ + 8 * J) ||| (((V <<< 1) >>> 1) <<< (sb.toNat % 64)))).writeW
        (off B (dQ + 8 * J + 8))
        (word (t.mem.writeW (off B (dQ + 8 * J)) (word t.mem B (dQ + 8 * J) ||| (((V <<< 1) >>> 1) <<< (sb.toNat % 64))))
          B (dQ + 8 * J + 8) ||| ((((V <<< 1) >>> 1) >>> 1) >>> ((sb ^^^ BitVec.ofNat 64 63).toNat % 64)))) (by
    unfold combBody
    brun [j2, j1, jt2, rd, hc, hh, hV, hsb, ea, exec_sllReg, exec_srlReg, BitVec.add_zero,
      off_sub B (show 8 ≤ dD + 8 * (S - 1 - k) by omega),
      hs'.ld (show dD + 8 * (S - 1 - k) + 8 ≤ Z by omega), hs'.al8 (show dD + 8 * (S - 1 - k) + 8 ≤ Z by omega) (by omega),
      hs'.ld (show dQ + 8 * J + 8 ≤ Z by omega), hs'.al8 (show dQ + 8 * J + 8 ≤ Z by omega) (by omega),
      hs'.st (show dQ + 8 * J + 8 ≤ Z by omega),
      hs'.ld (show dQ + 8 * J + 8 + 8 ≤ Z by omega), hs'.al8 (show dQ + 8 * J + 8 + 8 ≤ Z by omega) (by omega),
      hs'.st (show dQ + 8 * J + 8 + 8 ≤ Z by omega)]) (by rfl) (by rfl)) fun t' ⟨⟨u1, u2, u0, us1, ua1, um⟩, uk⟩ => ?_
  rw [sh1, sh2] at um
  -- The sum's digit `e = V mod 2^63` and carry `⌊V / 2^63⌋`, `V = lo + h + c` without wrapping.
  have hlo := lo63 d
  have hhi := hi63 d
  have hd2 := Nat.mod_add_div d.toNat (2 ^ 63)
  have hdl := d.isLt
  have hVv : V.toNat = d.toNat % 2 ^ 63 + h.toNat + c.toNat := by
    rw [← hV, BitVec.toNat_add, BitVec.toNat_add, hlo]
    have : d.toNat % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have he := lo63 V
  have hc' := hi63 V
  have hV2 := Nat.mod_add_div V.toNat (2 ^ 63)
  have hW := orIn_val t.mem B (d := dQ) (K := K) (J := J) (b := b) ((V <<< 1) >>> 1) hJK (by omega)
    (by rw [hJb]; exact jlt) (by omega)
  rw [← um] at hW
  rw [he] at hW
  have hP : 2 ^ (64 * J + b) = 2 ^ (63 * k) := by rw [hJb]
  rw [hP] at hW
  have hP1 : 2 ^ (63 * (k + 1)) = 2 ^ (63 * k) * 2 ^ 63 := by
    rw [← Nat.pow_add, show 63 * k + 63 = 63 * (k + 1) by omega]
  have hlt' : V.toNat % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by decide)
  have kk : Keep combRegs s t' := (jk.trans uk).mono (by decide)
  refine ⟨⟨(uk.gpr (by decide)).trans j2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, kk⟩, ua1⟩
  · rw [u1, ← BitVec.ofNat_add, show 63 * k + 63 = 63 * (k + 1) by omega]
  · rw [u2, show dD + 8 * (S - 1 - k) - 8 = dD + 8 * S - 8 * (k + 1 + 1) by omega]
  · rw [u0, hc']; omega
  · rw [us1, hhi]; omega
  · rw [hW, hP1]
    have := Nat.mul_le_mul_left (2 ^ (63 * k)) (show V.toNat % 2 ^ 63 + 1 ≤ 2 ^ 63 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    rw [Nat.mul_comm] at hW ⊢
    omega
  · rw [hW, u0, us1, hc', hhi, lowSum, hd, hP1]
    generalize 2 ^ (63 * k) = P at jv ⊢
    have e1 : P * d.toNat = P * (d.toNat % 2 ^ 63) + 2 ^ 63 * (P * (d.toNat / 2 ^ 63)) := by
      have h := congrArg (P * ·) hd2
      rw [Nat.mul_add, Nat.mul_left_comm] at h
      exact h.symm
    have e2 : P * (V.toNat % 2 ^ 63) + 2 ^ 63 * (P * (V.toNat / 2 ^ 63)) =
        P * (d.toNat % 2 ^ 63) + P * h.toNat + P * c.toNat := by
      rw [Nat.mul_left_comm, ← Nat.mul_add, hV2, hVv, Nat.mul_add, Nat.mul_add]
    rw [Nat.mul_add] at jv
    rw [Nat.mul_assoc, Nat.mul_add, Nat.mul_add, Nat.mul_comm (V.toNat % 2 ^ 63) P, Nat.mul_comm d.toNat P,
      Nat.mul_left_comm P (2 ^ 63) (V.toNat / 2 ^ 63), Nat.mul_left_comm P (2 ^ 63) (d.toNat / 2 ^ 63)]
    omega
  · rw [um]
    exact (jout.trans ((writeW_outside t.mem B (d := dQ + 8 * J) _ (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ B (d := dQ + 8 * J + 8) _ (by omega)).mono (by omega) (by omega))

theorem ofNat_add_off (B : Addr) (a d : Nat) : BitVec.ofNat 64 a + off B d = off B (d + a) := by
  simp only [off, BitVec.ofNat_add]; rw [BitVec.add_comm, BitVec.add_assoc]

theorem mask_and1 {g : Nat} (hg : g ≤ 1) : (0 - BitVec.ofNat 64 g) &&& 1#64 = BitVec.ofNat 64 g := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with rfl | rfl <;> decide

/-- `combine q`: `[q] := qa + g` for `qa` the `S` digits at `dD` (`s8`, `S` in
`s7`) and `g` in `finish`'s mask `s1 = 0 - g`, from `[q]` zero, for a sum
below `2^(63 S)`. -/
theorem combine_ok {s : State} {B : Addr} {Z w N q dD S g : Nat} (h : Ws s B Z w N) (hq : q < N) (hN : N ≤ 2048)
    (hS1 : 1 ≤ S) (hS : S < 2 ^ 14) (hK : 63 * (S - 1) / 64 + 2 ≤ w + 1) (hD8 : dD % 8 = 0) (hD : 8 ≤ dD)
    (hDZ : dD + 8 * S ≤ Z) (dQD : arr w q + 8 * (w + 1) ≤ dD ∨ dD + 8 * S ≤ arr w q)
    (h7 : s.gpr .s7 = BitVec.ofNat 64 S) (h8 : s.gpr .s8 = off B dD) (h1 : s.gpr .s1 = 0 - BitVec.ofNat 64 g)
    (hg : g ≤ 1) (hq0 : wordsVal s.mem B (arr w q) (w + 1) = 0) (hfit : digVal s.mem B dD S + g < 2 ^ (63 * S)) :
    WP isa (combine q) s fun t => Ws t B Z w N ∧ Frame B w [q] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w q) (w + 1) = digVal s.mem B dD S + g ∧ Keep combRegs s t := by
  have fitq := h.arr_fit hq
  have nw := h.nowrap
  have hSw : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  unfold combine
  refine WP.seq ?_
  refine ptr_ok h (by decide) (by decide) (show q < 2048 by omega) ?_
  refine WP.mono (WP.keep [.s0, .s1, .t2, .t1, .a1] (Q := fun u => u.gpr .s0 = BitVec.ofNat 64 g ∧ u.gpr .s1 = 0 ∧
      u.gpr .t2 = off B (dD + 8 * S - 8 * (0 + 1)) ∧ u.gpr .t1 = BitVec.ofNat 64 (63 * 0) ∧
      u.gpr .a1 = BitVec.ofNat 64 S ∧ u.mem = s.mem) (by
    brun [h7, h8, h1, mask_and1 hg, shl3_ofNat, ofNat_add_off, off_sub B (show 8 ≤ dD + 8 * S by omega),
      exec_li_zero, BitVec.add_zero]
    rfl) (by rfl) (by rfl)) fun s₁ ⟨⟨u0, u1, u2, ut1, ua1, um⟩, uk⟩ => ?_
  have k1 : Keep combRegs s s₁ := ((Keep.write _ _ _).trans uk).mono (by decide)
  have h₁ := h.of_keep k1
  have g2 : s₁.gpr .a2 = off B (arr w q) := by rw [uk.gpr (by decide)]; simp [gpr_write]
  have I0 : CbInv s₁ B (arr w q) (w + 1) dD S g 0 s₁ := ⟨g2, ut1, u2, by rw [u0, BitVec.toNat_ofNat]; omega,
    by rw [u1]; decide, by rw [um, hq0]; decide, by rw [um, hq0, u0, u1, BitVec.toNat_ofNat]; simp [lowSum]; omega,
    Outside.refl _ _ _ _, Keep.refl _ _⟩
  refine WP.mono (wp_countdown (cnt := .a1) (N := S) (by omega) (by omega) (CbInv s₁ B (arr w q) (w + 1) dD S g)
    (fun k hk t hI _ => combBody_ok h₁.scr hk hS hK (arr_al w q) hD8 hD (by omega) hDZ dQD hI) I0 ua1)
    fun t ⟨_, _, _, tc, th, tlt, tv, tout, tk⟩ => ?_
  rw [um, ← digVal_lowSum] at tv
  have hz : (t.gpr .s0).toNat + (t.gpr .s1).toNat = 0 := by
    rcases Nat.eq_zero_or_pos ((t.gpr .s0).toNat + (t.gpr .s1).toNat) with e | e
    · exact e
    · exfalso
      have := Nat.le_mul_of_pos_right (2 ^ (63 * S)) e
      omega
  rw [hz, Nat.mul_zero, Nat.add_zero] at tv
  rw [um] at tout
  have kk : Keep combRegs s t := (k1.trans tk).mono (by decide)
  exact ⟨h.of_keep kk,
    Frame.of_arr (o := q) (d := 0) (n := 8 * (w + 1)) (by simpa using tout) (by omega) (by simp), tv, kk⟩

/-! ## The division -/

/-- Changed only within two arrays. -/
theorem Frame.of_out2 {B : Addr} {w o1 o2 d1 n1 d2 n2 : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Out2 B (arr w o1 + d1) n1 (arr w o2 + d2) n2 m m') (h1 : d1 + n1 ≤ S w) (h2 : d2 + n2 ≤ S w)
    (ho1 : o1 ∈ js) (ho2 : o2 ∈ js) : Frame B w js ds m m' := by
  intro x hx
  have a1 := hx (arr w o1, S w) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨o1, ho1, rfl⟩)
  have a2 := hx (arr w o2, S w) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨o2, ho2, rfl⟩)
  exact h x (by omega) (by omega)

/-- Two ranges in different arrays are apart. -/
theorem rgn {w j k : Nat} (h : j ≠ k) {x y x' y' : Nat} (h1 : x + y ≤ S w) (h2 : x' + y' ≤ S w) :
    arr w j + x + y ≤ arr w k + x' ∨ arr w k + x' + y' ≤ arr w j + x := by
  rcases arr_disj (w := w) h with e | e <;> omega

/-- The steps of `divCore`'s quotient: `stepsQ_ok` with `chunk` and the digits
stored, from the state `divInit` and `digInit` leave. -/
theorem stepsDig_ok {u : State} {B : Addr} {Z w N a r m t dig v Wd X S z M : Nat} (h : Ws u B Z w N)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (hdg : dig < N)
    (hra : r ≠ a) (hrm : r ≠ m) (hrt : r ≠ t) (hgr : dig ≠ r) (hgm : dig ≠ m) (hga : dig ≠ a) (hgt : dig ≠ t)
    (hv : 4 ≤ v) (hvw : v ≤ w) (hWd : Wd ≤ w + 2) (hS1 : 1 ≤ S) (hSw : S ≤ w + 2)
    (hSW : 63 * (S - 1) / 64 + 2 ≤ Wd)
    (h2 : u.gpr .a2 = off B (arr w r)) (h6 : u.gpr .a6 = off B (arr w t)) (h7 : u.gpr .a7 = off B (arr w m))
    (ht0 : u.gpr .t0 = BitVec.ofNat 64 v) (h4 : u.gpr .a4 = 0) (h1 : u.gpr .a1 = BitVec.ofNat 64 S)
    (ht1 : u.gpr .t1 = BitVec.ofNat 64 (63 * (S - 1))) (h5 : u.gpr .a5 = off B (arr w a))
    (ht2 : u.gpr .t2 = off B (arr w dig + 8 * 0))
    (nm : Norm u.mem B (arr w t) M v z) (hM : wordsVal u.mem B (arr w m) v = M)
    (hV0 : wordsVal u.mem B (arr w r) (v + 1) = X / 2 ^ (63 * (S - 1))) (hX0 : X / 2 ^ (63 * S) < 2 * M)
    (hX : wordsVal u.mem B (arr w a) Wd = X) :
    WP isa (steps chunk storeQ) u fun u' =>
      (∃ r' qa, r' < 2 * M ∧ X = qa * M + r' ∧ wordsVal u'.mem B (arr w r) (v + 1) / 2 ^ 63 = r' ∧
        Out2 B (arr w r) (8 * (v + 1)) (arr w dig) (8 * S) u.mem u'.mem ∧
        digVal u'.mem B (arr w dig) S = qa) ∧
      Keep (.a1 :: (stepRegs ++ chunkRegs ++ ([.t2] : List Reg))) u u' := by
  have fita := h.arr_fit ha
  have fitr := h.arr_fit hr
  have fitm := h.arr_fit hm
  have fitt := h.arr_fit ht
  have fitg := h.arr_fit hdg
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  -- The ranges apart.
  have dNV : arr w m + 8 * v ≤ arr w r ∨ arr w r + 8 * (v + 1) ≤ arr w m := by
    have := rgn (w := w) hrm.symm (x := 0) (y := 8 * v) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega); simpa using this
  have dTV : arr w t + 32 ≤ arr w r ∨ arr w r + 8 * (v + 1) ≤ arr w t := by
    have := rgn (w := w) hrt.symm (x := 0) (y := 32) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega); simpa using this
  have dND : arr w m + 8 * v ≤ arr w dig ∨ arr w dig + 8 * S ≤ arr w m := by
    have := rgn (w := w) hgm.symm (x := 0) (y := 8 * v) (x' := 0) (y' := 8 * S) (by omega) (by omega); simpa using this
  have dTD : arr w t + 32 ≤ arr w dig ∨ arr w dig + 8 * S ≤ arr w t := by
    have := rgn (w := w) hgt.symm (x := 0) (y := 32) (x' := 0) (y' := 8 * S) (by omega) (by omega); simpa using this
  have dVD : arr w r + 8 * (v + 1) ≤ arr w dig ∨ arr w dig + 8 * S ≤ arr w r := by
    have := rgn (w := w) hgr.symm (x := 0) (y := 8 * (v + 1)) (x' := 0) (y' := 8 * S) (by omega) (by omega); simpa using this
  have dAV : ∀ {k : Nat}, k ≤ w + 2 → arr w a + 8 * k ≤ arr w r ∨ arr w r + 8 * (v + 1) ≤ arr w a := fun {k} hk => by
    have := rgn (w := w) hra.symm (x := 0) (y := 8 * k) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega); simpa using this
  have dAD : ∀ {k : Nat}, k ≤ w + 2 → arr w a + 8 * k ≤ arr w dig ∨ arr w dig + 8 * S ≤ arr w a := fun {k} hk => by
    have := rgn (w := w) hga.symm (x := 0) (y := 8 * k) (x' := 0) (y' := 8 * S) (by omega) (by omega); simpa using this
  have dGV : ∀ {i : Nat}, i < S → arr w dig + 8 * i + 8 ≤ arr w r ∨ arr w r + 8 * (v + 1) ≤ arr w dig + 8 * i :=
    fun {i} hi => rgn (w := w) hgr (x := 8 * i) (y := 8) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega) |>.imp
      (fun e => by omega) (fun e => by omega)
  have dGA : ∀ {i : Nat}, i < S → arr w dig + 8 * i + 8 ≤ arr w a ∨ arr w a + 8 * Wd ≤ arr w dig + 8 * i :=
    fun {i} hi => rgn (w := w) hga (x := 8 * i) (y := 8) (x' := 0) (y' := 8 * Wd) (by omega) (by omega) |>.imp
      (fun e => by omega) (fun e => by omega)
  have dD8 := arr_al w dig
  exact WP.mono (stepsQ_ok (mid := chunk) (midRegs := chunkRegs) (post := storeQ) (postRegs := [.t2])
    (X := X) (S := S) (z := z) (dV := arr w r) (dN := arr w m) (dT := arr w t) (dD := arr w dig) (nD := 8 * S)
    (Q := fun j qa u' => u'.gpr .t1 = BitVec.ofNat 64 (63 * (S - 1 - j)) ∧ u'.gpr .a5 = off B (arr w a) ∧
      u'.wr = u.wr ∧ u'.gpr .t2 = off B (arr w dig + 8 * j) ∧ wordsVal u'.mem B (arr w a) Wd = X ∧
      digVal u'.mem B (arr w dig) j = qa ∧ j ≤ S)
    (Q' := fun j qa u' => u'.gpr .t1 = BitVec.ofNat 64 (63 * (S - 1 - (j + 1))) ∧ u'.gpr .a5 = off B (arr w a) ∧
      u'.wr = u.wr ∧ u'.gpr .t2 = off B (arr w dig + 8 * j) ∧ wordsVal u'.mem B (arr w a) Wd = X ∧
      digVal u'.mem B (arr w dig) j = qa ∧ j < S)
    h.scr h2 h6 h7 ht0 h4 h1 hS1 (by omega) hv (by omega) (arr_al w r) (arr_al w m) (arr_al w t)
    (by omega) (by omega) (by omega) dNV dTV dND dTD dVD nm.hP nm.hz (by rw [hM]; exact nm.hd63)
    (by rw [hM]; exact nm.hd) nm.hv (by rw [hM]; exact nm.hdl) hV0 (by rw [hM]; exact hX0)
    ⟨by rw [ht1, Nat.sub_zero], h5, rfl, ht2, hX, rfl, Nat.zero_le _⟩
    (fun j qa u₁ u₂ ⟨q1, q5, qw, qt2, qx, qd, qj⟩ ku ou => ⟨(ku.gpr (by decide)).trans q1,
      (ku.gpr (by decide)).trans q5, ku.2.2.trans qw, (ku.gpr (by decide)).trans qt2,
      by rw [Outside.wordsVal ou (dAV hWd) (by omega)]; exact qx,
      by rw [digVal_congr j fun i hi => ou.word (dGV (by omega)) (by omega)]; exact qd, qj⟩)
    (fun j qa u₁ u₂ ⟨q1, q5, qw, qt2, qx, qd, qj⟩ ku ou => ⟨(ku.gpr (by decide)).trans q1,
      (ku.gpr (by decide)).trans q5, ku.2.2.trans qw, (ku.gpr (by decide)).trans qt2,
      by rw [Outside.wordsVal ou (dAV hWd) (by omega)]; exact qx,
      by rw [digVal_congr j fun i hi => ou.word (dGV (by omega)) (by omega)]; exact qd, qj⟩)
    (fun j hj qa u₁ ⟨q1, q5, qw, qt2, qx, qd, _⟩ => by
      refine WP.mono (chunk_ok (Wd := Wd) (h.scr.congr qw) q1 q5 (by omega) (by omega) (by omega) qx)
        fun u' ⟨⟨c1, c6, cm⟩, ck⟩ => ⟨by rw [c6, show S - 1 - j - 1 = S - 2 - j by omega], cm, ck,
          by rw [c1, show S - 1 - j - 1 = S - 1 - (j + 1) by omega], (ck.gpr (by decide)).trans q5,
          ck.2.2.trans qw, (ck.gpr (by decide)).trans qt2, by rw [cm]; exact qx, by rw [cm]; exact qd, hj⟩)
    (fun j hj qa u₁ ⟨q1, q5, qw, qt2, qx, qd, _⟩ => by
      refine WP.mono (storeQ_ok (h.scr.congr qw) qt2 dD8 (by omega)) fun u' ⟨⟨s2, sm⟩, sk⟩ => ?_
      have so := writeW_outside u₁.mem B (d := arr w dig + 8 * j) (u₁.gpr .s1) (by omega)
      refine ⟨⟨by rw [sk.gpr (by decide), q1], (sk.gpr (by decide)).trans q5, sk.2.2.trans qw, s2, ?_,
        by rw [sm, digVal_store _ (by omega), qd], hj⟩, sk, by rw [sm]; exact so.mono (by omega) (by omega)⟩
      rw [sm, Outside.wordsVal so ((dGA hj).symm.imp (fun e => by omega) (fun e => by omega)) (by omega)]
      exact qx)
    (by decide) (by decide)) fun u' ⟨⟨r', qa, hr', hXq, hV', o', ⟨_, _, _, _, _, qd, _⟩⟩, k'⟩ =>
      ⟨⟨r', qa, by rw [← hM]; exact hr', by rw [← hM]; exact hXq, hV', o', qd⟩, k'⟩

theorem seq3_then {a b c d : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a (.seq b c)) s P)
    (k : ∀ u, P u → WP isa d u Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun u hu => ?_
  rw [WP.seq_iff] at hu ⊢
  refine WP.mono hu fun u' hu' => ?_
  rw [WP.seq_iff]
  exact WP.mono hu' k

/-- The registers `divCore` writes with the quotient. -/
abbrev divQRegs : List Reg := divWRegs ++ [.s7, .s8]

/-- `[j]`'s first `k` words, apart from the array `t`'s changes. -/
theorem words_of_frame1 {m m' : Mem} {B : Addr} {w j t k : Nat} (f : Frame B w [t] [] m m')
    (hjt : j ≠ t) (hk : k ≤ w + 2) (hfit : arr w j + S w ≤ 2 ^ 64) :
    wordsVal m' B (arr w j) k = wordsVal m B (arr w j) k := by
  have hSz : S w = 8 * (w + 2) := rfl
  refine f.words (fun k' hk' => ?_) (by simp) (by omega)
  simp at hk'; subst hk'
  have := rgn (w := w) hjt (x := 0) (y := 8 * k) (x' := 0) (y' := S w) (by omega) (by omega)
  simpa using this

/-- The head of `divCore`'s quotient: the divisor normalized, the first `V`,
and the digits' pointer, `S` and it kept for `combine`; `[a]`, `[m]`, `[q]`
and `[r]`'s words from `v + 1` as they were. -/
theorem divQHead_ok {s : State} {B : Addr} {Z w N a r m t dig q v Wd : Nat} (h : Ws s B Z w N) (hN : N ≤ 2048)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (hdg : dig < N) (hq : q < N)
    (hra : r ≠ a) (hrm : r ≠ m) (hrt : r ≠ t) (hmt : m ≠ t) (hat : a ≠ t) (hqr : q ≠ r) (hqt : q ≠ t)
    (hv : 4 ≤ v) (hvw : v ≤ w) (hvW : v < Wd) (hWd : Wd ≤ w + 2) (hY : Wd - v ≤ 187)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 v) (ht6 : s.gpr .t6 = BitVec.ofNat 64 Wd)
    (hr0 : wordsVal s.mem B (arr w r) (v + 1) = 0) (hT : 0 < (word s.mem B (arr w m + 8 * (v - 1))).toNat) :
    WP isa (seqs [prep m t, divInit a r, .block (digInit dig)]) s fun u => Ws u B Z w N ∧
      Frame B w [r, t] [] s.mem u.mem ∧ Keep (prepRegs ++ divInitRegs ++ ([.t2, .s7, .s8] : List Reg)) s u ∧
      u.gpr .a2 = off B (arr w r) ∧ u.gpr .a6 = off B (arr w t) ∧ u.gpr .a7 = off B (arr w m) ∧
      u.gpr .t0 = BitVec.ofNat 64 v ∧ u.gpr .a4 = 0 ∧ u.gpr .a1 = BitVec.ofNat 64 (sOf v Wd) ∧
      u.gpr .t1 = BitVec.ofNat 64 (63 * (sOf v Wd - 1)) ∧ u.gpr .a5 = off B (arr w a) ∧
      u.gpr .t2 = off B (arr w dig + 8 * 0) ∧ u.gpr .s7 = BitVec.ofNat 64 (sOf v Wd) ∧
      u.gpr .s8 = off B (arr w dig) ∧
      (∃ z, Norm u.mem B (arr w t) (wordsVal s.mem B (arr w m) v) v z) ∧
      wordsVal u.mem B (arr w m) v = wordsVal s.mem B (arr w m) v ∧
      wordsVal u.mem B (arr w a) Wd = wordsVal s.mem B (arr w a) Wd ∧
      wordsVal u.mem B (arr w q) (w + 1) = wordsVal s.mem B (arr w q) (w + 1) ∧
      wordsVal u.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) = wordsVal s.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) ∧
      wordsVal u.mem B (arr w r) (v + 1) = wordsVal s.mem B (arr w a) Wd / 2 ^ (63 * (sOf v Wd - 1)) := by
  have fita := h.arr_fit ha
  have fitr := h.arr_fit hr
  have fitm := h.arr_fit hm
  have fitt := h.arr_fit ht
  have fitq := h.arr_fit hq
  have fitg := h.arr_fit hdg
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  simp only [seqs]
  -- The divisor normalized.
  refine WP.seq (WP.mono (wdPrep_ok h hm ht hN hmt hv hvw ht0 hT)
    fun u₁ ⟨h1, f1, k1, a7, a6, t0, a4, nm⟩ => ?_)
  have t6 : u₁.gpr .t6 = BitVec.ofNat 64 Wd := (k1.gpr (by decide)).trans ht6
  have r1 : wordsVal u₁.mem B (arr w r) (v + 1) = 0 := by
    rw [words_of_frame1 f1 hrt (by omega) (by omega), hr0]
  -- `V := ⌊X / 2^o⌋`.
  refine WP.seq (WP.mono (divInit_ok h1 ha hr hN hra t0 t6 (by omega) hvW hWd hY r1)
    fun u₂ ⟨v2, a52, a22, a12, t12, o2, k2⟩ => ?_)
  have h2 := h1.of_keep k2
  have g2 : ∀ q ∈ [Reg.a6, .a7, .t0, .a4], u₂.gpr q = u₁.gpr q := fun q hq => k2.gpr (by revert q hq; decide)
  -- The values kept: apart from `[t]` (`prep`) and `[r]`'s first `v + 1` words (`divInit`).
  have kept : ∀ {j k : Nat}, j < N → j ≠ t → j ≠ r → k ≤ w + 2 →
      wordsVal u₂.mem B (arr w j) k = wordsVal s.mem B (arr w j) k := fun {j k} hj hjt hjr hk => by
    have fj := h.arr_fit hj
    rw [Outside.wordsVal o2 (by
      have := rgn (w := w) hjr (x := 0) (y := 8 * k) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega)
      simpa using this) (by omega)]
    exact words_of_frame1 f1 hjt hk (by omega)
  -- The digits' pointer, `S` and it.
  rw [digInit, List.append_assoc]
  refine ptr_ok h2 (by decide) (by decide) (show dig < 2048 by omega) ?_
  refine WP.mono (WP.keep [.s7, .s8] (Q := fun u => u.gpr .s7 = BitVec.ofNat 64 (sOf v Wd) ∧
      u.gpr .s8 = off B (arr w dig) ∧ u.mem = u₂.mem) (by
    brun [a12, BitVec.add_zero]) (by rfl) (by rfl)) fun u₃ ⟨⟨s73, s83, m3⟩, k3'⟩ => ?_
  have k3 : Keep [.t2, .s7, .s8] u₂ u₃ := ((Keep.write _ _ _).trans k3').mono (by decide)
  have g3 : ∀ q ∈ [Reg.a2, .a6, .a7, .t0, .a4, .a1, .t1, .a5], u₃.gpr q = u₂.gpr q := fun q hq =>
    k3.gpr (by revert q hq; decide)
  obtain ⟨z, nm⟩ := nm
  have tw : ∀ j, j < 4 → word u₂.mem B (arr w t + 8 * j) = word u₁.mem B (arr w t + 8 * j) := fun j hj =>
    Outside.word o2 (by
      have := rgn (w := w) hrt.symm (x := 8 * j) (y := 8) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega)
      simpa using this) (by omega)
  have nm2 := nm.congr (by simpa using tw 0 (by decide)) (tw 1 (by decide)) (tw 2 (by decide)) (tw 3 (by decide))
  refine ⟨h2.of_keep k3, ?_, ((k1.trans k2).trans k3).mono (by decide), (g3 .a2 (by decide)).trans a22,
    (g3 .a6 (by decide)).trans ((g2 .a6 (by decide)).trans a6), (g3 .a7 (by decide)).trans ((g2 .a7 (by decide)).trans a7),
    (g3 .t0 (by decide)).trans ((g2 .t0 (by decide)).trans t0), (g3 .a4 (by decide)).trans ((g2 .a4 (by decide)).trans a4),
    (g3 .a1 (by decide)).trans a12, (g3 .t1 (by decide)).trans t12, (g3 .a5 (by decide)).trans a52,
    by rw [k3'.gpr (by decide)]; simp [gpr_write], s73, s83, ⟨z, by rw [m3]; exact nm2⟩,
    by rw [m3]; exact kept hm hmt hrm.symm (by omega), by rw [m3]; exact kept ha hat hra.symm hWd,
    by rw [m3]; exact kept hq hqt hqr (by omega), ?_, by rw [m3, v2, words_of_frame1 f1 hat hWd (by omega)]⟩
  · rw [m3]
    exact (f1.mono (js' := [r, t]) (ds' := [])).trans (Frame.of_arr (o := r) (d := 0) (by simpa using o2) (by omega)
      (by simp))
  · rw [m3, Outside.wordsVal o2 (by omega) (by omega)]
    refine f1.words (fun k' hk' => ?_) (by simp) (by omega)
    simp at hk'; subst hk'
    have := rgn (w := w) hrt (x := 8 * (v + 1)) (y := 8 * (w - 1 - v)) (x' := 0) (y' := S w) (by omega) (by omega)
    simpa using this

/-- `divCore a r m t (some (dig, q))`, `v` in `t0` and `Wd` in `t6`: as
`divCore_ok`, `[r]`'s first `v` words := `X mod M`, and `[q] := ⌊X / M⌋`, for
`X` `[a]`'s first `Wd` words and `M` `[m]`'s first `v`, whose top word is not
zero, `[r]`'s first `v + 1` words and `[q]` zero; `[dig]` and the temporary
`[t]` written. -/
theorem divQ_ok {s : State} {B : Addr} {Z w N a r m t dig q v Wd : Nat} (h : Ws s B Z w N) (hN : N ≤ 2048)
    (ha : a < N) (hr : r < N) (hm : m < N) (ht : t < N) (hdg : dig < N) (hq : q < N)
    (hra : r ≠ a) (hrm : r ≠ m) (hrt : r ≠ t) (hmt : m ≠ t) (hat : a ≠ t) (hgr : dig ≠ r) (hgm : dig ≠ m)
    (hga : dig ≠ a) (hgt : dig ≠ t) (hqr : q ≠ r) (hqm : q ≠ m) (hqt : q ≠ t) (hqg : q ≠ dig)
    (hv : 4 ≤ v) (hvw : v ≤ w) (hvW : v < Wd) (hWd : Wd ≤ w + 2) (hY : Wd - v ≤ 187) (hYw : Wd - v + 2 ≤ w)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 v) (ht6 : s.gpr .t6 = BitVec.ofNat 64 Wd)
    (hr0 : wordsVal s.mem B (arr w r) (v + 1) = 0) (hq0 : wordsVal s.mem B (arr w q) (w + 1) = 0)
    (hT : 0 < (word s.mem B (arr w m + 8 * (v - 1))).toNat) :
    WP isa (divCore a r m t (some (dig, q))) s fun u => Ws u B Z w N ∧
      Frame B w [r, t, dig, q] [] s.mem u.mem ∧ Keep divQRegs s u ∧
      wordsVal u.mem B (arr w r) v = wordsVal s.mem B (arr w a) Wd % wordsVal s.mem B (arr w m) v ∧
      word u.mem B (arr w r + 8 * v) = 0 ∧
      wordsVal u.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) =
        wordsVal s.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) ∧
      wordsVal u.mem B (arr w q) (w + 1) = wordsVal s.mem B (arr w a) Wd / wordsVal s.mem B (arr w m) v := by
  have fitr := h.arr_fit hr
  have fitm := h.arr_fit hm
  have fitq := h.arr_fit hq
  have fitg := h.arr_fit hdg
  have nw := h.nowrap
  have hSz : VG.Proof.Rsa.RISCV64.Keys.S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have hc := div_counts hY
  have hgh := hdr_le_arr w dig
  have hhdr : hdr = 256 := rfl
  generalize hX : wordsVal s.mem B (arr w a) Wd = X
  generalize hM : wordsVal s.mem B (arr w m) v = M
  have hM1 : 2 ^ (64 * (v - 1)) ≤ M := by
    have e := wordsVal_succ_top s.mem B (arr w m) (v - 1)
    rw [show v - 1 + 1 = v by omega, hM] at e
    have := Nat.le_mul_of_pos_right (2 ^ (64 * (v - 1))) hT
    omega
  have hXl : X < 2 ^ (64 * Wd) := hX ▸ wordsVal_lt _ _ _ _
  have hM0 : 0 < M := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hM1
  generalize hSd : sOf v Wd = S at hc
  have hX0 : X / 2 ^ (63 * S) < 2 * M := by
    have : X / 2 ^ (63 * S) < 2 ^ (64 * (v - 1)) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      exact Nat.lt_of_lt_of_le hXl (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  have hXM : X / M < 2 ^ (63 * S) := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    calc X < 2 ^ (64 * Wd) := hXl
      _ ≤ 2 ^ (63 * S + 64 * (v - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ (63 * S) * 2 ^ (64 * (v - 1)) := Nat.pow_add _ _ _
      _ ≤ 2 ^ (63 * S) * M := Nat.mul_le_mul_left _ hM1
  -- The ranges apart.
  have dmr : ∀ {k : Nat}, k ≤ w + 2 → arr w m + 8 * k ≤ arr w r ∨ arr w r + 8 * (v + 1) ≤ arr w m := fun {k} hk => by
    have := rgn (w := w) hrm.symm (x := 0) (y := 8 * k) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega)
    simpa using this
  have dmg : arr w m + 8 * v ≤ arr w dig ∨ arr w dig + 8 * S ≤ arr w m := by
    have := rgn (w := w) hgm.symm (x := 0) (y := 8 * v) (x' := 0) (y' := 8 * S) (by omega) (by omega)
    simpa using this
  have dqr : arr w q + 8 * (w + 1) ≤ arr w r ∨ arr w r + 8 * (v + 1) ≤ arr w q := by
    have := rgn (w := w) hqr (x := 0) (y := 8 * (w + 1)) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega)
    simpa using this
  have dqg : arr w q + 8 * (w + 1) ≤ arr w dig ∨ arr w dig + 8 * S ≤ arr w q := by
    have := rgn (w := w) hqg (x := 0) (y := 8 * (w + 1)) (x' := 0) (y' := 8 * S) (by omega) (by omega)
    simpa using this
  have dgr : ∀ {i : Nat}, i < S → arr w dig + 8 * i + 8 ≤ arr w r ∨ arr w r + 8 * (v + 1) ≤ arr w dig + 8 * i :=
    fun {i} hi => rgn (w := w) hgr (x := 8 * i) (y := 8) (x' := 0) (y' := 8 * (v + 1)) (by omega) (by omega) |>.imp
      (fun e => by omega) (fun e => by omega)
  have drest : arr w r + 8 * (v + 1) + 8 * (w - 1 - v) ≤ arr w dig ∨ arr w dig + 8 * S ≤ arr w r + 8 * (v + 1) := by
    have := rgn (w := w) hgr.symm (x := 8 * (v + 1)) (y := 8 * (w - 1 - v)) (x' := 0) (y' := 8 * S) (by omega) (by omega)
    simpa using this
  simp only [divCore, seqs]
  -- The head.
  refine seq3_then (divQHead_ok h hN ha hr hm ht hdg hq hra hrm hrt hmt hat hqr hqt hv hvw hvW hWd hY ht0 ht6 hr0 hT)
    fun u₃ ⟨h3, f3, k3, a23, a63, a73, t03, a43, a13, t13, a53, t23, s73, s83, ⟨z, nm3⟩, m3, x3, q3, rr3, v3⟩ => ?_
  rw [hM] at nm3 m3
  rw [hX] at x3 v3
  rw [hq0] at q3
  rw [hSd] at a13 t13 s73 v3
  -- The steps.
  refine WP.seq (WP.mono (stepsDig_ok (X := X) (S := S) (M := M) h3 ha hr hm ht hdg hra hrm hrt hgr hgm hga hgt hv
    hvw hWd (by omega) (by omega) (by omega) a23 a63 a73 t03 a43 a13 t13 a53 t23 nm3 m3 v3 hX0 x3)
    fun u₄ ⟨⟨r', qa, hr', hXq, hV4, o4, qd4⟩, k4⟩ => ?_)
  have h4 := h3.of_keep k4
  have g4 : ∀ q ∈ [Reg.a2, .a7, .t0, .a4, .s7, .s8], u₄.gpr q = u₃.gpr q := fun q hq => k4.gpr (by revert q hq; decide)
  have m4 : wordsVal u₄.mem B (arr w m) v = M := by rw [Out2.wordsVal o4 (dmr (by omega)) dmg (by omega), m3]
  -- The remainder `r' mod M`, and `g = [r' ≥ M]`.
  refine WP.seq (WP.mono (finish_ok (dV := arr w r) (dN := arr w m) (w := v) h4.scr
    ((g4 .a2 (by decide)).trans a23) ((g4 .a7 (by decide)).trans a73) ((g4 .t0 (by decide)).trans t03)
    ((g4 .a4 (by decide)).trans a43) (arr_al w r) (arr_al w m) (by omega) (by omega) (by omega) (by omega)
    (dmr (by omega)) (by rw [hV4, m4]; exact hr')) fun u₅ ⟨⟨ux, u0, o5, s15⟩, k5⟩ => ?_)
  rw [m4, hV4] at s15
  rw [m4, hV4] at ux
  have h5 := h4.of_keep k5
  have g5 : ∀ q ∈ [Reg.s7, .s8], u₅.gpr q = u₄.gpr q := fun q hq => k5.gpr (by revert q hq; decide)
  have q5 : wordsVal u₅.mem B (arr w q) (w + 1) = 0 := by
    rw [Outside.wordsVal o5 dqr (by omega), Out2.wordsVal o4 dqr dqg (by omega), q3]
  have d5 : digVal u₅.mem B (arr w dig) S = qa := by
    rw [digVal_congr S fun i hi => o5.word (dgr hi) (by omega), qd4]
  generalize hg : (if M ≤ r' then 1 else 0) = g at s15
  have hg1 : g ≤ 1 := by rw [← hg]; split <;> omega
  have hq' : X / M = qa + g := by
    rw [hXq, Nat.mul_comm, Nat.mul_add_div (by omega), ← hg]
    split
    · rw [show r' / M = 1 from Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hM0).mpr (by omega)))
        ((Nat.le_div_iff_mul_le hM0).mpr (by omega))]
    · rw [Nat.div_eq_of_lt (by omega)]
  -- The quotient.
  refine WP.mono (combine_ok h5 hq hN (by omega) (by omega) (by omega) (arr_al w dig) (by omega) (by omega) dqg
    ((g5 .s7 (by decide)).trans ((g4 .s7 (by decide)).trans s73))
    ((g5 .s8 (by decide)).trans ((g4 .s8 (by decide)).trans s83)) s15 hg1 q5 (by rw [d5, ← hq']; exact hXM))
    fun u ⟨hu, fu, qv, ku⟩ => ?_
  have dr6 : wordsVal u.mem B (arr w r) v = wordsVal u₅.mem B (arr w r) v := by
    refine fu.words (fun k hk => ?_) (by simp) (by omega)
    simp at hk; subst hk
    have := rgn (w := w) hqr.symm (x := 0) (y := 8 * v) (x' := 0) (y' := VG.Proof.Rsa.RISCV64.Keys.S w) (by omega) (by omega); simpa using this
  have dr7 : word u.mem B (arr w r + 8 * v) = word u₅.mem B (arr w r + 8 * v) := by
    have e := fu.words (d := arr w r + 8 * v) (k := 1) (fun k hk => by
      simp at hk; subst hk
      have := rgn (w := w) hqr.symm (x := 8 * v) (y := 8) (x' := 0) (y' := VG.Proof.Rsa.RISCV64.Keys.S w)
        (by omega) (by omega)
      simpa using this) (by simp) (by omega)
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e
    exact BitVec.eq_of_toNat_eq e
  have dr8 : wordsVal u.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) =
      wordsVal u₅.mem B (arr w r + 8 * (v + 1)) (w - 1 - v) := by
    refine fu.words (fun k hk => ?_) (by simp) (by omega)
    simp at hk; subst hk
    have := rgn (w := w) hqr.symm (x := 8 * (v + 1)) (y := 8 * (w - 1 - v)) (x' := 0)
      (y' := VG.Proof.Rsa.RISCV64.Keys.S w) (by omega) (by omega)
    simpa using this
  refine ⟨hu, ?_, ?_, by rw [dr6, ux, hXq, Nat.mul_comm, Nat.mul_add_mod], by rw [dr7, u0], ?_, by rw [qv, d5, hq']⟩
  · exact ((f3.mono (js' := [r, t, dig, q]) (ds' := [])).trans
      (Frame.of_out2 (o1 := r) (o2 := dig) (d1 := 0) (d2 := 0) (by simpa using o4) (by omega) (by omega) (by simp)
        (by simp))).trans ((Frame.of_arr (o := r) (d := 0) (by simpa using (show Outside B (arr w r) (8 * (v + 1)) u₄.mem u₅.mem from o5))
        (by omega) (by simp)).trans
          (fu.mono (js' := [r, t, dig, q]) (ds' := [])))
  · exact ((((k3.trans k4).trans k5).trans ku).mono (by decide))
  · rw [dr8, Outside.wordsVal o5 (by omega) (by omega), Out2.wordsVal o4 (by omega) drest (by omega), rr3]



end VG.Proof.Rsa.RISCV64.Keys
