module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: `R² mod n` by word steps

`r2Words_ok`: `vg_rsa_public_precompute`'s `R² mod n` (`Precompute.r2Words`,
after `lz`) for any odd `n` of `w ≥ 3` words whose top word is not zero, in
array 1, from its pieces:

* `normTail_ok`: `P = 2^z` and `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` in the
  temporary (array 3);
* `recip_ok`: `v = ⌊(2^128 - 1) / d'⌋ - 2^64` there, by restoring division
  (`WordStep.divBit_inv`, `WordStep.recip_eq`);
* `quot_ok`: the estimate `q̂ = min(⌊u / d'⌋, 2^64 - 1)` of `⌊x 2^64 / n⌋`
  from the top two words `u` of `x P` (`WordStep.qhat_norm`), by Möller and
  Granlund's division (`WordStep.mg_quot`);
* `mulSub_ok`, `addBack_ok`: `t = x 2^64 - q̂ n` in place of `x`, then `n`
  added twice while it is negative (`WordStep.wordStepQ_val`);
* `wordStep_ok`: `x := x 2^64 mod n`, and `wordSteps_ok`, `w + 1` of them.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Precompute
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.WordStep (shl_add_lt top_shift)

/-! ## Normalization -/

/-- `8 w + d - c`: a word near the top of `w` words at `d`. -/
theorem ea_top (B : Addr) {d w c : Nat} (hc : c ≤ 8 * w) (hn : B.toNat + d + 8 * w < 2 ^ 64) :
    BitVec.ofNat 64 w <<< 3 + off B d - BitVec.ofNat 64 c = off B (d + 8 * w - c) := by
  have hB := B.isLt
  have h1 : (BitVec.ofNat 64 w <<< 3).toNat = 8 * w := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hn, hB]), Nat.mod_eq_of_lt (by omega_using [hn, hB])]; omega_using []
  have h2 : (off B d).toNat = B.toNat + d := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d) (by omega_using [hn, hB]), Nat.mod_eq_of_lt (by omega_using [hn])]
  have h3 : (off B (d + 8 * w - c)).toNat = B.toNat + (d + 8 * w - c) := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d + 8 * w - c) (by omega_using [hn, hB]), Nat.mod_eq_of_lt (by omega_using [hn])]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, h1, h2, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega_using [hc, hn])]
  omega_using [hc, hn]

/-- `8 w + d`: the word after `w` words at `d`. -/
theorem ea_end (B : Addr) {d w : Nat} (hn : B.toNat + d + 8 * w < 2 ^ 64) :
    BitVec.ofNat 64 w <<< 3 + off B d = off B (d + 8 * w) := by
  have h := ea_top B (c := 0) (Nat.zero_le _) hn
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.sub_zero, Nat.sub_zero] at h

/-- The value of `n`'s top two words `T` and `L` and the rest. -/
theorem top_two (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 2 ≤ w) :
    wordsVal m B d w = (Mont.word m B (d + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 2) + 64) +
      (Mont.word m B (d + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wordsVal m B d (w - 2) := by
  have e1 := wordsVal_succ_top m B d (w - 1)
  have e2 := wordsVal_succ_top m B d (w - 2)
  rw [show w - 1 + 1 = w by omega] at e1
  rw [show w - 2 + 1 = w - 1 by omega] at e2
  rw [e1, e2, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega, Nat.mul_comm (2 ^ (64 * (w - 2) + 64)),
    Nat.mul_comm (2 ^ (64 * (w - 2)))]
  omega

/-- The registers `normTail` writes. -/
def normRegs : List Reg := [.s0, .s2, .s3, .t3]

/-- `normTail`, after `lz` (`a1 = z`, `2^63 ≤ T 2^z < 2^64` for `n`'s top
word `T`): `P = 2^z` and `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` in the
temporary's words 0 and 1, `d'` also in `s2`. -/
theorem normTail_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .a6 = off B (slot w 3)) (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hb1 : 2 ^ 63 ≤ topW s.mem B w * 2 ^ z) (hb2 : topW s.mem B w * 2 ^ z < 2 ^ 64) :
    WP isa (.block normTail) s fun t =>
      ((Mont.word t.mem B (slot w 3)).toNat = 2 ^ z ∧ z ≤ 63 ∧
        (Mont.word t.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
        2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)) ∧
        t.gpr .s2 = Mont.word t.mem B (slot w 3 + 8) ∧ Outside B (slot w 3) 16 s.mem t.mem) ∧ Keep normRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have al := slot_al8 w
  have a0 := al 0; have a3 := al 3
  unfold topW at hb1 hb2
  generalize hTw : Mont.word s.mem B (slot w 0 + 8 * (w - 1)) = T at hb1 hb2
  generalize hLw : Mont.word s.mem B (slot w 0 + 8 * (w - 2)) = L
  have hT0 : 0 < T.toNat := by
    rcases Nat.eq_zero_or_pos T.toNat with h | h
    · rw [h, Nat.zero_mul] at hb1; exact absurd hb1 (by decide)
    · exact h
  have hz : z ≤ 63 := by
    refine Nat.le_of_lt_succ (Nat.lt_of_not_le fun h => ?_)
    have := Nat.mul_le_mul hT0 (Nat.pow_le_pow_right (show 0 < 2 by decide) h)
    omega
  have ea := ea_top B (d := slot w 0) (w := w) (c := 16) (by omega_arith) (by omega_arith)
  rw [show slot w 0 + 8 * w - 16 = slot w 0 + 8 * (w - 2) by omega] at ea
  have hz64 : (BitVec.ofNat 64 z).toNat % 64 = z := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hP : ((1 : BitVec 64) <<< z).toNat = 2 ^ z := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hTP : (T <<< z).toNat = T.toNat * 2 ^ z := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt hb2
  have hLP : L.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
    exact Nat.mul_lt_mul_of_pos_right L.isLt (Nat.two_pow_pos z)
  have rT : s.mem.readW (off B (slot w 0 + 8 * (w - 2) + 8)) 64 = T := by
    rw [← hTw, show slot w 0 + 8 * (w - 2) + 8 = slot w 0 + 8 * (w - 1) by omega_arith]
  have rL : s.mem.readW (off B (slot w 0 + 8 * (w - 2))) 64 = L := hLw
  generalize hD : T <<< z + BitVec.ofNat 64 (L.toNat * ((1 : BitVec 64) <<< z).toNat / 2 ^ 64) = D
  refine WP.mono (WP.keep normRegs (Q := fun t => t.gpr .s2 = D ∧
      t.mem = (s.mem.writeW (off B (slot w 3)) ((1 : BitVec 64) <<< z)).writeW (off B (slot w 3 + 8)) D) (by
    unfold normTail
    brun [r2_exec_li_one, exec_sllReg, h1, h6, h7, ht0, hz64, ea, rT, rL, hD, BitVec.add_zero,
      hs.ld (show slot w 0 + 8 * (w - 2) + 8 + 8 ≤ Z by omega),
      hs.al8 (show slot w 0 + 8 * (w - 2) + 8 + 8 ≤ Z by omega) (by omega),
      hs.ld (show slot w 0 + 8 * (w - 2) + 8 ≤ Z by omega),
      hs.al8 (show slot w 0 + 8 * (w - 2) + 8 ≤ Z by omega) (by omega),
      hs.st (show slot w 3 + 8 ≤ Z by omega), hs.al8 (show slot w 3 + 8 ≤ Z by omega) a3,
      hs.st (show slot w 3 + 8 + 8 ≤ Z by omega), hs.al8 (show slot w 3 + 8 + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl))
    fun t ⟨⟨t2, tm⟩, k⟩ => ⟨?_, k⟩
  have wD : Mont.word t.mem B (slot w 3 + 8) = D := by rw [tm, Mont.word_writeW_self]
  have hN := top_two s.mem B (slot w 0) hw
  rw [hTw, hLw] at hN
  have hNv : wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)) =
      T.toNat * 2 ^ z + L.toNat * 2 ^ z / 2 ^ 64 := by
    rw [hN, show 64 * (w - 1) = 64 * (w - 2) + 64 by omega_arith]
    exact top_shift (by omega_arith) (wordsVal_lt _ _ _ _)
  have hpz : 2 ^ z ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hz
  have hDv : D.toNat = T.toNat * 2 ^ z + L.toNat * 2 ^ z / 2 ^ 64 := by
    rw [← hD, BitVec.toNat_add, hTP, BitVec.toNat_ofNat, hP,
      Nat.mod_eq_of_lt (show L.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64 by omega_using [hLP, hpz]),
      Nat.mod_eq_of_lt (shl_add_lt (by omega_arith) hb2 hLP)]
  refine ⟨?_, hz, by rw [wD, hDv, hNv], by rw [hNv]; omega_using [hb1], by rw [t2, wD], ?_⟩
  · rw [tm, ← hP]
    exact congrArg BitVec.toNat ((Outside.word (writeW_outside _ B (d := slot w 3 + 8) _ (by omega))
      (Or.inl (Nat.le_refl _)) (by omega)).trans (Mont.word_writeW_self _ _ _ _))
  · rw [tm]
    exact ((writeW_outside s.mem B (d := slot w 3) _ (by omega)).mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside _ B (d := slot w 3 + 8) _ (by omega)).mono (by omega) (by omega))


/-! ## The reciprocal -/

/-- `2 x + b` modulo `2^64`, as a shift and an or. -/
theorem shl1_or_bit (x : BitVec 64) (b : Bool) :
    (x <<< 1 ||| BitVec.ofNat 64 b.toNat).toNat = (2 * x.toNat + b.toNat) % 2 ^ 64 := by
  have h : x <<< 1 &&& BitVec.ofNat 64 b.toNat = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    cases b
    · simp
    · rw [BitVec.toNat_and, BitVec.toNat_shiftLeft, show (BitVec.ofNat 64 (true : Bool).toNat).toNat = 1 from rfl,
        Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.pow_one, show (0#64).toNat = 0 from rfl]
      omega
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ h, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, Nat.pow_one, BitVec.toNat_ofNat]
  have := Bool.toNat_le b
  omega

/-- `2 r + 1` modulo `2^64`, as `divBit` computes it. -/
def dS (r : BitVec 64) : BitVec 64 := r <<< 1 ||| 1#64

/-- The bit of the quotient: `2 r + 1 ≥ d`, or the carry out of `2 r + 1`. -/
def dB (r d : BitVec 64) : BitVec 64 := (if dS r < d then (1 : BitVec 64) else 0) ^^^ 1#64 ||| r >>> 63

/-- The remainder. -/
def dR (r d : BitVec 64) : BitVec 64 := dS r - ((0 - dB r d) &&& d)

theorem shr63_toNat (r : BitVec 64) : (r >>> 63) = BitVec.ofNat 64 (decide (2 ^ 63 ≤ r.toNat)).toNat := by
  have := r.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 63 ≤ r.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega

theorem lt_xor_one (a b : BitVec 64) :
    (if a < b then (1 : BitVec 64) else 0) ^^^ 1#64 = BitVec.ofNat 64 (decide (b.toNat ≤ a.toNat)).toNat := by
  by_cases h : a < b
  · rw [ite_eq_left h, decide_eq_false (by rw [BitVec.lt_def] at h; omega)]; rfl
  · rw [ite_eq_right h, decide_eq_true (by rw [BitVec.lt_def] at h; omega)]; rfl

theorem or_bits (a b : Bool) :
    BitVec.ofNat 64 a.toNat ||| BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (a || b).toNat := by
  cases a <;> cases b <;> rfl

theorem dB_val {r d : Nat} (hr : r < d) (hd : d < 2 ^ 64) :
    dB (BitVec.ofNat 64 r) (BitVec.ofNat 64 d) = BitVec.ofNat 64 (decide (d ≤ 2 * r + 1)).toNat := by
  have hR : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hS : (dS (BitVec.ofNat 64 r)).toNat = (2 * r + 1) % 2 ^ 64 := by
    rw [dS, show (1#64 : BitVec 64) = BitVec.ofNat 64 (true : Bool).toNat from rfl, shl1_or_bit, hR]; rfl
  rw [dB, lt_xor_one, shr63_toNat, hS, hR, hD, or_bits]
  congr 2
  by_cases h : 2 ^ 63 ≤ r
  · simp only [h, decide_true, Bool.or_true]
    symm; apply decide_eq_true; omega
  · simp only [h, decide_false, Bool.or_false]
    apply decide_eq_decide.mpr
    rw [Nat.mod_eq_of_lt (by omega)]

theorem dR_val {r d : Nat} (hr : r < d) (hd : d < 2 ^ 64) :
    dR (BitVec.ofNat 64 r) (BitVec.ofNat 64 d) =
      BitVec.ofNat 64 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by
  have hR : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hS : (dS (BitVec.ofNat 64 r)).toNat = (2 * r + 1) % 2 ^ 64 := by
    rw [dS, show (1#64 : BitVec 64) = BitVec.ofNat 64 (true : Bool).toNat from rfl, shl1_or_bit, hR]; rfl
  rw [dR, dB_val hr hd]
  apply BitVec.eq_of_toNat_eq
  by_cases h : d ≤ 2 * r + 1
  · rw [decide_eq_true h, ite_eq_left h, show (0 : BitVec 64) - BitVec.ofNat 64 (true : Bool).toNat =
      BitVec.allOnes 64 from rfl, BitVec.allOnes_and, BitVec.toNat_sub, hS, hD, BitVec.toNat_ofNat]
    omega
  · rw [decide_eq_false h, ite_eq_right h, show (0 : BitVec 64) - BitVec.ofNat 64 (false : Bool).toNat = 0#64 from rfl,
      BitVec.zero_and, BitVec.sub_zero, hS, BitVec.toNat_ofNat]

/-- After `k` bits of `recip`'s loop from `s₀`: `s3 = r`, `s4 = q` for
`r₀ 2^k + 2^k - 1 = q d + r`, `r < d`. -/
structure RecInv (s₀ : State) (d r0 : Nat) (k : Nat) (t : State) : Prop where
  keep : Keep [.s0, .s1, .s3, .s4, .t5] s₀ t
  mem : t.mem = s₀.mem
  val : ∃ q r, t.gpr .s3 = BitVec.ofNat 64 r ∧ t.gpr .s4 = BitVec.ofNat 64 q ∧
    r0 * 2 ^ k + (2 ^ k - 1) = q * d + r ∧ r < d

theorem divBit_ok (t : State) (h4 : t.gpr .a4 = 0) :
    WP isa (.block (divBit ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .s3 = dR (t.gpr .s3) (t.gpr .s2) ∧
        t'.gpr .s4 = t.gpr .s4 <<< 1 ||| dB (t.gpr .s3) (t.gpr .s2) ∧ t'.mem = t.mem ∧
        t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.s0, .s1, .s3, .s4, .t5] t t' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold divBit
  brun [h4]
  exact ⟨rfl, rfl⟩

theorem divStep_ok {s₀ : State} {d r0 : Nat} (hd : d < 2 ^ 64) (hr0 : r0 < d) (h4 : s₀.gpr .a4 = 0)
    (h2 : s₀.gpr .s2 = BitVec.ofNat 64 d) {k : Nat} (hk : k < 64) {t : State} (hI : RecInv s₀ d r0 k t) :
    WP isa (.block (divBit ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      RecInv s₀ d r0 (k + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  obtain ⟨q, r, h3, h4q, hP, hr⟩ := hI.val
  have t4 := (hI.keep.gpr (r := .a4) (by decide)).trans h4
  have t2 := (hI.keep.gpr (r := .s2) (by decide)).trans h2
  refine WP.mono (divBit_ok t t4) fun t' ⟨⟨u3, u4, um, u5⟩, k'⟩ => ⟨?_, u5⟩
  -- `q < 2^k`, as `q d ≤ r₀ 2^k + 2^k - 1 < d 2^k`.
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : q < 2 ^ k := by
    have h1 : q * d < 2 ^ k * d := by
      have := Nat.mul_le_mul_left (2 ^ k) (show r0 + 1 ≤ d by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      rw [Nat.mul_comm r0] at hP
      omega
    exact Nat.lt_of_mul_lt_mul_right h1
  have hk' : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hP', hr'⟩ := WordStep.divBit_inv (P := r0 * 2 ^ k + (2 ^ k - 1)) (q := q) (r := r)
    (d := d) hP hr (b := 1) (by decide)
  refine ⟨Keep.trans' hI.keep k', by rw [um, hI.mem], ?_⟩
  refine ⟨2 * q + (if d ≤ 2 * r + 1 then 1 else 0), if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1,
    by rw [u3, h3, t2, dR_val hr hd], ?_, ?_, hr'⟩
  · rw [u4, h3, t2, h4q, dB_val hr hd]
    apply BitVec.eq_of_toNat_eq
    rw [shl1_or_bit, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)]
    by_cases h : d ≤ 2 * r + 1 <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false,
      ↓reduceIte] <;> omega
  · rw [Nat.pow_succ]
    have e : r0 * (2 ^ k * 2) + (2 ^ k * 2 - 1) = 2 * (r0 * 2 ^ k + (2 ^ k - 1)) + 1 := by
      have := Nat.two_pow_pos k; rw [← Nat.mul_assoc, Nat.mul_add, Nat.mul_comm 2 (r0 * 2 ^ k)]; omega
    rw [e, hP']

theorem exec_li_m1 {s : State} {d : Reg} : exec (.li d (-1)) s = some (s.write d (BitVec.allOnes 64)) := by
  rw [exec_li (by decide)]; rfl

theorem exec_li_64 {s : State} {d : Reg} : exec (.li d 64) s = some (s.write d (BitVec.ofNat 64 64)) := by
  rw [exec_li (by decide)]; rfl

theorem exec_li_zero {s : State} {d : Reg} : exec (.li d 0) s = some (s.write d 0) := by
  rw [exec_li (by decide)]; rfl

/-- The registers `recip` writes. -/
def recipRegs : List Reg := [.a4, .s0, .s1, .s3, .s4, .t5]

/-- `recip`, for `d' ≥ 2^63` in `s2`: `v = ⌊(2^128 - 1) / d'⌋ - 2^64` into the
temporary's word 2 (`a6` at array 3), and `a4 := 0`. -/
theorem recip_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h6 : s.gpr .a6 = off B (slot w 3))
    (hZ : slot w 3 + 24 ≤ Z) (hd : 2 ^ 63 ≤ (s.gpr .s2).toNat) :
    WP isa recip s fun t =>
      ((Mont.word t.mem B (slot w 3 + 16)).toNat = (2 ^ 128 - 1) / (s.gpr .s2).toNat - 2 ^ 64 ∧
        t.gpr .a4 = 0 ∧ Outside B (slot w 3 + 16) 8 s.mem t.mem) ∧ Keep recipRegs s t := by
  have hn := hs.nowrap
  generalize hD : s.gpr .s2 = D at hd
  have hD' := D.isLt
  have hsub : BitVec.allOnes 64 - D = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_allOnes, BitVec.toNat_ofNat]
    omega_using [hD']
  unfold recip
  refine WP.seq (WP.mono (WP.keep [.a4, .s3, .s4, .t5] (Q := fun t =>
    t.gpr .a4 = 0 ∧ t.gpr .s3 = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) ∧
    t.gpr .s4 = BitVec.ofNat 64 0 ∧ t.gpr .t5 = BitVec.ofNat 64 64 ∧ t.mem = s.mem)
    (by unfold recipHead; brun [exec_li_zero, exec_li_m1, exec_li_64, hD, hsub]; rfl) (by rfl) (by rfl))
    fun s₁ ⟨⟨a4, a3, a4q, a5, hm₁⟩, k₁⟩ => ?_)
  have hr0 : 2 ^ 64 - 1 - D.toNat < D.toNat := by omega
  have h2₁ : s₁.gpr .s2 = BitVec.ofNat 64 D.toNat := by rw [k₁.gpr (by decide), hD, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h0 : RecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat) 0 s₁ :=
    ⟨Keep.refl _ _, rfl, 0, 2 ^ 64 - 1 - D.toNat, a3, a4q, by simp, hr0⟩
  refine WP.seq (WP.mono (wp_countdown (N := 64) (by decide) (by decide) (RecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat))
    (fun k hk t hI _ => divStep_ok hD' hr0 a4 h2₁ hk hI) h0 a5) fun t hI => ?_)
  obtain ⟨q, r, _, h4t, hP, hr⟩ := hI.val
  have t6 : t.gpr .a6 = off B (slot w 3) := (hI.keep.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h6)
  have hs' := hs.congr (k₁.trans hI.keep).2.2
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (slot w 3 + 16)) (t.gpr .s4))
    (by brun [t6, hs'.st (show slot w 3 + 16 + 8 ≤ Z by omega),
      hs'.al8 (show slot w 3 + 16 + 8 ≤ Z by omega) (by have := slot_al8 w 3; omega)]) (by rfl) (by rfl))
    fun t' ⟨hm', k'⟩ => ?_
  have hq : q = (2 ^ 128 - 1) / D.toNat - 2 ^ 64 := by
    rw [← WordStep.recip_eq hD' (by omega), hP, Nat.mul_comm q, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr,
      Nat.add_zero]
  have hqB : q < 2 ^ 64 := by
    rw [hq]
    have : (2 ^ 128 - 1) / D.toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := Nat.mul_le_mul_left (2 ^ 65) hd
      omega
    omega
  refine ⟨⟨by rw [hm', Mont.word_writeW_self, h4t, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, hq],
    by rw [k'.gpr (by decide), hI.keep.gpr (by decide), a4], ?_⟩, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  rw [hm', hI.mem, hm₁]
  exact writeW_outside _ _ _ (by omega)


/-! ## The estimate of the quotient -/

/-- What `quotMG` computes from `v` (`s3`), `u` (`t4`), `a` (`t5`) and `d`
(`s2`), instruction by instruction. -/
def mgq (v u a d : BitVec 64) : BitVec 64 :=
  let q0 := v * u + a
  let Q := BitVec.ofNat 64 (v.toNat * u.toNat / 2 ^ 64) + u + (if q0 < a then (1 : BitVec 64) else 0) + 1#64
  let r := a - Q * d
  let c : BitVec 64 := if q0 < r then 1 else 0
  let r1 := r + ((0 - c) &&& d)
  Q - c + ((if r1 < d then (1 : BitVec 64) else 0) ^^^ 1#64)

/-- The carry of `x + y`, by `sltu`. -/
theorem carry_val (x y : BitVec 64) :
    (if x + y < y then (1 : BitVec 64) else 0).toNat = (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat := by
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x + y < y
  · rw [ite_eq_left h]
    rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [decide_eq_true (by omega)]; rfl
  · rw [ite_eq_right h]
    rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [decide_eq_false (by omega)]; rfl

theorem mgq_val {v u a d : Nat} (hd : d < 2 ^ 64) (hn : 2 ^ 63 ≤ d) (hu : u < d) (ha : a < 2 ^ 64)
    (hv : v = (2 ^ 128 - 1) / d - 2 ^ 64) :
    (mgq (BitVec.ofNat 64 v) (BitVec.ofNat 64 u) (BitVec.ofNat 64 a) (BitVec.ofNat 64 d)).toNat =
      (u * 2 ^ 64 + a) / d := by
  have hd0 : 0 < d := by omega
  have hVd : (2 ^ 128 - 1) / d * d ≤ 2 ^ 128 - 1 := Nat.div_mul_le_self _ _
  have hVB : 2 ^ 64 ≤ (2 ^ 128 - 1) / d := by
    rw [Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_left (2 ^ 64) (show d ≤ 2 ^ 64 - 1 by omega)
    omega
  generalize hV : (2 ^ 128 - 1) / d = V at hVd hVB hv
  have hVu : V * u + V ≤ V * d := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hu
  have hPe : v * u + a + 2 ^ 64 * u = V * u + a := by
    rw [hv, Nat.sub_mul]; have := Nat.mul_le_mul_right u hVB; omega
  have hVd' : V * d = d * V := Nat.mul_comm _ _
  have hPB : V * u + a < 2 ^ 128 := by omega
  have hvl : v < 2 ^ 64 := by
    rw [hv]
    have : V < 2 ^ 65 := by
      rw [← hV, Nat.div_lt_iff_lt_mul hd0]
      have := Nat.mul_le_mul_left (2 ^ 65) hn
      omega
    omega
  have hul : u < 2 ^ 64 := by omega
  have hU : (BitVec.ofNat 64 u).toNat = u := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
  have hA : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hVv : (BitVec.ofNat 64 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvl]
  unfold mgq
  simp only []
  -- `(q₁, q₀) = V u + a`.
  have hl : v * u ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hvu : v * u / 2 ^ 64 ≤ 2 ^ 64 - 2 := Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64) hl) (by decide)
  have hdm := Nat.div_add_mod (v * u) (2 ^ 64)
  have hmm := Nat.mod_lt (v * u) (show 0 < 2 ^ 64 by decide)
  generalize hq0 : BitVec.ofNat 64 v * BitVec.ofNat 64 u + BitVec.ofNat 64 a = q0
  have hq0v : q0.toNat = (V * u + a) % 2 ^ 64 := by
    rw [← hq0, BitVec.toNat_add, BitVec.toNat_mul, hVv, hU, hA, ← hPe]
    omega
  have hc := carry_val (BitVec.ofNat 64 v * BitVec.ofNat 64 u) (BitVec.ofNat 64 a)
  rw [hq0] at hc
  rw [BitVec.toNat_mul, hVv, hU, hA] at hc
  generalize hQ : BitVec.ofNat 64 ((BitVec.ofNat 64 v).toNat * (BitVec.ofNat 64 u).toNat / 2 ^ 64) +
    BitVec.ofNat 64 u + (if q0 < BitVec.ofNat 64 a then (1 : BitVec 64) else 0) + 1#64 = Q
  have hQv : Q.toNat = ((V * u + a) / 2 ^ 64 + 1) % 2 ^ 64 := by
    rw [← hQ, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hc, hVv, hU, BitVec.toNat_ofNat,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (show v * u / 2 ^ 64 < 2 ^ 64 by omega), ← hPe]
    have : (v * u + a + 2 ^ 64 * u) / 2 ^ 64 = v * u / 2 ^ 64 + u + (decide (2 ^ 64 ≤ v * u % 2 ^ 64 + a)).toNat := by
      by_cases h : 2 ^ 64 ≤ v * u % 2 ^ 64 + a <;> simp only [h, decide_true, decide_false, Bool.toNat_true,
        Bool.toNat_false] <;> omega
    rw [this]
    have := Bool.toNat_le (decide (2 ^ 64 ≤ v * u % 2 ^ 64 + a))
    omega
  generalize hr : BitVec.ofNat 64 a - Q * BitVec.ofNat 64 d = r
  have hrv : r.toNat = (a + (2 ^ 64 - Q.toNat * d % 2 ^ 64)) % 2 ^ 64 := by
    rw [← hr, BitVec.toNat_sub, BitVec.toNat_mul, hA, hD]
    have : Q.toNat * d % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [Nat.add_comm]
  generalize hcv : decide ((V * u + a) % 2 ^ 64 < r.toNat) = c
  have hcb : (if q0 < r then (1 : BitVec 64) else 0) = BitVec.ofNat 64 c.toNat := by
    rw [← hcv]
    by_cases h : q0 < r
    · rw [ite_eq_left h, decide_eq_true (by rw [BitVec.lt_def, hq0v] at h; exact h)]; rfl
    · rw [ite_eq_right h, decide_eq_false (by rw [BitVec.lt_def, hq0v] at h; exact h)]; rfl
  rw [hcb]
  have hQ1 : (Q - BitVec.ofNat 64 c.toNat).toNat = (Q.toNat + if c then 2 ^ 64 - 1 else 0) % 2 ^ 64 := by
    have := Q.isLt
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt this, Bool.toNat_false]
      rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.sub_zero]
    · simp only [↓reduceIte, BitVec.toNat_sub, BitVec.toNat_ofNat, Bool.toNat_true]
      omega
  have hr1 : (r + ((0 - BitVec.ofNat 64 c.toNat) &&& BitVec.ofNat 64 d)).toNat = (r.toNat + if c then d else 0) % 2 ^ 64 := by
    have := r.isLt
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt this, Bool.toNat_false]
      rw [show (0 : BitVec 64) - BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.zero_and, BitVec.add_zero]
    · simp only [↓reduceIte, Bool.toNat_true]
      rw [show (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.allOnes_and,
        BitVec.toNat_add, hD]
  generalize hQ1v : Q - BitVec.ofNat 64 c.toNat = Q1 at hQ1
  generalize hr1v : r + ((0 - BitVec.ofNat 64 c.toNat) &&& BitVec.ofNat 64 d) = r1 at hr1
  have hfin := WordStep.mg_quot hd hn hu ha hV.symm rfl hQv hrv (Q1 := Q1.toNat) (r1 := r1.toNat)
    (by rw [hQ1, ← hcv]; simp only [decide_eq_true_eq]) (by rw [hr1, ← hcv]; simp only [decide_eq_true_eq])
  rw [← hfin, lt_xor_one, BitVec.toNat_add, BitVec.toNat_ofNat, hD]
  have := Q1.isLt
  by_cases h : d ≤ r1.toNat
  · simp only [h, decide_true, Bool.toNat_true, show d - 1 < r1.toNat by omega, ↓reduceIte]
  · simp only [h, decide_false, Bool.toNat_false, show ¬ d - 1 < r1.toNat by omega, ↓reduceIte]

/-- The estimate as `quotFix` makes it, all ones when the top word `u₂` of
the dividend is the divisor `d`. -/
theorem fix_val (q u2 d : BitVec 64) :
    (q ||| ((if 0 < d - u2 then (1 : BitVec 64) else 0) - 1#64)) = if u2 = d then BitVec.allOnes 64 else q := by
  by_cases h : u2 = d
  · subst h
    rw [BitVec.sub_self, ite_eq_right (by decide), ite_eq_left rfl]
    exact BitVec.or_allOnes
  · have hne : 0 < d - u2 := by
      rw [BitVec.lt_def]
      refine Nat.pos_of_ne_zero fun e => h ?_
      have := BitVec.eq_of_toNat_eq (x := d - u2) (y := 0) e
      rw [BitVec.sub_eq_iff_eq_add] at this
      exact (this.trans (BitVec.zero_add u2)).symm
    rw [ite_eq_left hne, ite_eq_right h, show (1 : BitVec 64) - 1#64 = 0#64 from rfl, BitVec.or_zero]

/-- The registers `quot` writes. -/
def quotRegs : List Reg := [.a3, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `quot`, `x` (`w ≥ 3` words) at `a2` and the temporary at `a6`, holding
`P = 2^z`, `d' ≥ 2^63` and `v = ⌊(2^128 - 1) / d'⌋ - 2^64`, with
`⌊x P / 2^(64 (w - 1))⌋ ≤ d'`: `q̂ = min(⌊u / d'⌋, 2^64 - 1)` in `s1` for the
top two words `u = ⌊x P / 2^(64 (w - 2))⌋` of `x P`. -/
theorem quot_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h6 : s.gpr .a6 = off B (slot w 3))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h4 : s.gpr .a4 = 0) (hw : 3 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 4 ≤ Z) (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : 2 ^ 63 ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat)
    (hv : (Mont.word s.mem B (slot w 3 + 16)).toNat =
      (2 ^ 128 - 1) / (Mont.word s.mem B (slot w 3 + 8)).toNat - 2 ^ 64)
    (hXd : wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (Mont.word s.mem B (slot w 3 + 8)).toNat) :
    WP isa (.block quot) s fun t => ((t.gpr .s1).toNat =
      min (wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 2)) / (Mont.word s.mem B (slot w 3 + 8)).toNat)
        (2 ^ 64 - 1) ∧ t.mem = s.mem) ∧ Keep quotRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have al := slot_al8 w
  have a1 := al 1; have a3 := al 3
  generalize hDw : Mont.word s.mem B (slot w 3 + 8) = D at hd hv hXd ⊢
  generalize hPw : Mont.word s.mem B (slot w 3) = P at hP
  generalize hVw : Mont.word s.mem B (slot w 3 + 16) = V at hv
  generalize hx2 : Mont.word s.mem B (slot w 1 + 8 * (w - 1)) = x2
  generalize hx1 : Mont.word s.mem B (slot w 1 + 8 * (w - 2)) = x1
  generalize hx0 : Mont.word s.mem B (slot w 1 + 8 * (w - 3)) = x0
  generalize hK : 64 * (w - 3) = K
  have hk1 : 64 * (w - 1) = K + 64 + 64 := by omega
  have hk2 : 64 * (w - 2) = K + 64 := by omega
  rw [hk1] at hXd
  rw [hk2]
  generalize hX : wordsVal s.mem B (slot w 1) w = X at hXd ⊢
  have hlow := wordsVal_lt s.mem B (slot w 1) (w - 3)
  rw [hK] at hlow
  have hXe : X = x2.toNat * 2 ^ (K + 64 + 64) + x1.toNat * 2 ^ (K + 64) + x0.toNat * 2 ^ K +
      wordsVal s.mem B (slot w 1) (w - 3) := by
    have f1 := wordsVal_succ_top s.mem B (slot w 1) (w - 1)
    have f2 := wordsVal_succ_top s.mem B (slot w 1) (w - 2)
    have f3 := wordsVal_succ_top s.mem B (slot w 1) (w - 3)
    rw [show w - 1 + 1 = w by omega, hx2, hX, hk1] at f1
    rw [show w - 2 + 1 = w - 1 by omega, hx1, hk2] at f2
    rw [show w - 3 + 1 = w - 2 by omega, hx0, hK] at f3
    rw [f1, f2, f3, Nat.mul_comm x2.toNat, Nat.mul_comm x1.toNat, Nat.mul_comm x0.toNat]
    generalize 2 ^ (K + 64 + 64) * x2.toNat = a
    generalize 2 ^ (K + 64) * x1.toNat = b
    generalize 2 ^ K * x0.toNat = c
    omega_using []
  -- The top words of `x P`.
  have hu2 : X * 2 ^ z / 2 ^ (K + 64 + 64) = x2.toNat * 2 ^ z + x1.toNat * 2 ^ z / 2 ^ 64 := by
    rw [hXe, Nat.add_assoc _ (x0.toNat * 2 ^ K)]
    refine top_shift (by omega) ?_
    have := Nat.mul_le_mul_right (2 ^ K) (show x0.toNat + 1 ≤ 2 ^ 64 from x0.isLt)
    rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, Nat.add_comm 64 K] at this
    omega_using [this, hlow]
  have hU : X * 2 ^ z / 2 ^ (K + 64) = x2.toNat * 2 ^ z * 2 ^ 64 + (x1.toNat * 2 ^ z + x0.toNat * 2 ^ z / 2 ^ 64) := by
    have : X = (x2.toNat * 2 ^ 64 + x1.toNat) * 2 ^ (K + 64) + x0.toNat * 2 ^ K +
        wordsVal s.mem B (slot w 1) (w - 3) := by
      rw [hXe, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm 64 (K + 64)]
    rw [this, top_shift (by omega) hlow, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ 64), ← Nat.mul_assoc,
      Nat.add_assoc]
  generalize hUd : X * 2 ^ z / 2 ^ (K + 64) = U at hU ⊢
  have hUu : U / 2 ^ 64 = X * 2 ^ z / 2 ^ (K + 64 + 64) := by
    rw [← hUd, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hf0 : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
    exact Nat.mul_lt_mul_of_pos_right x0.isLt (Nat.two_pow_pos z)
  have hpz : 2 ^ z ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hz
  have hf1 : x1.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64 := by
    have : x1.toNat * 2 ^ z / 2 ^ 64 < 2 ^ z := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), Nat.mul_comm (2 ^ z)]
      exact Nat.mul_lt_mul_of_pos_right x1.isLt (Nat.two_pow_pos z)
    omega_using [this, hpz]
  have hDlt := D.isLt
  -- `u₂` and `u₁` as `quotHead` computes them.
  generalize hU2 : x2 * P + BitVec.ofNat 64 (x1.toNat * P.toNat / 2 ^ 64) = U2
  generalize hU1 : x1 * P + BitVec.ofNat 64 (x0.toNat * P.toNat / 2 ^ 64) = U1
  have hU2v : U2.toNat = U / 2 ^ 64 := by
    rw [← hU2, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP, Nat.mod_eq_of_lt hf1, Nat.mod_add_mod,
      hUu, hu2]
    exact Nat.mod_eq_of_lt (by omega_using [hu2, hXd, hDlt])
  have hU1v : U1.toNat = U % 2 ^ 64 := by
    rw [← hU1, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hP,
      Nat.mod_eq_of_lt (by omega_using [hf0, hpz] : x0.toNat * 2 ^ z / 2 ^ 64 < 2 ^ 64), Nat.mod_add_mod, hU,
      Nat.add_comm (x2.toNat * 2 ^ z * 2 ^ 64), Nat.add_mul_mod_self_right]
  have ea := ea_top B (d := slot w 1) (w := w) (c := 24) (by omega) (by omega)
  rw [show slot w 1 + 8 * w - 24 = slot w 1 + 8 * (w - 3) by omega] at ea
  have r2 : s.mem.readW (off B (slot w 1 + 8 * (w - 3) + 16)) 64 = x2 := by
    rw [← hx2, show slot w 1 + 8 * (w - 3) + 16 = slot w 1 + 8 * (w - 1) by omega]
  have r1 : s.mem.readW (off B (slot w 1 + 8 * (w - 3) + 8)) 64 = x1 := by
    rw [← hx1, show slot w 1 + 8 * (w - 3) + 8 = slot w 1 + 8 * (w - 2) by omega]
  have r0 : s.mem.readW (off B (slot w 1 + 8 * (w - 3))) 64 = x0 := hx0
  have rP : s.mem.readW (off B (slot w 3)) 64 = P := hPw
  have rD : s.mem.readW (off B (slot w 3 + 8)) 64 = D := hDw
  have rV : s.mem.readW (off B (slot w 3 + 16)) 64 = V := hVw
  refine WP.mono (WP.keep quotRegs (Q := fun t =>
      t.gpr .s1 = (mgq V U2 U1 D ||| ((if 0 < D - U2 then (1 : BitVec 64) else 0) - 1#64)) ∧ t.mem = s.mem) (by
    unfold quot quotHead quotMG quotFix
    brun [h2, h6, ht0, h4, ea, r2, r1, r0, rP, rD, rV, hU2, hU1, BitVec.add_zero,
      hs.ld (show slot w 1 + 8 * (w - 3) + 16 + 8 ≤ Z by omega),
      hs.al8 (show slot w 1 + 8 * (w - 3) + 16 + 8 ≤ Z by omega) (by omega),
      hs.ld (show slot w 1 + 8 * (w - 3) + 8 + 8 ≤ Z by omega),
      hs.al8 (show slot w 1 + 8 * (w - 3) + 8 + 8 ≤ Z by omega) (by omega),
      hs.ld (show slot w 1 + 8 * (w - 3) + 8 ≤ Z by omega),
      hs.al8 (show slot w 1 + 8 * (w - 3) + 8 ≤ Z by omega) (by omega),
      hs.ld (show slot w 3 + 8 ≤ Z by omega), hs.al8 (show slot w 3 + 8 ≤ Z by omega) a3,
      hs.ld (show slot w 3 + 8 + 8 ≤ Z by omega), hs.al8 (show slot w 3 + 8 + 8 ≤ Z by omega) (by omega),
      hs.ld (show slot w 3 + 16 + 8 ≤ Z by omega), hs.al8 (show slot w 3 + 16 + 8 ≤ Z by omega) (by omega)]
    rfl) (by rfl) (by rfl)) fun t ⟨⟨t1, tm⟩, k⟩ => ⟨⟨?_, tm⟩, k⟩
  have hu2D : U / 2 ^ 64 ≤ D.toNat := by rw [hUu]; exact hXd
  have hd0 : 0 < D.toNat := by omega_using [hd]
  have hfix := WordStep.qhat_fix hd0 hu2D (Nat.mod_lt U (show 0 < 2 ^ 64 by decide))
  rw [Nat.div_add_mod'] at hfix
  rw [← hfix, t1, fix_val]
  by_cases hc : U2 = D
  · rw [ite_eq_left hc, ite_eq_left (by rw [← hU2v, hc]), BitVec.toNat_allOnes]
  · have hne : U / 2 ^ 64 ≠ D.toNat := fun h => hc (BitVec.eq_of_toNat_eq (by rw [hU2v, h]))
    rw [ite_eq_right hc, ite_eq_right hne]
    have hlt : U2.toNat < D.toNat := by rw [hU2v]; exact Nat.lt_of_le_of_ne hu2D hne
    have hq := mgq_val (v := V.toNat) (u := U2.toNat) (a := U1.toNat) hDlt hd hlt U1.isLt hv
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hq
    rw [hq, hU2v, hU1v, Nat.div_add_mod']


/-! ## `t = x 2^64 - q̂ n` -/

/-- A word of `q̂ n`: the low word of `n q + c`, and the high word of `n q`
plus the carry, the next carry. -/
theorem mul_arith (n q c : BitVec 64) :
    (n * q + c).toNat + 2 ^ 64 * (BitVec.ofNat 64 (n.toNat * q.toNat / 2 ^ 64) +
      (if n * q + c < c then 1 else 0)).toNat = n.toNat * q.toNat + c.toNat := by
  have hn := n.isLt; have hq := q.isLt; have hc := c.isLt
  have hhi : n.toNat * q.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    have := Nat.mul_le_mul (show n.toNat ≤ 2 ^ 64 - 1 by omega) (show q.toNat ≤ 2 ^ 64 - 1 by omega)
    exact Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64) this) (by decide)
  have hd := Nat.div_add_mod (n.toNat * q.toNat) (2 ^ 64)
  have hlo := Nat.mod_lt (n.toNat * q.toNat) (show 0 < 2 ^ 64 by decide)
  have e := carry_val (n * q) c
  rw [BitVec.toNat_add (BitVec.ofNat 64 _), e, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n.toNat * q.toNat / 2 ^ 64 < 2 ^ 64 by omega)]
  rw [BitVec.toNat_mul] at e
  generalize n.toNat * q.toNat / 2 ^ 64 = hi at hhi hd ⊢
  generalize n.toNat * q.toNat % 2 ^ 64 = lo at hd hlo ⊢
  generalize n.toNat * q.toNat = P at hd ⊢
  by_cases h : 2 ^ 64 ≤ lo + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `x`'s previous word: 0 before word 0. -/
def xPrev (m : Mem) (B : Addr) (dX i : Nat) : BitVec 64 := if i = 0 then 0 else Mont.word m B (dX + 8 * (i - 1))

/-- What `mulSub` keeps after `i` words, from `s` (`q` in `s1`): the
pointers, `x`'s words from `i` on, the carry `c` (`s0`), the borrow `b`
(`s4`) and the previous word of `x` (`t6`), for
`T + q n_{<i} = 2^64 x_{<i-1} + 2^(64 i) (b + c)`. -/
def MSInv (s : State) (B : Addr) (dX dN : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (dX + 8 * i) ∧ t.gpr .t4 = off B (dN + 8 * i) ∧ t.gpr .s1 = s.gpr .s1 ∧
    (t.gpr .s4).toNat ≤ 1 ∧ t.gpr .t6 = xPrev s.mem B dX i ∧ Outside B dX (8 * i) s.mem t.mem ∧
    wordsVal t.mem B dX i + (s.gpr .s1).toNat * wordsVal s.mem B dN i =
      2 ^ 64 * wordsVal s.mem B dX (i - 1) + 2 ^ (64 * i) * ((t.gpr .s4).toNat + (t.gpr .s0).toNat) ∧
    Keep [.a0, .a3, .s0, .s2, .s3, .s4, .t3, .t4, .t5, .t6] s t

theorem xPrev_succ (m : Mem) (B : Addr) (dX i : Nat) : xPrev m B dX (i + 1) = Mont.word m B (dX + 8 * i) := by
  simp [xPrev]

/-- `2^64 x_{<i}` from `2^64 x_{<i-1}` and `x`'s previous word. -/
theorem shift_eq (m : Mem) (B : Addr) (dX : Nat) : ∀ i,
    2 ^ 64 * wordsVal m B dX i = 2 ^ 64 * wordsVal m B dX (i - 1) + 2 ^ (64 * i) * (xPrev m B dX i).toNat
  | 0 => by
    rw [Nat.zero_sub, xPrev, ite_eq_left rfl]
    show _ = _ + _ * 0
    rw [Nat.mul_zero, Nat.add_zero]
  | k + 1 => by
    rw [xPrev_succ, Nat.add_sub_cancel, wordsVal_succ_top, Nat.mul_add, Nat.mul_succ, Nat.pow_add,
      Nat.mul_comm (2 ^ (64 * k)) (2 ^ 64), Nat.mul_assoc]

theorem mulSubWord_ok {s : State} {B : Addr} {Z dX dN w : Nat} (hs : Scr s B Z) (hX8 : dX % 8 = 0)
    (hN8 : dN % 8 = 0) (hX : dX + 8 * (w + 1) ≤ Z) (hN : dN + 8 * w ≤ Z)
    (dNX : dN + 8 * w ≤ dX ∨ dX + 8 * (w + 1) ≤ dN) {i : Nat} (hi : i < w) {t : State} (hI : MSInv s B dX dN i t) :
    WP isa (.block (mulSubWord ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      MSInv s B dX dN (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, j1, jb, j6, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.2.2
  have wX : Mont.word t.mem B (dX + 8 * i) = Mont.word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
  have wN : Mont.word t.mem B (dN + 8 * i) = Mont.word s.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
  generalize hn : Mont.word s.mem B (dN + 8 * i) = n at wN
  generalize hlo : n * t.gpr .s1 + t.gpr .s0 = lo
  refine WP.mono (WP.keep [.a0, .a3, .s0, .s2, .s3, .s4, .t3, .t4, .t5, .t6] (Q := fun t' =>
      t'.gpr .t3 = off B (dX + 8 * i + 8) ∧ t'.gpr .t4 = off B (dN + 8 * i + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
      t'.gpr .s0 = BitVec.ofNat 64 (n.toNat * (t.gpr .s1).toNat / 2 ^ 64) + (if lo < t.gpr .s0 then 1 else 0) ∧
      t'.gpr .s4 = ((if t.gpr .t6 < lo then (1 : BitVec 64) else 0) ||| (if t.gpr .t6 - lo < t.gpr .s4 then 1 else 0)) ∧
      t'.gpr .t6 = Mont.word s.mem B (dX + 8 * i) ∧
      t'.mem = t.mem.writeW (off B (dX + 8 * i)) (t.gpr .t6 - lo - t.gpr .s4)) (by
    have rN : t.mem.readW (off B (dN + 8 * i)) 64 = n := wN
    have rX : t.mem.readW (off B (dX + 8 * i)) 64 = Mont.word s.mem B (dX + 8 * i) := wX
    unfold mulSubWord
    brun [j3, j4, rN, rX, hlo, BitVec.add_zero, hs'.ld (show dN + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dN + 8 * i + 8 ≤ Z by omega) (by omega), hs'.ld (show dX + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega) (by omega), hs'.st (show dX + 8 * i + 8 ≤ Z by omega)])
    (by rfl) (by rfl)) fun t' ⟨⟨u3, u4, u5, u0, u4b, u6, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Keep.trans' jk uk⟩, u5⟩
  · rw [u3, show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega]
  · rw [u4, show dN + 8 * i + 8 = dN + 8 * (i + 1) by omega]
  · rw [uk.gpr (by decide), j1]
  · rw [u4b]; exact (sub64_arith _ _ _ jb).2
  · rw [u6, xPrev_succ]
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dX + 8 * i) _ (by omega)).mono (by omega) (by omega))
  · have km := mul_arith n (t.gpr .s1) (t.gpr .s0)
    have ks := (sub64_arith (t.gpr .t6) lo (t.gpr .s4) jb).1
    rw [hlo, j1] at km
    rw [um, u4b, u0, fin64_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B dN i, hn, j1,
      Nat.add_sub_cancel, shift_eq s.mem B dX i, show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by
        rw [Nat.mul_succ, Nat.pow_add], ← j6]
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize ((if t.gpr .t6 < lo then (1 : BitVec 64) else 0) ||| (if t.gpr .t6 - lo < t.gpr .s4 then 1 else 0)).toNat
      = b' at ks ⊢
    generalize (BitVec.ofNat 64 (n.toNat * (s.gpr .s1).toNat / 2 ^ 64) + (if lo < t.gpr .s0 then 1 else 0)).toNat
      = c' at km ⊢
    generalize (t.gpr .t6 - lo - t.gpr .s4).toNat = tw at ks ⊢
    generalize lo.toNat = l at km ks
    generalize (t.gpr .t6).toNat = xp at ks ⊢
    generalize (s.gpr .s1).toNat = q at km jv ⊢
    generalize n.toNat = nn at km ⊢
    generalize (t.gpr .s4).toNat = b at ks jv
    generalize (t.gpr .s0).toNat = c at km jv
    generalize wordsVal t.mem B dX i = W at jv ⊢
    generalize wordsVal s.mem B dN i = Nw at jv ⊢
    generalize 2 ^ 64 * wordsVal s.mem B dX (i - 1) = Xs at jv ⊢
    have hin : b + c + tw + nn * q = xp + 2 ^ 64 * (b' + c') := by omega_using [km, ks]
    have := congrArg (P * ·) hin
    grind


/-- The registers `mulSub` writes. -/
def mulSubRegs : List Reg := [.a0, .a3, .s0, .s2, .s3, .s4, .t3, .t4, .t5, .t6]

/-- `mulSub`, `x` (`w` words, and room for a word more) at `dX` (`a2`), `n`
at `dN` (`a7`) and `q` in `s1`: `x`'s first `w + 1` words := `t` with
`t + q n = x 2^64 + 2^(64 (w + 1)) b`, for the borrow `b`. -/
theorem mulSub_ok {s : State} {B : Addr} {Z dX dN w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B dX) (h7 : s.gpr .a7 = off B dN) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hX8 : dX % 8 = 0) (hN8 : dN % 8 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hX : dX + 8 * (w + 1) ≤ Z)
    (hN : dN + 8 * w ≤ Z) (dNX : dN + 8 * w ≤ dX ∨ dX + 8 * (w + 1) ≤ dN) :
    WP isa mulSub s fun t =>
      ((∃ b < 2, wordsVal t.mem B dX (w + 1) + (s.gpr .s1).toNat * wordsVal s.mem B dN w =
        wordsVal s.mem B dX w * 2 ^ 64 + 2 ^ (64 * (w + 1)) * b) ∧
      Outside B dX (8 * (w + 1)) s.mem t.mem) ∧ Keep mulSubRegs s t := by
  have hnw := hs.nowrap
  unfold mulSub
  refine WP.seq (WP.mono (WP.keep [.t3, .t4, .t5, .s0, .s4, .t6] (Q := fun t =>
      t.gpr .t3 = off B dX ∧ t.gpr .t4 = off B dN ∧ t.gpr .t5 = BitVec.ofNat 64 w ∧ t.gpr .s0 = 0 ∧
        t.gpr .s4 = 0 ∧ t.gpr .t6 = 0 ∧ t.mem = s.mem)
    (by unfold mulSubHead; brun [h2, h7, ht0, exec_li_zero, BitVec.add_zero]) (by rfl) (by rfl))
    fun s₁ ⟨⟨i3, i4, i5, i0, i4b, i6, im⟩, k₁⟩ => ?_)
  have I0 : MSInv s₁ B dX dN 0 s₁ := ⟨by rw [i3]; rfl, by rw [i4]; rfl, rfl, by rw [i4b]; decide,
    by rw [i6]; rfl, Outside.refl _ _ _ _, by simp [wordsVal, i4b, i0], Keep.refl _ _⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := w) (by omega) (by omega) (MSInv s₁ B dX dN)
    (fun i hi t hI _ => mulSubWord_ok (hs.congr k₁.2.2) hX8 hN8 hX hN dNX hi hI) I0 i5)
    fun t ⟨j3, _, j1, jb, j6, jout, jv, jk⟩ => ?_)
  have hs' := hs.congr (k₁.trans jk).2.2
  refine WP.mono (WP.keep [.s2, .s3, .a3] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dX + 8 * w)) (t.gpr .t6 - t.gpr .s0 - t.gpr .s4)) (by
    unfold mulSubTop
    brun [j3, hs'.st (show dX + 8 * w + 8 ≤ Z by omega), hs'.al8 (show dX + 8 * w + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t' ⟨tm, tk⟩ => ⟨⟨?_, ?_⟩, ((k₁.trans jk).trans tk).mono (by decide)⟩
  · have ks := sub64_arith (t.gpr .t6) (t.gpr .s0) (t.gpr .s4) jb
    refine ⟨_, Nat.lt_succ_of_le ks.2, ?_⟩
    have hq : s₁.gpr .s1 = s.gpr .s1 := k₁.gpr (by decide)
    rw [im, hq] at jv
    rw [im] at j6
    rw [tm, fin64_wordsVal_write_top _ _ _ _ _ (by omega)]
    have hsh := shift_eq s.mem B dX w
    rw [← j6] at hsh
    have e1 : 2 ^ (64 * (w + 1)) = 2 ^ (64 * w) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [e1]
    have ks1 := ks.1
    generalize 2 ^ (64 * w) = P at jv hsh ⊢
    generalize (t.gpr .t6 - t.gpr .s0 - t.gpr .s4).toNat = tw at ks1 ⊢
    generalize ((if t.gpr .t6 < t.gpr .s0 then (1 : BitVec 64) else 0) |||
      (if t.gpr .t6 - t.gpr .s0 < t.gpr .s4 then 1 else 0)).toNat = b' at ks1 ⊢
    generalize (t.gpr .t6).toNat = xp at ks1 hsh
    generalize (t.gpr .s0).toNat = c at ks1 jv
    generalize (t.gpr .s4).toNat = b at ks1 jv
    have hin : b + c + tw = xp + 2 ^ 64 * b' := by omega_using [ks1]
    have := congrArg (P * ·) hin
    grind
  · rw [tm]
    exact (Outside.mono (fun x hx => (jout x hx).trans (by rw [im])) (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dX + 8 * w) _ (by omega)).mono (by omega) (by omega))


/-! ## Adding `n` back -/

/-- The mask of the sign of `x`. -/
theorem sign_mask (x : BitVec 64) :
    0 - x >>> 63 = if decide (2 ^ 63 ≤ x.toNat) then BitVec.allOnes 64 else 0 := by
  rw [shr63_toNat]
  cases decide (2 ^ 63 ≤ x.toNat) <;> rfl

/-- The top half of `k + 1` words: their top word's top bit. -/
theorem top_half (m : Mem) (B : Addr) (d k : Nat) :
    2 ^ (64 * (k + 1)) / 2 ≤ wordsVal m B d (k + 1) ↔ 2 ^ 63 ≤ (Mont.word m B (d + 8 * k)).toNat := by
  rw [wordsVal_succ_top, show 2 ^ (64 * (k + 1)) / 2 = 2 ^ (64 * k) * 2 ^ 63 by
    rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc,
      Nat.mul_div_cancel _ (by decide)]]
  have hl := wordsVal_lt m B d k
  have hp := Nat.two_pow_pos (64 * k)
  generalize wordsVal m B d k = l at hl ⊢
  generalize (Mont.word m B (d + 8 * k)).toNat = t
  generalize 2 ^ (64 * k) = P at hl hp ⊢
  constructor
  · intro h
    refine Nat.le_of_not_lt fun ht => ?_
    have := Nat.mul_le_mul_left P (show t + 1 ≤ 2 ^ 63 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · intro h
    have := Nat.mul_le_mul_left P h
    omega

/-- What `addBack`'s loop keeps after `i` words, from `s`: the pointers, the
mask (`b`), the carry (`s1`), and `x`'s words from `i` on. -/
def ABInv (s : State) (B : Addr) (dX dN : Nat) (b : Bool) (i : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (dX + 8 * i) ∧ t.gpr .t4 = off B (dN + 8 * i) ∧ (t.gpr .s1).toNat ≤ 1 ∧
    t.gpr .s4 = (if b then BitVec.allOnes 64 else 0) ∧ Outside B dX (8 * i) s.mem t.mem ∧
    wordsVal t.mem B dX i + 2 ^ (64 * i) * (t.gpr .s1).toNat =
      wordsVal s.mem B dX i + (if b then wordsVal s.mem B dN i else 0) ∧
    Keep [.t3, .t4, .t5, .s0, .s1, .s2, .s3] s t

theorem addBackWord_ok {s : State} {B : Addr} {Z dX dN w : Nat} {b : Bool} (hs : Scr s B Z) (hX8 : dX % 8 = 0)
    (hN8 : dN % 8 = 0) (hX : dX + 8 * w ≤ Z) (hN : dN + 8 * w ≤ Z) (dNX : dN + 8 * w ≤ dX ∨ dX + 8 * w ≤ dN)
    {i : Nat} (hi : i < w) {t : State} (hI : ABInv s B dX dN b i t) :
    WP isa (.block (addBackWord ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      ABInv s B dX dN b (i + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, j1, j44, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.2.2
  have wT : Mont.word t.mem B (dX + 8 * i) = Mont.word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
  have wM : Mont.word t.mem B (dN + 8 * i) = Mont.word s.mem B (dN + 8 * i) := jout.word (by omega) (by omega)
  refine WP.mono (WP.keep [.t3, .t4, .t5, .s0, .s1, .s2, .s3] (Q := fun t' =>
      t'.gpr .t3 = off B (dX + 8 * i + 8) ∧ t'.gpr .t4 = off B (dN + 8 * i + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
      let y := Mont.word t.mem B (dN + 8 * i) &&& t.gpr .s4
      let x := Mont.word t.mem B (dX + 8 * i)
      t'.gpr .s1 = ((if x + y + t.gpr .s1 < t.gpr .s1 then (1 : BitVec 64) else 0) |||
        (if x + y < y then 1 else 0)) ∧
      t'.mem = t.mem.writeW (off B (dX + 8 * i)) (x + y + t.gpr .s1)) ?_ (by rfl) (by rfl))
    fun t' ⟨⟨u3, u4, u5, u1, um⟩, uk⟩ => ⟨⟨u3.trans (by rw [Nat.mul_succ, Nat.add_assoc]),
      u4.trans (by rw [Nat.mul_succ, Nat.add_assoc]), ?_, by rw [uk.gpr (by decide), j44], ?_, ?_, Keep.trans' jk uk⟩,
      u5⟩
  · unfold addBackWord
    brun [j3, j4, hs'.ld (show dX + 8 * i + 8 ≤ Z by omega), hs'.ld (show dN + 8 * i + 8 ≤ Z by omega),
      hs'.st (show dX + 8 * i + 8 ≤ Z by omega),
      hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega) (by omega),
      hs'.al8 (show dN + 8 * i + 8 ≤ Z by omega) (by omega), BitVec.add_zero]
  · rw [u1]; exact (ModArith.add_arith _ _ _ j1).2
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dX + 8 * i) _ (by omega)).mono (by omega) (by omega))
  · have e := (ModArith.add_arith (Mont.word t.mem B (dX + 8 * i)) (Mont.word t.mem B (dN + 8 * i) &&& t.gpr .s4)
      (t.gpr .s1) j1).1
    rw [j44, ModArith.and_mask, wT, wM] at e
    rw [um, u1, j44, ModArith.and_mask, wT, wM, fin64_wordsVal_write_top _ _ _ _ _ (by omega), Nat.mul_succ,
      Nat.pow_add, wordsVal_succ_top s.mem B dX i, wordsVal_succ_top s.mem B dN i]
    cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at e jv ⊢ <;> grind

/-- The registers `addBack` writes. -/
def addBackRegs : List Reg := [.t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `addBack`, `t` (`w + 1` words) at `dX` (`a2`), `n` at `dN` (`a7`) and
zero in `a4`: `t := t + n` modulo `2^(64 (w + 1))`, with the carry `c`, if
`t`'s top half is set. -/
theorem addBack_ok {s : State} {B : Addr} {Z dX dN w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B dX) (h7 : s.gpr .a7 = off B dN) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h4 : s.gpr .a4 = 0) (hX8 : dX % 8 = 0) (hN8 : dN % 8 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : dX + 8 * (w + 1) ≤ Z) (hN : dN + 8 * w ≤ Z) (dNX : dN + 8 * w ≤ dX ∨ dX + 8 * (w + 1) ≤ dN) :
    WP isa addBack s fun t =>
      ((∃ c < 2, wordsVal t.mem B dX (w + 1) + 2 ^ (64 * (w + 1)) * c = wordsVal s.mem B dX (w + 1) +
        if 2 ^ (64 * (w + 1)) / 2 ≤ wordsVal s.mem B dX (w + 1) then wordsVal s.mem B dN w else 0) ∧
      Outside B dX (8 * (w + 1)) s.mem t.mem) ∧ Keep addBackRegs s t := by
  have hnw := hs.nowrap
  unfold addBack
  simp only [top_half]
  generalize hb : decide (2 ^ 63 ≤ (Mont.word s.mem B (dX + 8 * w)).toNat) = b
  have hif : (if 2 ^ 63 ≤ (Mont.word s.mem B (dX + 8 * w)).toNat then wordsVal s.mem B dN w else 0) =
      if b then wordsVal s.mem B dN w else 0 := by
    rw [← hb]; by_cases h : 2 ^ 63 ≤ (Mont.word s.mem B (dX + 8 * w)).toNat <;> simp [h]
  rw [hif]
  have rT : s.mem.readW (off B (dX + 8 * w)) 64 = Mont.word s.mem B (dX + 8 * w) := rfl
  refine WP.seq (WP.mono (WP.keep [.t3, .t4, .t5, .s1, .s4] (Q := fun t =>
      t.gpr .t3 = off B dX ∧ t.gpr .t4 = off B dN ∧ t.gpr .t5 = BitVec.ofNat 64 w ∧ t.gpr .s1 = 0 ∧
        t.gpr .s4 = (if b then BitVec.allOnes 64 else 0) ∧ t.mem = s.mem)
    (by
      unfold addBackHead
      brun [h2, h7, ht0, h4, exec_li_zero, BitVec.add_zero, ea_end B (show B.toNat + dX + 8 * w < 2 ^ 64 by omega),
        rT, hs.ld (show dX + 8 * w + 8 ≤ Z by omega), hs.al8 (show dX + 8 * w + 8 ≤ Z by omega) (by omega),
        sign_mask, hb]
      exact (sign_mask _).trans (by rw [hb])) (by rfl) (by rfl))
    fun s₁ ⟨⟨i3, i4, i5, i1, i44, im⟩, k₁⟩ => ?_)
  have I0 : ABInv s₁ B dX dN b 0 s₁ := ⟨by rw [i3]; rfl, by rw [i4]; rfl, by rw [i1]; decide, i44,
    Outside.refl _ _ _ _, by simp [wordsVal, i1], Keep.refl _ _⟩
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := w) (by omega) (by omega) (ABInv s₁ B dX dN b)
    (fun i hi t hI _ => addBackWord_ok (hs.congr k₁.2.2) hX8 hN8 (by omega) hN (by omega) hi hI) I0 i5)
    fun t ⟨j3, _, j1, _, jout, jv, jk⟩ => ?_)
  have hs' := hs.congr (k₁.trans jk).2.2
  have wT : Mont.word t.mem B (dX + 8 * w) = Mont.word s.mem B (dX + 8 * w) := by
    have := Outside.word jout (d := dX + 8 * w) (by omega) (by omega)
    rwa [im] at this
  have rT' : t.mem.readW (off B (dX + 8 * w)) 64 = Mont.word s.mem B (dX + 8 * w) := wT
  refine WP.mono (WP.keep [.s2] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dX + 8 * w)) (Mont.word s.mem B (dX + 8 * w) + t.gpr .s1)) (by
    brun [j3, rT', hs'.ld (show dX + 8 * w + 8 ≤ Z by omega), hs'.st (show dX + 8 * w + 8 ≤ Z by omega),
      hs'.al8 (show dX + 8 * w + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl))
    fun t' ⟨tm, tk⟩ => ⟨⟨?_, ?_⟩, ((k₁.trans jk).trans tk).mono (by decide)⟩
  · rw [im] at jv
    have hv : (Mont.word s.mem B (dX + 8 * w)).toNat + (t.gpr .s1).toNat < 2 ^ 65 := by
      have := (Mont.word s.mem B (dX + 8 * w)).isLt; omega
    have hc := carry_val (Mont.word s.mem B (dX + 8 * w)) (t.gpr .s1)
    refine ⟨(decide (2 ^ 64 ≤ (Mont.word s.mem B (dX + 8 * w)).toNat + (t.gpr .s1).toNat)).toNat,
      Nat.lt_succ_of_le (Bool.toNat_le _), ?_⟩
    rw [tm, fin64_wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_succ_top s.mem B dX w,
      show 2 ^ (64 * (w + 1)) = 2 ^ (64 * w) * 2 ^ 64 by rw [Nat.mul_succ, Nat.pow_add]]
    have ha : (Mont.word s.mem B (dX + 8 * w) + t.gpr .s1).toNat + 2 ^ 64 *
        (decide (2 ^ 64 ≤ (Mont.word s.mem B (dX + 8 * w)).toNat + (t.gpr .s1).toNat)).toNat =
        (Mont.word s.mem B (dX + 8 * w)).toNat + (t.gpr .s1).toNat := by
      rw [BitVec.toNat_add]
      by_cases h : 2 ^ 64 ≤ (Mont.word s.mem B (dX + 8 * w)).toNat + (t.gpr .s1).toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
    generalize (Mont.word s.mem B (dX + 8 * w) + t.gpr .s1).toNat = a at ha ⊢
    generalize (decide (2 ^ 64 ≤ (Mont.word s.mem B (dX + 8 * w)).toNat + (t.gpr .s1).toNat)).toNat = c at ha ⊢
    generalize (Mont.word s.mem B (dX + 8 * w)).toNat = x at ha ⊢
    generalize (t.gpr .s1).toNat = c0 at ha jv
    generalize 2 ^ (64 * w) = P at jv ⊢
    have := congrArg (P * ·) ha
    grind
  · rw [tm]
    exact (Outside.mono (fun x hx => (jout x hx).trans (by rw [im])) (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dX + 8 * w) _ (by omega)).mono (by omega) (by omega))


/-! ## A word step -/

/-- The registers `wordStep` writes. -/
def wordStepRegs : List Reg := [.a0, .a3, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `wordStep`, `n` in array 0 (`a7`), `x < n` in array 1 (`a2`), and `P =
2^z`, `d' = ⌊n P / 2^(64 (w - 1))⌋ ≥ 2^63` and `v = ⌊(2^128 - 1) / d'⌋ - 2^64`
in the temporary (array 3, `a6`), zero in `a4`: `x := x 2^64 mod n`,
changing only `x`'s first `w + 1` words. -/
theorem wordStep_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h6 : s.gpr .a6 = off B (slot w 3)) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h4 : s.gpr .a4 = 0) (hw : 3 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 4 ≤ Z) (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (Mont.word s.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (Mont.word s.mem B (slot w 3 + 16)).toNat =
      (2 ^ 128 - 1) / (Mont.word s.mem B (slot w 3 + 8)).toNat - 2 ^ 64)
    (hx : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w) :
    WP isa wordStep s fun t =>
      (wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w * 2 ^ 64 % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (8 * (w + 1)) s.mem t.mem) ∧ Keep wordStepRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have al := slot_al8 w
  generalize hX : wordsVal s.mem B (slot w 1) w = X at hx ⊢
  generalize hN : wordsVal s.mem B (slot w 0) w = N at hx hd hd63 ⊢
  have hXd : wordsVal s.mem B (slot w 1) w * 2 ^ z / 2 ^ (64 * (w - 1)) ≤
      (Mont.word s.mem B (slot w 3 + 8)).toNat := by
    rw [hd, hX]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hx))
  unfold wordStep
  -- `q̂`.
  refine WP.seq (WP.mono (quot_ok hs h2 h6 ht0 h4 hw hw' hZ hP hz (by rw [hd]; exact hd63) hv hXd)
    fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_)
  rw [hX, hd] at q1
  have g1 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0, .a4], s₁.gpr r = s.gpr r := fun r hr => k1.gpr (by revert r hr; decide)
  -- `t = x 2^64 - q̂ n`.
  refine WP.seq (WP.mono (mulSub_ok (dX := slot w 1) (dN := slot w 0) (hs.congr k1.2.2)
    ((g1 .a2 (by decide)).trans h2) ((g1 .a7 (by decide)).trans h7) ((g1 .t0 (by decide)).trans ht0)
    (al 1) (al 0) (by omega) hw' (by omega) (by omega) (by omega)) fun s₂ ⟨⟨⟨b, hb, a2⟩, o2⟩, k2⟩ => ?_)
  rw [m1, hN, q1, hX] at a2
  have k12 := k1.trans k2
  have g2 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0, .a4], s₂.gpr r = s.gpr r := fun r hr => k12.gpr (by revert r hr; decide)
  have n2 : wordsVal s₂.mem B (slot w 0) w = N := by rw [Outside.wordsVal o2 (by omega) (by omega), m1, hN]
  -- `n` added twice while negative.
  refine WP.seq (WP.mono (addBack_ok (dX := slot w 1) (dN := slot w 0) (hs.congr k12.2.2)
    ((g2 .a2 (by decide)).trans h2) ((g2 .a7 (by decide)).trans h7) ((g2 .t0 (by decide)).trans ht0)
    ((g2 .a4 (by decide)).trans h4) (al 1) (al 0) (by omega) hw' (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨⟨c1, hc1, a3⟩, o3⟩, k3⟩ => ?_)
  rw [n2] at a3
  have k13 := k12.trans k3
  have g3 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0, .a4], s₃.gpr r = s.gpr r := fun r hr => k13.gpr (by revert r hr; decide)
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal o3 (by omega) (by omega), n2]
  refine WP.mono (addBack_ok (dX := slot w 1) (dN := slot w 0) (hs.congr k13.2.2)
    ((g3 .a2 (by decide)).trans h2) ((g3 .a7 (by decide)).trans h7) ((g3 .t0 (by decide)).trans ht0)
    ((g3 .a4 (by decide)).trans h4) (al 1) (al 0) (by omega) hw' (by omega) (by omega) (by omega))
    fun t ⟨⟨⟨c2, hc2, a4⟩, o4⟩, k4⟩ => ⟨⟨?_, ?_⟩, (k13.trans k4).mono (by decide)⟩
  · rw [n3] at a4
    -- `x 2^64 mod n`.
    have hN0 : 0 < N := by omega
    have hNlt : N < 2 ^ (64 * w) := hN ▸ wordsVal_lt _ _ _ _
    have hW : 4 * N < 2 ^ (64 * (w + 1)) / 2 := by
      rw [show 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 by
        rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc,
          Nat.mul_div_cancel _ (by decide)]]
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 8 ≤ 2 ^ 63 by decide)
      omega
    obtain ⟨hge, hle⟩ := WordStep.qhat_norm (X := X) (M := N) (P := 2 ^ z) (K := 64 * (w - 2)) (Nat.two_pow_pos z)
      hx (by rw [show 64 * (w - 2) + 64 = 64 * (w - 1) by omega]; exact hd63)
    rw [show 64 * (w - 2) + 64 = 64 * (w - 1) by omega] at hge hle
    have hT := WordStep.wordStepQ_val hN0 hW hge hle (wordsVal_lt _ _ _ _) hb a2 (wordsVal_lt _ _ _ _) hc1 a3
      (wordsVal_lt _ _ _ _) hc2 a4
    have e5 := wordsVal_succ_top t.mem B (slot w 1) w
    have hr := Nat.mod_lt (X * 2 ^ 64) hN0
    rw [hT] at e5
    rcases Nat.eq_zero_or_pos (Mont.word t.mem B (slot w 1 + 8 * w)).toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at e5; exact e5.symm
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * w)) h
      omega
  · rw [m1] at o2
    exact Outside.trans (Outside.trans o2 o3) o4


/-- `wordSteps`, from `x = 2^(64 (w - 1)) < n` and the temporary as
`wordStep_ok` needs it: `x := 2^(128 w) mod n`, changing only `x`'s first
`w + 1` words. -/
theorem wordSteps_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h6 : s.gpr .a6 = off B (slot w 3)) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h4 : s.gpr .a4 = 0) (hw : 3 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 4 ≤ Z) (hP : (Mont.word s.mem B (slot w 3)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hd : (Mont.word s.mem B (slot w 3 + 8)).toNat = wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd63 : 2 ^ 63 ≤ wordsVal s.mem B (slot w 0) w * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (Mont.word s.mem B (slot w 3 + 16)).toNat =
      (2 ^ 128 - 1) / (Mont.word s.mem B (slot w 3 + 8)).toNat - 2 ^ 64)
    (hx : wordsVal s.mem B (slot w 1) w = 2 ^ (64 * (w - 1)))
    (hxN : 2 ^ (64 * (w - 1)) < wordsVal s.mem B (slot w 0) w) :
    WP isa wordSteps s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (8 * (w + 1)) s.mem t.mem) ∧ Keep (.a1 :: wordStepRegs) s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  generalize hN : wordsVal s.mem B (slot w 0) w = N at hd hd63 hxN ⊢
  have hN0 : 0 < N := by omega
  unfold wordSteps
  refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun t => t.gpr .a1 = BitVec.ofNat 64 (w + 1) ∧ t.mem = s.mem)
    (by brun [ht0]; exact (BitVec.ofNat_add _ _).symm) (by rfl) (by rfl)) fun s₁ ⟨⟨a1, m1⟩, k1⟩ => ?_)
  let Inv : Nat → State → Prop := fun j t =>
    wordsVal t.mem B (slot w 1) w = 2 ^ (64 * (w - 1) + 64 * j) % N ∧
      Outside B (slot w 1) (8 * (w + 1)) s.mem t.mem ∧ Keep (.a1 :: wordStepRegs) s t
  refine WP.mono (wp_countdown (body := .seq wordStep (.block [.addi .a1 .a1 (-1)])) (cnt := .a1) (N := w + 1)
    (by omega) (by omega) Inv (fun j _ t ⟨tx, to, tk⟩ _ => ?_)
    ⟨by rw [m1, hx, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hxN], by rw [m1]; exact Outside.refl _ _ _ _,
      k1.mono (by decide)⟩ a1)
    fun t ⟨tx, to, tk⟩ => ⟨⟨by rw [tx, show 64 * (w - 1) + 64 * (w + 1) = 128 * w by omega], to⟩, tk⟩
  have g : ∀ r ∈ [Reg.a2, .a6, .a7, .t0, .a4], t.gpr r = s.gpr r := fun r hr => tk.gpr (by revert r hr; decide)
  have n0 : wordsVal t.mem B (slot w 0) w = N := by rw [Outside.wordsVal to (by omega) (by omega), hN]
  have w3 : Mont.word t.mem B (slot w 3) = Mont.word s.mem B (slot w 3) := Outside.word to (by omega) (by omega)
  have w38 : Mont.word t.mem B (slot w 3 + 8) = Mont.word s.mem B (slot w 3 + 8) :=
    Outside.word to (by omega) (by omega)
  have w316 : Mont.word t.mem B (slot w 3 + 16) = Mont.word s.mem B (slot w 3 + 16) :=
    Outside.word to (by omega) (by omega)
  refine WP.seq (WP.mono (wordStep_ok (z := z) (hs.congr tk.2.2) ((g .a2 (by decide)).trans h2)
    ((g .a6 (by decide)).trans h6) ((g .a7 (by decide)).trans h7) ((g .t0 (by decide)).trans ht0)
    ((g .a4 (by decide)).trans h4) hw hw' hZ (by rw [w3]; exact hP) hz (by rw [w38, n0]; exact hd)
    (by rw [n0]; exact hd63) (by rw [w316, w38]; exact hv) (by rw [tx, n0]; exact Nat.mod_lt _ hN0))
    fun t₁ ⟨⟨x1, o1⟩, k1⟩ => ?_)
  refine WP.mono (dec_ok t₁ .a1) fun t₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, by rw [mem_write]; exact Outside.trans to o1,
    ((tk.trans k1).trans (Keep.write _ _ _)).mono (by decide)⟩, ?_⟩
  · rw [mem_write, x1, tx, n0, Nat.mod_mul_mod, ← Nat.pow_add, Nat.mul_succ, Nat.add_assoc]
  · gsimp; rw [k1.gpr (by decide)]

/-- The registers `r2Words` writes. -/
def r2WordsRegs : List Reg := [.a0, .a1, .a3, .a4, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `r2Words`, after `lz` (`a1 = zOf T`, `T` the top word): `x := R² mod n =
2^(128 w) mod n` in array 1, for an odd `n` of `w ≥ 3` words, at least
`2^(64 (w - 1))`, in array 0, changing only arrays 1–3. -/
theorem r2Words_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 (zOf (topW s.mem B w)))
    (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hN : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa r2Words s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep r2WordsRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have hT := topW_pos (by omega) hN
  generalize hTd : topW s.mem B w = T at hT h1
  -- `T`'s bounds: `2^63 ≤ T 2^z < 2^64`.
  have hTl : T < 2 ^ 64 := by rw [← hTd]; exact BitVec.isLt _
  have l1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hT)
  have l2 := Nat.lt_log2_self (n := T)
  have hl : Nat.log2 T < 64 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt l1 hTl)
  have hb1 : 2 ^ 63 ≤ T * 2 ^ (zOf T) := by
    unfold zOf
    calc 2 ^ 63 = 2 ^ Nat.log2 T * 2 ^ (63 - Nat.log2 T) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ T * 2 ^ (63 - Nat.log2 T) := Nat.mul_le_mul_right _ l1
  have hb2 : T * 2 ^ (zOf T) < 2 ^ 64 := by
    unfold zOf
    calc T * 2 ^ (63 - Nat.log2 T) < 2 ^ (Nat.log2 T + 1) * 2 ^ (63 - Nat.log2 T) :=
          Nat.mul_lt_mul_of_pos_right l2 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  generalize hz : zOf T = z at h1 hb1 hb2
  rw [← hTd] at hb1 hb2
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd ⊢
  have hx0 : 2 ^ (64 * (w - 1)) < N := by
    refine Nat.lt_of_le_of_ne hN fun h => ?_
    rw [← h, show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left] at hodd
    exact absurd hodd (by decide)
  unfold r2Words
  -- `P` and `d'`.
  refine WP.seq (WP.mono (normTail_ok hs h6 h7 ht0 h1 (by omega) hw' hZ hb1 hb2)
    fun s₁ ⟨⟨wP, hz63, wD, hD63, s2D, o1⟩, k1⟩ => ?_)
  rw [hNd] at wD hD63
  have g1 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0], s₁.gpr r = s.gpr r := fun r hr => k1.gpr (by revert r hr; decide)
  -- `v`.
  refine WP.seq (WP.mono (recip_ok (hs.congr k1.2.2) ((g1 .a6 (by decide)).trans h6) (by omega)
    (by rw [s2D, wD]; exact hD63)) fun s₂ ⟨⟨wV, a4, o2⟩, k2⟩ => ?_)
  rw [s2D] at wV
  have k12 := k1.trans k2
  have g2 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0], s₂.gpr r = s.gpr r := fun r hr => k12.gpr (by revert r hr; decide)
  -- `x := 2^(64 (w - 1))`.
  refine WP.seq (WP.mono (r2Top_ok (hs.congr k12.2.2) ((g2 .a2 (by decide)).trans h2)
    ((g2 .t0 (by decide)).trans ht0) (by omega) hw' (by omega)) fun s₃ ⟨⟨x3, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have O3 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₃.mem :=
    Outside.trans (Outside.trans (Outside.mono o1 (by omega) (by omega)) (Outside.mono o2 (by omega) (by omega)))
      (Outside.mono o3 (Nat.le_refl _) (by omega))
  have w3 : ∀ d, slot w 3 ≤ d → d + 8 ≤ slot w 4 → Mont.word s₃.mem B d = Mont.word s₂.mem B d := fun d h1 h2 =>
    Outside.word o3 (Or.inr (by omega)) (by omega)
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal O3 (by omega) (by omega), hNd]
  have w38 : Mont.word s₂.mem B (slot w 3 + 8) = Mont.word s₁.mem B (slot w 3 + 8) :=
    Outside.word o2 (Or.inl (by omega)) (by omega)
  have w30 : Mont.word s₂.mem B (slot w 3) = Mont.word s₁.mem B (slot w 3) :=
    Outside.word o2 (Or.inl (by omega)) (by omega)
  -- `w + 1` word steps.
  refine WP.mono (wordSteps_ok (z := z) (hs.congr k13.2.2) ((k13.gpr (by decide)).trans h2)
    ((k13.gpr (by decide)).trans h6) ((k13.gpr (by decide)).trans h7) ((k13.gpr (by decide)).trans ht0)
    ((k3.gpr (by decide)).trans a4) hw hw' hZ
    (by rw [w3 _ (Nat.le_refl _) (by omega), w30]; exact wP) hz63
    (by rw [w3 _ (by omega) (by omega), w38, n3]; exact wD) (by rw [n3]; exact hD63)
    (by rw [w3 _ (by omega) (by omega), w3 _ (by omega) (by omega), w38]; exact wV) x3 (by rw [n3]; exact hx0))
    fun t ⟨⟨tx, to⟩, tk⟩ => ⟨⟨by rw [tx, n3], Outside.trans O3 (Outside.mono to (Nat.le_refl _) (by omega))⟩,
      (k13.trans tk).mono (by decide)⟩

end VG.Proof.Bignum.RISCV64
