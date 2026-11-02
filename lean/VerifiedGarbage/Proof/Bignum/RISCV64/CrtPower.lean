module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtR2
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: `c^d mod p`

`power_ok`: `Crt.power`, in a prime's working space of 24 arrays, as on
PPC64LE (`Proof/Bignum/PPC64LE/{CrtReduce,CrtPowerA,CrtPowerB}.lean`): the
prime from `X`'s array, `-p⁻¹ mod 2⁶⁴` (`minv_ok`), `R² mod p`
(`r2Prime_ok`), `c mod p` (`reduceIn_ok`: a chunk `C_i` of `w` words of `c`
at a time from the bottom, by Montgomery multiplications: with
`q ≡ -R^(i+1)` and `T = C_i q R⁻¹ ≡ -C_i R^i`, `S - T` adds `C_i R^i` to `S`),
then `c^d mod p` (`powWin_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Win

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)

/-! ## The arithmetic -/

/-- `x ≡ 0 (mod p)` from `R x ≡ 0`, for `R` prime to `p`. -/
theorem mod_cancel {R p x : Nat} (hR : Nat.Coprime R p) (h : R * x % p = 0) : x % p = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.Coprime.dvd_of_dvd_mul_left hR.symm (Nat.dvd_of_mod_eq_zero h))

/-- `T ≡ C q R⁻¹` and `q ≡ -R^(i+1)` give `T ≡ -C R^i`. -/
theorem chunk_t {R p T C q i : Nat} (hR : Nat.Coprime R p) (hT : T * R % p = C * q % p)
    (hq : (q + R ^ (i + 1)) % p = 0) : (T + C * R ^ i) % p = 0 := by
  refine mod_cancel hR ?_
  have e : R * (T + C * R ^ i) = T * R + C * (q + R ^ (i + 1)) - C * q := by
    rw [Nat.pow_succ]; grind
  have h1 : (T * R + C * (q + R ^ (i + 1))) % p = (C * q) % p := by
    rw [Nat.add_mod, hT, Nat.mul_mod C (q + R ^ (i + 1)), hq, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  have h2 : C * q ≤ T * R + C * (q + R ^ (i + 1)) := by rw [Nat.mul_add]; omega_arith
  rw [e]
  exact Nat.sub_mod_eq_zero_of_mod_eq h1

/-- `q' ≡ q R² R⁻¹` and `q ≡ -R^(i+1)` give `q' ≡ -R^(i+2)`. -/
theorem chunk_q {R p q q' r2 i : Nat} (hR : Nat.Coprime R p) (hq' : q' * R % p = q * r2 % p)
    (hr2 : r2 % p = R * R % p) (hq : (q + R ^ (i + 1)) % p = 0) : (q' + R ^ (i + 1 + 1)) % p = 0 := by
  refine mod_cancel hR ?_
  have e : R * (q' + R ^ (i + 1 + 1)) = q' * R + R * R * (q + R ^ (i + 1)) - R * R * q := by
    rw [show R ^ (i + 1 + 1) = R ^ (i + 1) * R from Nat.pow_succ _ _]; grind
  have h1 : (q' * R + R * R * (q + R ^ (i + 1))) % p = (R * R * q) % p := by
    rw [Nat.add_mod, hq', Nat.mul_mod (R * R) (q + R ^ (i + 1)), hq, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.mod_mod, Nat.mul_mod q r2, hr2, ← Nat.mul_mod, Nat.mul_comm]
  have h2 : R * R * q ≤ q' * R + R * R * (q + R ^ (i + 1)) := by rw [Nat.mul_add]; omega_arith
  rw [e]
  exact Nat.sub_mod_eq_zero_of_mod_eq h1

/-- `q₀ ≡ (p - 1) R² R⁻¹ ≡ -R`. -/
theorem chunk_q0 {R p q r2 : Nat} (hR : Nat.Coprime R p) (hp : 1 ≤ p) (hq : q * R % p = r2 * (p - 1) % p)
    (hr2 : r2 % p = R * R % p) : (q + R ^ (0 + 1)) % p = 0 := by
  refine mod_cancel hR ?_
  have e : R * (q + R ^ (0 + 1)) + R * R * (p - 1) = q * R + R * R * p := by
    rw [Nat.zero_add, Nat.pow_one]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega_arith⟩
    rw [Nat.add_sub_cancel]; grind
  have h1 : (q * R + R * R * p) % p = (R * R * (p - 1)) % p := by
    rw [Nat.add_mod, hq, Nat.mul_mod (R * R) p, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod,
      Nat.mul_mod r2, hr2, ← Nat.mul_mod, Nat.mul_comm]
  rw [← e] at h1
  have := Nat.sub_mod_eq_zero_of_mod_eq h1
  rwa [Nat.add_sub_cancel] at this

/-- `S' = (S + p - T) mod p` adds `C R^i` to `S` when `T ≡ -C R^i`. -/
theorem chunk_s {p S T A C Ri S' : Nat} (hT : T < p) (hS : S % p = A % p) (hTC : (T + C * Ri) % p = 0)
    (hS' : S' = (S + p - T) % p) : S' % p = (A + Ri * C) % p := by
  rw [hS', Nat.mod_mod]
  have e : (S + p - T + (T + C * Ri)) % p = (A + Ri * C) % p := by
    rw [show S + p - T + (T + C * Ri) = S + C * Ri + p by omega_arith, Nat.add_mod_right, Nat.add_mod, hS,
      ← Nat.add_mod, Nat.mul_comm]
  rw [Nat.add_mod, hTC, Nat.add_zero, Nat.mod_mod] at e
  exact e

/-- `subMod64` and `addMask64`'s `S - T`, `p` added back under the borrow:
`(S + p - T) mod p`, for `S, T < p < R`. -/
theorem sub_add_mod {S T N D c R : Nat} (hS : S < N) (hT : T < N) (hN : N < R) (hD : D < R) (hc : c ≤ 1)
    (h : D + T = S + R * c) : (D + (if 0 < c then N else 0)) % R = (S + N - T) % N := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp only [Nat.lt_irrefl, ↓reduceIte, Nat.add_zero]
    rw [Nat.mul_zero, Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt (show D < R by omega), show S + N - T = D + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show D < N by omega)]
  · simp only [Nat.zero_lt_one, ↓reduceIte]
    rw [Nat.mul_one] at h
    rw [show D + N = S + N - T + R by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show S + N - T < R by omega),
      Nat.mod_eq_of_lt (show S + N - T < N by omega)]

/-- The number of chunks of `w` words of `K` words. -/
abbrev nChunks (K w : Nat) : Nat := (K + w - 1) / w

theorem lt_nChunks {K w m : Nat} (hw : 1 ≤ w) : m < nChunks K w ↔ m * w < K := by
  unfold nChunks
  rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by omega_arith), Nat.succ_mul]
  omega_arith

theorem nChunks_pos {K w : Nat} (hw : 1 ≤ w) (hK : 1 ≤ K) : 0 < nChunks K w :=
  (lt_nChunks hw).mpr (by rw [Nat.zero_mul]; omega_arith)

theorem le_nChunks_mul {K w : Nat} (hw : 1 ≤ w) : K ≤ nChunks K w * w := by
  have := mt (lt_nChunks (K := K) (m := nChunks K w) hw).mpr (Nat.lt_irrefl _)
  omega_arith

theorem nChunks_mul_lt {K w : Nat} (hw : 1 ≤ w) (hK : 1 ≤ K) : nChunks K w * w < K + w := by
  have h := (lt_nChunks (K := K) (m := nChunks K w - 1) hw).mp (by have := nChunks_pos hw hK; omega_arith)
  have e : nChunks K w * w = (nChunks K w - 1) * w + w := by
    have := nChunks_pos hw hK
    rw [← Nat.succ_mul]; congr 1; omega_arith
  omega_arith

/-- `t2 := ((s10 - 1) >> 63) ^ 1`: 1 if `s10` is in `[1, 2^63]`. -/
theorem flag_ne_zero (x : BitVec 64) :
    ((x - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1).toNat ≠ 0 ↔ x.toNat ≠ 0 ∧ x.toNat ≤ 2 ^ 63 := by
  have h : ((x - BitVec.ofNat 64 1) >>> 63).toNat = if x.toNat ≠ 0 ∧ x.toNat ≤ 2 ^ 63 then 0 else 1 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    have := x.isLt
    simp only [BitVec.toNat_ofNat]
    split <;> omega_arith
  have hy : ∀ y : BitVec 64, y.toNat = 0 ∨ y.toNat = 1 → ((y ^^^ BitVec.ofNat 64 1).toNat ≠ 0 ↔ y.toNat = 0) := by
    intro y hy
    rcases hy with h0 | h1
    · have : y = 0#64 := BitVec.eq_of_toNat_eq h0
      subst this; decide
    · have : y = 1#64 := BitVec.eq_of_toNat_eq h1
      subst this; decide
  rw [hy _ (by rw [h]; split <;> simp), h]
  split <;> simp_all

/-- The words left after `j + 1` chunks, as `s10` holds them. -/
theorem flag_iff {K w j : Nat} (hw : 1 ≤ w) (hK : 1 ≤ K) (hK' : K < 2 ^ 40) (hw' : w < 2 ^ 40)
    (hj : j < nChunks K w) :
    let x := BitVec.ofNat 64 K - BitVec.ofNat 64 (w * (j + 1))
    (x.toNat ≠ 0 ∧ x.toNat ≤ 2 ^ 63) ↔ j + 1 ≠ nChunks K w := by
  intro x
  have hm := nChunks_mul_lt hw hK
  have hjw : (j + 1) * w ≤ nChunks K w * w := Nat.mul_le_mul_right _ hj
  have hc := (lt_nChunks (K := K) (m := j + 1) hw)
  have e : w * (j + 1) = (j + 1) * w := Nat.mul_comm _ _
  have hx : x.toNat = (2 ^ 64 - (j + 1) * w % 2 ^ 64 + K % 2 ^ 64) % 2 ^ 64 := by
    show (BitVec.ofNat 64 K - BitVec.ofNat 64 (w * (j + 1))).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e]
  rw [hx]
  constructor
  · intro ⟨h1, h2⟩ hn
    rw [hn] at hc
    have := le_nChunks_mul (K := K) hw
    rw [← hn] at this
    omega_arith
  · intro hn
    have hlt : (j + 1) * w < K := hc.mp (by omega_arith)
    omega_arith

/-! ## Memory -/

/-- Equal words, equal numbers. -/
theorem wv_words {m m' : Mem} {B B' : Addr} :
    ∀ {d d' k : Nat}, (∀ i < k, Mont.word m' B' (d' + 8 * i) = Mont.word m B (d + 8 * i)) →
      wordsVal m' B' d' k = wordsVal m B d k
  | _, _, 0, _ => rfl
  | d, d', k + 1, h => by
    simp only [wordsVal]
    have h0 := h 0 (by omega_arith)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, wv_words (d := d + 8) (d' := d' + 8) fun i hi => by
      rw [show d' + 8 + 8 * i = d' + 8 * (i + 1) by omega_arith, show d + 8 + 8 * i = d + 8 * (i + 1) by omega_arith]
      exact h (i + 1) (by omega_arith)]

/-- A number of `X`, apart from the prime's working space, after code that
wrote only its arrays. -/
theorem x_wv {B BX : Addr} {Z ZX w : Nat} {m m' : Mem} (o : WinO B w m m')
    (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x) (hZ : slot w 24 ≤ Z) (hX : BX.toNat + ZX ≤ 2 ^ 64) :
    ∀ {d k : Nat}, d + 8 * k ≤ ZX → wordsVal m' BX d k = wordsVal m BX d k
  | _, 0, _ => rfl
  | d, k + 1, hd => by
    simp only [wordsVal]
    have e24 := slot24 w
    rw [Outside.word_sep o hsep (by omega_arith) (show d + 8 ≤ ZX by omega_arith) hX,
      x_wv o hsep hZ hX (d := d + 8) (k := k) (by omega_arith)]

/-- A number of `X` after code that wrote only the prime's working space. -/
theorem x_wv' {B BX : Addr} {Z ZX o n : Nat} {m m' : Mem} (h : Outside B o n m m')
    (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x) (hon : o + n ≤ Z) (hX : BX.toNat + ZX ≤ 2 ^ 64) :
    ∀ {d k : Nat}, d + 8 * k ≤ ZX → wordsVal m' BX d k = wordsVal m BX d k
  | _, 0, _ => rfl
  | d, k + 1, hd => by
    simp only [wordsVal]
    rw [Outside.word_sep h hsep hon (show d + 8 ≤ ZX by omega_arith) hX,
      x_wv' h hsep hon hX (d := d + 8) (k := k) (by omega_arith)]

/-- An array apart from one that changed in its `n ≤ 8 (w + 2)` bytes. -/
theorem arr_n {B : Addr} {w o j n : Nat} {m m' : Mem} (h : Outside B (slot w o) n m m') (hn : n ≤ 8 * (w + 2))
    (hj : j < 24) (hne : j ≠ o) (hN : B.toNat + slot w 24 ≤ 2 ^ 64) : A m' B w j = A m B w j :=
  arr_eq (arr1 h hn) hj (by simp; omega_arith) hN

theorem arrO_n {B : Addr} {w o n : Nat} {m m' : Mem} (h : Outside B (slot w o) n m m') (hn : n ≤ 8 * (w + 2))
    (h1 : 1 ≤ o) (h24 : o < 24) : WinO B w m m' :=
  win_of_arrays (arr1 h hn) (by simp; omega_arith)

/-- `copyWords` within the working space, between ranges apart. -/
theorem copySame_ok {s : State} {B : Addr} {Z dS dD w : Nat} (hs : Scr s B Z)
    (h4 : s.gpr .t4 = off B dS) (h3 : s.gpr .t3 = off B dD) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0) (hS : dS + 8 * w ≤ Z)
    (hD : dD + 8 * w ≤ Z) (hsep : dS + 8 * w ≤ dD ∨ dD + 8 * w ≤ dS) :
    WP isa Precompute.copyWords s fun t =>
      ((∀ i < w, word t.mem B (dD + 8 * i) = word s.mem B (dS + 8 * i)) ∧
        Outside B dD (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  unfold Precompute.copyWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h0, add_ofNat_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i5, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dD + 8 * i) ∧ t.gpr .t4 = off B (dS + 8 * i) ∧ Outside B dD (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (dD + 8 * k) = word s.mem B (dS + 8 * k)) ∧ Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith)
      (by omega_arith) Inv (fun i hi t ⟨j3, j4, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr (r := .t3) (by decide), h3]; rfl, by rw [k₁.gpr (r := .t4) (by decide), h4]; rfl,
      by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), k₁.mono (by decide)⟩ i5)
    fun t ⟨_, _, tout, tc, tk⟩ => ⟨⟨tc, tout⟩, tk⟩
  have hsrc : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) :=
    Outside.word jout (by omega_arith) (by omega_arith)
  have hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
      .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ (t.write .s0 (word t.mem B (dS + 8 * i))) with
        mem := t.mem.writeW (off B (dD + 8 * i)) (word t.mem B (dS + 8 * i)) } :
        State).write .t3 (off B (dD + 8 * i + 8))).write .t4
          (off B (dS + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
    brun [j3, j4, (hs.congr jk.2.2).ld (show dS + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).st (show dD + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show dS + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      (hs.congr jk.2.2).al8 (show dD + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := dD + 8 * i) (word t.mem B (dS + 8 * i)) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega_arith],
    by gsimp; rw [show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsrc]
  · exact Keep.trans' jk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

theorem xb_cons (rd : Reg) (j : Nat) : Crt.xb rd (j + 1) = Crt.xb rd j ++ ([.add rd rd .s11] : List Instr) := by
  simp only [Crt.xb, List.replicate_succ', List.cons_append]

/-- `xb rd j`: the base of `X`'s array `j`, `X` at `s6` and its arrays' size
in `s11`. -/
theorem xbase_ok {t : State} {BX : Addr} {w : Nat} {rd : Reg} (hrd : rd ≠ .s11)
    (h6 : t.gpr .s6 = BX) (h11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (Crt.xb rd j)) t fun t' =>
      (t'.gpr rd = off BX (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    simp only [Crt.xb, List.replicate_zero]
    apply WP.of_runBlock
    refine ⟨t.write rd (off BX (slot w 0)), ?_, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
    rw [runBlock_cons, exec_addi_nat (show hdrBytes < 2048 by decide), runStep_some, runBlock_nil, h6]
    simp [off, slot]
  | j + 1 => by
    rw [xb_cons, WP.block_append_iff]
    refine WP.mono (xbase_ok hrd h6 h11 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr (r := .s11) (by simpa using Ne.symm hrd)).trans h11]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega_arith]

/-- The top word of array `j`, `w` past its base, := 0. -/
theorem top0_ok {t : State} {B : Addr} {Z w j N : Nat} (h : WCtx t B Z w N) (hj : j < 24) :
    WP isa (.block (base .t3 j ++ ([.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0] : List Instr))) t
      fun u => (u.mem = t.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64)) ∧ Keep [.t3, .s0] t u := by
  have hn := h.nw
  have sl := h.sl hj
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 j) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  have e16 : off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w j + 8 * w) := by
    rw [off_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith),
      show slot w j + 8 * (w + 2) - 16 = slot w j + 8 * w by omega_arith]
  have hs₁ := h.scr.congr k1.2.2
  refine WP.mono (WP.keep [.t3, .s0] (Q := fun u => u.mem = t₁.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64))
    (by brun [a3, (k1.gpr (r := .s5) (by decide)).trans h.s5, off_add, e16, Pub.pub_li0,
      hs₁.st (show slot w j + 8 * w + 8 ≤ Z by omega_arith),
      hs₁.al8 (show slot w j + 8 * w + 8 ≤ Z by omega_arith) (by have := slot_al w j; omega_arith)]; rfl)
    (by rfl) (by rfl)) fun u ⟨um, k2⟩ => ⟨by rw [um, m1], (k1.trans k2).mono (by decide)⟩

/-- The context after code that wrote `a7` but put back array 0's base. -/
theorem WCtx.of7 {s t : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ [Reg.s5, .t0, .t1], r ∉ rs) (h7 : t.gpr .a7 = off B (slot w 0)) (o : WinO B w s.mem t.mem) :
    WCtx t B Z w N := by
  have hn := h.nw
  have s0 := slot_lt (w := w) (show 0 < 24 by decide)
  have e1 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega_arith
  refine ⟨h.scr.congr k.2.2, h.w2, h.w31, h.hZ, h7, (k.gpr (hrs .s5 (by decide))).trans h.s5,
    (k.gpr (hrs .t0 (by decide))).trans h.t0, ?_, ?_⟩
  · have hw0 : Mont.word t.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
      Outside.word o (Or.inl (by omega_using [e1, s0])) (by omega_using [hn, s0])
    rw [k.gpr (hrs .t1 (by decide)), hw0]
    exact h.inv
  · rw [← h.n]
    exact Outside.wordsVal o (Or.inl (by omega_arith)) (by omega_arith)

/-! ## A chunk -/

/-- The registers `reduceIn` writes. -/
def redRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s9, .s10]

/-- Between the chunks of `reduceIn`, after `i` of them: in `p`'s working
space at `B` (`N`), `R² mod p` (`R2`), `p - 1`, `q ≡ -R^(i+1)` in array 5
and `S ≡` the first `w i` words of `X`'s array 6 (at `BX`) in array 4; the
next chunk at `s9`, the words left in `s10`. -/
structure ChunkI (s : State) (B BX : Addr) (Z w wX K N R2 i : Nat) (t : State) : Prop where
  ctx : WCtx t B Z w N
  ra : t.gpr .ra = off B (slot w 0)
  s9 : t.gpr .s9 = off BX (slot wX 6 + 8 * (w * i))
  s10 : t.gpr .s10 = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * i)
  p1 : A t.mem B w 1 = R2
  p8 : A t.mem B w 8 = N - 1
  qlt : A t.mem B w 5 < N
  q : (A t.mem B w 5 + (2 ^ (64 * w)) ^ (i + 1)) % N = 0
  slt : A t.mem B w 4 < N
  sv : A t.mem B w 4 % N = wordsVal s.mem BX (slot wX 6) (w * i) % N
  fix : ∀ j < 24, 8 < j → A t.mem B w j = A s.mem B w j
  out : WinO B w s.mem t.mem
  keep : Keep redRegs s t

theorem sub_flag (K a w : Nat) :
    BitVec.ofNat 64 K - BitVec.ofNat 64 a - BitVec.ofNat 64 w = BitVec.ofNat 64 K - BitVec.ofNat 64 (a + w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- One chunk. -/
theorem chunkStep_ok {s t : State} {B BX : Addr} {Z ZX w wX K N R2 i : Nat} (hx : Scr s BX ZX)
    (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x) (hX : slot wX 6 + 8 * (w * nChunks K w) ≤ ZX)
    (hK : 1 ≤ K) (hK' : K < 2 ^ 40) (hodd : N % 2 = 1) (hR2 : R2 < N)
    (hR2' : R2 % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N) (hi : i < nChunks K w)
    (I : ChunkI s B BX Z w wX K N R2 i t) :
    WP isa Crt.chunkStep t fun u => ChunkI s B BX Z w wX K N R2 (i + 1) u ∧
      ((u.gpr .t2).toNat ≠ 0 ↔ i + 1 ≠ nChunks K w) := by
  have h := I.ctx
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  have hxt := hx.congr I.keep.2.2
  have hxn := hx.nowrap
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hwi : w * i + w ≤ w * nChunks K w := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have hNR : N < 2 ^ (64 * w) := h.n ▸ wordsVal_lt _ _ _ _
  have e24 := slot24 w
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have s34 := slot_lt (w := w) (show 3 < 4 by decide)
  have s37 := slot_lt (w := w) (show 3 < 7 by decide)
  have s03 := slot_lt (w := w) (show 0 < 3 by decide)
  have s45 := slot_lt (w := w) (show 4 < 5 by decide)
  have s424 := slot_lt (w := w) (show 4 < 24 by decide)
  unfold Crt.chunkStep
  -- The chunk into array 6, and `s9` past it.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 6) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = t₁.gpr .s9 ∧ u.mem = t₁.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : t₂.mem = t.mem := by rw [m2, m1]
  have hx2 := hxt.congr k12.2.2
  refine WP.seq (WP.mono (Pub.copyIn_ok (B := B) (P := BX) (Zp := ZX) (dS := slot wX 6 + 8 * (w * i))
    (dD := slot w 6) (w := w) (h.scr.congr k12.2.2) hxn (fun j hj => hx2.ld (by omega_arith))
    (fun j hj => hx2.al8 (by omega_arith) (by have := slot_al wX 6; omega_arith))
    (by rw [a4, k1.gpr (by decide), I.s9]) ((k2.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans h.t0)
    (by omega_arith) hw' (slot_al w 6) (by omega_arith) (by have := sl 6 (by decide); omega_arith) hsep)
    fun t₃ ⟨⟨_, a4', c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  refine WP.seq (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = t₃.gpr .t4 ∧ u.mem = t₃.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun t₄ ⟨⟨a9, m4⟩, k4⟩ => ?_)
  have k14 := (k12.trans k3).trans k4
  have o4 : Outside B (slot w 6) (8 * w) t.mem t₄.mem := by rw [m4]; exact o3
  have c4 := h.of k14 (by decide) (arrO o4 (by decide) (by decide))
  have v6 : A t₄.mem B w 6 = wordsVal s.mem BX (slot wX 6 + 8 * (w * i)) w := by
    show wordsVal _ _ _ _ = _
    rw [m4, wv_words c3]
    exact x_wv I.out hsep h.hZ hxn (by omega_arith)
  have u4 : ∀ j < 24, j ≠ 6 → A t₄.mem B w j = A t.mem B w j := fun j hj hne => arr_out o4 hj hne hn
  -- `T := C q R⁻¹`.
  refine WP.seq (WP.mono (c4.mont (o := 7) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [u4 5 (by decide) (by decide)]; exact I.qlt))
    fun t₅ ⟨⟨c5, l5, e5, v5, o5⟩, k5⟩ => ?_)
  rw [v6, u4 5 (by decide) (by decide)] at e5
  -- `q := q R² R⁻¹`.
  have b1 : A t₅.mem B w 1 = R2 := by
    rw [v5 1 (by decide) (by decide) (by decide) (by decide), u4 1 (by decide) (by decide), I.p1]
  refine WP.seq (WP.mono (c5.mont (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [b1]; exact hR2))
    fun t₆ ⟨⟨c6, l6, e6, v6', o6⟩, k6⟩ => ?_)
  rw [b1, v5 5 (by decide) (by decide) (by decide) (by decide), u4 5 (by decide) (by decide)] at e6
  -- `S - T` into array 3.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (top0_ok c6 (j := 4) (by decide)) fun t₇ ⟨m7, k7⟩ => ?_
  have ow7 : Outside B (slot w 4) (8 * (w + 1)) t₆.mem t₇.mem := by
    rw [m7]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
  have c7 := c6.of k7 (by decide) (arrO_n ow7 (by omega_arith) (by decide) (by decide))
  have u7 : ∀ j < 24, j ≠ 4 → A t₇.mem B w j = A t₆.mem B w j := fun j hj hne => arr_n ow7 (by omega_arith) hj hne hn
  have s7 : A t₇.mem B w 4 = A t₆.mem B w 4 := by
    rw [m7]; exact Outside.wordsVal (writeW_outside _ _ _ (by omega_arith)) (Or.inl (Nat.le_refl _)) (by omega_arith)
  have top7 : Mont.word t₇.mem B (slot w 4 + 8 * w) = 0 := by rw [m7]; exact word_writeW_self _ _ _ _
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) c7.a7 c7.s5 4) fun t₈ ⟨⟨a5, m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k8.gpr (by decide)).trans c7.a7)
    ((k8.gpr (by decide)).trans c7.s5) 3) fun t₉ ⟨⟨a6, m9⟩, k9⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a7) (by decide) ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans c7.a7))
    ((k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans c7.s5)) 7) fun t₁₀ ⟨⟨a7, m10⟩, k10⟩ => ?_
  have hm10 : t₁₀.mem = t₇.mem := by rw [m10, m9, m8]
  have k810 := (k8.trans k9).trans k10
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 4) (dT := slot w 3) (dM := slot w 7)
    (c7.scr.congr k810.2.2) ((k10.gpr (by decide)).trans ((k9.gpr (by decide)).trans a5))
    ((k10.gpr (by decide)).trans a6) a7 ((k810.gpr (by decide)).trans c7.t0) (by omega_arith) hw'
    (slot_al w 4) (slot_al w 3) (slot_al w 7) (by have := sl 4 (by decide); omega_arith)
    (by have := sl 3 (by decide); omega_arith) (by have := sl 7 (by decide); omega_arith)
    (Or.inl (by omega_arith)) (Or.inl (by omega_arith))) fun t₁₁ ⟨⟨c, hc, hD, h4⟩, o11, k11⟩ => ?_)
  rw [hm10] at hD h4 o11
  rw [top7] at h4
  have k711 := (k7.trans k810).trans k11
  have ra11 : t₁₁.gpr .ra = off B (slot w 0) := by
    rw [k711.gpr (by decide), k6.gpr (by decide), k5.gpr (by decide), k14.gpr (by decide), I.ra]
  -- `p` added back under the borrow.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7] (Q := fun u => u.gpr .a7 = off B (slot w 0) ∧ u.mem = t₁₁.mem)
    (by brun [ra11, BitVec.add_zero]) (by rfl) (by rfl)) fun t₁₂ ⟨⟨b7, m12⟩, k12'⟩ => ?_
  have o12 : WinO B w t₇.mem t₁₂.mem := by rw [m12]; exact arrO o11 (by decide) (by decide)
  have c12 : WCtx t₁₂ B Z w N := by
    exact c7.of7 ((k810.trans k11).trans k12') (by decide) b7 o12
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c12.a7 c12.s5 3) fun t₁₃ ⟨⟨b3, m13⟩, k13⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k13.gpr (by decide)).trans c12.a7)
    ((k13.gpr (by decide)).trans c12.s5) 0) fun t₁₄ ⟨⟨b4, m14⟩, k14'⟩ => ?_
  have k1314 := k13.trans k14'
  have hm14 : t₁₄.mem = t₁₂.mem := by rw [m14, m13]
  have c14 := c12.regs k1314 (by decide) hm14
  have hm : t₁₄.gpr .s4 = if decide (0 < c) then BitVec.allOnes 64 else 0 := by
    rw [k1314.gpr (by decide), k12'.gpr (by decide), h4]; simp
  refine WP.seq (WP.mono (ModArith.addMask64_ok (b := decide (0 < c)) c14.scr ((k14'.gpr (by decide)).trans b3) b4
    c14.t0 hm (slot_al w 3) (slot_al w 0) (by omega_arith) hw' (by have := sl 3 (by decide); omega_arith)
    (by have := sl 0 (by decide); omega_arith) (Or.inr (by omega_arith))) fun t₁₅ ⟨d15, o15, k15⟩ => ?_)
  rw [hm14, m12] at d15
  rw [hm14] at o15
  have c15 := c14.of k15 (by decide) (by rw [hm14]; exact arrO o15 (by decide) (by decide))
  -- Back into array 4.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c15.a7 c15.s5 4) fun t₁₆ ⟨⟨d3, m16⟩, k16⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k16.gpr (by decide)).trans c15.a7)
    ((k16.gpr (by decide)).trans c15.s5) 3) fun t₁₇ ⟨⟨d4, m17⟩, k17⟩ => ?_
  have k1617 := k16.trans k17
  have hm17 : t₁₇.mem = t₁₅.mem := by rw [m17, m16]
  have c17 := c15.regs k1617 (by decide) hm17
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 3) (dD := slot w 4) c17.scr d4 ((k17.gpr (by decide)).trans d3)
    c17.t0 (by omega_arith) hw' (slot_al w 3) (slot_al w 4) (by have := sl 3 (by decide); omega_arith)
    (by have := sl 4 (by decide); omega_arith) (Or.inl (by omega_arith))) fun t₁₈ ⟨⟨c18, o18⟩, k18⟩ => ?_)
  rw [hm17] at c18 o18
  have c18' := c17.of k18 (by decide) (by rw [hm17]; exact arrO o18 (by decide) (by decide))
  -- The count.
  refine WP.mono (WP.keep [.s10, .t2] (Q := fun u => u.gpr .s10 = t₁₈.gpr .s10 - BitVec.ofNat 64 w ∧
      u.gpr .t2 = (t₁₈.gpr .s10 - BitVec.ofNat 64 w - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 ∧
      u.mem = t₁₈.mem)
    (by brun [c18'.t0]) (by rfl) (by rfl)) fun u ⟨⟨f10, f2, mu⟩, kf⟩ => ?_
  have cu := c18'.regs kf (by decide) mu
  have kpost := ((((((((k5.trans k6).trans k711).trans k12').trans k1314).trans k15).trans k1617).trans k18).trans kf)
  -- The arrays.
  have hU : ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 → A u.mem B w j = A t.mem B w j := by
    intro j hj h2 h3 h4' h5 h6 h7
    rw [mu, arr_out o18 hj h4' hn, arr_out o15 hj h3 hn, m12, arr_out o11 hj h3 hn, u7 j hj h4',
      v6' j hj h2 h3 h5, v5 j hj h2 h3 h7, u4 j hj h6]
  have hq5 : A u.mem B w 5 = A t₆.mem B w 5 := by
    rw [mu, arr_out o18 (by decide) (by decide) hn, arr_out o15 (by decide) (by decide) hn, m12,
      arr_out o11 (by decide) (by decide) hn, u7 5 (by decide) (by decide)]
  have hT : A t₇.mem B w 7 = A t₅.mem B w 7 := by
    rw [u7 7 (by decide) (by decide), v6' 7 (by decide) (by decide) (by decide) (by decide)]
  have hS : A t₇.mem B w 4 = A t.mem B w 4 := by
    rw [s7, v6' 4 (by decide) (by decide) (by decide) (by decide), v5 4 (by decide) (by decide) (by decide) (by decide),
      u4 4 (by decide) (by decide)]
  have hN11 : wordsVal t₁₁.mem B (slot w 0) w = N := by
    rw [← c7.n]; exact arr_out o11 (by decide) (by decide) hn
  have hSn : A u.mem B w 4 = (A t.mem B w 4 + N - A t₅.mem B w 7) % N := by
    show wordsVal _ _ _ _ = _
    rw [mu, wv_words c18, d15, hN11]
    simp only [decide_eq_true_eq]
    replace hD : wordsVal t₁₁.mem B (slot w 3) w + A t₇.mem B w 7 = A t₇.mem B w 4 + 2 ^ (64 * w) * c := hD
    rw [hT, hS] at hD
    exact sub_add_mod I.slt l5 hNR (wordsVal_lt _ _ _ _) hc hD
  have hwi1 : w * (i + 1) = w * i + w := Nat.mul_succ _ _
  have hpow : (2 ^ (64 * w)) ^ i = 2 ^ (64 * (w * i)) := by rw [← Nat.pow_mul, Nat.mul_assoc]
  refine ⟨⟨cu, ?_, ?_, ?_, ?_, ?_, by rw [hq5]; exact l6, by rw [hq5]; exact chunk_q hR e6 hR2' I.q,
    by rw [hSn]; exact Nat.mod_lt _ (by omega_arith), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kpost.gpr (by decide), k14.gpr (by decide), I.ra]
  · rw [kpost.gpr (by decide), a9, a4', hwi1, Nat.mul_add, Nat.add_assoc]
  · rw [f10, (((((((k5.trans k6).trans k711).trans k12').trans k1314).trans k15).trans k1617).trans k18).gpr
      (by decide), k14.gpr (by decide), I.s10, sub_flag, hwi1]
  · rw [hU 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I.p1]
  · rw [hU 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I.p8]
  · rw [hwi1, fios_wordsVal_append, ← hpow]
    exact chunk_s l5 I.sv (chunk_t hR e5 I.q) hSn
  · intro j hj h8
    rw [hU j hj (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
    exact I.fix j hj h8
  · rw [mu]
    refine I.out.trans ((((((arrO o4 (by decide) (by decide)).trans o5).trans o6).trans
      (arrO_n ow7 (by omega_arith) (by decide) (by decide))).trans o12).trans ?_)
    exact ((arrO o15 (by decide) (by decide))).trans (arrO o18 (by decide) (by decide))
  · refine Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within
      (Keep.within (Keep.within (Keep.within I.keep k1 (by decide)) k2 (by decide)) k3 (by decide)) k4 (by decide))
      k5 (by decide)) k6 (by decide)) k711 (by decide)) k12' (by decide)) k1314 (by decide)) k15 (by decide))
      ((k1617.trans k18).trans kf) (by decide)
  · rw [f2, flag_ne_zero, (((((((k5.trans k6).trans k711).trans k12').trans k1314).trans k15).trans k1617).trans
      k18).gpr (by decide), k14.gpr (by decide), I.s10, sub_flag, ← hwi1]
    exact flag_iff (by omega_arith) hK hK' (by omega_arith) hi


/-! ## The reduction -/

/-- `p - 1` from `p` (odd) in array 8: its low word less 1. -/
theorem pm1_ok {t : State} {B : Addr} {Z w N : Nat} (hs : Scr t B Z) (hZ : slot w 9 ≤ Z) (hw : 1 ≤ w)
    (h3 : t.gpr .t3 = off B (slot w 8)) (h8 : A t.mem B w 8 = N) (hodd : N % 2 = 1) :
    WP isa (.block [.load .d .s0 .t3 0, .addi .s0 .s0 (-1), .store .d .s0 .t3 0]) t fun u =>
      (A u.mem B w 8 = N - 1 ∧ Outside B (slot w 8) 8 t.mem u.mem) ∧ Keep [.s0] t u := by
  have hn := hs.nowrap
  have s89 := slot_lt (w := w) (show 8 < 9 by decide)
  have s8 : slot w 8 + 8 ≤ Z := by omega_arith
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h3, BitVec.add_zero, hs.ld s8, hs.st s8, hs.al8 s8 (slot_al w 8)]
  have ow := writeW_outside t.mem B (d := slot w 8) (Mont.word t.mem B (slot w 8) - BitVec.ofNat 64 1) (by omega_arith)
  refine ⟨?_, ow⟩
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega_arith⟩
  show wordsVal _ _ _ _ = _
  rw [← h8]
  simp only [wordsVal]
  rw [VG.Proof.Mont.word_writeW_self, Outside.wordsVal ow (Or.inr (by omega_arith)) (by omega_arith)]
  have hlow : (Mont.word t.mem B (slot (w' + 1) 8)).toNat % 2 = 1 := by
    rw [← h8] at hodd
    simp only [wordsVal] at hodd
    omega_arith
  change (t.mem.readW (off B (slot (w' + 1) 8)) 64).toNat % 2 = 1 at hlow
  change (t.mem.readW (off B (slot (w' + 1) 8)) 64 - 1#64).toNat + _ = (t.mem.readW (off B (slot (w' + 1) 8)) 64).toNat + _ - 1
  generalize t.mem.readW (off B (slot (w' + 1) 8)) 64 = x at hlow ⊢
  have hx : (x - BitVec.ofNat 64 1).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := x.isLt; omega_arith
  rw [hx]
  omega_arith

theorem chunks_count (k : Nat) (hk : k < 2 ^ 40) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- `reduceIn` with `c` in place of its loop of chunks. -/
abbrev reduceInP (c : Prog isa) : Prog isa :=
  .seq (.block (base .t3 8 ++ [.addi .t4 .a7 0])) (.seq Crt.copyN
  (.seq (.block (base .t3 8 ++ [.load .d .s0 .t3 0, .addi .s0 .s0 (-1), .store .d .s0 .t3 0]))
  (.seq (montOp 5 1 8) (.seq (.block (base .t3 4)) (.seq Precompute.zeroWords
  (.seq (.block (Crt.xb .s9 6 ++ [.load .d .s10 .s6 Crt.oNLen, .addi .s10 .s10 7, .shift .srl .d .s10 .s10 3])) c))))))

theorem reduceInP_loop : reduceInP (.loop Crt.chunkStep (.nonzero .t2)) = Crt.reduceIn := rfl

/-- `reduceIn` up to its chunks: the first chunk's invariant. -/
theorem reduceInA_ok {s : State} {B BX : Addr} {Z ZX w wX k N : Nat} (h : WCtx s B Z w N)
    (hra : s.gpr .ra = off B (slot w 0)) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hkw : Mont.word s.mem BX Crt.oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hXZ : slot wX 6 + 8 * (w * nChunks ((k + 7) / 8) w) ≤ ZX) (hN : 2 ≤ N) (hodd : N % 2 = 1)
    (hR2 : A s.mem B w 1 = 2 ^ (128 * w) % N)
    {c : Prog isa} {Q : State → Prop}
    (hc : ∀ u, ChunkI s B BX Z w wX ((k + 7) / 8) N (A s.mem B w 1) 0 u → WP isa c u Q) :
    WP isa (reduceInP c) s Q := by
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  have hxn := hx.nowrap
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have e24 := slot24 w
  have sl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  have s08 := slot_lt (w := w) (show 0 < 8 by decide)
  have s424 := slot_lt (w := w) (show 4 < 24 by decide)
  have hX0 : 256 ≤ slot wX 6 := by unfold slot hdrBytes; omega_arith
  have hR2' : 2 ^ (128 * w) % N % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [Nat.mod_mod, ← Nat.pow_add]; congr 2; omega_arith
  generalize hKd : (k + 7) / 8 = K at hXZ hc
  have hK1 : 1 ≤ K := by omega_arith
  have hK' : K < 2 ^ 40 := by omega_arith
  unfold reduceInP
  -- `p` into array 8.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 8) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = off B (slot w 0) ∧ u.mem = s₁.mem)
    (by brun [(k1.gpr (by decide)).trans h.a7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have c2 := h.regs k12 (by decide) hm2
  refine WP.seq (WP.mono (copySame_ok (dS := slot w 0) (dD := slot w 8) c2.scr a4 ((k2.gpr (by decide)).trans a3)
    c2.t0 (by omega_arith) hw' (slot_al w 0) (slot_al w 8) (by have := sl 0 (by decide); omega_arith)
    (by have := sl 8 (by decide); omega_arith) (Or.inl (by omega_arith))) fun s₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  have c3' := c2.of k3 (by decide) (by rw [hm2]; exact arrO o3 (by decide) (by decide))
  have v8 : A s₃.mem B w 8 = N := by
    show wordsVal _ _ _ _ = _
    rw [wv_words c3]; exact h.n
  -- `p - 1`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) c3'.a7 c3'.s5 8) fun s₄ ⟨⟨b3, m4⟩, k4⟩ => ?_
  refine WP.mono (pm1_ok (c3'.scr.congr k4.2.2) (by have := sl 9 (by decide); omega_arith) (by omega_arith) b3
    (by rw [m4]; exact v8) hodd) fun s₅ ⟨⟨v8', o5⟩, k5⟩ => ?_
  rw [m4] at o5
  have o5' : Outside B (slot w 8) (8 * w) s.mem s₅.mem :=
    o3.trans (o5.mono (Nat.le_refl _) (by omega_arith))
  have c5 := c3'.of (k4.trans k5) (by decide) (arrO_n o5 (by omega_arith) (by decide) (by decide))
  have u5 : ∀ j < 24, j ≠ 8 → A s₅.mem B w j = A s.mem B w j := fun j hj hne => arr_out o5' hj hne hn
  -- `q := (p - 1) R² R⁻¹`.
  refine WP.seq (WP.mono (c5.mont (o := 5) (a := 1) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [v8']; omega_arith))
    fun s₆ ⟨⟨c6, l6, e6, v6, o6⟩, k6⟩ => ?_)
  rw [v8', u5 1 (by decide) (by decide), hR2] at e6
  have hq0 := chunk_q0 hR (by omega_arith) e6 hR2'
  -- `S := 0`.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) c6.a7 c6.s5 4) fun s₇ ⟨⟨d3, m7⟩, k7⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (c6.scr.congr k7.2.2) d3 ((k7.gpr (by decide)).trans c6.t0) (by omega_arith)
    hw' (slot_al w 4) (by have := sl 4 (by decide); omega_arith)) fun s₈ ⟨⟨_, z8, o8⟩, k8⟩ => ?_)
  rw [m7] at o8
  have c8 := c6.of (k7.trans k8) (by decide) (arrO o8 (by decide) (by decide))
  have v4 : A s₈.mem B w 4 = 0 := wordsVal_zero z8
  have u8 : ∀ j < 24, j ≠ 4 → A s₈.mem B w j = A s₆.mem B w j := fun j hj hne => arr_out o8 hj hne hn
  -- `s9` and `s10`.
  have k28 := ((((k3.trans k4).trans k5).trans k6).trans k7).trans k8
  have o28 : WinO B w s₂.mem s₈.mem := by
    rw [hm2]
    exact (((arrO o3 (by decide) (by decide)).trans (arrO_n o5 (by omega_arith) (by decide) (by decide))).trans
      o6).trans (arrO o8 (by decide) (by decide))
  have o08 : WinO B w s.mem s₈.mem := by rw [← hm2]; exact o28
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xbase_ok (rd := .s9) (by decide) ((k28.gpr (by decide)).trans ((k12.gpr (by decide)).trans h6))
    ((k28.gpr (by decide)).trans ((k12.gpr (by decide)).trans h11)) 6) fun s₉ ⟨⟨a9, m9⟩, k9⟩ => ?_
  have hk8 : Mont.word s₉.mem BX 16 = BitVec.ofNat 64 k := by
    rw [m9, Outside.word_sep o08 hsep (by rw [← e24]; exact h.hZ) (show 16 + 8 ≤ ZX by omega_arith) hxn]
    exact hkw
  have hx9 := hx.congr (k12.trans (k28.trans k9)).2.2
  refine WP.mono (WP.keep [.s10] (Q := fun u => u.gpr .s10 = BitVec.ofNat 64 K ∧ u.mem = s₉.mem)
    (by
      brun [Crt.oNLen, (k9.gpr (by decide)).trans ((k28.gpr (by decide)).trans ((k12.gpr (by decide)).trans h6)),
        hx9.ld (show 16 + 8 ≤ ZX by omega_arith), hx9.al8 (show 16 + 8 ≤ ZX by omega_arith) (by decide), hk8,
        chunks_count k hk', hKd])
    (by rfl) (by rfl)) fun s₁₀ ⟨⟨a10, m10⟩, k10⟩ => ?_
  have hm10 : s₁₀.mem = s₈.mem := by rw [m10, m9]
  have k110 := (((k12.trans k28).trans k9).trans k10)
  -- The chunks.
  have I0 : ChunkI s B BX Z w wX K N (A s.mem B w 1) 0 s₁₀ := by
    refine ⟨c8.regs (k9.trans k10) (by decide) hm10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm10]; exact o08,
      ?_⟩
    · rw [(k9.trans k10).gpr (by decide), k28.gpr (by decide), k12.gpr (by decide), hra]
    · rw [k10.gpr (by decide), a9, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
    · rw [a10, Nat.mul_zero]; exact (BitVec.sub_zero _).symm
    · rw [hm10, u8 1 (by decide) (by decide), v6 1 (by decide) (by decide) (by decide) (by decide),
        u5 1 (by decide) (by decide)]
    · rw [hm10, u8 8 (by decide) (by decide), v6 8 (by decide) (by decide) (by decide) (by decide), v8']
    · rw [hm10, u8 5 (by decide) (by decide)]; exact l6
    · rw [hm10, u8 5 (by decide) (by decide)]; exact hq0
    · rw [hm10, v4]; omega_arith
    · rw [hm10, v4, Nat.mul_zero]; rfl
    · intro j hj h8
      rw [hm10, u8 j hj (by omega_arith), v6 j hj (by omega_arith) (by omega_arith) (by omega_arith),
        u5 j hj (by omega_arith)]
    · exact Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within
        (Keep.within (Keep.within (Keep.within (Keep.refl redRegs s) k1 (by decide)) k2 (by decide)) k3 (by decide))
        k4 (by decide)) k5 (by decide)) k6 (by decide)) k7 (by decide)) k8 (by decide)) k9 (by decide)) k10
        (by decide)
  exact hc s₁₀ I0

/-- `reduceIn`, in `p`'s working space at `B` (`WCtx`, with `ra` array 0's
base too), for `c` the first `w n` words of `X`'s array 6 (`n` chunks of the
`⌈k / 8⌉` words; `X` at `BX`, in `s6`, apart from `B`, its arrays' size in
`s11`, `k` in its header): `c mod p` into array 4, changing only arrays
2–8. -/
theorem reduceIn_ok {s : State} {B BX : Addr} {Z ZX w wX k N Cv : Nat} (h : WCtx s B Z w N)
    (hra : s.gpr .ra = off B (slot w 0)) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hkw : Mont.word s.mem BX Crt.oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hXZ : slot wX 6 + 8 * (w * nChunks ((k + 7) / 8) w) ≤ ZX) (hN : 2 ≤ N) (hodd : N % 2 = 1)
    (hR2 : A s.mem B w 1 = 2 ^ (128 * w) % N)
    (hC : wordsVal s.mem BX (slot wX 6) (w * nChunks ((k + 7) / 8) w) = Cv) :
    WP isa Crt.reduceIn s fun t =>
      (WCtx t B Z w N ∧ t.gpr .ra = off B (slot w 0) ∧ A t.mem B w 4 = Cv % N ∧
        A t.mem B w 1 = A s.mem B w 1 ∧ (∀ j < 24, 8 < j → A t.mem B w j = A s.mem B w j) ∧
        WinO B w s.mem t.mem) ∧ Keep redRegs s t := by
  have hw := h.w2
  have hK1 : 1 ≤ (k + 7) / 8 := by omega_arith
  have hK' : (k + 7) / 8 < 2 ^ 40 := by omega_arith
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hR2' : 2 ^ (128 * w) % N % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [Nat.mod_mod, ← Nat.pow_add]; congr 2; omega_arith
  rw [← reduceInP_loop]
  refine reduceInA_ok h hra hx hsep h6 h11 hkw hk hk' hXZ hN hodd hR2 fun u I0 => ?_
  refine WP.mono (count_loop (cr := .t2) (nChunks_pos (by omega_arith) hK1)
    (fun j u => ChunkI s B BX Z w wX ((k + 7) / 8) N (A s.mem B w 1) j u)
    (fun j hj u I => chunkStep_ok hx hsep hXZ hK1 hK' hodd (by rw [hR2]; exact Nat.mod_lt _ (by omega_arith))
      (by rw [hR2]; exact hR2') hj I) I0)
    fun t I => ⟨⟨I.ctx, I.ra, ?_, I.p1, I.fix, I.out⟩, I.keep⟩
  rw [← Nat.mod_eq_of_lt I.slt, I.sv, hC]

/-! ## The power -/

/-- The registers `power` writes. -/
def powerRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s7, .s8, .s9,
    .s10]

/-- The prime's working space of 24 arrays. -/
abbrev PFr (B : Addr) (w : Nat) (m m' : Mem) : Prop := Outside B (slot w 0) (24 * (8 * (w + 2))) m m'

theorem slot24' (w : Nat) : slot w 0 + 24 * (8 * (w + 2)) = slot w 24 := by unfold slot; omega_arith

theorem PFr.of_win {B : Addr} {w : Nat} {m m' : Mem} (h : WinO B w m m') : PFr B w m m' :=
  h.mono (by unfold slot; omega_arith) (by unfold slot; omega_arith)

theorem bytes_out {B D : Addr} {Z w L : Nat} {m m' : Mem} (h : PFr B w m m') (hZ : slot w 24 ≤ Z)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    Spec.Rsa.bytesAt m' D L = Spec.Rsa.bytesAt m D L := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  have := slot24' w
  by_contra hc
  obtain ⟨h1, h2⟩ := not_or.mp hc
  exact hsep i hi (D + BitVec.ofNat 64 i) (by simp only [VG.Proof.Bignum.ofs] at h1 h2 ⊢; omega) rfl

theorem low_odd {m : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) (h : wordsVal m B d w % 2 = 1) :
    (Mont.word m B d).toNat % 2 = 1 := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega_arith⟩
  simp only [wordsVal] at h
  omega_arith

/-- `power` with `c` in place of its reduction and exponentiation. -/
abbrev powerP (xj : Nat) (c : Prog isa) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ Crt.xb .t4 xj)) (.seq Crt.copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3)) (.seq (Crt.r2Prime 4) c)))

/-- `power` up to the reduction: `p` in array 0, `-p⁻¹ mod 2⁶⁴` and `R² mod
p`. -/
theorem powerA_ok {s : State} {B BX : Addr} {Z ZX w wX xj Pv : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2))) (hxj : slot wX xj + 8 * w ≤ ZX)
    (hP : wordsVal s.mem BX (slot wX xj) w = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hc : ∀ u, WCtx u B Z w Pv → A u.mem B w 1 = 2 ^ (128 * w) % Pv → PFr B w s.mem u.mem →
      Keep powerRegs s u → WP isa c u Q) :
    WP isa (powerP xj c) s Q := by
  have hn : B.toNat + slot w 24 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
  have hxn := hx.nowrap
  have e24 := slot24' w
  have s01 := slot_lt (w := w) (show 0 < 1 by decide)
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold powerP
  -- The prime into array 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = off B (slot w 0) ∧ u.mem = s.mem)
    (by brun [h7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (xbase_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h6)
    ((k1.gpr (by decide)).trans h11) xj) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have hx2 := hx.congr k12.2.2
  refine WP.seq (WP.mono (Pub.copyIn_ok (B := B) (P := BX) (Zp := ZX) (dS := slot wX xj) (dD := slot w 0) (w := w)
    (hs.congr k12.2.2) hxn (fun j hj => hx2.ld (by omega_arith))
    (fun j hj => hx2.al8 (by omega_arith) (by have := slot_al wX xj; omega_arith)) a4
    ((k2.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans ht0) (by omega_arith) hw' (slot_al w 0) hxj
    (by omega_arith) hsep) fun s₃ ⟨⟨_, _, c3, o3⟩, k3⟩ => ?_)
  rw [hm2] at c3 o3
  have v0 : wordsVal s₃.mem B (slot w 0) w = Pv := by rw [wv_words c3, hP]
  have k13 := k12.trans k3
  have h7' : s₃.gpr .a7 = off B (slot w 0) := (k13.gpr (by decide)).trans h7
  have h5' : s₃.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (k13.gpr (by decide)).trans h5
  -- `-p⁻¹ mod 2⁶⁴` and the bases.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (minv_ok (hs.congr k13.2.2) h7' (slot_al w 0) (by omega_arith)
    (low_odd (w := w) (by omega_arith) (by rw [v0]; exact hodd))) fun s₄ ⟨⟨inv4, m4⟩, k4⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k4.gpr (by decide)).trans h7')
    ((k4.gpr (by decide)).trans h5') 1) fun s₅ ⟨⟨a2, m5⟩, k5⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans h7'))
    ((k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans h5')) 2) fun s₆ ⟨⟨a5, m6⟩, k6⟩ => ?_
  have k46 := (k4.trans k5).trans k6
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k46.gpr (by decide)).trans h7')
    ((k46.gpr (by decide)).trans h5') 3) fun s₇ ⟨⟨a6, m7⟩, k7⟩ => ?_
  have k37 := k46.trans k7
  have hm7 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  have c7 : WCtx s₇ B Z w Pv := ⟨hs.congr (k13.trans k37).2.2, hw2, hw', hZ, (k37.gpr (by decide)).trans h7',
    (k37.gpr (by decide)).trans h5', (k37.gpr (by decide)).trans ((k13.gpr (by decide)).trans ht0),
    by rw [((k5.trans k6).trans k7).gpr (by decide), hm7]; exact inv4, by rw [hm7]; exact v0⟩
  -- `R² mod p`.
  refine WP.seq (WP.mono (r2Prime_ok (tmp := 4) c7 (((k6.trans k7).gpr (by decide)).trans a2)
    ((k7.gpr (by decide)).trans a5) a6 (by decide) (by decide) hP2 hodd) fun s₈ ⟨⟨c8, r8, _, o8⟩, k8⟩ => ?_)
  have F8 : PFr B w s.mem s₈.mem := by
    rw [← hm7] at o3
    exact (o3.mono (Nat.le_refl _) (by omega_arith)).trans (PFr.of_win o8)
  have k18 := (k13.trans k37).trans k8
  exact hc s₈ c8 r8 F8 (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within (Keep.within
    (Keep.within (Keep.within (Keep.refl powerRegs s) k1 (by decide)) k2 (by decide)) k3 (by decide))
    k4 (by decide)) k5 (by decide)) k6 (by decide)) k7 (by decide)) k8 (by decide))

/-- `power xj oD oLen`, in a prime's working space at `B` of 24 arrays of `w`
words (array 0's base in `a7` and `ra`, the arrays' size in `s5`, `w` in
`t0`), for the prime `p` (`Pv`, odd, at least 2) in `X`'s array `xj` (`X` at
`BX`, in `s6`, apart from `B`, its arrays' size in `s11`), `c` the first
`w n` words of `X`'s array 6 (`n` chunks of the `⌈k / 8⌉` words, `k` in
`X`'s header) and the exponent's `L ≥ 1` bytes at `D`, and `L`, in `X`'s
header words `oD` and `oLen`: `c^d mod p` in array 4, as a number of the
exponent's bytes, most significant first; nothing but the working space
written. -/
theorem power_ok {s : State} {B BX D : Addr} {Z ZX w wX k xj oD oLen L Pv Cv : Nat} (hs : Scr s B Z)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (hra : s.gpr .ra = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hx : Scr s BX ZX) (hsep : ∀ x, ofs BX x < ZX → Z ≤ ofs B x)
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2))) (hxj : slot wX xj + 8 * w ≤ ZX)
    (hP : wordsVal s.mem BX (slot wX xj) w = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hkw : Mont.word s.mem BX Crt.oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hXZ : slot wX 6 + 8 * (w * nChunks ((k + 7) / 8) w) ≤ ZX)
    (hC : wordsVal s.mem BX (slot wX 6) (w * nChunks ((k + 7) / 8) w) = Cv)
    (hoD : oD + 8 ≤ ZX) (hoD8 : oD % 8 = 0) (hoD' : oD < 2048) (hoL : oLen + 8 ≤ ZX) (hoL8 : oLen % 8 = 0)
    (hoL' : oLen < 2048) (hDw : Mont.word s.mem BX oD = D) (hLw : Mont.word s.mem BX oLen = BitVec.ofNat 64 L)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 63) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hDsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa (Crt.power xj oD oLen) s fun t =>
      (wordsVal t.mem B (slot w 4) w = Cv ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % Pv ∧
        wordsVal t.mem B (slot w 0) w = Pv ∧ PFr B w s.mem t.mem ∧ t.gpr .a7 = off B (slot w 0)) ∧
      Keep powerRegs s t := by
  have hn : B.toNat + slot w 24 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
  have hxn := hx.nowrap
  have e24 := slot24' w
  rw [show Crt.power xj oD oLen = powerP xj (.seq Crt.reduceIn (.seq (.block [.load .d .s9 .s6 oD,
    .load .d .s10 .s6 oLen]) ModExp.powWin)) from rfl]
  refine powerA_ok hs hw2 hw' hZ h7 h5 ht0 hx hsep h6 h11 hxj hP hP2 hodd fun s₈ c8 r8 F8 k18 => ?_
  -- `c mod p`.
  refine WP.seq (WP.mono (reduceIn_ok (k := k) (Cv := Cv) c8 ((k18.gpr (by decide)).trans hra) (hx.congr k18.2.2) hsep
    ((k18.gpr (by decide)).trans h6) ((k18.gpr (by decide)).trans h11)
    (by rw [Outside.word_sep F8 hsep (by omega_arith) (show Crt.oNLen + 8 ≤ ZX by unfold Crt.oNLen; unfold slot hdrBytes at hXZ; omega_arith)
      hxn]; exact hkw) hk hk' hXZ hP2 hodd r8 (by rw [x_wv' F8 hsep (by omega_arith) hxn hXZ]; exact hC))
    fun s₉ ⟨⟨c9, _, r9, p9, _, o9⟩, k9⟩ => ?_)
  have F9 : PFr B w s.mem s₉.mem := F8.trans (PFr.of_win o9)
  have k19 := k18.trans k9
  -- The exponent.
  refine WP.seq (WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off D 0 ∧ u.gpr .s10 = BitVec.ofNat 64 L ∧
      u.mem = s₉.mem)
    (by
      have hx9 := hx.congr k19.2.2
      brun [(k19.gpr (by decide)).trans h6, hoD', hoL', hx9.ld hoD, hx9.ld hoL, hx9.al8 hoD hoD8, hx9.al8 hoL hoL8,
        Outside.word_sep F9 hsep (by omega_arith) hoD hxn, Outside.word_sep F9 hsep (by omega_arith) hoL hxn, hDw, hLw,
        BitVec.add_zero])
    (by rfl) (by rfl)) fun s₁₀ ⟨⟨a9, a10, m10⟩, k10⟩ => ?_)
  have c10 := c9.regs k10 (by decide) m10
  have k110 := k19.trans k10
  have n10 : wordsVal s₁₀.mem B (slot w 0) w = Pv := c10.n
  have hR2 : A s₁₀.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv := by
    rw [m10, p9, r8, ← Nat.pow_add]; congr 2; omega_arith
  refine WP.mono (powWin_ok c10.scr hw2 hw' hZ c10.a7 c10.s5 c10.t0 c10.inv
    (by rw [n10]; exact hP2) (by rw [n10]; exact hodd)
    (by rw [n10, show wordsVal s₁₀.mem B (slot w 1) w = _ from hR2]; exact Nat.mod_lt _ (by omega_arith)) a9 a10 hL hL'
    (by rw [k110.2.1, k110.2.2]; exact hrd) hDsep) fun t ⟨⟨ht, ot⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ht (by rw [n10]; exact hR2), n10, show wordsVal s₁₀.mem B (slot w 4) w = Cv % Pv by rw [m10]; exact r9,
      ← Nat.pow_mod, bytes_out (by rw [← m10] at F9; exact F9) hZ hDsep]
  · rw [← n10]
    exact Outside.wordsVal ot (Or.inl (by unfold slot; omega_arith)) (by omega_arith)
  · rw [← m10] at F9
    exact F9.trans (PFr.of_win ot)
  · exact (kt.gpr (by decide)).trans c10.a7
  · exact Keep.within (Keep.within (Keep.within k18 k9 (by decide)) k10 (by decide)) kt (by decide)

end VG.Proof.Bignum.RISCV64.Win
