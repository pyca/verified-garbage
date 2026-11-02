module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Trial
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Trial32
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Trial division on RISC-V

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Trial/{Digit,Entry,Loop}.lean`):

* `digit_ok`: one 32-bit digit `x` of the candidate (`lwu`) reduced into the
  accumulator by Montgomery's reduction by `2³²` (`redc32_math`): from
  `acc < 2 s`, `acc' < 2 s` and `acc' 2³² ≡ x + acc (mod s)`; the 64-bit
  arithmetic is exact (`redc_word`).
* `digits_ok`: the `2 w` digits of the candidate `c` reduced into `acc`, with
  `acc < 2 s` and `acc 2^(64 w) ≡ c (mod s)` (`trial_word32`).
* `entry_ok`: the entry `i` of the table at `s9`, its flag of dividing `c`
  in `a4` (`trial_div`), `s9` at the next entry, and `s10` counted down, or
  cleared on a hit.
* `loop_ok`: the first `n` entries in turn until one divides `c`: `a4 :=` 1
  if one does (`trialPrefix c n`), else 0.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Trial

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.RISCV64.Trial VG.Proof.Bignum.RISCV64
  VG.Proof.Mont
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Proof.RsaKeyGen (trialPrefix trialPrefix_succ trialPrefix_hit entryDivides)

/-! ## One digit -/

/-- The reduction's value in 64-bit words: exact, since nothing overflows. -/
theorem redc_word {X s sv : Nat} (hX : X < 2 ^ 34) (hs : s < 2 ^ 14) :
    ((BitVec.ofNat 64 X * BitVec.ofNat 64 sv) <<< 32 >>> 32 * BitVec.ofNat 64 s + BitVec.ofNat 64 X) >>> 32 =
      BitVec.ofNat 64 ((X + X * sv % 2 ^ 32 * s) / 2 ^ 32) := by
  have hq : ((BitVec.ofNat 64 X * BitVec.ofNat 64 sv) <<< 32 >>> 32).toNat = X * sv % 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_mul_mod,
      show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
      Nat.mul_div_cancel _ (Nat.two_pow_pos 32), Nat.mod_eq_of_lt (show X < 2 ^ 32 * 2 ^ 32 by omega),
      Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right _ _), ← Nat.mul_mod]
  have hq' : X * sv % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hqs : X * sv % 2 ^ 32 * s < 2 ^ 46 := by
    calc X * sv % 2 ^ 32 * s < 2 ^ 32 * 2 ^ 14 := Nat.mul_lt_mul'' hq' hs
      _ = 2 ^ 46 := (Nat.pow_add 2 32 14).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_mul, hq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show X < 2 ^ 64 by omega)]
  generalize X * sv % 2 ^ 32 * s = qs at hqs ⊢
  omega

/-- A word of the working space at an offset that is a multiple of 4 is
4-aligned. -/
theorem scr_al4 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 4 ≤ size) (h4 : d % 4 = 0) : (off base d).toNat % 4 = 0 := by
  have hn := hs.nowrap
  have ha := hs.al
  have e : (off base d).toNat = base.toNat + d := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]
  omega

/-- The registers `digit` writes. -/
def digitRegs : List Reg := [.s0, .t2, .t3, .t4]

/-- One digit `x` at `o + 4 j` into `acc`. -/
theorem digit_ok {u : State} {B : Addr} {Z o j s sv acc : Nat} (hs : Scr u B Z)
    (h3 : u.gpr .t3 = off B (o + 4 * j)) (h0 : u.gpr .s0 = BitVec.ofNat 64 acc)
    (h1 : u.gpr .s1 = BitVec.ofNat 64 s) (h2 : u.gpr .s2 = BitVec.ofNat 64 sv) (hacc : acc < 2 * s)
    (hs2 : 2 ≤ s) (hs' : s < 2 ^ 14) (hinv : (s * sv + 1) % 2 ^ 32 = 0) (hZ : o + 4 * j + 4 ≤ Z)
    (ho : o % 4 = 0) :
    WP isa (.block digit) u fun t =>
      ((∃ r, t.gpr .s0 = BitVec.ofNat 64 r ∧ r < 2 * s ∧ r * 2 ^ 32 % s = (w32 u.mem B (o + 4 * j) + acc) % s) ∧
        t.gpr .t3 = off B (o + 4 * (j + 1)) ∧ t.mem = u.mem) ∧ Keep digitRegs u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hld : InRegions (u.rd ++ u.wr) (off B (o + 4 * j)) 4 := hs.ld hZ
  have hal : (off B (o + 4 * j)).toNat % 4 = 0 := scr_al4 hs hZ (by omega)
  have hx : w32 u.mem B (o + 4 * j) < 2 ^ 32 := (u.mem.readW (off B (o + 4 * j)) 32).isLt
  have eX : (u.mem.readW (off B (o + 4 * j)) 32).setWidth 64 + BitVec.ofNat 64 acc =
      BitVec.ofNat 64 (w32 u.mem B (o + 4 * j) + acc) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [w32]
    omega
  simp only [digit]
  brun [h3, h0, h1, h2, hld, hal, exec_load_w (show 0 < 2048 by decide), BitVec.add_zero]
  rw [eX, redc_word (by omega) hs']
  obtain ⟨-, hlt, hcong⟩ := VG.Proof.RsaKeyGen.redc32_math (X := w32 u.mem B (o + 4 * j) + acc) hinv (by
    have : 2 ^ 32 + 2 * s ≤ s * 2 ^ 32 := by
      have : 2 * 2 ^ 32 ≤ s * 2 ^ 32 := Nat.mul_le_mul_right _ hs2
      omega
    omega)
  refine ⟨⟨_, rfl, hlt, hcong⟩, ?_⟩
  rw [show o + 4 * j + 4 = o + 4 * (j + 1) by omega]

/-! ## One table entry -/

/-- The `2 w` digits at `o` (from `t3`) into `acc` (`s0`), counted by `t5`. -/
theorem digits_ok {u : State} {B : Addr} {Z o w s sv : Nat} (hs : Scr u B Z)
    (h3 : u.gpr .t3 = off B o) (h0 : u.gpr .s0 = BitVec.ofNat 64 0) (h5 : u.gpr .t5 = BitVec.ofNat 64 (2 * w))
    (h1 : u.gpr .s1 = BitVec.ofNat 64 s) (h2 : u.gpr .s2 = BitVec.ofNat 64 sv) (hs2 : 2 ≤ s) (hs' : s < 2 ^ 14)
    (hinv : (s * sv + 1) % 2 ^ 32 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 4 = 0) :
    WP isa (countLoop .t5 digit) u fun t =>
      ((∃ acc, t.gpr .s0 = BitVec.ofNat 64 acc ∧ acc < 2 * s ∧
        acc * 2 ^ (64 * w) % s = val32 u.mem B o (2 * w) % s) ∧ t.mem = u.mem) ∧ Keep (.t5 :: digitRegs) u t := by
  let Inv : Nat → State → Prop := fun j t =>
    ((∃ acc, t.gpr .s0 = BitVec.ofNat 64 acc ∧ acc < 2 * s ∧ acc * 2 ^ (32 * j) % s = val32 u.mem B o j % s) ∧
      t.gpr .t3 = off B (o + 4 * j) ∧ t.mem = u.mem) ∧ Keep (.t5 :: digitRegs) u t
  refine WP.mono (wp_countdown (cnt := .t5) (N := 2 * w) (by omega) (by omega) Inv
    (fun j hj t ⟨⟨⟨acc, t0, hacc, hv⟩, t3, tm⟩, kt⟩ _ => ?_)
    ⟨⟨⟨0, h0, by omega, by simp [val32]⟩, by rw [h3, Nat.mul_zero, Nat.add_zero], rfl⟩, Keep.refl _ _⟩ h5)
    fun t ⟨⟨⟨acc, t0, hacc, hv⟩, _, tm⟩, kt⟩ => ⟨⟨⟨acc, t0, hacc, by rw [← hv, ← Nat.mul_assoc]⟩, tm⟩, kt⟩
  rw [WP.block_append_iff]
  have ht : Scr t B Z := hs.congr kt.2.2
  refine WP.mono (digit_ok ht t3 t0 ((kt.gpr (by decide)).trans h1) ((kt.gpr (by decide)).trans h2) hacc hs2
    hs' hinv (by omega) ho) fun t₁ ⟨⟨⟨r, a0, hr, hrv⟩, a3, am⟩, k1⟩ => ?_
  have hdec : WP isa (.block [.addi .t5 .t5 (-1)]) t₁ fun t₂ =>
      (t₂.gpr .t5 = t₁.gpr .t5 - BitVec.ofNat 64 1 ∧ t₂.mem = t₁.mem) ∧ Keep [.t5] t₁ t₂ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun
  refine WP.mono hdec fun t₂ ⟨⟨b5, bm⟩, k2⟩ => ?_
  refine ⟨⟨⟨⟨r, by rw [k2.gpr (by decide)]; exact a0, hr, ?_⟩,
    by rw [k2.gpr (by decide)]; exact a3, by rw [bm, am, tm]⟩,
    (kt.trans (k1.trans k2)).mono (by decide)⟩, ?_⟩
  · rw [VG.Proof.RsaKeyGen.trial_word32 hrv hv, val32_succ, tm, Nat.add_comm (val32 _ _ _ _)]
  · rw [b5, k1.gpr (by decide)]

/-- `x <u 1` exactly for `x = 0`. -/
theorem lt_one (x : BitVec 64) : x < 1#64 ↔ x.toNat = 0 := by
  rw [BitVec.lt_def, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega

/-- `(n − 1) & (f − 1)`: 0 for the flag `f = 1`, `n − 1` for `f = 0`. -/
theorem count_flag {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 64) (b : Bool) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1) &&& (BitVec.ofNat 64 (if b then 1 else 0) - BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (if b then 0 else n - 1) := by
  apply BitVec.eq_of_toNat_eq
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn',
      show (2 ^ 64 - 1 % 2 ^ 64 + 0 % 2 ^ 64) % 2 ^ 64 = 2 ^ 64 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.mod_eq_of_lt (show n - 1 < 2 ^ 64 by omega)]
    omega
  · simp only [↓reduceIte]
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    simp

theorem xor_toNat_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b).toNat = 0 ↔ a = b := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  constructor
  · intro h
    have := congrArg (a ^^^ ·) h
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at this
    exact this.symm
  · rintro rfl; exact Nat.xor_self a

/-- The registers `entry` writes. -/
def entryRegs : List Reg := [.s0, .s1, .s2, .t2, .t3, .t4, .t5, .t6, .a4, .s9, .s10]

/-- The entry `i` at `T` (`s9`): `a4 :=` its flag of dividing `c`, `s9 :=`
the next entry, `s10 :=` 0 on a hit, else one less. -/
theorem entry_ok {u : State} {B T : Addr} {Z o w c i n : Nat} (hs : Scr u B Z)
    (h7 : u.gpr .a7 = off B o) (ht0 : u.gpr .t0 = BitVec.ofNat 64 w)
    (hc : val32 u.mem B o (2 * w) = c) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 4 = 0)
    (hi : i < 1024) (h9 : u.gpr .s9 = T) (hT : u.mem.readW T 64 = BitVec.ofNat 64 (TrialTable32.entry i))
    (hTr : InRegions (u.rd ++ u.wr) T 8) (hTa : T.toNat % 8 = 0) (h10 : u.gpr .s10 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) :
    WP isa entry u fun t =>
      (t.gpr .a4 = BitVec.ofNat 64 (if c % tabEntry i = 0 then 1 else 0) ∧ t.gpr .s9 = T + BitVec.ofNat 64 8 ∧
        t.gpr .s10 = BitVec.ofNat 64 (if c % tabEntry i = 0 then 0 else n - 1) ∧ t.mem = u.mem) ∧
        Keep entryRegs u t := by
  obtain ⟨hodd, h3, h8162⟩ := VG.Proof.RsaKeyGen.tabEntry_facts hi
  have hinv := VG.Proof.RsaKeyGen.TrialTable32.inverse_entry hi
  have hlo := VG.Proof.RsaKeyGen.TrialTable32.entry_low hi
  have hhi := VG.Proof.RsaKeyGen.TrialTable32.entry_high hi
  have heb := VG.Proof.RsaKeyGen.TrialTable32.entry_bound hi
  have hsv := (TrialTable32.inverse (BitVec.ofNat 32 (tabEntry i))).isLt
  generalize tabEntry i = s at hodd h3 h8162 hinv hlo hhi hsv ⊢
  generalize (TrialTable32.inverse (BitVec.ofNat 32 s)).toNat = sv at hinv hhi hsv
  unfold entry
  refine WP.seq (WP.mono (WP.keep [.s0, .s1, .s2, .t3, .t5] (Q := fun v => v.gpr .s1 = BitVec.ofNat 64 s ∧
      v.gpr .s2 = BitVec.ofNat 64 sv ∧ v.gpr .s0 = BitVec.ofNat 64 0 ∧ v.gpr .t3 = off B o ∧
      v.gpr .t5 = BitVec.ofNat 64 (2 * w) ∧ v.mem = u.mem) ?_ (by rfl) (by rfl))
    fun v ⟨⟨v1, v2, v0, v3, v5, vm⟩, kv⟩ => ?_)
  · simp only [load]
    brun [h9, hT, hTr, h7, ht0, BitVec.add_zero, hTa, exec_li (show imm12 0 by decide)]
    refine ⟨?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt heb,
        show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
        Nat.mul_div_cancel _ (Nat.two_pow_pos 32), hlo, Nat.mod_eq_of_lt (by omega)]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt heb, hhi, Nat.mod_eq_of_lt (by omega)]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
  have hv' : Scr v B Z := hs.congr kv.2.2
  refine WP.seq (WP.mono (digits_ok hv' v3 v0 v5 v1 v2 (by omega) (by omega) hinv hw hw' hZ ho)
    fun x ⟨⟨⟨acc, x0, hacc, hacv⟩, xm⟩, kx⟩ => ?_)
  rw [vm, hc] at hacv
  have key : c % s = 0 ↔ acc = 0 ∨ acc = s := VG.Proof.RsaKeyGen.trial_div hodd hacc hacv
  have x1 : x.gpr .s1 = BitVec.ofNat 64 s := (kx.gpr (by decide)).trans v1
  have x9 : x.gpr .s9 = T := (kx.gpr (by decide)).trans ((kv.gpr (by decide)).trans h9)
  have x10 : x.gpr .s10 = BitVec.ofNat 64 n := (kx.gpr (by decide)).trans ((kv.gpr (by decide)).trans h10)
  have hacc' : acc < 2 ^ 64 := by omega
  have hs64 : s < 2 ^ 64 := by omega
  have hf : ((if BitVec.ofNat 64 acc < 1#64 then (1 : BitVec 64) else 0) |||
      if BitVec.ofNat 64 acc ^^^ BitVec.ofNat 64 s < 1#64 then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if decide (c % s = 0) then 1 else 0) := by
    simp only [lt_one, xor_toNat_zero hacc' hs64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hacc']
    by_cases a0 : acc = 0
    · have hd : decide (c % s = 0) = true := decide_eq_true (key.mpr (Or.inl a0))
      have a1 : ¬ (0 = s) := by omega
      simp only [a0, a1, hd, ↓reduceIte]
      decide
    · by_cases a1 : acc = s
      · have hd : decide (c % s = 0) = true := decide_eq_true (key.mpr (Or.inr a1))
        have s0 : ¬ (s = 0) := by omega
        simp only [a1, s0, hd, ↓reduceIte]
        decide
      · have hd : decide (c % s = 0) = false := decide_eq_false (fun h => (key.mp h).elim a0 a1)
        simp only [a0, a1, hd, ↓reduceIte, Bool.false_eq_true]
        decide
  refine WP.mono (WP.keep [.t2, .t4, .t6, .a4, .s9, .s10] (Q := fun y =>
      y.gpr .a4 = BitVec.ofNat 64 (if c % s = 0 then 1 else 0) ∧ y.gpr .s9 = T + BitVec.ofNat 64 8 ∧
        y.gpr .s10 = BitVec.ofNat 64 (if c % s = 0 then 0 else n - 1) ∧ y.mem = x.mem) ?_ (by rfl) (by rfl))
    fun y ⟨⟨y4, y9, y10, ym⟩, ky⟩ => ⟨⟨y4, y9, y10, by rw [ym, xm, vm]⟩,
      ((kv.trans kx).trans ky).mono (by decide)⟩
  simp only [finish]
  brun [x0, x1, x9, x10, exec_li (show imm12 1 by decide)]
  rw [hf, count_flag hn (by omega)]
  by_cases hit : c % s = 0 <;> simp [hit]

/-! ## The table's first `n` entries -/

/-- The loop's state with `m` entries left of the first `n`, from its entry `u`:
`k = n − m` entries tested, none dividing `c`, the next at `s9` and the
count in `s10`. -/
def TInv (u : State) (T : Addr) (c n m : Nat) (v : State) : Prop :=
  ∃ k, m = n - k ∧ k < n ∧ (v.gpr .s9 = T + BitVec.ofNat 64 (8 * k) ∧ v.gpr .s10 = BitVec.ofNat 64 (n - k) ∧
    trialPrefix c k = false ∧ v.mem = u.mem) ∧ Keep entryRegs u v

/-- The table's first `n` entries at `T`, readable and aligned. -/
def Tab (u : State) (T : Addr) (n : Nat) : Prop :=
  ∀ i < n, u.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i) ∧
    InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (8 * i)) 8 ∧ (T + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0

/-- One entry: the loop goes on exactly when it does not divide and is not
the last; then with one entry fewer left, else with the result. -/
theorem step_ok {u : State} {B T : Addr} {Z o w c n m : Nat} (hs : Scr u B Z)
    (h7 : u.gpr .a7 = off B o) (ht0 : u.gpr .t0 = BitVec.ofNat 64 w)
    (hc : val32 u.mem B o (2 * w) = c) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 4 = 0)
    (hn' : n ≤ 1024) (htab : Tab u T n) {v : State} (hI : TInv u T c n m v) :
    WP isa entry v fun t =>
      isa.eval (.nonzero .s10) t = some (decide (c % tabEntry (n - m) ≠ 0 ∧ n - m + 1 ≠ n)) ∧
      (isa.eval (.nonzero .s10) t = some false →
        (t.gpr .a4 = BitVec.ofNat 64 (if trialPrefix c n then 1 else 0) ∧ t.mem = u.mem) ∧ Keep entryRegs u t) ∧
      (isa.eval (.nonzero .s10) t = some true → 0 < m ∧ TInv u T c n (m - 1) t) := by
  obtain ⟨k, hm, hk, ⟨v9, v10, hpre, vm⟩, kv⟩ := hI
  subst hm
  have hv : Scr v B Z := hs.congr kv.2.2
  obtain ⟨tk, tr, ta⟩ := htab k hk
  have hnk : n - (n - k) = k := by omega
  rw [hnk]
  refine WP.mono (entry_ok (c := c) (i := k) (n := n - k) hv ((kv.gpr (by decide)).trans h7)
    ((kv.gpr (by decide)).trans ht0) (by rw [vm]; exact hc) hw hw' hZ ho (by omega) v9 (by rw [vm]; exact tk)
    (by rw [kv.2.1, kv.2.2]; exact tr) ta v10 (by omega) (by omega))
    fun t ⟨⟨t4, t9, t10, tm⟩, kt⟩ => ?_
  have kut := (kv.trans kt).mono (by intro r hr; simp only [List.mem_append] at hr; rcases hr with hr | hr <;> exact hr)
  by_cases hit : c % tabEntry k = 0
  · simp only [hit, ↓reduceIte] at t4 t10
    have ev : isa.eval (.nonzero .s10) t = some false := by rw [Steps.eval_nonzero, t10]; rfl
    refine ⟨by rw [ev]; simp [hit], fun _ => ⟨⟨by rw [t4, trialPrefix_hit hk (by
      simp only [entryDivides, decide_eq_true_eq]; exact hit)]; rfl, by rw [tm, vm]⟩, kut⟩,
      fun h => by rw [ev] at h; cases h⟩
  · simp only [hit, ↓reduceIte] at t4 t10
    have hpre' : trialPrefix c (k + 1) = false := by
      rw [trialPrefix_succ, hpre, Bool.false_or]
      simp only [entryDivides, decide_eq_false_iff_not]; exact hit
    by_cases hl : k + 1 = n
    · subst hl
      have ev : isa.eval (.nonzero .s10) t = some false := by
        rw [Steps.eval_nonzero, t10, Nat.add_sub_cancel_left, Nat.sub_self]; rfl
      refine ⟨by rw [ev]; simp, fun _ => ⟨⟨by rw [t4, hpre']; rfl, by rw [tm, vm]⟩, kut⟩,
        fun h => by rw [ev] at h; cases h⟩
    · have ev : isa.eval (.nonzero .s10) t = some true := by
        rw [Steps.eval_nonzero, t10, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [Option.some.injEq, decide_eq_true_eq]
        omega
      refine ⟨by rw [ev]; simp only [Option.some.injEq]; exact (decide_eq_true ⟨hit, hl⟩).symm,
        fun h => (by rw [ev] at h; cases h), fun _ => ⟨by omega, k + 1, by omega, by omega,
          ⟨by rw [t9, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2,
            by rw [t10]; congr 1, hpre', by rw [tm, vm]⟩, kut⟩⟩

/-- The first `n` entries of the table at `T`. -/
theorem loop_ok {u : State} {B T : Addr} {Z o w c n : Nat} (hs : Scr u B Z)
    (h7 : u.gpr .a7 = off B o) (ht0 : u.gpr .t0 = BitVec.ofNat 64 w)
    (hc : val32 u.mem B o (2 * w) = c) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 4 = 0)
    (hn : 1 ≤ n) (hn' : n ≤ 1024) (h9 : u.gpr .s9 = T) (htab : Tab u T n)
    (h10 : u.gpr .s10 = BitVec.ofNat 64 n) :
    WP isa loop u fun t =>
      (t.gpr .a4 = BitVec.ofNat 64 (if trialPrefix c n then 1 else 0) ∧ t.mem = u.mem) ∧ Keep entryRegs u t := by
  refine WP.loop (M := isa) (Q := fun t => (t.gpr .a4 = BitVec.ofNat 64 (if trialPrefix c n then 1 else 0) ∧
      t.mem = u.mem) ∧ Keep entryRegs u t) (TInv u T c n) (fun m v hI => ?_) n u
    ⟨0, by omega, by omega, ⟨by rw [h9, Nat.mul_zero, BitVec.add_zero], by rw [h10, Nat.sub_zero], rfl, rfl⟩,
      Keep.refl _ _⟩
  refine WP.mono (step_ok hs h7 ht0 hc hw hw' hZ ho hn' htab hI) fun t ⟨he, hf, ht⟩ => ?_
  cases e : isa.eval (.nonzero .s10) t with
  | none => rw [e] at he; cases he
  | some b =>
    cases b
    · exact .inl ⟨rfl, hf e⟩
    · obtain ⟨hm, hI'⟩ := ht e
      exact .inr ⟨rfl, m - 1, by omega, hI'⟩

end VG.Proof.RsaKeyGen.RISCV64.Trial
