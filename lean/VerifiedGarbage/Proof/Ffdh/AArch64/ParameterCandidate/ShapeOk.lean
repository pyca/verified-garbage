module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Halve
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero

/-! ### `Ffdh.AArch64.ParameterCandidate.Residue`, which only this module used -/

section

/-!
# An FFDH parameter candidate on AArch64: the generator's congruence

`residue` (`residue_ok`): `r = c mod e`, `e` 24 for the generator 2 and 10
for 5, and `fBad := resFlag g r`, zero exactly for `r = 11` (generator 2)
or `r ∈ {3, 7}` (generator 5). The sum `S` of the halves of 32 bits of
`aN`'s words (`hsum`, `halfSum_ok`) is congruent to `c` modulo 3 and 5,
which divide `2³² − 1` (`wv_hsum_mod`), so `T = 105 (c mod 8) + 16 S` is
congruent to `c` modulo 24 and 10, and `reduce` (`reduce_ok`) takes `T`'s
remainder by `umulh` with `e`'s reciprocal (`redBV_24`, `redBV_10`), which
`modSelect` (`modSelect_ok`) chose with `e`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The modulus of the congruence: 10 for the generator 5, 24 for 2. -/
def resMod (g : Nat) : Nat := if 3 ≤ g then 10 else 24

/-- The congruence's flag for the remainder `r`. -/
def resFlag (g : Nat) (r : BitVec 64) : BitVec 64 :=
  if 3 ≤ g then (r ||| BitVec.ofNat 64 4) ^^^ BitVec.ofNat 64 7 else r ^^^ BitVec.ofNat 64 11

theorem resFlag_two {r : Nat} (hr : r < 24) : resFlag 2 (BitVec.ofNat 64 r) = 0 ↔ r = 11 := by
  unfold resFlag
  simp only [show ¬ 3 ≤ 2 by decide, ite_false]
  revert r; decide

theorem resFlag_five {r : Nat} (hr : r < 10) : resFlag 5 (BitVec.ofNat 64 r) = 0 ↔ r = 3 ∨ r = 7 := by
  unfold resFlag
  simp only [show 3 ≤ 5 by decide, ite_true]
  revert r; decide

/-- The congruence's flag is zero exactly for the generator's congruence. -/
theorem resFlag_zero {g c : Nat} (hg : g = 2 ∨ g = 5) :
    resFlag g (BitVec.ofNat 64 (c % resMod g)) = 0 ↔
      (if g = 2 then c % 24 = 11 else g = 5 ∧ (c % 10 = 3 ∨ c % 10 = 7)) := by
  rcases hg with rfl | rfl
  · rw [resFlag_two (by unfold resMod; simp only [show ¬ 3 ≤ 2 by decide, ite_false]; omega_arith)]
    simp [resMod]
  · rw [resFlag_five (by unfold resMod; simp only [show 3 ≤ 5 by decide, ite_true]; omega_arith)]
    simp [resMod]

/-! ### The sum of the words' halves -/

/-- The sum of the halves of 32 bits of the `k` words at `o`. -/
def hsum (m : Mem) (B : Addr) (o : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => hsum m B o k + ((word m B (o + 8 * k)).toNat / 2 ^ 32 + (word m B (o + 8 * k)).toNat % 2 ^ 32)

theorem hsum_le (m : Mem) (B : Addr) (o : Nat) : ∀ k, hsum m B o k ≤ k * 2 ^ 33
  | 0 => Nat.le_refl _
  | k + 1 => by
    have h1 := hsum_le m B o k
    have h2 := (word m B (o + 8 * k)).isLt
    show hsum m B o k + ((word m B (o + 8 * k)).toNat / 2 ^ 32 + (word m B (o + 8 * k)).toNat % 2 ^ 32) ≤
      (k + 1) * 2 ^ 33
    rw [Nat.add_mul, Nat.one_mul]
    omega_using [h1, h2]

/-- Modulo a divisor of `2³² − 1`, a number is the sum of its words' halves. -/
theorem wv_hsum_mod {d : Nat} (hd : 2 ^ 32 % d = 1) (m : Mem) (B : Addr) (o : Nat) :
    ∀ k, wv m B o k % d = hsum m B o k % d
  | 0 => rfl
  | k + 1 => by
    have hd1 : 1 % d = 1 := by
      rcases Nat.lt_or_ge d 2 with h | h
      · have : d = 0 ∨ d = 1 := by omega_using [h]
        rcases this with rfl | rfl <;> simp at hd
      · exact Nat.mod_eq_of_lt h
    have hp : 2 ^ (64 * k) % d = 1 := by
      rw [show 64 * k = 32 * (2 * k) by omega_using [], Nat.pow_mul, Nat.pow_mod, hd, Nat.one_pow, hd1]
    rw [wv, hsum]
    generalize (word m B (o + 8 * k)).toNat = W
    have hW : W % d = (W / 2 ^ 32 + W % 2 ^ 32) % d := by
      conv => lhs; rw [← Nat.div_add_mod W (2 ^ 32), Nat.add_mod, Nat.mul_mod, hd, Nat.one_mul, Nat.mod_mod,
        ← Nat.add_mod]
    have e1 : (wv m B o k + 2 ^ (64 * k) * W) % d = (hsum m B o k + W) % d := by
      conv => lhs; rw [Nat.add_mod, Nat.mul_mod, hp, Nat.one_mul, Nat.mod_mod, wv_hsum_mod hd m B o k,
        ← Nat.add_mod]
    have e2 : (hsum m B o k + (W / 2 ^ 32 + W % 2 ^ 32)) % d = (hsum m B o k + W) % d := by
      conv => lhs; rw [Nat.add_mod, ← hW, ← Nat.add_mod]
    rw [e1, e2]

/-- A word's halves, as `halfSum` takes them. -/
theorem halves_bv (x : BitVec 64) :
    x >>> 32 + (x - (x >>> 32) <<< 32) = BitVec.ofNat 64 (x.toNat / 2 ^ 32 + x.toNat % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega_using [hx]

/-- The sum's start: `aN`'s base, its low word, the count and the sum. -/
theorem residueHead_ok {s : State} {p : PP} {w : Nat} (h : PSt p w s) :
    WP isa (.block (ws ++ base aN .x16 ++ ([ld .x2 .x16, mov .x14 .x12, movi .x3 0] : List Instr))) s fun t =>
      (t.gpr .x16 = off p.B (slot w aN) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x3 = 0 ∧
        t.gpr .x2 = word s.mem p.B (slot w aN) ∧ t.mem = s.mem) ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have sN := hws.sl (show aN < 16 by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono hws.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans hws.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  refine WP.mono (WP.keep [.x2, .x14, .x3] (Q := fun t =>
      t.gpr .x16 = off p.B (slot w aN) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x3 = 0 ∧
        t.gpr .x2 = word s.mem p.B (slot w aN) ∧ t.mem = s.mem) (by
    brun [h16, e12, hm₂, hs₂.ld (d := slot w aN) (by omega_arith), imm16 (show 0 < 65536 by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hq, k₃⟩ => ⟨hq, (k12.trans k₃).mono (by decide)⟩

/-- `countLoop .x14 halfSum`: the sum of the halves of the `n` words at
`x16` into `x3`. -/
theorem halfSum_ok {s : State} {B : Addr} {Z d n : Nat} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B d)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 n) (h3 : s.gpr .x3 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 24)
    (hZ : d + 8 * n ≤ Z) :
    WP isa (countLoop .x14 halfSum) s fun t =>
      t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (hsum s.mem B d n) ∧
        Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t => t.mem = s.mem ∧ t.gpr .x16 = off B (d + 8 * i) ∧
    t.gpr .x3 = BitVec.ofNat 64 (hsum s.mem B d i) ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t
  unfold halfSum
  refine WP.mono (wp_countdown (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨jm, j16, j3, jk⟩ _ => ?_) ⟨rfl, by rw [h16]; rfl, by rw [h3]; rfl, Keep.refl _ _⟩ h14)
    fun t ⟨tm, _, t3, tk⟩ => ⟨tm, t3, tk⟩
  have hst := hs.congr jk.wr
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x14, .x16] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .x16 = off B (d + 8 * (i + 1)) ∧
      t'.gpr .x3 = t.gpr .x3 + word s.mem B (d + 8 * i) >>> 32 +
        (word s.mem B (d + 8 * i) - (word s.mem B (d + 8 * i) >>> 32) <<< 32) ∧
      t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) (by
    brun [j16, jm, hst.ld (show d + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), off_add,
      show d + 8 * i + 8 = d + 8 * (i + 1) by omega_using []])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨m', a16, a3, a14⟩, k'⟩ =>
      ⟨⟨by rw [m', jm], a16, ?_, (jk.trans k').mono⟩, a14⟩
  rw [a3, j3, BitVec.add_assoc, halves_bv, ← BitVec.ofNat_add]
  rfl

/-! ### The remainder by the reciprocal -/

/-- `reduce`'s value, for the divisor `e` and its reciprocal `M`. -/
def redBV (e M : Nat) (L : BitVec 64) (S : Nat) : BitVec 64 :=
  BitVec.ofNat 64 S * BitVec.ofNat 64 16 + (L &&& BitVec.ofNat 64 7) * BitVec.ofNat 64 105 -
    BitVec.ofNat 64 ((BitVec.ofNat 64 S * BitVec.ofNat 64 16 + (L &&& BitVec.ofNat 64 7) * BitVec.ofNat 64 105).toNat *
      (BitVec.ofNat 64 M).toNat / 2 ^ 64) * BitVec.ofNat 64 e

/-- `T = 105 (L mod 8) + 16 S`, as `reduce` computes it. -/
theorem redT (L : BitVec 64) (S : Nat) :
    BitVec.ofNat 64 S * BitVec.ofNat 64 16 + (L &&& BitVec.ofNat 64 7) * BitVec.ofNat 64 105 =
      BitVec.ofNat 64 (105 * (L.toNat % 8) + 16 * S) := by
  have h7 : (L &&& BitVec.ofNat 64 7).toNat = L.toNat % 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h7, Nat.reducePow, Nat.reduceMod]
  omega_using []

/-- The remainder modulo 24 by `⌈2⁶⁴ / 24⌉`. -/
theorem redBV_24 (L : BitVec 64) {S : Nat} (hS : 16 * S + 735 < 2 ^ 61) :
    redBV 24 recip24 L S = BitVec.ofNat 64 ((105 * (L.toNat % 8) + 16 * S) % 24) := by
  have h8 := Nat.mod_lt L.toNat (show 0 < 8 by decide)
  have hT : 105 * (L.toNat % 8) + 16 * S < 2 ^ 61 := by omega_using [hS, h8]
  unfold redBV
  rw [redT L S]
  generalize 105 * (L.toNat % 8) + 16 * S = T at hT ⊢
  have hq : T * 768614336404564651 / 18446744073709551616 = T / 24 := by omega_using [hT]
  have hp : BitVec.ofNat 64 (T / 24) * BitVec.ofNat 64 24 = BitVec.ofNat 64 (T / 24 * 24) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega_using [hT]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hT]),
    show (BitVec.ofNat 64 recip24).toNat = 768614336404564651 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, hq, hp,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hT]) (Nat.div_mul_le_self T 24),
    show T - T / 24 * 24 = T % 24 by omega_using []]

/-- The remainder modulo 10 by `⌈2⁶⁴ / 10⌉`. -/
theorem redBV_10 (L : BitVec 64) {S : Nat} (hS : 16 * S + 735 < 2 ^ 61) :
    redBV 10 recip10 L S = BitVec.ofNat 64 ((105 * (L.toNat % 8) + 16 * S) % 10) := by
  have h8 := Nat.mod_lt L.toNat (show 0 < 8 by decide)
  have hT : 105 * (L.toNat % 8) + 16 * S < 2 ^ 61 := by omega_using [hS, h8]
  unfold redBV
  rw [redT L S]
  generalize 105 * (L.toNat % 8) + 16 * S = T at hT ⊢
  have hq : T * 1844674407370955162 / 18446744073709551616 = T / 10 := by omega_using [hT]
  have hp : BitVec.ofNat 64 (T / 10) * BitVec.ofNat 64 10 = BitVec.ofNat 64 (T / 10 * 10) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega_using [hT]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hT]),
    show (BitVec.ofNat 64 recip10).toNat = 1844674407370955162 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, hq, hp,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hT]) (Nat.div_mul_le_self T 10),
    show T - T / 10 * 10 = T % 10 by omega_using []]

/-- The reciprocals, into `x7` and `x6`. -/
theorem recips_ok (s : State) :
    WP isa (.block (loadWord .x7 recip10 ++ loadWord .x6 recip24)) s fun t =>
      (t.gpr .x7 = BitVec.ofNat 64 recip10 ∧ t.gpr .x6 = BitVec.ofNat 64 recip24 ∧ t.mem = s.mem) ∧
        Keep [.x6, .x7] s t := by
  unfold loadWord
  -- Kept opaque: `simp` would otherwise evaluate the pieces.
  generalize recip10 = W₁
  generalize recip24 = W₂
  refine WP.keep [.x6, .x7] ?_ rfl rfl rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, List.cons_append, List.nil_append,
    exec_movz_x' (show 0 < 4 by decide), exec_movk_x (show 1 < 4 by decide), exec_movk_x (show 2 < 4 by decide),
    exec_movk_x (show 3 < 4 by decide), RegUpd.gpr_write, RegUpd.mem_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq, movk_word, and_true]

/-- The generator's reciprocal. -/
def resRecip (g : Nat) : Nat := if 3 ≤ g then recip10 else recip24

/-- `modSelect`: the generator's modulus and its reciprocal. -/
theorem modSelect_ok {s : State} {p : PP} {w : Nat} (h : PSt p w s) (h7 : s.gpr .x7 = BitVec.ofNat 64 recip10)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 recip24) :
    WP isa (.block modSelect) s fun t =>
      (t.gpr .x7 = BitVec.ofNat 64 (resRecip p.g) ∧ t.gpr .x13 = BitVec.ofNat 64 (resMod p.g) ∧ t.mem = s.mem) ∧
        Keep [.x6, .x7, .x8, .x9, .x10, .x13] s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hg := h.dims.g
  have h256 := hws.h256
  have hgen := h.args.gen
  unfold modSelect
  refine WP.keep [.x6, .x7, .x8, .x9, .x10, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  rcases hg with hg | hg <;> rw [hg] at hgen ⊢ <;>
  brun [hws.x0, h7, h6, hdr_enc (show fGen < 32 by decide),
    hs.ld (d := 8 * fGen) (by simp only [fGen, sFn]; omega_arith), hgen, resRecip, resMod,
    imm16 (show 3 < 65536 by decide), imm16 (show 10 < 65536 by decide), imm16 (show 24 < 65536 by decide)]

/-- `reduce`: `T = 105 (L mod 8) + 16 S` less `e` times its quotient by the
reciprocal `M`. -/
theorem reduce_ok {s : State} {S e M : Nat} {L : BitVec 64} (h2 : s.gpr .x2 = L)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 S) (h7 : s.gpr .x7 = BitVec.ofNat 64 M)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 e) :
    WP isa (.block reduce) s fun t =>
      (t.gpr .x3 = redBV e M L S ∧ t.mem = s.mem) ∧ Keep [.x2, .x3, .x4] s t := by
  unfold reduce
  refine WP.keep [.x2, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, movi, exec_movz_x, exec_logic_x, exec_mul_x, exec_add_x,
    exec_umulh, exec_sub_x, RegUpd.gpr_write, RegUpd.mem_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq, h2, h3, h7, h13, redBV,
    imm16 (show 7 < 65536 by decide), imm16 (show 105 < 65536 by decide), imm16 (show 16 < 65536 by decide),
    and_true]

/-- The flag, from the remainder in `x3`. -/
theorem residueTail_ok {s : State} {p : PP} {w : Nat} {X : BitVec 64} (h : PSt p w s) (h3 : s.gpr .x3 = X) :
    WP isa (.block [ldh .x9 fGen, movi .x6 3, .subs .x .x8 .x9 .x6, movi .x4 4, .logic .orr .x .x5 .x3 .x4,
      .csel .x .x5 .x5 .x3, movi .x6 7, movi .x7 11, .csel .x .x6 .x6 .x7, .logic .eor .x .x5 .x5 .x6,
      sth .x5 fBad]) s fun t =>
      t.mem = s.mem.writeW (off p.B (8 * fBad)) (resFlag p.g X) ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hg := h.dims.g
  have h256 := hws.h256
  have hgen := h.args.gen
  refine WP.mono (WP.keep [.x9, .x6, .x8, .x4, .x5, .x7] (Q := fun t =>
      t.mem = s.mem.writeW (off p.B (8 * fBad)) (resFlag p.g X)) (by
    rcases hg with hg | hg <;> rw [hg] at hgen ⊢ <;>
    brun [hws.x0, h3, hdr_enc (show fGen < 32 by decide), hdr_enc (show fBad < 32 by decide),
      hs.ld (d := 8 * fGen) (by simp only [fGen, sFn]; omega_arith), hs.st (d := 8 * fBad) (by simp only [fBad]; omega_arith),
      hgen, resFlag, imm16 (show 3 < 65536 by decide), imm16 (show 4 < 65536 by decide),
      imm16 (show 7 < 65536 by decide), imm16 (show 11 < 65536 by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨hm, k⟩ => ⟨hm, k.mono (by decide)⟩

/-- `residue`: the congruence's flag into `fBad`. -/
theorem residue_ok {s : State} {p : PP} {w c : Nat} (h : PSt p w s) (hc : wv s.mem p.B (slot w aN) w = c) :
    WP isa (seqs residue) s fun t =>
      PSt p w t ∧ word t.mem p.B (8 * fBad) = resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) ∧
      Frm p.B [(8 * fBad, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hw1 := hws.w1
  have hw2 := hws.w2
  have sN := hws.sl (show aN < 16 by decide)
  have h256 := hws.h256
  simp only [residue, seqs]
  -- The low word and the sum of the halves.
  refine WP.seq (WP.mono (residueHead_ok h) fun s₁ ⟨⟨h16, h14, h3, h2, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (halfSum_ok hs₁ h16 h14 h3 (by omega_arith) hw2 (by omega_arith))
    fun s₂ ⟨hm₂, h3₂, k₂⟩ => ?_)
  rw [hm₁] at h3₂
  -- The reciprocals.
  refine WP.seq (WP.mono (recips_ok s₂) fun s₃ ⟨⟨h7, h6, hm₃⟩, k₃⟩ => ?_)
  have k13 := (k₁.trans k₂).trans k₃
  have mem₃ : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have st₃ : PSt p w s₃ := h.step (rs := []) (hws.congr' (rs := []) (by rw [mem₃]; exact Frm.refl _ _ _)
    (by simp) k13 (by decide)) (by rw [mem₃]; exact Frm.refl _ _ _) (by simp) (by simp) k13
  -- The modulus and its reciprocal, and the remainder.
  refine WP.seq (WP.mono (modSelect_ok st₃ h7 h6) fun s₃' ⟨⟨h7', h13', hm₃'⟩, k₃'⟩ => ?_)
  have hS := hsum_le s.mem p.B (slot w aN) w
  have hS' : 16 * hsum s.mem p.B (slot w aN) w + 735 < 2 ^ 61 := by omega_arith
  refine WP.seq (WP.mono (reduce_ok
    ((k₃'.gpr .x2 (by decide)).trans ((k₃.gpr .x2 (by decide)).trans ((k₂.gpr .x2 (by decide)).trans h2)))
    ((k₃'.gpr .x3 (by decide)).trans ((k₃.gpr .x3 (by decide)).trans h3₂)) h7' h13')
    fun s₄ ⟨⟨h3₄, hm₄⟩, k₄⟩ => ?_)
  have k14 := (k13.trans k₃').trans k₄
  have mem₄ : s₄.mem = s.mem := hm₄.trans (hm₃'.trans mem₃)
  have st₄ : PSt p w s₄ := h.step (rs := []) (hws.congr' (rs := []) (by rw [mem₄]; exact Frm.refl _ _ _)
    (by simp) k14 (by decide)) (by rw [mem₄]; exact Frm.refl _ _ _) (by simp) (by simp) k14
  have h3' : s₄.gpr .x3 = BitVec.ofNat 64 (c % resMod p.g) := by
    have hl : (word s.mem p.B (slot w aN)).toNat = c % 2 ^ 64 := by rw [← hc, wv_mod64 _ _ _ (by omega_arith)]
    have m3 : c % 3 = hsum s.mem p.B (slot w aN) w % 3 := by rw [← hc]; exact wv_hsum_mod (by decide) _ _ _ _
    have m5 : c % 5 = hsum s.mem p.B (slot w aN) w % 5 := by rw [← hc]; exact wv_hsum_mod (by decide) _ _ _ _
    rw [h3₄]
    rcases h.dims.g with hg | hg
    · rw [hg, show resMod 2 = 24 from rfl, show resRecip 2 = recip24 from rfl, redBV_24 _ hS']
      refine congrArg (BitVec.ofNat 64) ?_
      omega_using [hl, m3]
    · rw [hg, show resMod 5 = 10 from rfl, show resRecip 5 = recip10 from rfl, redBV_10 _ hS']
      refine congrArg (BitVec.ofNat 64) ?_
      omega_using [hl, m5]
  refine WP.mono (residueTail_ok st₄ h3') fun t ⟨hm, k₅⟩ => ?_
  have hf : Frm p.B [(8 * fBad, 8)] s.mem t.mem := by
    rw [hm, mem₄]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fBad]; omega_arith)) (by simp)
  refine ⟨h.step (hws.congr' hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide))
      (k14.trans k₅) (by decide)) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fBad]; omega_arith) (k14.trans k₅), ?_, hf,
    (k14.trans k₅).mono (by decide)⟩
  rw [hm, word_writeW_self]

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on AArch64: the shape's flag

`shapeFlag g w c`, the value `fBad` ends with for the candidate `c` in `w`
words: zero exactly when `c` has the generator's shape and `c` and
`(c − 1) / 2` pass `primeShape` and RSA's trial division,
`obviouslyComposite` (`shapeFlag_zero`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen.AArch64 VG.Spec.Ffdh VG.Impl.RsaKeyGen

/-- The flag of the shape checks of `c`. -/
def shapeFlag (g w c : Nat) : BitVec 64 :=
  resFlag g (BitVec.ofNat 64 (c % resMod g)) ||| mask (anyPre c (4 * trialN w)) ||| evenFlag (c / 2) |||
    mask (anyPre (c / 2) (4 * trialN w))

theorem mask_eq_zero (b : Bool) : mask b = 0 ↔ b = false := by cases b <;> decide

/-- Above the table's largest prime, the sieve of `4 (trialN (mW bits))`
entries is `primeShape` and RSA's trial division for `bits`. -/
theorem sieved_sieve {bits c : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hc : 8161 < c) (ho : c % 2 = 1) :
    (primeShape c && !Spec.RsaKeyGen.obviouslyComposite bits c) = !anyPre c (4 * trialN (mW bits)) := by
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hc ho]
  have ht : anyPre c (4 * trialN (mW bits)) = Spec.RsaKeyGen.obviouslyComposite bits c := by
    have e := VG.Proof.RsaKeyGen.trialAny_eq (w := mW bits) hc
    have e2 : Spec.RsaKeyGen.obviouslyComposite (64 * mW bits) c = Spec.RsaKeyGen.obviouslyComposite bits c := by
      unfold Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
      have : (1024 < 64 * mW bits) = (1024 < bits) := propext (by simp only [mW]; omega)
      simp only [this]
    rw [← e2, ← e]
    rfl
  rw [← ht]
  have h53 : ((List.range 53).any fun i => c % tabEntry i == 0) = anyPre c 53 := rfl
  rw [h53]
  have hle : 53 ≤ 4 * trialN (mW bits) := by unfold trialN; split <;> omega_using []
  cases h4 : anyPre c (4 * trialN (mW bits))
  · cases h5 : anyPre c 53
    · rfl
    · exact absurd (anyPre_mono hle h5) (by rw [h4]; decide)
  · cases anyPre c 53 <;> rfl

theorem shapeFlag_zero {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    shapeFlag g (mW bits) (candidateOf bits x) = 0 ↔
      (generationShape bits g (candidateOf bits x) && primeShape (candidateOf bits x) &&
        primeShape ((candidateOf bits x - 1) / 2) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (candidateOf bits x) &&
        !Spec.RsaKeyGen.obviouslyComposite bits ((candidateOf bits x - 1) / 2)) = true := by
  obtain ⟨ho, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega_using [hb1]) x
  have hlen := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := bits) (by omega_using [hb1]) x).1
  generalize candidateOf bits x = c at ho hl hlen ⊢
  have hbig : 2 ^ 14 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_using [hb1])
  have hq : (c - 1) / 2 = c / 2 := by omega_using [ho]
  rw [hq]
  have reorder (a b c d e : Bool) : (a && b && c && !d && !e) = (a && (b && !d) && (c && !e)) := by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
  rw [reorder, sieved_sieve hb1 hb2 (by omega) ho]
  have hgen : generationShape bits g c = (if g = 2 then decide (c % 24 = 11) else
      decide (g = 5 ∧ (c % 10 = 3 ∨ c % 10 = 7))) := by
    unfold generationShape
    rcases hg with rfl | rfl <;> simp only [hb1, hb2, hlen, decide_true, beq_self_eq_true, Bool.and_true,
      Bool.true_and, ite_true, show ¬ (5 = 2) by decide, ite_false, true_and,
      Bool.decide_or, Nat.reduceBEq, Bool.false_eq_true] <;> simp only [trial_decide_beq]
  simp only [shapeFlag, VG.Proof.Rsa.AArch64.or_eq_zero, mask_eq_zero, evenFlag_zero, resFlag_zero hg]
  rw [hgen]
  rcases Nat.mod_two_eq_zero_or_one (c / 2) with hq2 | hq2
  · have hpq : primeShape (c / 2) = false := by
      unfold primeShape; simp [hq2]
    rw [hpq]
    simp only [hq2, Bool.false_and, Bool.and_false]
    simp
  · rw [sieved_sieve hb1 hb2 (by omega) hq2]
    rcases hg with rfl | rfl <;> simp [hq2]

/-! ### The flag, as the code's checks build it -/

/-- The flag after the congruence. -/
abbrev scr1 (g c : Nat) : BitVec 64 := resFlag g (BitVec.ofNat 64 (c % resMod g))

/-- After the sieve of `c` by the table's first words. -/
abbrev scr2 (g w c : Nat) : BitVec 64 := scr1 g c ||| mask (anyPre c (4 * sieveWords true w))

/-- After the oddness of `c / 2`. -/
abbrev scr3 (g w c : Nat) : BitVec 64 := scr2 g w c ||| evenFlag (c / 2)

/-- After the sieve of `c / 2`. -/
abbrev scr4 (g w c : Nat) : BitVec 64 := scr3 g w c ||| mask (anyPre (c / 2) (4 * sieveWords false w))

/-- After the whole sieve of `c`. -/
abbrev scr5 (g w c : Nat) : BitVec 64 := scr4 g w c ||| mask (anyPre c (4 * sieveWords false w))

/-- The last is the shape's flag, but for the first words, which are among
the whole sieve's. -/
theorem scr5_zero {g w c : Nat} : scr5 g w c = 0 ↔ shapeFlag g w c = 0 := by
  simp only [scr5, scr4, scr3, scr2, scr1, shapeFlag, VG.Proof.Rsa.AArch64.or_eq_zero, mask_eq_zero,
    sieveWords_false]
  constructor
  · rintro ⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩
    exact ⟨⟨⟨h1, h5⟩, h3⟩, h4⟩
  · rintro ⟨⟨⟨h1, h5⟩, h3⟩, h4⟩
    refine ⟨⟨⟨⟨h1, ?_⟩, h3⟩, h4⟩, h5⟩
    cases h : anyPre c (4 * sieveWords true w)
    · rfl
    · rw [anyPre_mono (Nat.mul_le_mul_left 4 (sieveWords_trialN true w)) h] at h5
      cases h5

theorem or_ne_zero {x : BitVec 64} (y : BitVec 64) (h : x ≠ 0) : x ||| y ≠ 0 :=
  fun h0 => h ((VG.Proof.Rsa.AArch64.or_eq_zero _ _).mp h0).1

/-- A check that fails: the shape's flag is not zero. -/
theorem shape_ne {g w c : Nat}
    (h : scr1 g c ≠ 0 ∨ scr2 g w c ≠ 0 ∨ scr3 g w c ≠ 0 ∨ scr4 g w c ≠ 0 ∨ scr5 g w c ≠ 0) :
    shapeFlag g w c ≠ 0 := by
  have h5 : scr5 g w c ≠ 0 := by
    rcases h with h | h | h | h | h
    · exact or_ne_zero _ (or_ne_zero _ (or_ne_zero _ (or_ne_zero _ h)))
    · exact or_ne_zero _ (or_ne_zero _ (or_ne_zero _ h))
    · exact or_ne_zero _ (or_ne_zero _ h)
    · exact or_ne_zero _ h
    · exact h
  exact fun h0 => h5 (scr5_zero.mpr h0)

end VG.Proof.Ffdh.AArch64.ParameterCandidate
