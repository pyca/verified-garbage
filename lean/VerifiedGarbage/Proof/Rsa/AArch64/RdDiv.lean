module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.AArch64.RdStages
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dNorm
import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.LongDivision

/-!
# `vg_rsa_recover_primes_det` on AArch64: `a` and the divisions

`mulRowsLow_ok`: a product by rows modulo `2^(64 W)`, row `i` over the low `W - i` words;
`aProd_ok`: `a = g · 2^k X mod 2^(64 W)` (wide array 7);
`divA_ok`: `m = a / n` and `r = a mod n` (wide arrays 7 and 6), and `m < n`
and'ed into the mask; `divB_ok`: the quotient and remainder of `n - r` by
`m + 1` (narrow), and the remainder zero and'ed into the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet
open VG.Impl.Bignum.Public (sCnt)

theorem hb32_of {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    slot (vk I.k) 32 ≤ 2 ^ 64 := by
  have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
  have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega_arith

/-! ## A product by rows, modulo its width -/

theorem pow_add' {a b c : Nat} (h : a + b = c) : 2 ^ a * 2 ^ b = 2 ^ c := by rw [← Nat.pow_add, h]

/-- The sum of rows `0, …, i - 1`: row `j` is word `j` of `A` times the low `W - j` words of `Bv`, at
word `j`. -/
def rowsLow (A Bv W : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => rowsLow A Bv W i + 2 ^ (64 * i) * ((A / 2 ^ (64 * i) % 2 ^ 64) * (Bv % 2 ^ (64 * (W - i))))

/-- The rows' sum stays below `i 2^(64 (W + 1))`. -/
theorem rowsLow_le (A Bv W : Nat) (i : Nat) (hi : i ≤ W) : rowsLow A Bv W i ≤ i * 2 ^ (64 * (W + 1)) := by
  induction i with
  | zero => simp [rowsLow]
  | succ i ih =>
    have ih := ih (by omega_using [hi])
    have ha : A / 2 ^ (64 * i) % 2 ^ 64 ≤ 2 ^ 64 := Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
    have hb : Bv % 2 ^ (64 * (W - i)) ≤ 2 ^ (64 * (W - i)) := Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
    have e : 2 ^ (64 * i) * (2 ^ 64 * 2 ^ (64 * (W - i))) = 2 ^ (64 * (W + 1)) := by
      rw [pow_add' (show 64 + 64 * (W - i) = 64 * (W - i + 1) by omega_using []),
        pow_add' (show 64 * i + 64 * (W - i + 1) = 64 * (W + 1) by omega_using [hi])]
    have ht : 2 ^ (64 * i) * ((A / 2 ^ (64 * i) % 2 ^ 64) * (Bv % 2 ^ (64 * (W - i)))) ≤ 2 ^ (64 * (W + 1)) := by
      rw [← e]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul ha hb)
    rw [rowsLow, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add ih ht

/-- The rows' sum modulo `2^(64 W)`: `A`'s low `i` words times `Bv`. -/
theorem rowsLow_mod (A Bv W : Nat) (i : Nat) (hi : i ≤ W) :
    rowsLow A Bv W i % 2 ^ (64 * W) = A % 2 ^ (64 * i) * Bv % 2 ^ (64 * W) := by
  induction i with
  | zero => simp [rowsLow, Nat.mod_one]
  | succ i ih =>
    have ih := ih (by omega_using [hi])
    have eW : 2 ^ (64 * W) = 2 ^ (64 * i) * 2 ^ (64 * (W - i)) := (pow_add' (by omega_using [hi])).symm
    have hsplit : A % 2 ^ (64 * (i + 1)) = A % 2 ^ (64 * i) + 2 ^ (64 * i) * (A / 2 ^ (64 * i) % 2 ^ 64) := by
      rw [show 64 * (i + 1) = 64 * i + 64 by omega_using [], Nat.pow_add, Nat.mod_mul]
    -- The row: `2^(64 i) a (Bv mod 2^(64 (W - i)))` is `2^(64 i) a Bv` modulo `2^(64 W)`.
    have hrow : ∀ a, 2 ^ (64 * i) * (a * (Bv % 2 ^ (64 * (W - i)))) % 2 ^ (64 * W) =
        2 ^ (64 * i) * a * Bv % 2 ^ (64 * W) := by
      intro a
      conv_rhs => rw [← Nat.mod_add_div Bv (2 ^ (64 * (W - i)))]
      rw [show 2 ^ (64 * i) * a * (Bv % 2 ^ (64 * (W - i)) + 2 ^ (64 * (W - i)) * (Bv / 2 ^ (64 * (W - i)))) =
        2 ^ (64 * i) * (a * (Bv % 2 ^ (64 * (W - i)))) + 2 ^ (64 * W) * (a * (Bv / 2 ^ (64 * (W - i)))) by
          rw [eW]; ring, Nat.add_mul_mod_self_left]
    rw [rowsLow, hsplit, Nat.add_mod, ih, hrow, Nat.add_mul, Nat.add_mod (A % 2 ^ (64 * i) * Bv)]

/-- The registers `mulRowsLow` writes. -/
def mlRegs : List Reg := [.x1, .x2, .x3, .x4, .x8, .x11, .x12, .x13, .x14, .x16, .x17]

/-- After rows `0, …, i - 1`. -/
structure MLInv (s₀ : State) (B : Addr) (Z ea eb eA wa W : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep mlRegs s₀ t
  x11 : t.gpr .x11 = off B (ea + 8 * i)
  x8 : t.gpr .x8 = off B (eA + 8 * i)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (W - i)
  out : Outside B eA (8 * (W + 2)) s₀.mem t.mem
  val : wv t.mem B eA (W + 2) = rowsLow (wv s₀.mem B ea wa) (wv s₀.mem B eb W) W i

theorem mlStep_ok {s₀ : State} {B : Addr} {Z ea eb eA wa W : Nat} (hs : Scr s₀ B Z)
    (h9 : s₀.gpr .x9 = off B eb) (h7 : s₀.gpr .x7 = 0) (hW : wa < W) (hW' : W < 2 ^ 30)
    (hA : eA + 8 * (W + 2) ≤ Z) (ha : ea + 8 * wa ≤ Z) (hb : eb + 8 * W ≤ Z)
    (sa : ea + 8 * wa ≤ eA ∨ eA + 8 * (W + 2) ≤ ea) (sb : eb + 8 * W ≤ eA ∨ eA + 8 * (W + 2) ≤ eb)
    {i : Nat} (hi : i < wa) {t : State} (hI : MLInv s₀ B Z ea eb eA wa W i t) :
    WP isa (.seq (.block [ld .x1 .x11, next .x11])
      (.seq mulAddRow (.block [next .x8, .subImm .x .x12 .x12 1, .subImm .x .x13 .x13 1]))) t
      fun t' => MLInv s₀ B Z ea eb eA wa W (i + 1) t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hs.nowrap
  have hk := hI.keep
  have t9 : t.gpr .x9 = off B eb := (hk.gpr .x9 (by decide)).trans h9
  have t7 : t.gpr .x7 = 0 := (hk.gpr .x7 (by decide)).trans h7
  -- `x1 := a_i`.
  refine WP.seq (WP.mono (WP.keep [.x1, .x11] (Q := fun t₁ => t₁.gpr .x1 = word t.mem B (ea + 8 * i) ∧
      t₁.gpr .x11 = off B (ea + 8 * i + 8) ∧ t₁.mem = t.mem)
    (by brun [hI.x11, hI.scr.ld (show ea + 8 * i + 8 ≤ Z by omega_using [ha, hi])]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hx1, h11, hm₁⟩, k₁⟩ => ?_)
  have hai : word t.mem B (ea + 8 * i) = word s₀.mem B (ea + 8 * i) := hI.out.word (by omega_using [sa, hi]) (by omega_using [ha, hi, hn])
  have fb : wv t.mem B eb (W - i) = wv s₀.mem B eb (W - i) := hI.out.wv (by omega_using [sb]) (by omega_using [hb, hn])
  -- The low words and the window.
  have sp := wv_add t.mem B eA i (W - i + 2)
  rw [show i + (W - i + 2) = W + 2 by omega_using [hW, hi]] at sp
  have hval := hI.val
  have hW2 : wv t.mem B (eA + 8 * i) (W - i + 2) + (word s₀.mem B (ea + 8 * i)).toNat * wv s₀.mem B eb (W - i) <
      2 ^ (64 * (W - i + 2)) := by
    have hle : 2 ^ (64 * i) * wv t.mem B (eA + 8 * i) (W - i + 2) ≤ i * 2 ^ (64 * (W + 1)) := by
      have := rowsLow_le (wv s₀.mem B ea wa) (wv s₀.mem B eb W) W i (by omega_using [hW, hi])
      rw [← hval, sp] at this; omega_using [this]
    have e1 : 2 ^ (64 * (W + 1)) = 2 ^ (64 * i) * 2 ^ (64 * (W - i + 1)) := (pow_add' (by omega_using [hW, hi])).symm
    rw [e1, Nat.mul_left_comm] at hle
    have hw := Nat.le_of_mul_le_mul_left hle (Nat.two_pow_pos _)
    have hab : (word s₀.mem B (ea + 8 * i)).toNat * wv s₀.mem B eb (W - i) < 2 ^ (64 * (W - i + 1)) := by
      have h1 := (word s₀.mem B (ea + 8 * i)).isLt
      have h2 := wv_lt s₀.mem B eb (W - i)
      calc (word s₀.mem B (ea + 8 * i)).toNat * wv s₀.mem B eb (W - i) < 2 ^ 64 * 2 ^ (64 * (W - i)) :=
            Nat.mul_lt_mul_of_lt_of_le h1 (Nat.le_of_lt h2) (Nat.two_pow_pos _)
        _ = 2 ^ (64 * (W - i + 1)) := pow_add' (by omega_using [])
    have e2 : 2 ^ (64 * (W - i + 2)) = 2 ^ 64 * 2 ^ (64 * (W - i + 1)) := (pow_add' (by omega_using [])).symm
    have hi64 : i + 1 ≤ 2 ^ 64 := by omega_using [hW, hW', hi]
    have := Nat.mul_le_mul_right (2 ^ (64 * (W - i + 1))) hi64
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [e2]
    omega_using [hw, hab, this]
  have hs₁ := hI.scr.congr k₁.wr
  have t₁8 : t₁.gpr .x8 = off B (eA + 8 * i) := (k₁.gpr .x8 (by decide)).trans hI.x8
  refine WP.seq (WP.mono (mulAddRow_ok (w := W - i) hs₁ t₁8 ((k₁.gpr .x9 (by decide)).trans t9)
    ((k₁.gpr .x12 (by decide)).trans hI.x12) ((k₁.gpr .x7 (by decide)).trans t7) (by omega_using [hW, hi]) (by omega_using [hW']) (by omega_using [hW, hA, hi])
    (by omega_using [hb]) (by omega_using [hW, sb, hi]) (by rw [hm₁, hx1, hai, fb]; exact hW2)) fun t₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hx1, hai, fb] at hv₂
  rw [hm₁] at ho₂
  have t₂8 : t₂.gpr .x8 = off B (eA + 8 * i) := (k₂.gpr .x8 (by decide)).trans t₁8
  have t₂12 : t₂.gpr .x12 = BitVec.ofNat 64 (W - i) := (k₂.gpr .x12 (by decide)).trans ((k₁.gpr .x12 (by decide)).trans hI.x12)
  refine WP.mono (WP.keep [.x8, .x12, .x13] (Q := fun t' => t'.gpr .x8 = off B (eA + 8 * i + 8) ∧
      t'.gpr .x12 = BitVec.ofNat 64 (W - i) - BitVec.ofNat 64 1 ∧
      t'.gpr .x13 = t₂.gpr .x13 - BitVec.ofNat 64 1 ∧ t'.mem = t₂.mem)
    (by brun [t₂8, t₂12]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h8', h12', h13', hm'⟩, k'⟩ => ⟨?_, ?_⟩
  · refine ⟨hI.scr.congr ((k₁.trans k₂).trans k').wr, ((hk.trans (k₁.trans k₂)).trans k').mono (by decide),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [(k₂.trans k').gpr .x11 (by decide), h11, Nat.mul_succ, Nat.add_assoc]
    · rw [h8', Nat.mul_succ, Nat.add_assoc]
    · rw [h12', ofNat_sub_ofNat (by omega_using [hW, hi]) (by omega_using [hW'])]; congr 1
    · rw [hm']
      exact hI.out.trans (ho₂.mono (by omega_using []) (by omega_using [hW, hi]))
    · have sp' := wv_add t₂.mem B eA i (W - i + 2)
      rw [show i + (W - i + 2) = W + 2 by omega_using [hW, hi]] at sp'
      have lo : wv t₂.mem B eA i = wv t.mem B eA i := ho₂.wv (Or.inl (by omega_using [])) (by omega_using [hW, hA, hi, hn])
      rw [hm', sp', lo, hv₂, rowsLow, ← hval, sp, wv_word_at s₀.mem B ea (show i < wa by omega_using [hi]),
        wv_mod _ _ _ (show W - i ≤ W by omega_using [])]
      ring
  · rw [h13', (k₁.trans k₂).gpr .x13 (by decide)]

/-- `mulRowsLow`: `acc := ∑ rows` for an accumulator of `W + 2` words starting at zero, the `w_a < W`
words of `a` (`x11`, `x13`) and `b`'s `W` words (`x9`, `x12`). -/
theorem mulRowsLow_ok {s : State} {B : Addr} {Z ea eb eA wa W : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B ea) (h9 : s.gpr .x9 = off B eb) (h13 : s.gpr .x13 = BitVec.ofNat 64 wa)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 W) (h8 : s.gpr .x8 = off B eA) (h7 : s.gpr .x7 = 0)
    (hwa : 1 ≤ wa) (hW : wa < W) (hW' : W < 2 ^ 30)
    (hA : eA + 8 * (W + 2) ≤ Z) (ha : ea + 8 * wa ≤ Z) (hb : eb + 8 * W ≤ Z)
    (sa : ea + 8 * wa ≤ eA ∨ eA + 8 * (W + 2) ≤ ea) (sb : eb + 8 * W ≤ eA ∨ eA + 8 * (W + 2) ≤ eb)
    (h0 : wv s.mem B eA (W + 2) = 0) :
    WP isa mulRowsLow s fun t =>
      wv t.mem B eA (W + 2) = rowsLow (wv s.mem B ea wa) (wv s.mem B eb W) W wa ∧
      Outside B eA (8 * (W + 2)) s.mem t.mem ∧ Keep mlRegs s t := by
  unfold mulRowsLow
  exact WP.mono (wp_countdown (N := wa) (by omega_using [hW, hW']) (by omega_using [hwa]) (MLInv s B Z ea eb eA wa W)
    (fun i hi t hI _ => mlStep_ok hs h9 h7 hW hW' hA ha hb sa sb hi hI)
    ⟨hs, Keep.refl _ _, by rw [h11]; simp, by rw [h8]; simp, by rw [h12]; simp, Outside.refl _ _ _ _,
      by rw [h0]; rfl⟩ h13)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-- `clearTop j`: words `W` and `W + 1` of wide array `j` cleared. -/
theorem clearTop_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {j : Nat} (hj : j < 16) :
    WP isa (.block (clearTop j)) s fun t => G I m₀ (Wk I.k) c t ∧
      Frm I.B (hdrW ++ [(slot (Wk I.k) j + 8 * Wk I.k, 16)]) s.mem t.mem ∧
      word t.mem I.B (slot (Wk I.k) j + 8 * Wk I.k) = 0 ∧ word t.mem I.B (slot (Wk I.k) j + 8 * Wk I.k + 8) = 0 ∧
      Keep [.x3, .x4, .x7, .x11, .x12, .x16] s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  unfold clearTop
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.setWid_ok L) fun t₀ ⟨g₀, f₀, k₀⟩ => ?_
  have hn := g₀.ws.scr.nowrap
  have hZ := g₀.ws.sl hj
  refine WP.mono (ws_ok g₀.ws.scr g₀.ws.x0 g₀.ws.h256 g₀.ws.hw g₀.ws.hS) fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok j .x16 ((k₁.gpr .x0 (by decide)).trans g₀.ws.x0) h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have h12₂ : t₂.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := (k₂.gpr .x12 (by decide)).trans h12
  have hs₂ := g₀.ws.scr.congr (k₁.trans k₂).wr
  have hW : Wk I.k < 2 ^ 20 := by simp only [Wk, vk]; omega_using [hk2]
  have hw8 : BitVec.ofNat 64 (Wk I.k) <<< 3 = BitVec.ofNat 64 (8 * Wk I.k) := by
    rw [shl_ofNat (show Wk I.k * 2 ^ 3 < 2 ^ 64 by omega_using [hW]), Nat.mul_comm]
  refine WP.mono (WP.keep [.x3, .x7, .x16] (Q := fun t => t.mem = (t₂.mem.writeW (off I.B (slot (Wk I.k) j + 8 * Wk I.k)) (0 : BitVec 64)).writeW
      (off I.B (slot (Wk I.k) j + 8 * Wk I.k + 8)) (0 : BitVec 64)) (by
    brun [h12₂, h16, hw8, off_add,
      hs₂.st (show slot (Wk I.k) j + 8 * Wk I.k + 8 ≤ I.Z by omega_using [hZ]),
      hs₂.st (show slot (Wk I.k) j + 8 * Wk I.k + 8 + 8 ≤ I.Z by omega_using [hZ]),
      show (BitVec.setWidth 64 0#16 : BitVec 64) = 0 from rfl]
    done) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ?_
  have o1 := writeW_outside t₂.mem I.B (0 : BitVec 64) (d := slot (Wk I.k) j + 8 * Wk I.k) (by omega_using [hn, hZ])
  have o2 := writeW_outside (t₂.mem.writeW (off I.B (slot (Wk I.k) j + 8 * Wk I.k)) (0 : BitVec 64)) I.B (0 : BitVec 64)
    (d := slot (Wk I.k) j + 8 * Wk I.k + 8) (by omega_using [hn, hZ])
  rw [← hm] at o2
  have oT : Outside I.B (slot (Wk I.k) j + 8 * Wk I.k) 16 t₂.mem t.mem :=
    (o1.mono (by omega_using []) (by omega_using [])).trans (o2.mono (by omega_using []) (by omega_using []))
  have hm₂ : t₂.mem = t₀.mem := by rw [m₂, m₁]
  rw [hm₂] at oT
  have g₃ : G I m₀ (Wk I.k) c t := (g₀.out hj (n := 8 * (Wk I.k + 2)) (by omega_using []) (oT.mono (by omega_using []) (by omega_using []))
    ((k₁.trans k₂).trans k₃) (by decide))
  refine ⟨g₃, (f₀.mono fun r hr => List.mem_append_left _ hr).trans
      (Frm.of_outside oT (List.mem_append_right _ (List.mem_singleton_self _))), ?_, ?_,
    (((k₀.trans k₁).trans k₂).trans k₃).mono (by decide)⟩
  · rw [hm, (writeW_outside _ I.B (0 : BitVec 64) (d := slot (Wk I.k) j + 8 * Wk I.k + 8) (by omega_using [hn, hZ])).word
      (by omega_using []) (by omega_using [hn, hZ]), word_writeW_self]
  · rw [hm, word_writeW_self]

/-! ## `a` -/

/-- `aProd`: `a = (prodStep^[64 v] (g, X, 0)).2.2 = g X mod 2^(64 W)` into wide array 7. -/
theorem aProd_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) :
    WP isa aProd s fun t => G I m₀ (vk I.k) c t ∧
      wv t.mem I.B (slot (Wk I.k) wA) (Wk I.k) = ((prodStep (64 * Wk I.k))^[64 * vk I.k]
        (wv s.mem I.B (slot (vk I.k) gT) (vk I.k), wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k), 0)).2.2 ∧
      (∀ j k, j < 12 → k ≤ vk I.k + 2 → wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hv2 : 2 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
  have hvl : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  have hb32 : 256 + 32 * (8 * (vk I.k + 2)) ≤ 2 ^ 64 := hb32_of h L
  unfold aProd
  simp only [seqs]
  refine WP.seq (WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := wA) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (g₂.setNar_ok L) fun t₃ ⟨g₃, f₃, k₃⟩ => ?_
  refine WP.mono (ws_ok g₃.ws.scr g₃.ws.x0 g₃.ws.h256 g₃.ws.hw g₃.ws.hS) fun t₄ ⟨⟨_, h11₄, m₄, _⟩, k₄⟩ => ?_
  refine WP.mono (base_ok gT .x5 ((k₄.gpr .x0 (by decide)).trans g₃.ws.x0) h11₄) fun t₅ ⟨⟨h5₅, m₅, _⟩, k₅⟩ => ?_
  have g₅ := g₃.same (by rw [m₅, m₄]) (k₄.trans k₅) (by decide)
  refine WP.mono (g₅.setWid_ok L) fun t₆ ⟨g₆, f₆, k₆⟩ => ?_
  refine WP.mono (ws_ok g₆.ws.scr g₆.ws.x0 g₆.ws.h256 g₆.ws.hw g₆.ws.hS) fun t₇ ⟨⟨h12₇, h11₇, m₇, _⟩, k₇⟩ => ?_
  refine WP.mono (base_ok wX .x9 ((k₇.gpr .x0 (by decide)).trans g₆.ws.x0) h11₇) fun t₈ ⟨⟨h9₈, m₈, _⟩, k₈⟩ => ?_
  refine WP.mono (base_ok wA .x8 ((k₈.gpr .x0 (by decide)).trans ((k₇.gpr .x0 (by decide)).trans g₆.ws.x0))
    ((k₈.gpr .x11 (by decide)).trans h11₇)) fun t₉ ⟨⟨h8₉, m₉, _⟩, k₉⟩ => ?_
  have h5₉ : t₉.gpr .x5 = off I.B (slot (vk I.k) gT) := by
    rw [k₉.gpr .x5 (by decide), k₈.gpr .x5 (by decide), k₇.gpr .x5 (by decide), k₆.gpr .x5 (by decide), h5₅]
  have h12₉ : t₉.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := by rw [k₉.gpr .x12 (by decide), k₈.gpr .x12 (by decide), h12₇]
  refine WP.mono (WP.keep [.x7, .x11, .x13] (Q := fun t => t.gpr .x11 = off I.B (slot (vk I.k) gT) ∧
      t.gpr .x13 = BitVec.ofNat 64 (vk I.k) ∧ t.gpr .x7 = 0 ∧ t.mem = t₉.mem) (by
    brun [h5₉, h12₉]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    simp only [Wk, vk] at *
    omega_using [hk2]) (by decide) (by decide) (by decide +kernel)) fun t₁₀ ⟨⟨h11, h13, h7, m₁₀⟩, k₁₀⟩ => ?_
  have g₁₀ : G I m₀ (Wk I.k) c t₁₀ := g₆.same (by rw [m₁₀, m₉, m₈, m₇]) (((k₇.trans k₈).trans k₉).trans k₁₀) (by decide)
  have hn := g₁₀.ws.scr.nowrap
  have zA := g₁₀.ws.sl (j := wA) (by decide)
  have zX := g₁₀.ws.sl (j := wX) (by decide)
  have zg := g₃.ws.sl (j := gT) (by decide)
  -- What the rows read and the accumulator, as before.
  have mS : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → (d + 8 * n ≤ slot (Wk I.k) wA ∨ slot (Wk I.k) wA + 8 * (Wk I.k + 2) ≤ d) →
      wv t₁₀.mem I.B d n = wv s.mem I.B d n := fun d n hd hd' hsep => by
    rw [m₁₀, m₉, m₈, m₇, Frm.hdrW_wv f₆ hd hd', m₅, m₄, Frm.hdrW_wv f₃ hd hd', o₂.wv hsep hd', Frm.hdrW_wv f₁ hd hd']
  have hA0 : wv t₁₀.mem I.B (slot (Wk I.k) wA) (Wk I.k + 2) = 0 := by
    rw [m₁₀, m₉, m₈, m₇, Frm.hdrW_wv f₆ (slot_ge _ _) (by omega_using [hn, zA]), m₅, m₄, Frm.hdrW_wv f₃ (slot_ge _ _) (by omega_using [hn, zA]), z₂]
  refine WP.seq (WP.mono (mulRowsLow_ok (ea := slot (vk I.k) gT) (eb := slot (Wk I.k) wX) (eA := slot (Wk I.k) wA)
    (wa := vk I.k) (W := Wk I.k) g₁₀.ws.scr h11
    (by rw [k₁₀.gpr .x9 (by decide), k₉.gpr .x9 (by decide), h9₈]) h13 (by rw [k₁₀.gpr .x12 (by decide), h12₉])
    (by rw [k₁₀.gpr .x8 (by decide), h8₉]) h7 (by omega_using [hv2]) (by simp only [Wk]; omega_using []) (by simp only [Wk]; omega_using [hvl])
    zA (by omega_using [zg]) (by omega_using [zX]) (by simp only [slot, hdrBytes, gT, wA, Wk]; omega_using [])
    (by simp only [slot, hdrBytes, wX, wA, Wk]; omega_using []) hA0) fun t₁₁ ⟨v₁₁, o₁₁, k₁₁⟩ => ?_)
  have g₁₁ := g₁₀.out (by decide) (Nat.le_refl _) o₁₁ k₁₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (clearTop_ok g₁₁ L (j := wA) (by decide)) fun t₁₂ ⟨g₁₂, f₁₂, _, _, _⟩ => ?_
  refine WP.mono (g₁₂.setNar_ok L) fun t ⟨g, f, _⟩ => ⟨g, ?_, fun j k hj hk => ?_⟩
  · have hXl : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k) < 2 ^ (64 * Wk I.k) := wv_lt _ _ _ _
    rw [prod_iter _ _ _ hXl, Frm.hdrW_wv f (slot_ge _ _) (by omega_using [hn, zA]),
      Frm.hdr_wv f₁₂ (slot_ge _ _) (by omega_using [hn, zA]) (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_using []),
      ← wv_mod _ _ _ (show Wk I.k ≤ Wk I.k + 2 by omega_using []), v₁₁, rowsLow_mod _ _ _ _ (by simp only [Wk]; omega_using []),
      mS _ _ (slot_ge _ _) (by omega_using [hn, zg]) (by simp only [slot, hdrBytes, gT, wA, Wk]; omega_using []),
      mS _ _ (slot_ge _ _) (by omega_using [hn, zX]) (by simp only [slot, hdrBytes, wX, wA, Wk]; omega_using []),
      Nat.mod_eq_of_lt (wv_lt _ _ _ _)]
  · have sj : slot (vk I.k) j + 8 * k ≤ slot (Wk I.k) wA := by
      have := slot_lt (w := vk I.k) (show j < 12 from hj)
      have : slot (vk I.k) 12 ≤ slot (Wk I.k) wA := by simp only [slot, hdrBytes, wA, Wk]; omega_using []
      omega_arith
    have bj : slot (vk I.k) j + 8 * k ≤ 2 ^ 64 := by omega_using [hn, zA, sj]
    rw [Frm.hdrW_wv f (slot_ge _ _) bj,
      Frm.hdr_wv f₁₂ (slot_ge _ _) bj (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_using [sj]),
      o₁₁.wv (.inl sj) bj, mS _ _ (slot_ge _ _) bj (.inl sj)]

/-! ## A step of long division with its quotient digit -/

/-- `addBack`, and the mask of the sign it tested left in `x15`. -/
theorem addBackQ_ok {s : State} {B : Addr} {Z w eA eM : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B eA) (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eA + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eA) :
    WP isa R2Div.addBack s fun t => (∃ c : Bool,
      wv t.mem B eA (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat =
        wv s.mem B eA (w + 1) + (if 2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1) then wv s.mem B eM w else 0)) ∧
      t.gpr .x15 = mask (decide (2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1))) ∧
      Outside B eA (8 * (w + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have hT : decide (2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat) = decide (2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1)) := by
    rw [sign_top]
  generalize hg : decide (2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat) = g at hT
  unfold R2Div.addBack
  refine WP.seq (WP.mono (WP.keep [.x3, .x13, .x14, .x15, .x16, .x17] (Q := fun t =>
    t.gpr .x15 = mask g ∧ t.gpr .x16 = off B eA ∧ t.gpr .x17 = off B eM ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
    t.c = false ∧ t.mem = s.mem)
    (by brun [h11, h9, h12, h7, r2d_ofNat_shl3 (show w < 2 ^ 61 by omega_using [hw']), hs.ld (show eA + 8 * w + 8 ≤ Z by omega_using [hA]),
        hg]; exact (sign_mask _).trans (congrArg mask hg)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h15, h16, h17, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : AddBInv s.mem s₁ B Z eA eM g 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [hm₁]; exact Outside.refl _ _ _ _,
      by rw [hc₁]; cases g <;> rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega_using [hw']) (by omega_using [hw]) (AddBInv s.mem s₁ B Z eA eM g)
    (fun j hj t hI _ => addBStep_ok h15 hA hM sM hj hI) h0 h14) fun t hI => ?_)
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans ((k₁.gpr .x7 (by decide)).trans h7)
  have t15 : t.gpr .x15 = mask g := (hI.keep.gpr .x15 (by decide)).trans h15
  have hy : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) :=
    hI.out.word (d := eA + 8 * w) (Or.inr (Nat.le_refl _)) (by omega_using [hA, hn])
  refine WP.mono (WP.keep [.x3] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (eA + 8 * w)) (word t.mem B (eA + 8 * w) + 0 + BitVec.ofNat 64 t.c.toNat))
    (by brun [hI.x16, t7, hI.scr.ld (show eA + 8 * w + 8 ≤ Z by omega_using [hA]),
      hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega_using [hA])]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨hm', k'⟩ => ?_
  have hs' := adcs_val (word t.mem B (eA + 8 * w)) 0 t.c
  refine ⟨⟨decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * w)).toNat + (0 : BitVec 64).toNat + t.c.toNat), ?_⟩,
    by rw [k'.gpr .x15 (by decide), t15, hT], ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · have hT' : (2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1)) = (g = true) := by
      rw [hT]; simp
    simp only [hT']
    rw [hm', wv_writeW_top _ _ _ _ _ (by omega_using [hA, hn]), wv, ← hy, pow64_succ]
    exact addB_tail hI.val hs'
  · rw [hm']
    exact fun x hx' => (writeW_outside t.mem B _ (by omega_using [hA, hn]) x (by omega_using [hx'])).trans (hI.out x (by omega_using [hx']))

/-- `quotN`'s and `quot3N`'s estimate of `⌊(x 2^64 + u) / m⌋`, for `w ≥ 4`: `u` is below the three words of
`(x 2^64 + u) P` it is estimated from (`WordStep.shift_u`), so the estimate is within one above. -/
theorem r2dQN_div {X M w z u : Nat} (hw : 4 ≤ w) (hz : z ≤ 63) (hu : u < 2 ^ 64) (hXM : X < M)
    (hd : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (w - 1))) :
    (X * 2 ^ 64 + u) / M ≤ r2dQN X M w z ∧ r2dQN X M w z ≤ (X * 2 ^ 64 + u) / M + 1 := by
  have hYM : X * 2 ^ 64 + u < M * 2 ^ 64 := by
    have := Nat.mul_le_mul_right (2 ^ 64) (Nat.succ_le_of_lt hXM)
    rw [Nat.succ_mul] at this
    omega_using [hu, hXM]
  have e1 : 64 * (w - 3) + 64 = 64 * (w - 2) := by omega_using [hw]
  have hd' : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (w - 3) + 64) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * (w - 3) + 64 + 64 = 64 * (w - 1) by omega_using [hw]]
    exact hd
  obtain ⟨-, -, -, hge, hle⟩ := WordStep.qhat3_div (Y := X * 2 ^ 64 + u) (M := M) (P := 2 ^ z)
    (K := 64 * (w - 3)) (Nat.two_pow_pos z) hYM hd'
  have hs := WordStep.shift_u (X := X) (u := u) (z := z) (K := 64 * (w - 4)) (by omega_using [hz]) hu
  rw [show 64 * (w - 4) + 128 = 64 * (w - 3) + 64 by omega_using [hw], show 64 * (w - 4) + 64 = 64 * (w - 3) by omega_using [hw]] at hs
  rw [hs, e1] at hge hle
  exact ⟨hge, hle⟩

/-- The digit, `q̂` less one where the step added `m` back, from the sign's mask. -/
theorem digit_bv {q : Nat} (hq : q < 2 ^ 64) {P : Prop} [Decidable P] (h : P → 1 ≤ q) :
    BitVec.ofNat 64 q + mask (decide P) = BitVec.ofNat 64 (if P then q - 1 else q) := by
  by_cases hP : P
  · have h1 := h hP
    simp only [hP, decide_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (mask true).toNat = 2 ^ 64 - 1 from rfl,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show q - 1 < 2 ^ 64 by omega_using [hq])]
    omega_using [hq, h1]
  · simp only [hP, decide_false, ↓reduceIte]
    rw [show mask false = 0 from rfl]; simp

/-- Where the step added `m` back, `q̂ ≥ 1`. -/
theorem neg_q_pos {W T1 q M y b : Nat} (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + q * M = y + W * b)
    (hM0 : 0 < M) (hMW : 2 * M < W / 2) (hge : y / M ≤ q) (hneg : W / 2 ≤ T1) : 1 ≤ q := by
  rcases Nat.eq_zero_or_pos q with rfl | h
  · rw [Nat.zero_mul, Nat.add_zero] at h1
    have hy : y < M := by
      rw [Nat.le_zero, Nat.div_eq_zero_iff] at hge
      omega_using [hM0, hge]
    rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl
    · omega_using [hMW, hneg, hy, h1]
    · omega_using [hT1, h1]
  · exact h

/-- The registers `stepQ` writes. -/
abbrev sqRegs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17]

/-- `stepQ`: `x := (x 2^64 + u) mod m` (`u` in `x10`, `x < m` the `w ≥ 4` words at `x11`, its word `w`
overwritten, `m` at `x9`) and the digit `⌊(x 2^64 + u) / m⌋` into `x1`, from `P = 2^z`, `d'`, `d'ₗ` and `v`
in the temporary at `x6`. -/
theorem stepQ_ok {t : State} {B : Addr} {Z w eX eM eT M z : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B eX) (h9 : t.gpr .x9 = off B eM) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h6 : t.gpr .x6 = off B eT) (h7 : t.gpr .x7 = 0) (hw : 4 ≤ w) (hw' : w < 2 ^ 31) (hX8 : 8 ≤ eX)
    (hX : eX + 8 * (w + 1) ≤ Z) (hMZ : eM + 8 * w ≤ Z) (hT : eT + 32 ≤ Z)
    (sXM : eX + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eX) (sXT : eX + 8 * (w + 1) ≤ eT ∨ eT + 32 ≤ eX)
    (hM : wv t.mem B eM w = M)
    (hP : (word t.mem B (eT + 8)).toNat = 2 ^ z) (hz : z ≤ 63)
    (hD : (word t.mem B (eT + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hd : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (w - 1)))
    (hv : (word t.mem B eT).toNat = (2 ^ 128 - 1) / (M * 2 ^ z / 2 ^ (64 * (w - 1))) - 2 ^ 64)
    (hDl : (word t.mem B (eT + 24)).toNat = M * 2 ^ z / 2 ^ (64 * (w - 2)) % 2 ^ 64)
    (hXM : wv t.mem B eX w < M) :
    WP isa stepQ t fun t' =>
      wv t'.mem B eX (w + 1) = (wv t.mem B eX w * 2 ^ 64 + (t.gpr .x10).toNat) % M ∧
      t'.gpr .x1 = BitVec.ofNat 64 ((wv t.mem B eX w * 2 ^ 64 + (t.gpr .x10).toNat) / M) ∧
      Outside B eX (8 * (w + 1)) t.mem t'.mem ∧ Keep sqRegs t t' := by
  have hn := hs.nowrap
  generalize hXv : wv t.mem B eX w = X at hXM
  generalize hUv : t.gpr .x10 = U
  have hXd : X * 2 ^ z / 2 ^ (64 * (w - 1)) ≤ (word t.mem B (eT + 16)).toNat := by
    rw [hD]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hXM))
  obtain ⟨hge, hle⟩ := r2dQN_div (u := U.toNat) hw hz U.isLt hXM hd
  unfold stepQ
  simp only [seqs]
  refine WP.seq (WP.mono (r2dQuotN_ok hs h11 h12 h6 h7 (by omega) hw' (by omega) (by omega) hP hz
    (by rw [hD]; exact hd) (by rw [hv, hD]) (by rw [hXv]; exact hXd)) fun t₁ ⟨h1, h2, h5, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  rw [← hm₁] at h1 h2 h5 hP hD hDl
  refine WP.seq (WP.mono (r2dQuot3N_ok hs₁ ((k₁.gpr .x11 (by decide)).trans h11) ((k₁.gpr .x12 (by decide)).trans h12)
    ((k₁.gpr .x6 (by decide)).trans h6) ((k₁.gpr .x7 (by decide)).trans h7) (by omega) hw' hX8 (by omega) hT
    hP hz hD hd hDl (by rw [hm₁, hXv]; exact hXM) h1 h2 h5) fun t₂ ⟨⟨hq₂, hm₂⟩, k₂⟩ => ?_)
  rw [hm₁, hXv] at hq₂
  have k₁₂ := k₁.trans k₂
  have hs₂ := hs.congr k₁₂.wr
  generalize hQ : r2dQN X M w z = q at hq₂ hge hle
  have hqB : q < 2 ^ 64 := by rw [← hQ]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  refine WP.seq (WP.mono (mulSubU_ok hs₂ ((k₁₂.gpr .x11 (by decide)).trans h11)
    ((k₁₂.gpr .x9 (by decide)).trans h9) ((k₁₂.gpr .x12 (by decide)).trans h12)
    ((k₁₂.gpr .x7 (by decide)).trans h7) (by rw [← hq₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hqB
    (by omega) hw' hX hMZ sXM) fun t₃ ⟨b, hv₃, o₃, k₃⟩ => ?_)
  rw [hm₂, hm₁, hXv, hM, k₁₂.gpr .x10 (by decide), hUv] at hv₃
  have k₁₃ := k₁₂.trans k₃
  have hs₃ := hs.congr k₁₃.wr
  refine WP.seq (WP.mono (addBackQ_ok hs₃ ((k₁₃.gpr .x11 (by decide)).trans h11) ((k₁₃.gpr .x9 (by decide)).trans h9)
    ((k₁₃.gpr .x12 (by decide)).trans h12) ((k₁₃.gpr .x7 (by decide)).trans h7) (by omega) hw' hX hMZ sXM)
    fun t₄ ⟨⟨c, hv₄⟩, h15, o₄, k₄⟩ => ?_)
  have hM₃ : wv t₃.mem B eM w = M := by
    rw [o₃.wv (by omega) (by omega), hm₂, hm₁, hM]
  rw [hM₃] at hv₄
  have hM0 : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hXM
  have hMB : M < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  have hW : 2 * M < 2 ^ (64 * (w + 1)) / 2 := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (by decide)]
    have : 2 ^ (64 * w) ≤ 2 ^ (64 * w) * 2 ^ 62 := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    rw [show (2 : Nat) ^ 63 = 2 * 2 ^ 62 from rfl]
    omega
  have h1' : wv t₃.mem B eX (w + 1) + q * M = X * 2 ^ 64 + U.toNat + 2 ^ (64 * (w + 1)) * b.toNat := by
    rw [hv₃, Nat.mul_comm (2 ^ 64) X]
  have hdig := LongDivision.digit_eq (W := 2 ^ (64 * (w + 1))) hM0 hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) h1'
  have k₁₄ := k₁₃.trans k₄
  have t₄1 : t₄.gpr .x1 = BitVec.ofNat 64 q := by
    rw [k₄.gpr .x1 (by decide), k₃.gpr .x1 (by decide), ← hq₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (WP.keep [.x1] (Q := fun t' => t'.gpr .x1 = t₄.gpr .x1 + t₄.gpr .x15 ∧ t'.mem = t₄.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hx1, hm'⟩, k'⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁₄.trans k').mono (by decide)⟩
  · rw [hm']
    exact WordStep.wordStepQ1_div (W := 2 ^ (64 * (w + 1))) hM0 hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b)
      h1' (wv_lt _ _ _ _) (Bool.toNat_lt c) hv₄
  · rw [hx1, t₄1, h15, ← hdig]
    exact digit_bv hqB fun hneg => neg_q_pos (wv_lt _ _ _ _) (Bool.toNat_lt b) h1' hM0 hW hge hneg
  · rw [hm']
    rw [hm₂, hm₁] at o₃
    exact o₃.trans o₄

/-! ## Long division with the quotient in place -/

/-- The registers `divQN` writes. -/
abbrev dqRegs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x8, .x10, .x12, .x13, .x14, .x15, .x16, .x17]

/-- After `j` of `divQN`'s `c` steps from `s₀`, the dividend `U` (words at `eU`): the remainder of `U`'s
top part `⌊U / 2^(64 (c - j))⌋` in `[R]` (`eR`), its quotient in `[U]`'s words `c - j, …, c - 1`, and `[U]`'s
words below as they were. -/
structure DQInv (s₀ : State) (B : Addr) (Z eU eR eM eT wm c M z U : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep dqRegs s₀ t
  x8 : t.gpr .x8 = off B (eU + 8 * (c - j) - 8)
  x12 : t.gpr .x12 = BitVec.ofNat 64 wm
  cnt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j)
  r : wv t.mem B eR (wm + 1) = U / 2 ^ (64 * (c - j)) % M
  q : wv t.mem B (eU + 8 * (c - j)) j = U / 2 ^ (64 * (c - j)) / M
  low : ∀ i < c - j, word t.mem B (eU + 8 * i) = word s₀.mem B (eU + 8 * i)
  m : wv t.mem B eM wm = M
  p : (word t.mem B (eT + 8)).toNat = 2 ^ z
  d : (word t.mem B (eT + 16)).toNat = M * 2 ^ z / 2 ^ (64 * (wm - 1))
  v : (word t.mem B eT).toNat = (2 ^ 128 - 1) / (M * 2 ^ z / 2 ^ (64 * (wm - 1))) - 2 ^ 64
  dl : (word t.mem B (eT + 24)).toNat = M * 2 ^ z / 2 ^ (64 * (wm - 2)) % 2 ^ 64
  frm : Frm B [(eU, 8 * c), (eR, 8 * (wm + 1)), (8 * sCnt, 8)] s₀.mem t.mem

theorem dqStep_ok {s₀ : State} {B : Addr} {Z eU eR eM eT wm c M z U : Nat} (hs : Scr s₀ B Z)
    (h0 : s₀.gpr .x0 = B) (h11 : s₀.gpr .x11 = off B eR) (h9 : s₀.gpr .x9 = off B eM)
    (h6 : s₀.gpr .x6 = off B eT) (h7 : s₀.gpr .x7 = 0) (hw : 4 ≤ wm) (hw' : wm < 2 ^ 20) (hc : c < 2 ^ 20)
    (hU8 : 8 ≤ eU) (hR8 : 8 ≤ eR) (hH : 8 * sCnt + 8 ≤ eU) (hHR : 8 * sCnt + 8 ≤ eR) (hHM : 8 * sCnt + 8 ≤ eM)
    (hHT : 8 * sCnt + 8 ≤ eT)
    (hUZ : eU + 8 * c ≤ Z) (hRZ : eR + 8 * (wm + 1) ≤ Z) (hMZ : eM + 8 * wm ≤ Z) (hTZ : eT + 32 ≤ Z)
    (sUR : eU + 8 * c ≤ eR ∨ eR + 8 * (wm + 1) ≤ eU) (sUM : eU + 8 * c ≤ eM ∨ eM + 8 * wm ≤ eU)
    (sUT : eU + 8 * c ≤ eT ∨ eT + 32 ≤ eU) (sRM : eR + 8 * (wm + 1) ≤ eM ∨ eM + 8 * wm ≤ eR)
    (sRT : eR + 8 * (wm + 1) ≤ eT ∨ eT + 32 ≤ eR) (sMT : eM + 8 * wm ≤ eT ∨ eT + 32 ≤ eM)
    (hz : z ≤ 63) (hd : 2 ^ 63 ≤ M * 2 ^ z / 2 ^ (64 * (wm - 1))) (hM0 : 0 < M)
    (hUw : ∀ i < c, (word s₀.mem B (eU + 8 * i)).toNat = U / 2 ^ (64 * i) % 2 ^ 64)
    {j : Nat} (hj : j < c) {t : State} (hI : DQInv s₀ B Z eU eR eM eT wm c M z U j t) :
    WP isa (seqs [.block [ld .x10 .x8], stepQ,
      .block [st .x1 .x8, .subImm .x .x8 .x8 8, ldh .x13 sCnt, .subImm .x .x13 .x13 1, sth .x13 sCnt]]) t
      fun t' => DQInv s₀ B Z eU eR eM eT wm c M z U (j + 1) t' ∧ ((t'.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ c) := by
  have hn := hs.nowrap
  have hst := hs.congr hI.keep.wr
  have k := hI.keep
  have t0 : t.gpr .x0 = B := (k.gpr .x0 (by decide)).trans h0
  -- `u := U`'s word `i`.
  have hi : c - j - 1 + 1 = c - j := by omega_using [hj]
  generalize hi' : c - j - 1 = i at hi
  have e8 : eU + 8 * (c - j) - 8 = eU + 8 * i := by omega_using [hj, hi']
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x10] (Q := fun t₁ => t₁.gpr .x10 = word t.mem B (eU + 8 * i) ∧ t₁.mem = t.mem)
    (by brun [hI.x8, e8, hst.ld (show eU + 8 * i + 8 ≤ Z by omega_using [hU8, hH, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, hn, hi', hi, e8])]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h10, hm₁⟩, k₁⟩ => ?_)
  have hu : word t.mem B (eU + 8 * i) = word s₀.mem B (eU + 8 * i) := hI.low i (by omega_using [hj, hi'])
  have hs₁ := hst.congr k₁.wr
  have k₀₁ := k.trans k₁
  have hR : wv t₁.mem B eR wm < M := by
    rw [hm₁]; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (hI.r ▸ Nat.mod_lt _ hM0)
  refine WP.seq (WP.mono (stepQ_ok (M := M) (z := z) hs₁ ((k₀₁.gpr .x11 (by decide)).trans h11)
    ((k₀₁.gpr .x9 (by decide)).trans h9) ((k₁.gpr .x12 (by decide)).trans hI.x12) ((k₀₁.gpr .x6 (by decide)).trans h6)
    ((k₀₁.gpr .x7 (by decide)).trans h7) hw (by omega_using [hw']) hR8 hRZ hMZ hTZ sRM sRT (by rw [hm₁]; exact hI.m)
    (by rw [hm₁]; exact hI.p) hz (by rw [hm₁]; exact hI.d) hd (by rw [hm₁]; exact hI.v) (by rw [hm₁]; exact hI.dl) hR)
    fun t₂ ⟨r₂, d₂, o₂, k₂⟩ => ?_)
  have hrw : wv t.mem B eR wm = U / 2 ^ (64 * (c - j)) % M := by
    have hlt : wv t.mem B eR (wm + 1) < 2 ^ (64 * wm) := by
      rw [hI.r]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hM0) (by rw [← hI.m]; exact Nat.le_of_lt (wv_lt _ _ _ _))
    rw [wv_low_of_lt (by omega_using []) hlt, hI.r]
  rw [hm₁, h10, hu, hUw i (by omega_using [hj, hi']), hrw] at r₂ d₂
  rw [hm₁] at o₂
  have k₀₂ := k₀₁.trans k₂
  have hs₂ := hs.congr k₀₂.wr
  have t₂8 : t₂.gpr .x8 = off B (eU + 8 * i) := by rw [k₂.gpr .x8 (by decide), k₁.gpr .x8 (by decide), hI.x8, e8]
  have t₂0 : t₂.gpr .x0 = B := (k₀₂.gpr .x0 (by decide)).trans h0
  have hcnt₂ : word t₂.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j) := by
    rw [o₂.word (by omega_using [hw, hw', hR8, hH, hHR, hHM, hHT, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT]) (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8]), hI.cnt]
  have hsc : sCnt < 32 := by decide
  refine WP.mono (WP.keep [.x8, .x13] (Q := fun t' =>
      t'.mem = (t₂.mem.writeW (off B (eU + 8 * i)) (t₂.gpr .x1)).writeW (off B (8 * sCnt))
        (BitVec.ofNat 64 (c - j) - BitVec.ofNat 64 1) ∧
      t'.gpr .x8 = off B (eU + 8 * i) - BitVec.ofNat 64 8 ∧ t'.gpr .x13 = BitVec.ofNat 64 (c - j) - BitVec.ofNat 64 1)
    (by
      have hsw : word (t₂.mem.writeW (off B (eU + 8 * i)) (t₂.gpr .x1)) B (8 * sCnt) = BitVec.ofNat 64 (c - j) := by
        rw [(writeW_outside t₂.mem B (t₂.gpr .x1) (d := eU + 8 * i) (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc])).word (by omega_using [hU8, hH, hHR, hHM, hHT, hUZ, sUR, sUM, sUT, hi', hi, e8, hsc]) (by omega_using [hsc]), hcnt₂]
      brun [t₂8, t₂0, hdr_enc hsc, hs₂.st (show eU + 8 * i + 8 ≤ Z by omega_using [hU8, hH, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, hn, hi', hi, e8]), hs₂.ld (show 8 * sCnt + 8 ≤ Z by omega_using [hH, hUZ]),
        hs₂.st (show 8 * sCnt + 8 ≤ Z by omega_using [hH, hUZ]), hsw])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hm', h8', h13'⟩, k'⟩ => ?_
  have oW : Outside B (eU + 8 * i) 8 t₂.mem (t₂.mem.writeW (off B (eU + 8 * i)) (t₂.gpr .x1)) :=
    writeW_outside _ B _ (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc])
  have oC : Outside B (8 * sCnt) 8 (t₂.mem.writeW (off B (eU + 8 * i)) (t₂.gpr .x1)) t'.mem := by
    rw [hm']; exact writeW_outside _ B _ (by omega_using [hsc])
  -- What the stores keep.
  have kp : ∀ d n, d + 8 * n ≤ 2 ^ 64 → (d + 8 * n ≤ eU + 8 * i ∨ eU + 8 * i + 8 ≤ d) →
      (d + 8 * n ≤ 8 * sCnt ∨ 8 * sCnt + 8 ≤ d) → wv t'.mem B d n = wv t₂.mem B d n := fun d n hd h1 h2 => by
    rw [oC.wv h2 hd, oW.wv h1 hd]
  have kw : ∀ d, d + 8 ≤ 2 ^ 64 → (d + 8 ≤ eU + 8 * i ∨ eU + 8 * i + 8 ≤ d) →
      (d + 8 ≤ 8 * sCnt ∨ 8 * sCnt + 8 ≤ d) → word t'.mem B d = word t₂.mem B d := fun d hd h1 h2 => by
    rw [oC.word h2 hd, oW.word h1 hd]
  have kt : ∀ d, d + 8 ≤ 2 ^ 64 → (d + 8 ≤ eR ∨ eR + 8 * (wm + 1) ≤ d) → (d + 8 ≤ eU + 8 * i ∨ eU + 8 * i + 8 ≤ d) →
      (d + 8 ≤ 8 * sCnt ∨ 8 * sCnt + 8 ≤ d) → word t'.mem B d = word t.mem B d := fun d hd h0 h1 h2 => by
    rw [kw d hd h1 h2, o₂.word h0 hd]
  have hA := Nat.div_add_mod (U / 2 ^ (64 * (i + 1))) M
  have hsplit : U / 2 ^ (64 * i) = U / 2 ^ (64 * (i + 1)) * 2 ^ 64 + U / 2 ^ (64 * i) % 2 ^ 64 := by
    rw [show 64 * (i + 1) = 64 * i + 64 by omega_using [], Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact (Nat.div_add_mod' _ _).symm
  have hci : c - j = i + 1 := hi.symm
  have hrv : wv t₂.mem B eR (wm + 1) = U / 2 ^ (64 * i) % M := by
    rw [r₂, hci, ← LongDivision.mod_step, ← hsplit]
  refine ⟨⟨hs.congr (k₀₂.trans k').wr, (k₀₂.trans k').mono (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [h8', off_sub B (show 8 ≤ eU + 8 * i by omega_using [hU8]), show c - (j + 1) = i by omega_using [hi']]
  · rw [k'.gpr .x12 (by decide), k₂.gpr .x12 (by decide), k₁.gpr .x12 (by decide), hI.x12]
  · rw [hm', word_writeW_self, ofNat_sub_ofNat (a := c - j) (b := 1) (by omega_using [hj]) (by omega_using [hc]),
      show c - j - 1 = c - (j + 1) by omega_using []]
  · -- The remainder.
    rw [kp _ _ (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]) (by omega_using [hw, hw', hU8, hR8, hH, hHR, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hi', hi, e8, hci]) (by omega_using [hw, hw', hR8, hH, hHR, hHM, hHT, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT, hsc]), hrv, show c - (j + 1) = i by omega_using [hi']]
  · -- The quotient's digits.
    rw [show c - (j + 1) = i by omega_using [hi'], wv_cons, kp (eU + 8 * i + 8) j (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]) (by omega_using []) (by omega_using [hU8, hH, hHR, hHM, hHT, hUZ, sUR, sUM, sUT, hj, hi', hi, e8, hsc, hci]),
      o₂.wv (by omega_using [hw, hw', hU8, hR8, hH, hHR, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hi', hi, e8, hci]) (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]), show eU + 8 * i + 8 = eU + 8 * (c - j) by omega_using [hj, hi'], hI.q, hm',
      (writeW_outside _ B _ (d := 8 * sCnt) (by omega_using [hsc])).word (by omega_using [hU8, hH, hHR, hHM, hHT, hUZ, sUR, sUM, sUT, hi', hi, e8, hsc, hci]) (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]), word_writeW_self, d₂, hci]
    have hdl := LongDivision.digit_lt (Nat.mod_lt (U / 2 ^ (64 * (i + 1))) hM0)
      (Nat.mod_lt (U / 2 ^ (64 * i)) (Nat.two_pow_pos 64))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdl]
    conv_rhs => rw [hsplit, LongDivision.div_step]
    ring
  · intro i' hi'
    rw [kt _ (by omega_arith) (by omega_using [hw, hw', hU8, hR8, hH, hHR, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, e8, hi']) (by omega_arith) (by omega_using [hH])]
    exact hI.low i' (by omega_using [hi'])
  · rw [kp _ _ (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]) (by omega_using [hw, hw', hU8, hH, hHM, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hi', hi, e8, hci]) (by omega_using [hw, hw', hH, hHR, hHM, hHT, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT, hsc]), o₂.wv (by omega_using [sRM]) (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci])]; exact hI.m
  · rw [kt _ (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]) (by omega_using [hw, hw', hR8, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT]) (by omega_using [hU8, hH, hHT, hUZ, hTZ, sUR, sUM, sUT, sRT, sMT, hi', hi, e8, hci]) (by omega_using [hHT])]; exact hI.p
  · rw [kt _ (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]) (by omega_using [hw, hw', hR8, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT]) (by omega_using [hU8, hH, hHT, hUZ, hTZ, sUR, sUM, sUT, sRT, sMT, hi', hi, e8, hci]) (by omega_using [hHT])]; exact hI.d
  · rw [kt _ (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]) (by omega_using [hw, hw', hR8, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT]) (by omega_using [hU8, hH, hHT, hUZ, hTZ, sUR, sUM, sUT, sRT, sMT, hi', hi, e8, hci]) (by omega_using [hHT])]; exact hI.v
  · rw [kt _ (by omega_using [hw, hw', hc, hU8, hR8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hj, hn, hi', hi, e8, hsc, hci]) (by omega_using [hw, hw', hR8, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT]) (by omega_using [hU8, hH, hHT, hUZ, hTZ, sUR, sUM, sUT, sRT, sMT, hi', hi, e8, hci]) (by omega_using [hHT])]; exact hI.dl
  · refine hI.frm.trans ?_
    have f₁ : Frm B [(eU, 8 * c), (eR, 8 * (wm + 1)), (8 * sCnt, 8)] t.mem t₂.mem := Frm.of_outside o₂ (by simp)
    exact (f₁.trans (Frm.of_outside (oW.mono (o' := eU) (n' := 8 * c) (by omega_using []) (by omega_using [hj, hi'])) (by simp))).trans
      (Frm.of_outside oC (by simp))
  · rw [h13', ofNat_sub_ofNat (a := c - j) (b := 1) (by omega_using [hj]) (by omega_using [hc]), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc])]
    omega_using [hj]

/-- `divQN`'s set-up: the remainder from `U`'s top words, the normalization and the reciprocal. -/
abbrev dqHead : List (Prog isa) := [
  .block [.sub .x .x14 .x13 .x12, .addImm .x .x14 .x14 1, sth .x14 sCnt, .lsl .x .x3 .x14 3, .add .x .x16 .x8 .x3,
    .subImm .x .x8 .x16 8, mov .x17 .x11, .subImm .x .x12 .x12 1],
  copyWords,
  .block [.addImm .x .x12 .x12 1],
  R2Div.normN,
  R2Div.recipN]

/-- `divQN`'s step. -/
abbrev dqBody : Prog isa := seqs [.block [ld .x10 .x8], stepQ,
  .block [st .x1 .x8, .subImm .x .x8 .x8 8, ldh .x13 sCnt, .subImm .x .x13 .x13 1, sth .x13 sCnt]]

theorem divQN_eq : divQN = seqs (dqHead ++ ([.loop dqBody (.nonzero .x .x13)] : List (Prog isa))) := rfl

/-- `divQN`'s set-up, up to its loop: the invariant at step 0. -/
theorem dqHead_ok {s : State} {B : Addr} {Z eU eR eM eT L wm : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h8 : s.gpr .x8 = off B eU) (h13 : s.gpr .x13 = BitVec.ofNat 64 L) (h11 : s.gpr .x11 = off B eR)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 wm) (h9 : s.gpr .x9 = off B eM) (h6 : s.gpr .x6 = off B eT)
    (h7 : s.gpr .x7 = 0) (hw : 4 ≤ wm) (hL : wm ≤ L) (hL' : L < 2 ^ 19)
    (_hU8 : 8 ≤ eU) (hH : 8 * sCnt + 8 ≤ eU) (hHR : 8 * sCnt + 8 ≤ eR) (hHM : 8 * sCnt + 8 ≤ eM)
    (hHT : 8 * sCnt + 8 ≤ eT)
    (hUZ : eU + 8 * L ≤ Z) (hRZ : eR + 8 * (wm + 1) ≤ Z) (hMZ : eM + 8 * wm ≤ Z) (hTZ : eT + 32 ≤ Z)
    (sUR : eU + 8 * L ≤ eR ∨ eR + 8 * (wm + 1) ≤ eU) (sUM : eU + 8 * L ≤ eM ∨ eM + 8 * wm ≤ eU)
    (sUT : eU + 8 * L ≤ eT ∨ eT + 32 ≤ eU) (sRM : eR + 8 * (wm + 1) ≤ eM ∨ eM + 8 * wm ≤ eR)
    (sRT : eR + 8 * (wm + 1) ≤ eT ∨ eT + 32 ≤ eR) (sMT : eM + 8 * wm ≤ eT ∨ eT + 32 ≤ eM)
    (hR0 : word s.mem B (eR + 8 * (wm - 1)) = 0) (hR1 : word s.mem B (eR + 8 * wm) = 0)
    (htop : 2 ^ (64 * (wm - 1)) ≤ wv s.mem B eM wm) :
    WP isa (seqs dqHead) s fun s₀ => ∃ z, z ≤ 63 ∧
      2 ^ 63 ≤ wv s.mem B eM wm * 2 ^ z / 2 ^ (64 * (wm - 1)) ∧
      (∀ i < L - wm + 1, (word s₀.mem B (eU + 8 * i)).toNat = wv s.mem B eU L / 2 ^ (64 * i) % 2 ^ 64) ∧
      DQInv s₀ B Z eU eR eM eT wm (L - wm + 1) (wv s.mem B eM wm) z (wv s.mem B eU L) 0 s₀ ∧ Keep dqRegs s s₀ ∧
      wv s₀.mem B (eU + 8 * (L - wm + 1)) (wm - 1) = wv s.mem B (eU + 8 * (L - wm + 1)) (wm - 1) ∧
      Frm B [(eU, 8 * (L - wm + 1)), (eR, 8 * (wm + 1)), (eT, 32), (8 * sCnt, 8)] s.mem s₀.mem := by
  have hn := hs.nowrap
  generalize hc : L - wm + 1 = c
  generalize hUv : wv s.mem B eU L = U
  generalize hMv : wv s.mem B eM wm = M at htop
  have hM0 : 0 < M := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) htop
  have hc1 : 1 ≤ c := by omega_using [hc]
  have hsc : sCnt < 32 := by decide
  have hcv : BitVec.ofNat 64 L - BitVec.ofNat 64 wm + BitVec.ofNat 64 1 = BitVec.ofNat 64 c := by
    rw [ofNat_sub_ofNat (by omega_using [hw, hL, hL', hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc]) (by omega_using [hL']), BitVec.ofNat_add_ofNat, ← hc]
  have h8c : BitVec.ofNat 64 c <<< 3 = BitVec.ofNat 64 (8 * c) := by
    rw [shl_ofNat (show c * 2 ^ 3 < 2 ^ 64 by omega_using [hw, hL, hL', hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hcv]), Nat.mul_comm]
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3, .x8, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 c) ∧ t.gpr .x8 = off B (eU + 8 * c - 8) ∧
      t.gpr .x16 = off B (eU + 8 * c) ∧ t.gpr .x17 = off B eR ∧ t.gpr .x12 = BitVec.ofNat 64 (wm - 1))
    (by
      brun [h13, h12, h8, h11, h0, hcv, h8c, hdr_enc hsc, hs.st (show 8 * sCnt + 8 ≤ Z by omega_using [hH, hUZ]), off_add]
      exact ⟨off_sub B (by omega_using [_hU8]), ofNat_sub_ofNat (by omega_using [hw]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hcv])⟩) (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm₁, h8₁, h16₁, h17₁, h12₁⟩, k₁⟩ => ?_)
  have oC : Outside B (8 * sCnt) 8 s.mem t₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by omega_using [hsc])
  have hs₁ := hs.congr k₁.wr
  -- `[R] :=` the top `w_m - 1` words of `U`.
  refine WP.seq (WP.mono (copyWords_ok h16₁ h17₁ h12₁ (by omega_using [hw]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv])
    (fun i hi => hs₁.ld (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv, hi])) (fun i hi => hs₁.st (by omega_using [hRZ, hi]))
    (fun i hi b hb => by rw [ofs_off B (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv, hi, hb])]; omega_using [hw, hL, _hU8, hH, hHR, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hcv, hi, hb])) fun t₂ ⟨v₂, _, o₂, _, _, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  refine WP.seq (WP.mono (WP.keep [.x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 wm ∧ t.mem = t₂.mem)
    (by brun [(k₂.gpr .x12 (by decide)).trans h12₁]; rw [BitVec.ofNat_add_ofNat]; congr 1; omega_using [hw])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h12₃, m₃⟩, k₃⟩ => ?_)
  have k₀₃ := (k₁.trans k₂).trans k₃
  have hs₃ := hs.congr k₀₃.wr
  -- The divisor's normalization and the reciprocal.
  have hM₃ : wv t₃.mem B eM wm = M := by
    rw [m₃, o₂.wv (by omega_using [hw, hL, hHR, hHM, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT, hc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]), oC.wv (by omega_using [hw, hL, hH, hHR, hHM, hHT, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT, hc, hsc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]), hMv]
  refine WP.seq (WP.mono (normN_ok hs₃ ((k₀₃.gpr .x9 (by decide)).trans h9) h12₃ ((k₀₃.gpr .x6 (by decide)).trans h6)
    (by omega_using [hw]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hcv]) hMZ hTZ (by rw [hM₃]; exact htop)) fun t₄ ⟨⟨z, hz, hP₄, hD₄, hd₄, hDl₄⟩, o₄, k₄⟩ => ?_)
  rw [hM₃] at hD₄ hd₄ hDl₄
  have hs₄ := hs₃.congr k₄.wr
  refine WP.mono (recipN_ok hs₄ ((k₄.gpr .x6 (by decide)).trans ((k₀₃.gpr .x6 (by decide)).trans h6))
    ((k₄.gpr .x7 (by decide)).trans ((k₀₃.gpr .x7 (by decide)).trans h7)) (by omega_using [hTZ]) (by rw [hD₄]; exact hd₄))
    fun s₀ ⟨hv₀, o₅, k₅⟩ => ?_
  rw [hD₄] at hv₀
  have k₀₅ := (k₀₃.trans k₄).trans k₅
  have hs₀ := hs.congr k₀₅.wr
  -- What the set-up kept.
  have kS : ∀ d n, d + 8 * n ≤ 2 ^ 64 → (d + 8 * n ≤ 8 * sCnt ∨ 8 * sCnt + 8 ≤ d) →
      (d + 8 * n ≤ eR ∨ eR + 8 * (wm - 1) ≤ d) → (d + 8 * n ≤ eT ∨ eT + 32 ≤ d) →
      wv s₀.mem B d n = wv s.mem B d n := fun d n hd h1 h2 h3 => by
    rw [o₅.wv (by omega_using [h3]) hd, o₄.wv (by omega_using [h3]) hd, m₃, o₂.wv h2 hd, oC.wv h1 hd]
  have kSw : ∀ d, d + 8 ≤ 2 ^ 64 → (d + 8 ≤ 8 * sCnt ∨ 8 * sCnt + 8 ≤ d) →
      (d + 8 ≤ eR ∨ eR + 8 * (wm - 1) ≤ d) → (d + 8 ≤ eT ∨ eT + 32 ≤ d) →
      word s₀.mem B d = word s.mem B d := fun d hd h1 h2 h3 => by
    rw [o₅.word (by omega_using [h3]) hd, o₄.word (by omega_using [h3]) hd, m₃, o₂.word h2 hd, oC.word h1 hd]
  have hU₀ : wv s₀.mem B eU L = U := by rw [kS _ _ (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]) (by omega_using [hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, sUR, sUM, sUT, hc, hsc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hcv]) (by omega_using [hL, hL', _hU8, hH, hHT, hUZ, hTZ, sUR, sUM, sUT, sRT, sMT, hc, hcv]), hUv]
  have hUw : ∀ i < c, (word s₀.mem B (eU + 8 * i)).toNat = U / 2 ^ (64 * i) % 2 ^ 64 := fun i hi => by
    rw [← hU₀, wv_word_at _ _ _ (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hcv, hi])]
  have hUtop : U / 2 ^ (64 * c) < 2 ^ (64 * (wm - 1)) := by
    rw [← hUv, wv_shr_words _ _ _ (show c ≤ L by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hcv]), show L - c = wm - 1 by omega_using [hw, hL, hL', hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hcv]]; exact wv_lt _ _ _ _
  have hUM : U / 2 ^ (64 * c) < M := Nat.lt_of_lt_of_le hUtop htop
  have hr₀ : wv s₀.mem B eR (wm + 1) = U / 2 ^ (64 * c) % M := by
    rw [wv, kSw _ (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]) (by omega_using [hw, hL, hH, hHR, hHM, hHT, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT, hc, hsc, hcv]) (by omega_using []) (by omega_using [hw, hL, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hcv]), hR1, show (0 : BitVec 64).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero]
    rw [Nat.mod_eq_of_lt hUM, show wm = wm - 1 + 1 by omega_using [hw], wv,
      kSw _ (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]) (by omega_using [hw, hL, hH, hHR, hHM, hHT, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT, hc, hsc, hcv]) (by omega_using []) (by omega_using [hw, hL, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hcv]), hR0, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
      o₅.wv (by omega_using [hw, hL, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]), o₄.wv (by omega_using [hw, hL, hHR, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]), m₃, v₂, oC.wv (by omega_using [hw, hL, _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hsc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]), ← hUv,
      wv_shr_words _ _ _ (show c ≤ L by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hcv]), show L - c = wm - 1 by omega_using [hw, hL, hL', hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hcv]]
  have h₀ : DQInv s₀ B Z eU eR eM eT wm c M z U 0 s₀ := by
    refine ⟨hs₀, Keep.refl _ _, ?_, ?_, ?_, by rw [Nat.sub_zero]; exact hr₀, ?_, fun i _ => rfl, ?_, ?_, ?_, hv₀, ?_,
      Frm.refl _ _ _⟩
    · rw [k₅.gpr .x8 (by decide), k₄.gpr .x8 (by decide), k₃.gpr .x8 (by decide), k₂.gpr .x8 (by decide), h8₁,
        Nat.sub_zero]
    · rw [k₅.gpr .x12 (by decide), k₄.gpr .x12 (by decide), h12₃]
    · rw [o₅.word (by omega_using [hHT]) (by omega_using [hsc]), o₄.word (by omega_using [hHT]) (by omega_using [hsc]), m₃, o₂.word (by omega_using [hw, hL, hH, hHR, hHM, hHT, hRZ, hMZ, sUR, sUM, sRM, sRT, sMT, hc, hsc, hcv]) (by omega_using [hsc]), hm₁,
        word_writeW_self, Nat.sub_zero]
    · rw [Nat.sub_zero, Nat.div_eq_of_lt hUM]; rfl
    · rw [o₅.wv (by omega_using [hw, hL, hHM, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]), o₄.wv (by omega_using [hw, hL, hHM, hHT, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hcv]) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]), hM₃]
    · rw [o₅.word (by omega_using []) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hsc, hcv])]; exact hP₄
    · rw [o₅.word (by omega_using []) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hsc, hcv])]; exact hD₄
    · rw [o₅.word (by omega_using []) (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hsc, hcv])]; exact hDl₄
  have f₀ : Frm B [(eU, 8 * c), (eR, 8 * (wm + 1)), (eT, 32), (8 * sCnt, 8)] s.mem s₀.mem :=
    (((((Frm.of_outside oC (by simp)).trans (by rw [m₃]; exact Frm.of_outside (o₂.mono (o' := eR)
      (n' := 8 * (wm + 1)) (by omega_using []) (by omega_using [])) (by simp))).trans
      (Frm.of_outside (o₄.mono (o' := eT) (n' := 32) (by omega_using []) (by omega_using [])) (by simp))).trans
      (Frm.of_outside (o₅.mono (o' := eT) (n' := 32) (by omega_using []) (by omega_using [])) (by simp))))
  exact ⟨z, hz, hd₄, hUw, h₀, k₀₅.mono (by decide), kS _ _ (by omega_using [hw, hL, hL', _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hc1, hsc, hcv]) (by omega_using [hw, hL, _hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hsc, hcv]) (by omega_using [hw, hL, _hU8, hH, hHR, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hcv]) (by omega_using [hw, hL, _hU8, hH, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hc1, hcv]), f₀⟩

/-- `divQN`: `⌊U / M⌋` in place of `U`'s low `c = L - w_m + 1` words and `U mod M` into `[R]`, for `U` the `L`
words at `x8`, `M` the `w_m ≥ 4` words at `x9` (its top word not zero), `[R]` at `x11` (word `w_m - 1` zero) and
the temporary at `x6`. -/
theorem divQN_ok {s : State} {B : Addr} {Z eU eR eM eT L wm : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h8 : s.gpr .x8 = off B eU) (h13 : s.gpr .x13 = BitVec.ofNat 64 L) (h11 : s.gpr .x11 = off B eR)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 wm) (h9 : s.gpr .x9 = off B eM) (h6 : s.gpr .x6 = off B eT)
    (h7 : s.gpr .x7 = 0) (hw : 4 ≤ wm) (hL : wm ≤ L) (hL' : L < 2 ^ 19)
    (hU8 : 8 ≤ eU) (hH : 8 * sCnt + 8 ≤ eU) (hHR : 8 * sCnt + 8 ≤ eR) (hHM : 8 * sCnt + 8 ≤ eM)
    (hHT : 8 * sCnt + 8 ≤ eT)
    (hUZ : eU + 8 * L ≤ Z) (hRZ : eR + 8 * (wm + 1) ≤ Z) (hMZ : eM + 8 * wm ≤ Z) (hTZ : eT + 32 ≤ Z)
    (sUR : eU + 8 * L ≤ eR ∨ eR + 8 * (wm + 1) ≤ eU) (sUM : eU + 8 * L ≤ eM ∨ eM + 8 * wm ≤ eU)
    (sUT : eU + 8 * L ≤ eT ∨ eT + 32 ≤ eU) (sRM : eR + 8 * (wm + 1) ≤ eM ∨ eM + 8 * wm ≤ eR)
    (sRT : eR + 8 * (wm + 1) ≤ eT ∨ eT + 32 ≤ eR) (sMT : eM + 8 * wm ≤ eT ∨ eT + 32 ≤ eM)
    (hR0 : word s.mem B (eR + 8 * (wm - 1)) = 0) (hR1 : word s.mem B (eR + 8 * wm) = 0)
    (htop : 2 ^ (64 * (wm - 1)) ≤ wv s.mem B eM wm) :
    WP isa divQN s fun t =>
      wv t.mem B eR (wm + 1) = wv s.mem B eU L % wv s.mem B eM wm ∧
      wv t.mem B eU (L - wm + 1) = wv s.mem B eU L / wv s.mem B eM wm ∧
      wv t.mem B (eU + 8 * (L - wm + 1)) (wm - 1) = wv s.mem B (eU + 8 * (L - wm + 1)) (wm - 1) ∧
      Frm B [(eU, 8 * (L - wm + 1)), (eR, 8 * (wm + 1)), (eT, 32), (8 * sCnt, 8)] s.mem t.mem ∧
      t.gpr .x12 = BitVec.ofNat 64 wm ∧ Keep dqRegs s t := by
  have hn := hs.nowrap
  rw [divQN_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (dqHead_ok hs h0 h8 h13 h11 h12 h9 h6 h7 hw hL hL' hU8 hH hHR hHM hHT hUZ hRZ hMZ hTZ sUR sUM sUT sRM sRT sMT hR0 hR1 htop)
    fun s₀ ⟨z, hz, hd₄, hUw, h₀, k₀₅, kS₀, f₀⟩ => ?_)
  generalize hc : L - wm + 1 = c at hUw h₀ kS₀ f₀ ⊢
  generalize hUv : wv s.mem B eU L = U at hUw h₀ ⊢
  generalize hMv : wv s.mem B eM wm = M at htop hd₄ h₀ ⊢
  have hM0 : 0 < M := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) htop
  have hs₀ := h₀.scr
  simp only [seqs]
  refine WP.mono (VG.Proof.MlKem.AArch64.count_loop (n := c) (by omega_using [hc]) (DQInv s₀ B Z eU eR eM eT wm c M z U)
    (fun j hj t hI => dqStep_ok hs₀ ((k₀₅.gpr .x0 (by decide)).trans h0) ((k₀₅.gpr .x11 (by decide)).trans h11)
      ((k₀₅.gpr .x9 (by decide)).trans h9) ((k₀₅.gpr .x6 (by decide)).trans h6) ((k₀₅.gpr .x7 (by decide)).trans h7)
      hw (by omega_using [hw, hL, hL', hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hj]) (by omega_using [hw, hL, hL', hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hj]) hU8 (by omega_using [hHR]) hH hHR hHM hHT (by omega_using [hw, hL, hL', hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hj]) hRZ hMZ hTZ (by omega_using [hw, hL, hU8, hH, hHR, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hj]) (by omega_using [hw, hL, hU8, hH, hHM, hUZ, hRZ, hMZ, sUR, sUM, sUT, sRM, sRT, sMT, hc, hj])
      (by omega_using [hw, hL, hL', hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, hj]) sRM sRT sMT hz hd₄ hM0 hUw hj hI) h₀) fun t hI => ?_
  have e0 : c - c = 0 := Nat.sub_self c
  have hr := hI.r
  have hq := hI.q
  rw [e0, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at hr hq
  rw [Nat.add_zero] at hq
  refine ⟨by rw [hr, ← hUv, ← hMv], by rw [hq, ← hUv, ← hMv], ?_, ?_, hI.x12, (k₀₅.trans hI.keep).mono (by decide)⟩
  · rw [hI.frm.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [hw, hL, hL', hU8, hH, hHR, hHM, hHT, hUZ, hRZ, hMZ, hTZ, sUR, sUM, sUT, sRM, sRT, sMT, hn, hc, e0]), kS₀]
  · exact f₀.trans (hI.frm.mono (by simp))

/-- `clearN`: the `n ≥ 1` words at `x16` (`x14 = n`) cleared. -/
theorem clearN_ok {s : State} {B : Addr} {Z n e : Nat} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 n) (h7 : s.gpr .x7 = 0) (hn1 : 1 ≤ n) (hn' : n < 2 ^ 31) (he : e + 8 * n ≤ Z) :
    WP isa clearN s fun t => wv t.mem B e n = 0 ∧ Outside B e (8 * n) s.mem t.mem ∧ Keep [.x14, .x16] s t := by
  have hn := hs.nowrap
  have hstep : ∀ j < n, ∀ t, ZeroInv s B Z e j t → t.gpr .x14 = BitVec.ofNat 64 (n - j) →
      WP isa (.block ([st .x7 .x16, next .x16] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
        fun t' => ZeroInv s B Z e (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
    intro j hj t hI _
    have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x16] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (e + 8 * j)) (0 : BitVec 64) ∧
      t₁.gpr .x16 = off B (e + 8 * j + 8))
      (by brun [hI.x16, t7, hI.scr.st (show e + 8 * j + 8 ≤ Z by omega_using [he, hj])]) (by decide) (by decide)
        (by decide +kernel)) fun t₁ ⟨⟨hm, h16'⟩, k₁⟩ => ?_
    refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
    refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
      by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
    · rw [hm', hm]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega_using [he, hn, hj]) x (by omega_using [hx])]
      exact hI.out x (by omega_using [hx])
    · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [he, hn, hj]), hI.val]
      rfl
  unfold clearN
  exact WP.mono (wp_countdown (N := n) (by omega_using [hn']) (by omega_using [hn1]) (ZeroInv s B Z e) hstep
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, rfl⟩ h14)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## `m` and `r` -/

/-- A wide array whose words above the narrow width are zero has the narrow value. -/
theorem wide_low {m : Mem} {B : Addr} {v d : Nat} (hz : wv m B (d + 8 * v) (v + 2) = 0) :
    wv m B d (2 * v + 2) = wv m B d v := by
  rw [show 2 * v + 2 = v + (v + 2) by omega_using [], wv_add, hz, Nat.mul_zero, Nat.add_zero]

/-- What `divQN_ok` needs. -/
structure DQH (s : State) (B : Addr) (Z eU eR eM eT L wm : Nat) : Prop where
  hs : Scr s B Z
  h0 : s.gpr .x0 = B
  h8 : s.gpr .x8 = off B eU
  h13 : s.gpr .x13 = BitVec.ofNat 64 L
  h11 : s.gpr .x11 = off B eR
  h12 : s.gpr .x12 = BitVec.ofNat 64 wm
  h9 : s.gpr .x9 = off B eM
  h6 : s.gpr .x6 = off B eT
  h7 : s.gpr .x7 = 0
  hw : 4 ≤ wm
  hL : wm ≤ L
  hL' : L < 2 ^ 19
  hU8 : 8 ≤ eU
  hH : 8 * sCnt + 8 ≤ eU
  hHR : 8 * sCnt + 8 ≤ eR
  hHM : 8 * sCnt + 8 ≤ eM
  hHT : 8 * sCnt + 8 ≤ eT
  hUZ : eU + 8 * L ≤ Z
  hRZ : eR + 8 * (wm + 1) ≤ Z
  hMZ : eM + 8 * wm ≤ Z
  hTZ : eT + 32 ≤ Z
  sUR : eU + 8 * L ≤ eR ∨ eR + 8 * (wm + 1) ≤ eU
  sUM : eU + 8 * L ≤ eM ∨ eM + 8 * wm ≤ eU
  sUT : eU + 8 * L ≤ eT ∨ eT + 32 ≤ eU
  sRM : eR + 8 * (wm + 1) ≤ eM ∨ eM + 8 * wm ≤ eR
  sRT : eR + 8 * (wm + 1) ≤ eT ∨ eT + 32 ≤ eR
  sMT : eM + 8 * wm ≤ eT ∨ eT + 32 ≤ eM
  hR0 : word s.mem B (eR + 8 * (wm - 1)) = 0
  hR1 : word s.mem B (eR + 8 * wm) = 0
  htop : 2 ^ (64 * (wm - 1)) ≤ wv s.mem B eM wm

theorem DQH.ok {s : State} {B : Addr} {Z eU eR eM eT L wm : Nat} (h : DQH s B Z eU eR eM eT L wm) :
    WP isa divQN s fun t =>
      wv t.mem B eR (wm + 1) = wv s.mem B eU L % wv s.mem B eM wm ∧
      wv t.mem B eU (L - wm + 1) = wv s.mem B eU L / wv s.mem B eM wm ∧
      wv t.mem B (eU + 8 * (L - wm + 1)) (wm - 1) = wv s.mem B (eU + 8 * (L - wm + 1)) (wm - 1) ∧
      Frm B [(eU, 8 * (L - wm + 1)), (eR, 8 * (wm + 1)), (eT, 32), (8 * sCnt, 8)] s.mem t.mem ∧
      t.gpr .x12 = BitVec.ofNat 64 wm ∧ Keep dqRegs s t :=
  divQN_ok h.hs h.h0 h.h8 h.h13 h.h11 h.h12 h.h9 h.h6 h.h7 h.hw h.hL h.hL' h.hU8 h.hH h.hHR h.hHM h.hHT h.hUZ h.hRZ
    h.hMZ h.hTZ h.sUR h.sUM h.sUT h.sRM h.sRT h.sMT h.hR0 h.hR1 h.htop

/-- `divA` up to the division. -/
abbrev divAP : List (Prog isa) := [.block setWid, zeroA wN, .block setNar, copyA nN Public.aN, .block setWid,
  zeroA wX, zeroA wT,
  .block (setNar ++ ws ++ base Public.aN .x9 ++ setWid ++ ws ++ base wT .x6 ++ base wA .x8 ++ base wX .x5 ++
    [mov .x11 .x5, mov .x13 .x12, .lsr .x .x12 .x12 1, .subImm .x .x12 .x12 2, movi .x7 0])]

/-- `divA` after the division. -/
abbrev divAT : List (Prog isa) := [
  .block (ws ++ base wA .x16 ++ [.lsr .x .x14 .x12 1, .addImm .x .x3 .x14 3, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3,
    .subImm .x .x14 .x14 3, movi .x7 0]),
  clearN,
  .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base wA .x16 ++ base wN .x17), cmpLoop,
  .block (borrowMask ++ andMask)]

theorem divA_eq : divA = seqs (divAP ++ divQN :: divAT) := rfl

/-- `divA` up to the division: `n` wide, `r` and the temporary cleared, and `divQN`'s registers. -/
theorem divA1_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) {A N : Nat}
    (hA : wv s.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A) (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N)
    (hlo : 256 ^ (I.k - 1) ≤ N) (hNk : N < 2 ^ (8 * I.k)) :
    WP isa (seqs divAP) s fun t => G I m₀ (Wk I.k) c t ∧
      DQH t I.B I.Z (slot (Wk I.k) wA) (slot (Wk I.k) wX) (slot (vk I.k) 0) (slot (Wk I.k) wT) (Wk I.k) (vk I.k - 1) ∧
      wv t.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A ∧ wv t.mem I.B (slot (vk I.k) 0) (vk I.k - 1) = N ∧
      wv t.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N ∧
      (∀ q < Wk I.k + 2, word t.mem I.B (slot (Wk I.k) wX + 8 * q) = 0) ∧
      (∀ d n, 256 ≤ d → d + 8 * n ≤ slot (vk I.k) nN → wv t.mem I.B d n = wv s.mem I.B d n) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hk1 := L.k1
  have hk2 := L.k2
  have hv9 : 9 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
  have hv2 : vk I.k ≤ 200 := by simp only [vk]; omega_using [hk2]
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := hb32_of h L
  have q32 : slot (vk I.k) 32 = 256 + 32 * (8 * (vk I.k + 2)) := rfl
  have q0 : slot (vk I.k) 0 = 256 + 0 * (8 * (vk I.k + 2)) := rfl
  have q8 : slot (vk I.k) nN = 256 + 8 * (8 * (vk I.k + 2)) := rfl
  have qN : slot (Wk I.k) wN = 256 + 4 * (8 * (Wk I.k + 2)) := rfl
  have qX : slot (Wk I.k) wX = 256 + 6 * (8 * (Wk I.k + 2)) := rfl
  have qA : slot (Wk I.k) wA = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qT : slot (Wk I.k) wT = 256 + 9 * (8 * (Wk I.k + 2)) := rfl
  have e48 : slot (Wk I.k) wN = slot (vk I.k) nN := slot_wide _ _
  -- `n` in `v - 1` words, its top word not zero.
  have hN1 : N < 2 ^ (64 * (vk I.k - 1)) :=
    Nat.lt_of_lt_of_le hNk (Nat.pow_le_pow_right (by decide) (by simp only [vk]; omega_using []))
  have hNlo : 2 ^ (64 * (vk I.k - 2)) ≤ N := by
    refine Nat.le_trans ?_ hlo
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by simp only [vk]; omega_using [])
  simp only [seqs]
  -- `n` wide.
  refine WP.seq (WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := wN) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (g₂.setNar_ok L) fun s₃ ⟨g₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (copyA_ok g₃.ws (o := nN) (a := Public.aN) (by decide) (by decide) (by decide))
    fun s₄ ⟨v₄, o₄, _, _, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega_using []) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (g₄.setWid_ok L) fun s₅ ⟨g₅, f₅, k₅⟩ => ?_)
  have hn := g₅.ws.scr.nowrap
  have hZW := g₅.ws.hZ
  have qW16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  have hz₂ : wv s₂.mem I.B (slot (vk I.k) nN + 8 * vk I.k) (vk I.k + 2) = 0 := by
    have := wv_add s₂.mem I.B (slot (Wk I.k) wN) (vk I.k) (vk I.k + 2 + 2)
    rw [show vk I.k + (vk I.k + 2 + 2) = Wk I.k + 2 by omega_using [hW], z₂, e48] at this
    have e := wv_add s₂.mem I.B (slot (vk I.k) nN + 8 * vk I.k) (vk I.k + 2) 2
    have : 2 ^ (64 * vk I.k) * wv s₂.mem I.B (slot (vk I.k) nN + 8 * vk I.k) (vk I.k + 2 + 2) = 0 := by omega_using [this]
    have := (Nat.mul_eq_zero.mp this).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
    rw [e] at this; omega_using [this]
  have nW₅ : wv s₅.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N := by
    rw [Frm.hdrW_wv f₅ (slot_ge _ _) (by omega_using [hW, hv2, qN]), e48, hW, wide_low, v₄,
      show slot (vk I.k) Public.aN = slot (vk I.k) 0 from rfl,
      Frm.hdrW_wv f₃ (slot_ge _ _) (by omega_using [hv2, q0]), o₂.wv (by omega_using [hW, q0, qN]) (by omega_using [hv2, q0]),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega_using [hv2, q0]), hN]
    rw [o₄.wv (.inr (by omega_using [])) (by omega_using [hv2, q8]), Frm.hdrW_wv f₃ (by omega_using [q8]) (by omega_using [hv2, q8]), hz₂]
  -- What the start keeps of the arrays below wide array 4.
  have k₅ : ∀ d n, 256 ≤ d → d + 8 * n ≤ slot (vk I.k) nN → wv s₅.mem I.B d n = wv s.mem I.B d n := fun d n hd hd' => by
    rw [Frm.hdrW_wv f₅ hd (by omega_using [hv2, q8, hd']), o₄.wv (by omega_using [hd']) (by omega_using [hv2, q8, hd']), Frm.hdrW_wv f₃ hd (by omega_using [hv2, q8, hd']),
      o₂.wv (by omega_using [e48, hd']) (by omega_using [hv2, q8, hd']), Frm.hdrW_wv f₁ hd (by omega_using [hv2, q8, hd'])]
  have aW₅ : wv s₅.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A := by
    rw [Frm.hdrW_wv f₅ (slot_ge _ _) (by omega_using [hW, hv2, qA]), o₄.wv (by omega_using [hW, q8, qA]) (by omega_using [hW, hv2, qA]),
      Frm.hdrW_wv f₃ (slot_ge _ _) (by omega_using [hW, hv2, qA]), o₂.wv (by omega_using [qN, qA]) (by omega_using [hW, hv2, qA]),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega_using [hW, hv2, qA]), hA]
  -- `r` and the temporary cleared.
  refine WP.seq (WP.mono (zeroA_ok g₅.ws (j := wX) (by decide)) fun s₆ ⟨z₆, o₆, _, _, _, k₆⟩ => ?_)
  have g₆ := g₅.out (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine WP.seq (WP.mono (zeroA_ok g₆.ws (j := wT) (by decide)) fun s₇ ⟨_, o₇, _, _, _, k₇⟩ => ?_)
  have g₇ := g₆.out (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  -- The registers of the division.
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (g₇.setNar_ok L) fun t₁ ⟨g₁', f₁', k₁'⟩ => ?_
  refine WP.mono (ws_ok g₁'.ws.scr g₁'.ws.x0 g₁'.ws.h256 g₁'.ws.hw g₁'.ws.hS) fun t₂ ⟨⟨_, h11₂, m₂, _⟩, k₂'⟩ => ?_
  refine WP.mono (base_ok Public.aN .x9 ((k₂'.gpr .x0 (by decide)).trans g₁'.ws.x0) h11₂) fun t₃ ⟨⟨h9₃, m₃, _⟩, k₃'⟩ => ?_
  have g₃' := g₁'.same (by rw [m₃, m₂]) (k₂'.trans k₃') (by decide)
  refine WP.mono (g₃'.setWid_ok L) fun t₄ ⟨g₄', f₄', k₄'⟩ => ?_
  refine WP.mono (ws_ok g₄'.ws.scr g₄'.ws.x0 g₄'.ws.h256 g₄'.ws.hw g₄'.ws.hS) fun t₅ ⟨⟨h12₅, h11₅, m₅, _⟩, k₅'⟩ => ?_
  have x0₅ : t₅.gpr .x0 = I.B := (k₅'.gpr .x0 (by decide)).trans g₄'.ws.x0
  refine WP.mono (base_ok wT .x6 x0₅ h11₅) fun t₆ ⟨⟨h6₆, m₆, _⟩, k₆'⟩ => ?_
  refine WP.mono (base_ok wA .x8 ((k₆'.gpr .x0 (by decide)).trans x0₅) ((k₆'.gpr .x11 (by decide)).trans h11₅))
    fun t₇ ⟨⟨h8₇, m₇, _⟩, k₇'⟩ => ?_
  refine WP.mono (base_ok wX .x5 ((k₇'.gpr .x0 (by decide)).trans ((k₆'.gpr .x0 (by decide)).trans x0₅))
    ((k₇'.gpr .x11 (by decide)).trans ((k₆'.gpr .x11 (by decide)).trans h11₅))) fun t₈ ⟨⟨h5₈, m₈, _⟩, k₈'⟩ => ?_
  have h12₈ : t₈.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := by
    rw [k₈'.gpr .x12 (by decide), k₇'.gpr .x12 (by decide), k₆'.gpr .x12 (by decide), h12₅]
  refine WP.mono (WP.keep [.x7, .x11, .x12, .x13] (Q := fun t => t.gpr .x11 = off I.B (slot (Wk I.k) wX) ∧
      t.gpr .x13 = BitVec.ofNat 64 (Wk I.k) ∧ t.gpr .x12 = BitVec.ofNat 64 (vk I.k - 1) ∧ t.gpr .x7 = 0 ∧
      t.mem = t₈.mem) (by
    brun [h5₈, h12₈]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    simp only [Wk, vk] at *
    omega_using [hk2]) (by decide) (by decide) (by decide +kernel)) fun s₈ ⟨⟨h11, h13, h12, h7, m₉⟩, k₉⟩ => ?_
  have k₁₉ := (((((((k₁'.trans k₂').trans k₃').trans k₄').trans k₅').trans k₆').trans k₇').trans k₈').trans k₉
  have g₈ : G I m₀ (Wk I.k) c s₈ := g₄'.same (by rw [m₉, m₈, m₇, m₆, m₅]) ((((k₅'.trans k₆').trans k₇').trans k₈').trans k₉)
    (by decide)
  have k₈ : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → (d + 8 * n ≤ slot (Wk I.k) wX ∨ slot (Wk I.k) wX + 8 * (Wk I.k + 2) ≤ d) →
      (d + 8 * n ≤ slot (Wk I.k) wT ∨ slot (Wk I.k) wT + 8 * (Wk I.k + 2) ≤ d) →
      wv s₈.mem I.B d n = wv s₅.mem I.B d n := fun d n hd hd' h1 h2 => by
    rw [m₉, m₈, m₇, m₆, m₅, Frm.hdrW_wv f₄' hd hd', m₃, m₂, Frm.hdrW_wv f₁' hd hd', o₇.wv h2 hd', o₆.wv h1 hd']
  have kw₈ : ∀ d, 256 ≤ d → d + 8 ≤ 2 ^ 64 → (d + 8 ≤ slot (Wk I.k) wT ∨ slot (Wk I.k) wT + 8 * (Wk I.k + 2) ≤ d) →
      word s₈.mem I.B d = word s₆.mem I.B d := fun d hd hd' h2 => by
    rw [m₉, m₈, m₇, m₆, m₅, Frm.hdrW_word f₄' hd hd', m₃, m₂, Frm.hdrW_word f₁' hd hd', o₇.word h2 hd']
  have zX : ∀ q < Wk I.k + 2, word s₈.mem I.B (slot (Wk I.k) wX + 8 * q) = 0 := fun q hq => by
    rw [kw₈ _ (by omega_using [qX]) (by omega_using [hW, hv2, qX, hq]) (by omega_using [qX, qT, hq])]; exact (wv_eq_zero_iff _ _ _ _).mp z₆ q hq
  have hsC : 8 * sCnt + 8 ≤ 256 := by decide
  have hM₈ : wv s₈.mem I.B (slot (vk I.k) 0) (vk I.k - 1) = N := by
    rw [k₈ _ _ (by omega_using [q0]) (by omega_using [hv2, q0]) (by omega_using [hW, q0, qX]) (by omega_using [hW, q0, qT]), k₅ _ _ (by omega_using [q0]) (by omega_using [q0, q8]),
      ← wv_mod _ _ _ (show vk I.k - 1 ≤ vk I.k by omega_using []), hN, Nat.mod_eq_of_lt hN1]
  have hU₈ : wv s₈.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A := by
    rw [k₈ _ _ (by omega_using [qA]) (by omega_using [hW, hv2, qA]) (by omega_using [qX, qA]) (by omega_using [qA, qT]), aW₅]
  have h9₈ : s₈.gpr .x9 = off I.B (slot (vk I.k) 0) := by
    rw [k₉.gpr .x9 (by decide), k₈'.gpr .x9 (by decide), k₇'.gpr .x9 (by decide), k₆'.gpr .x9 (by decide),
      k₅'.gpr .x9 (by decide), k₄'.gpr .x9 (by decide), h9₃]; rfl
  refine ⟨g₈, ⟨g₈.ws.scr, g₈.ws.x0, by rw [k₉.gpr .x8 (by decide), k₈'.gpr .x8 (by decide), h8₇], h13, h11, h12,
    h9₈, by rw [k₉.gpr .x6 (by decide), k₈'.gpr .x6 (by decide), k₇'.gpr .x6 (by decide), h6₆], h7,
    by omega_using [hv9], by omega_using [hW], by simp only [Wk, vk]; omega_using [hk2], by omega_using [qA], by omega_using [qA, hsC], by omega_using [qX, hsC], by omega_using [q0, hsC], by omega_using [qT, hsC],
    by omega_using [qA, hZW, qW16], by omega_using [hW, qX, hZW, qW16], by omega_using [hW, q0, hZW, qW16], by omega_using [qT, hZW, qW16], by omega_using [hW, qX, qA], by omega_using [hW, q0, qA], by omega_using [qA, qT], by omega_using [hW, q0, qX], by omega_using [hW, qX, qT], by omega_using [hW, q0, qT],
    by rw [zX _ (by omega_using [hW])], by rw [zX _ (by omega_using [hW])], by rw [hM₈]; exact hNlo⟩, hU₈, hM₈, ?_, zX, fun d n hd hd' => ?_⟩
  · rw [k₈ _ _ (by omega_using [qN]) (by omega_using [hW, hv2, qN]) (by omega_using [qN, qX]) (by omega_using [qN, qT]), nW₅]
  · rw [k₈ _ _ hd (by omega_using [hv2, q8, hd']) (by omega_using [hW, q8, qX, hd']) (by omega_using [hW, q8, qT, hd']), k₅ _ _ hd hd']

/-- `divA`: `m = ⌊a / n⌋` (wide array 7) and `r = a mod n` (wide array 6) by long division with the quotient,
`n` wide (wide array 4), and `m < n` and'ed into the mask. -/
theorem divA_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) {A N : Nat}
    (hA : wv s.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A) (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N)
    (hlo : 256 ^ (I.k - 1) ≤ N) (hNk : N < 2 ^ (8 * I.k)) :
    WP isa divA s fun t => G I m₀ (Wk I.k) (c && decide (A / N < N)) t ∧
      wv t.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A / N ∧
      wv t.mem I.B (slot (Wk I.k) wX) (Wk I.k + 1) = A % N ∧
      wv t.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N ∧
      (∀ j k, j < 8 → k ≤ vk I.k + 2 → wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hk1 := L.k1
  have hk2 := L.k2
  have hv9 : 9 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
  have hv2 : vk I.k ≤ 200 := by simp only [vk]; omega_using [hk2]
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := hb32_of h L
  have q32 : slot (vk I.k) 32 = 256 + 32 * (8 * (vk I.k + 2)) := rfl
  have qN : slot (Wk I.k) wN = 256 + 4 * (8 * (Wk I.k + 2)) := rfl
  have qX : slot (Wk I.k) wX = 256 + 6 * (8 * (Wk I.k + 2)) := rfl
  have qA : slot (Wk I.k) wA = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qT : slot (Wk I.k) wT = 256 + 9 * (8 * (Wk I.k + 2)) := rfl
  have hn := h.ws.scr.nowrap
  have qW16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  rw [divA_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (divA1_ok h L hA hN hlo hNk)
    fun s₈ ⟨g₈, hh, hU₈, hM₈, nW₈, zX, kS₈⟩ => ?_)
  have hZW := g₈.ws.hZ
  have hsC : 8 * sCnt + 8 ≤ 256 := by decide
  have q8 : slot (vk I.k) nN = 256 + 8 * (8 * (vk I.k + 2)) := rfl
  have e48 : slot (Wk I.k) wN = slot (vk I.k) nN := slot_wide _ _
  simp only [seqs]
  -- The division.
  refine WP.seq (WP.mono hh.ok
    fun s₉ ⟨hr₉, hq₉, _, f₉, _, k₉'⟩ => ?_)
  rw [hU₈, hM₈, show vk I.k - 1 + 1 = vk I.k by omega_using [hv9]] at hr₉
  rw [hU₈, hM₈, show Wk I.k - (vk I.k - 1) + 1 = vk I.k + 4 by omega_using [hW, hv9]] at hq₉
  rw [show vk I.k - 1 + 1 = vk I.k by omega_using [hv9], show Wk I.k - (vk I.k - 1) + 1 = vk I.k + 4 by omega_using [hW, hv9]] at f₉
  have g₉ : G I m₀ (Wk I.k) c s₉ := g₈.frmOwn (sl := sCnt) ⟨by decide, by decide, by decide⟩
    (rs := [(slot (Wk I.k) wA, 8 * (vk I.k + 4)), (slot (Wk I.k) wX, 8 * vk I.k), (slot (Wk I.k) wT, 32)]) f₉
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
    k₉' (by decide)
  have k₉m : ∀ d n, d + 8 * n ≤ 2 ^ 64 → (d + 8 * n ≤ slot (Wk I.k) wA ∨ slot (Wk I.k) wA + 8 * (vk I.k + 4) ≤ d) →
      (d + 8 * n ≤ slot (Wk I.k) wX ∨ slot (Wk I.k) wX + 8 * vk I.k ≤ d) →
      (d + 8 * n ≤ slot (Wk I.k) wT ∨ slot (Wk I.k) wT + 32 ≤ d) → (d + 8 * n ≤ 8 * sCnt ∨ 8 * sCnt + 8 ≤ d) →
      wv s₉.mem I.B d n = wv s₈.mem I.B d n := fun d n hd h1 h2 h3 h4 => f₉.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4]) hd
  -- The quotient's top words cleared.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ws_ok g₉.ws.scr g₉.ws.x0 g₉.ws.h256 g₉.ws.hw g₉.ws.hS) fun s₁₀ ⟨⟨h12₁₀, h11₁₀, m₁₀, _⟩, k₁₀⟩ => ?_
  refine WP.mono (base_ok wA .x16 ((k₁₀.gpr .x0 (by decide)).trans g₉.ws.x0) h11₁₀) fun s₁₁ ⟨⟨h16₁₁, m₁₁, _⟩, k₁₁⟩ => ?_
  have h12₁₁ : s₁₁.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := (k₁₁.gpr .x12 (by decide)).trans h12₁₀
  refine WP.mono (WP.keep [.x3, .x7, .x14, .x16] (Q := fun t => t.gpr .x16 = off I.B (slot (Wk I.k) wA + 8 * (vk I.k + 4)) ∧
      t.gpr .x14 = BitVec.ofNat 64 (vk I.k - 2) ∧ t.gpr .x7 = 0 ∧ t.mem = s₁₁.mem) (by
    have e1 : BitVec.ofNat 64 (Wk I.k) >>> 1 = BitVec.ofNat 64 (vk I.k + 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [Wk, vk] at *; omega_using [hk2]
    have e2 : (BitVec.ofNat 64 (vk I.k + 1) + BitVec.ofNat 64 3) <<< 3 = BitVec.ofNat 64 (8 * (vk I.k + 4)) := by
      rw [BitVec.ofNat_add_ofNat, shl_ofNat (show (vk I.k + 1 + 3) * 2 ^ 3 < 2 ^ 64 by omega_using [hv2])]; congr 1; omega_using []
    brun [h16₁₁, h12₁₁, e1, e2, off_add, ofNat_sub_ofNat (show 3 ≤ vk I.k + 1 by omega_using [hv9]) (by omega_using [hv2])]
    congr 1) (by decide) (by decide) (by decide +kernel)) fun s₁₂ ⟨⟨h16₁₂, h14₁₂, h7₁₂, m₁₂⟩, k₁₂⟩ => ?_
  have g₁₂ : G I m₀ (Wk I.k) c s₁₂ := g₉.same (by rw [m₁₂, m₁₁, m₁₀]) ((k₁₀.trans k₁₁).trans k₁₂) (by decide)
  refine WP.seq (WP.mono (clearN_ok g₁₂.ws.scr h16₁₂ h14₁₂ h7₁₂ (by omega_using [hv9]) (by omega_using [hv2]) (by omega_using [hW, qA, qW16, hZW]))
    fun s₁₃ ⟨z₁₃, o₁₃, k₁₃⟩ => ?_)
  have g₁₃ := g₁₂.out (j := wA) (n := 8 * (Wk I.k + 2)) (by decide) (Nat.le_refl _) (o₁₃.mono (by omega_using []) (by omega_using [hW])) k₁₃
    (by decide)
  have vA₁₃ : wv s₁₃.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A / N := by
    have e := wv_add s₁₃.mem I.B (slot (Wk I.k) wA) (vk I.k + 4) (vk I.k - 2)
    rw [show vk I.k + 4 + (vk I.k - 2) = Wk I.k by omega_using [hW, hv9], z₁₃, Nat.mul_zero, Nat.add_zero] at e
    rw [e, o₁₃.wv (d := slot (Wk I.k) wA) (k := vk I.k + 4) (by omega_using []) (by omega_using [hW, hv2, qA]), m₁₂, m₁₁, m₁₀, hq₉]
  have vN₁₃ : wv s₁₃.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N := by
    rw [o₁₃.wv (by omega_using [qN, qA]) (by omega_using [hW, hv2, qN]), m₁₂, m₁₁, m₁₀, k₉m _ _ (by omega_using [hW, hv2, qN]) (by omega_using [qN, qA]) (by omega_using [qN, qX]) (by omega_using [qN, qT]) (by omega_using [qN, hsC]),
      nW₈]
  have vX₁₃ : wv s₁₃.mem I.B (slot (Wk I.k) wX) (Wk I.k + 1) = A % N := by
    have e := wv_add s₁₃.mem I.B (slot (Wk I.k) wX) (vk I.k) (Wk I.k + 1 - vk I.k)
    rw [show vk I.k + (Wk I.k + 1 - vk I.k) = Wk I.k + 1 by omega_using [hW]] at e
    rw [e, o₁₃.wv (by omega_using [qX, qA]) (by omega_using [hW, hv2, qX]), o₁₃.wv (by omega_using [qX, qA]) (by omega_using [hW, hv2, qX]), m₁₂, m₁₁, m₁₀, hr₉,
      k₉m _ _ (by omega_using [hW, hv2, qX]) (by omega_using [hW, qX, qA]) (by omega_using []) (by omega_using [hW, qX, qT]) (by omega_using [qX, hsC]),
      (wv_eq_zero_iff _ _ _ _).mpr (fun q hq => by rw [Nat.add_assoc, ← Nat.mul_add]; exact zX _ (by omega_using [hq])),
      Nat.mul_zero, Nat.add_zero]
  -- `m < n`.
  refine WP.seq (WP.mono (cmpSet_ok' g₁₃.ws wA wN) fun s₁₄ ⟨⟨h16, h17, h14, _, _, h7', hc, m₁₄⟩, k₁₄⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (g₁₃.ws.scr.congr k₁₄.wr) h16 h17 h14 hc (by omega_using [hW]) (by omega_using [hW, hv2]) (by omega_using [qA, qW16, hZW])
    (by omega_using [qN, qW16, hZW])) fun s₁₅ ⟨c₁₅, m₁₅, k₁₅⟩ => ?_)
  rw [m₁₄, vA₁₃, vN₁₃] at c₁₅
  have g₁₅ := (g₁₃.same m₁₄ k₁₄ (by decide)).same m₁₅ k₁₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (borrowMask_ok s₁₅ ((k₁₅.gpr .x7 (by decide)).trans h7')) fun s₁₆ ⟨⟨h15, m₁₆, _⟩, k₁₆⟩ => ?_
  rw [c₁₅, Bool.not_not] at h15
  refine WP.mono (andMask_ok (g₁₅.same m₁₆ k₁₆ (by decide)) h15) fun t ⟨gt, ot, _⟩ => ⟨gt, ?_, ?_, ?_, fun j k hj hk => ?_⟩
  · rw [ot.wv (hd_sep (by decide)) (by omega_using [hW, hv2, qA]), m₁₆, m₁₅, m₁₄, vA₁₃]
  · rw [ot.wv (hd_sep (by decide)) (by omega_using [hW, hv2, qX]), m₁₆, m₁₅, m₁₄, vX₁₃]
  · rw [ot.wv (hd_sep (by decide)) (by omega_using [hW, hv2, qN]), m₁₆, m₁₅, m₁₄, vN₁₃]
  · have sj := slot_lt (w := vk I.k) (show j < 8 from hj)
    have s8 : slot (vk I.k) 8 = 256 + 8 * (8 * (vk I.k + 2)) := rfl
    have sg := slot_ge (vk I.k) j
    rw [ot.wv (hd_sep (by decide)) (by omega_using [hv2, hk, sj, s8]), m₁₆, m₁₅, m₁₄, o₁₃.wv (d := slot (vk I.k) j) (k := k) (by omega_using [hW, qA, hk, sj, s8]) (by omega_using [hv2, hk, sj, s8]),
      m₁₂, m₁₁, m₁₀, k₉m (slot (vk I.k) j) k (by omega_using [hv2, hk, sj, s8]) (by omega_using [hW, qA, hk, sj, s8]) (by omega_using [hW, qX, hk, sj, s8]) (by omega_using [hW, qT, hk, sj, s8]) (by omega_using [hsC, sg]),
      kS₈ (slot (vk I.k) j) k (slot_ge _ _) (by omega_using [q8, hk, sj, s8])]

/-! ## The divisor's top nonzero word -/

/-- The index of the last nonzero word of `f` below `i`, or 0. -/
def hiOf (f : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | i + 1 => if f i = 0 then hiOf f i else i

theorem hiOf_spec (f : Nat → BitVec 64) (i : Nat) :
    (∀ j, hiOf f i < j → j < i → f j = 0) ∧ (hiOf f i < i ∨ i = 0) ∧
      (f (hiOf f i) ≠ 0 ∨ ∀ j < i, f j = 0) := by
  induction i with
  | zero => exact ⟨fun j h1 h2 => absurd h2 (Nat.not_lt_zero _), .inr rfl, .inr fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases hz : f i = 0
    · simp only [hiOf, hz, ↓reduceIte]
      have h2' : hiOf f i < i + 1 := by
        rcases h2 with h2 | rfl
        · omega_using [h2]
        · simp [hiOf]
      refine ⟨fun j hj hj' => ?_, .inl h2', ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
        · exact h1 j hj hj'
        · exact hz
      · rcases h3 with h3 | h3
        · exact .inl h3
        · right; intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact h3 j hj
          · exact hz
    · simp only [hiOf, hz, ↓reduceIte]
      exact ⟨fun j hj hj' => by omega, .inl (by omega_using []), .inl hz⟩

/-- A number's top nonzero word `hi`: the number is in `[2^(64 hi), 2^(64 (hi + 1)))`. -/
theorem wv_hi (m : Mem) (B : Addr) (e n : Nat) (h0 : wv m B e n ≠ 0) :
    2 ^ (64 * hiOf (fun j => word m B (e + 8 * j)) n) ≤ wv m B e n ∧
      wv m B e n < 2 ^ (64 * (hiOf (fun j => word m B (e + 8 * j)) n + 1)) ∧
      hiOf (fun j => word m B (e + 8 * j)) n < n := by
  obtain ⟨h1, h2, h3⟩ := hiOf_spec (fun j => word m B (e + 8 * j)) n
  generalize hiOf (fun j => word m B (e + 8 * j)) n = hi at h1 h2 h3
  have hn : n ≠ 0 := by rintro rfl; exact h0 rfl
  have h3' : word m B (e + 8 * hi) ≠ 0 := by
    rcases h3 with h3 | h3
    · exact h3
    · exfalso; exact h0 ((wv_eq_zero_iff _ _ _ _).mpr fun q hq => h3 q hq)
  have hlt : hi < n := by omega_using [h2, hn]
  have e1 := wv_add m B e (hi + 1) (n - (hi + 1))
  rw [show hi + 1 + (n - (hi + 1)) = n by omega_using [h2, hn],
    (wv_eq_zero_iff m B (e + 8 * (hi + 1)) (n - (hi + 1))).mpr (fun q hq => by
      rw [Nat.add_assoc, ← Nat.mul_add]; exact h1 _ (by omega_using []) (by omega_using [hq])),
    Nat.mul_zero, Nat.add_zero] at e1
  rw [e1]
  refine ⟨?_, wv_lt _ _ _ _, hlt⟩
  have : (word m B (e + 8 * hi)).toNat ≠ 0 := fun h => h3' (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rw [wv]
  calc 2 ^ (64 * hi) = 2 ^ (64 * hi) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (64 * hi) * (word m B (e + 8 * hi)).toNat := Nat.mul_le_mul_left _ (by omega_using [this])
    _ ≤ _ := Nat.le_add_left _ _

/-- After `i` words of `hiScan`. -/
structure HiInv (s₀ : State) (B : Addr) (Z e : Nat) (i : Nat) (t : State) : Prop where
  keep : Keep [.x3, .x4, .x5, .x6, .x14, .x16] s₀ t
  mem : t.mem = s₀.mem
  x16 : t.gpr .x16 = off B (e + 8 * i)
  x6 : t.gpr .x6 = BitVec.ofNat 64 i
  x5 : t.gpr .x5 = BitVec.ofNat 64 (hiOf (fun j => word s₀.mem B (e + 8 * j)) i)

theorem hiStep_ok {s₀ : State} {B : Addr} {Z e n : Nat} (hs : Scr s₀ B Z) (h7 : s₀.gpr .x7 = 0)
    (he : e + 8 * n ≤ Z) {i : Nat} (hi : i < n) {t : State} (hI : HiInv s₀ B Z e i t) :
    WP isa (.block (hiScan ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      HiInv s₀ B Z e (i + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  have hst := hs.congr hI.keep.wr
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  generalize hy : word s₀.mem B (e + 8 * i) = y
  have wy : word t.mem B (e + 8 * i) = y := by rw [hI.mem, hy]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x14, .x16] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .x16 = off B (e + 8 * (i + 1)) ∧ t'.gpr .x6 = BitVec.ofNat 64 (i + 1) ∧
      t'.gpr .x5 = (if decide (y ≠ 0) then BitVec.ofNat 64 i else t.gpr .x5) ∧
      t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) (by
    unfold hiScan
    brun [hI.x16, hI.x6, t7, wy, hst.ld (show e + 8 * i + 8 ≤ Z by omega_using [he, hi]), nz_mask, off_add, BitVec.ofNat_add_ofNat]
    refine ⟨by rw [show e + 8 * i + 8 = e + 8 * (i + 1) by omega_using []], ?_⟩
    rcases decide (y ≠ 0) with _ | _
    · simp [mask]
    · simp only [↓reduceIte]
      rw [show mask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self,
        BitVec.zero_xor]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm, h16, h6, h5, h14⟩, k⟩ => ⟨⟨(hI.keep.trans k).mono (by decide), hm.trans hI.mem, h16, h6, ?_⟩, h14⟩
  rw [h5, hI.x5]
  show _ = BitVec.ofNat 64 (hiOf (fun j => word s₀.mem B (e + 8 * j)) (i + 1))
  simp only [hiOf, hy]
  by_cases h : y = 0
  · simp [h]
  · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true, decide_true]

/-! ## `divB` -/

/-- The divisor's leading zero words `v - 1 - hi` into `sCnt`. -/
theorem hiZ_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) :
    WP isa (seqs [.block (ws ++ base nM1 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, mov .x14 .x12]),
      countLoop .x14 hiScan, .block [.sub .x .x10 .x12 .x5, .subImm .x .x10 .x10 1, sth .x10 sCnt]]) s fun t =>
      G I m₀ (vk I.k) c t ∧ Frm I.B [(8 * sCnt, 8)] s.mem t.mem ∧
      word t.mem I.B (8 * sCnt) =
        BitVec.ofNat 64 (vk I.k - 1 - hiOf (fun j => word s.mem I.B (slot (vk I.k) nM1 + 8 * j)) (vk I.k)) ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x10, .x11, .x12, .x14, .x16] s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hv2 : 2 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
  have hvl : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  have hn := h.ws.scr.nowrap
  have z2 := h.ws.sl (j := nM1) (by decide)
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ws_ok h.ws.scr h.ws.x0 h.ws.h256 h.ws.hw h.ws.hS) fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have x0₁ : t₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans h.ws.x0
  refine WP.mono (base_ok nM1 .x16 x0₁ h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have h12₂ : t₂.gpr .x12 = BitVec.ofNat 64 (vk I.k) := by rw [k₂.gpr .x12 (by decide), h12]
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x14] (Q := fun t => t.gpr .x7 = 0 ∧ t.gpr .x5 = BitVec.ofNat 64 0 ∧
      t.gpr .x6 = BitVec.ofNat 64 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (vk I.k) ∧ t.mem = t₂.mem) (by brun [h12₂, mov, movi])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h7, h5, h6, h14, m₃⟩, k₃⟩ => ?_
  have g₃ : G I m₀ (vk I.k) c t₃ := h.same (by rw [m₃, m₂, m₁]) ((k₁.trans k₂).trans k₃) (by decide)
  have h16₃ : t₃.gpr .x16 = off I.B (slot (vk I.k) nM1 + 8 * 0) := by
    rw [k₃.gpr .x16 (by decide), h16]; rfl
  have h12₃ : t₃.gpr .x12 = BitVec.ofNat 64 (vk I.k) := by rw [k₃.gpr .x12 (by decide), h12₂]
  have mem₃ : t₃.mem = s.mem := by rw [m₃, m₂, m₁]
  refine WP.seq (WP.mono (wp_countdown (N := vk I.k) (by omega_using [hvl]) (by omega_using [hv2]) (HiInv t₃ I.B I.Z (slot (vk I.k) nM1))
    (fun i hi t hI _ => hiStep_ok g₃.ws.scr h7 (by omega_using [z2]) hi hI)
    ⟨Keep.refl _ _, rfl, h16₃, h6, by rw [h5]; rfl⟩ h14) fun t₄ hI => ?_)
  have g₄ : G I m₀ (vk I.k) c t₄ := g₃.same hI.mem hI.keep (by decide)
  have h5₄ : t₄.gpr .x5 = BitVec.ofNat 64 (hiOf (fun j => word s.mem I.B (slot (vk I.k) nM1 + 8 * j)) (vk I.k)) := by
    rw [hI.x5, mem₃]
  obtain ⟨-, hlt, -⟩ := hiOf_spec (fun j => word s.mem I.B (slot (vk I.k) nM1 + 8 * j)) (vk I.k)
  generalize hiOf (fun j => word s.mem I.B (slot (vk I.k) nM1 + 8 * j)) (vk I.k) = hi at h5₄ hlt ⊢
  have hhi : hi < vk I.k := by omega_using [hv2, hlt]
  rw [show ([.sub .x .x10 .x12 .x5, .subImm .x .x10 .x10 1, sth .x10 sCnt] : List Instr) =
    [.sub .x .x10 .x12 .x5, .subImm .x .x10 .x10 1] ++ [sth .x10 sCnt] from rfl, WP.block_append_iff]
  have h12₄ : t₄.gpr .x12 = BitVec.ofNat 64 (vk I.k) := by rw [hI.keep.gpr .x12 (by decide), h12₃]
  refine WP.mono (WP.keep [.x10] (Q := fun t => t.gpr .x10 = BitVec.ofNat 64 (vk I.k - 1 - hi) ∧ t.mem = t₄.mem) (by
    brun [h12₄, h5₄, ofNat_sub_ofNat (show hi ≤ vk I.k by omega_using [hv2, hlt]) (show vk I.k < 2 ^ 64 by omega_using [hvl]),
      ofNat_sub_ofNat (show 1 ≤ vk I.k - hi by omega_using [hv2, hlt]) (show vk I.k - hi < 2 ^ 64 by omega_using [hvl])]
    congr 1; omega_using []) (by decide) (by decide) (by decide +kernel)) fun t₅ ⟨⟨h10, m₅⟩, k₅⟩ => ?_
  refine WP.mono (sthOwn_ok (g₄.same m₅ k₅ (by decide)) (sl := sCnt) ⟨by decide, by decide, by decide⟩ .x10)
    fun t ⟨g, f, hw, k⟩ => ⟨g, ?_, by rw [hw, h10], ?_⟩
  · rw [show s.mem = t₅.mem by rw [m₅, hI.mem, mem₃]]; exact f
  · exact (((((k₁.trans k₂).trans k₃).trans hI.keep).trans k₅).trans k).mono (by decide)

/-- Pairs of stages `0, …, M - 1` in sequence. -/
theorem seqs_pairs_ok {f g : Nat → Prog isa} {P Q : Nat → State → Prop} {M : Nat} (hM : 1 ≤ M)
    (hf : ∀ m < M, ∀ t, P m t → WP isa (f m) t (Q m)) (hg : ∀ m < M, ∀ t, Q m t → WP isa (g m) t (P (m + 1)))
    {s : State} (h0 : P 0 s) :
    WP isa (seqs ((List.range M).flatMap fun k => [f k, g k])) s (P M) := by
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM'
    · exact WP.seq (WP.mono (hf 0 (by omega_using []) s h0) fun t ht => hg 0 (by omega_using []) t ht)
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine wp_seqs_append (List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr hM', List.mem_cons_self⟩))
        (by simp)
        (WP.mono (ih hM' (fun m hm => hf m (by omega_using [hm])) fun m hm => hg m (by omega_using [hm])) fun t ht =>
          WP.seq (WP.mono (hf M (by omega_using []) t ht) fun u hu => hg M (by omega_using []) u hu))

theorem hdr_cnt {B : Addr} {m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm B (hdrW ++ rs) m m')
    (hrs : ∀ r ∈ rs, 256 ≤ r.1) : word m' B (8 * sCnt) = word m B (8 * sCnt) :=
  hf.word_eq (fun r hr => by
    rw [show 8 * sCnt = 208 from rfl]
    simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | hr
    · simp only [sW]; omega_using []
    · simp only [sArr]; omega_using []
    · simp only [sStride, sFn]; omega_using []
    · have := hrs r hr; omega_using [this]) (by rw [show 8 * sCnt = 208 from rfl]; omega_using [])

/-- The divisor (narrow array `nM1`) and the dividend (wide array `wM`) shifted up by the `z` words
in `sCnt`. -/
theorem zStages_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) {z : Nat}
    (hz : word s.mem I.B (8 * sCnt) = BitVec.ofNat 64 z) (hzv : z < vk I.k) :
    WP isa (seqs ((List.range 8).flatMap fun k =>
        [wstage nM1 false true sCnt false k, wstage wM true true sCnt false k])) s fun t =>
      G I m₀ (vk I.k) c t ∧
      Frm I.B (hdrW ++ [(slot (vk I.k) nM1, 8 * vk I.k), (slot (Wk I.k) wM, 8 * Wk I.k)]) s.mem t.mem ∧
      wv t.mem I.B (slot (vk I.k) nM1) (vk I.k) =
        wv s.mem I.B (slot (vk I.k) nM1) (vk I.k) * 2 ^ (64 * z) % 2 ^ (64 * vk I.k) ∧
      wv t.mem I.B (slot (Wk I.k) wM) (Wk I.k) =
        wv s.mem I.B (slot (Wk I.k) wM) (Wk I.k) * 2 ^ (64 * z) % 2 ^ (64 * Wk I.k) ∧
      Keep stRegs s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hvl : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have q16 : slot (vk I.k) 16 = 256 + 16 * (8 * (vk I.k + 2)) := rfl
  have q2 : slot (vk I.k) nM1 = 256 + 2 * (8 * (vk I.k + 2)) := rfl
  have q5 : slot (Wk I.k) wM = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  let R := hdrW ++ [(slot (vk I.k) nM1, 8 * vk I.k), (slot (Wk I.k) wM, 8 * Wk I.k)]
  have hR : ∀ r ∈ [(slot (vk I.k) nM1, 8 * vk I.k), (slot (Wk I.k) wM, 8 * Wk I.k)], 256 ≤ r.1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> dsimp only <;> omega_arith
  let D := wv s.mem I.B (slot (vk I.k) nM1) (vk I.k)
  let X := wv s.mem I.B (slot (Wk I.k) wM) (Wk I.k)
  let P : Nat → State → Prop := fun m t => G I m₀ (vk I.k) c t ∧ Frm I.B R s.mem t.mem ∧
    wv t.mem I.B (slot (vk I.k) nM1) (vk I.k) = shV D true (64 * (z % 2 ^ m)) (vk I.k) ∧
    wv t.mem I.B (slot (Wk I.k) wM) (Wk I.k) = shV X true (64 * (z % 2 ^ m)) (Wk I.k) ∧ Keep stRegs s t
  let Q : Nat → State → Prop := fun m t => G I m₀ (vk I.k) c t ∧ Frm I.B R s.mem t.mem ∧
    wv t.mem I.B (slot (vk I.k) nM1) (vk I.k) = shV D true (64 * (z % 2 ^ (m + 1))) (vk I.k) ∧
    wv t.mem I.B (slot (Wk I.k) wM) (Wk I.k) = shV X true (64 * (z % 2 ^ m)) (Wk I.k) ∧ Keep stRegs s t
  have hzt : ∀ t : State, Frm I.B R s.mem t.mem → word t.mem I.B (8 * sCnt) = BitVec.ofNat 64 z := fun t f =>
    (hdr_cnt f hR).trans hz
  have hadd : ∀ m, 64 * (z % 2 ^ m) + (if stBit z false m then 64 * 2 ^ m else 0) = 64 * (z % 2 ^ (m + 1)) := fun m => by
    have := stBit_add z false m 64
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    exact this
  refine WP.mono (seqs_pairs_ok (f := fun k => wstage nM1 false true sCnt false k)
    (g := fun k => wstage wM true true sCnt false k) (P := P) (Q := Q) (M := 8) (by decide) (fun m hm t ht => ?_) (fun m hm t ht => ?_) ?_)
    fun t ⟨g, f, v1, v2, k⟩ => ⟨g, f, ?_, ?_, k⟩
  · refine WP.mono (wstage_ok ht.1 L false true (j := nM1) (by decide) (by decide) (by decide) (by decide)
      (hzt t ht.2.1) (by omega_using [hzv, hvl]) false (by omega_using [hm]) (N := vk I.k) rfl (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [hzv]))
      fun u ⟨g, f, v, k⟩ => ⟨g, ht.2.1.trans (f.mono fun r hr => by
        simp only [R, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with hr | rfl
        · exact .inl hr
        · exact .inr (.inl rfl)), ?_, ?_, (ht.2.2.2.2.trans k).mono (by decide)⟩
    · rw [v, ht.2.2.1, stVal_shV, hadd]
    · rw [f.wv_eq (fun r hr => by
        simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl | rfl) | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega_arith) (by omega_using [hvl, hW, q5])]
      exact ht.2.2.2.1
  · refine WP.mono (wstage_ok ht.1 L true true (j := wM) (by decide) (by decide) (by decide) (by decide)
      (hzt t ht.2.1) (by omega_using [hzv, hvl]) false (by omega_using [hm]) (N := Wk I.k) rfl (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [hzv, hW]))
      fun u ⟨g, f, v, k⟩ => ⟨g, ht.2.1.trans (f.mono fun r hr => by
        simp only [R, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with hr | rfl
        · exact .inl hr
        · exact .inr (.inr rfl)), ?_, ?_, (ht.2.2.2.2.trans k).mono (by decide)⟩
    · rw [f.wv_eq (fun r hr => by
        simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl | rfl) | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega_arith) (by omega_using [hvl, q2])]
      exact ht.2.2.1
    · rw [v, ht.2.2.2.1, stVal_shV, hadd]
  · have e0 : ∀ V N, V < 2 ^ (64 * N) → V = shV V true (64 * (z % 2 ^ 0)) N := fun V N hV => by
      simp only [shV, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.mul_one, ↓reduceIte, Nat.mod_eq_of_lt hV]
    exact ⟨h, Frm.refl _ _ _, e0 _ _ (wv_lt _ _ _ _), e0 _ _ (wv_lt _ _ _ _), Keep.refl _ _⟩
  · rw [v1, Nat.mod_eq_of_lt (show z < 2 ^ 8 by omega_using [hzv, hvl])]; rfl
  · rw [v2, Nat.mod_eq_of_lt (show z < 2 ^ 8 by omega_using [hzv, hvl])]; rfl

theorem carry_one (y : BitVec 64) :
    BitVec.setWidth 64 0#16 + BitVec.setWidth 64 0#16 +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ y.toNat + (~~~BitVec.setWidth 64 1#16).toNat + true.toNat)).toNat =
      if y = 0 then 0 else 1 := by
  have e : (~~~BitVec.setWidth 64 1#16 : BitVec 64).toNat = 2 ^ 64 - 2 := by rfl
  rw [e]
  by_cases hy : y = 0
  · subst hy; simp
  · have : 1 ≤ y.toNat := by
      rcases Nat.eq_zero_or_pos y.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hy
      · exact h
    simp only [hy, ↓reduceIte, Bool.toNat_true]
    rw [decide_eq_true (by omega_using [this])]
    rfl

/-- `max(y, 1)`. -/
def fixW (y : BitVec 64) : BitVec 64 := if y = 0 then 1 else y

theorem fixW_eq (y : BitVec 64) : y + 1 - (if y = 0 then 0 else 1) = fixW y := by
  unfold fixW
  by_cases hy : y = 0
  · subst hy; rfl
  · simp only [hy, ↓reduceIte, BitVec.add_sub_cancel]

/-- The divisor's top word made at least 1. -/
theorem fixTop_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (.block (setNar ++ ws ++ topAt nM1 .x16 ++ ([.subImm .x .x16 .x16 8, ld .x3 .x16, movi .x4 1, movi .x7 0,
      .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7, .add .x .x3 .x3 .x4, .sub .x .x3 .x3 .x5, st .x3 .x16] : List Instr))) s fun t =>
      G I m₀ (vk I.k) c t ∧
      Frm I.B (hdrW ++ [(slot (vk I.k) nM1 + 8 * (vk I.k - 1), 8)]) s.mem t.mem ∧
      word t.mem I.B (slot (vk I.k) nM1 + 8 * (vk I.k - 1)) =
        fixW (word s.mem I.B (slot (vk I.k) nM1 + 8 * (vk I.k - 1))) ∧
      Keep [.x3, .x4, .x5, .x7, .x11, .x12, .x16] s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hv2 : 2 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
  have hvl : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.setNar_ok L) fun t₀ ⟨g₀, f₀, k₀⟩ => ?_
  have hn := g₀.ws.scr.nowrap
  have z2 := g₀.ws.sl (j := nM1) (by decide)
  refine WP.mono (ws_ok g₀.ws.scr g₀.ws.x0 g₀.ws.h256 g₀.ws.hw g₀.ws.hS) fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have x0₁ : t₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans g₀.ws.x0
  unfold topAt
  rw [WP.block_append_iff]
  refine WP.mono (base_ok nM1 .x16 x0₁ h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have h12₂ : t₂.gpr .x12 = BitVec.ofNat 64 (vk I.k) := by rw [k₂.gpr .x12 (by decide), h12]
  have hs₂ := g₀.ws.scr.congr (k₁.trans k₂).wr
  generalize hy : word t₂.mem I.B (slot (vk I.k) nM1 + 8 * (vk I.k - 1)) = y
  have ea : slot (vk I.k) nM1 + 8 * vk I.k - 8 = slot (vk I.k) nM1 + 8 * (vk I.k - 1) := by omega_using [hv2]
  have haddr : slot (vk I.k) nM1 + 8 * (vk I.k - 1) + 8 ≤ I.Z := by omega_using [z2]
  have q2 : slot (vk I.k) nM1 = 256 + 2 * (8 * (vk I.k + 2)) := rfl
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.gpr .x16 = off I.B (slot (vk I.k) nM1 + 8 * vk I.k) ∧
      t.mem = t₂.mem) (by
    brun [h16, h12₂, shl_ofNat (show vk I.k * 2 ^ 3 < 2 ^ 64 by omega_using [hvl]), off_add]
    congr 1; omega_using []) (by decide) (by decide) (by decide +kernel)) fun t₂' ⟨⟨h16', m₂'⟩, k₂'⟩ => ?_
  have hy' : word t₂'.mem I.B (slot (vk I.k) nM1 + 8 * (vk I.k - 1)) = y := by rw [m₂', hy]
  have hs₂' := hs₂.congr k₂'.wr
  rw [show ([.subImm .x .x16 .x16 8, ld .x3 .x16, movi .x4 1, movi .x7 0, .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7,
      .add .x .x3 .x3 .x4, .sub .x .x3 .x3 .x5, st .x3 .x16] : List Instr) = ([.subImm .x .x16 .x16 8, ld .x3 .x16] ++
      [movi .x4 1, movi .x7 0, .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7, .add .x .x3 .x3 .x4, .sub .x .x3 .x3 .x5]) ++
      [st .x3 .x16] from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.gpr .x16 = off I.B (slot (vk I.k) nM1 + 8 * (vk I.k - 1)) ∧
      t.gpr .x3 = y ∧ t.mem = t₂'.mem) (by
    brun [h16', off_sub I.B (show 8 ≤ slot (vk I.k) nM1 + 8 * vk I.k by omega_using [hv2]), ea, hy', hs₂'.ld haddr])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h16₃, h3₃, m₃⟩, k₃⟩ => ?_
  rw [show ([movi .x4 1, movi .x7 0, .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7, .add .x .x3 .x3 .x4,
      .sub .x .x3 .x3 .x5] : List Instr) = [movi .x4 1, movi .x7 0, .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7] ++
      [.add .x .x3 .x3 .x4, .sub .x .x3 .x3 .x5] from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.x4, .x5, .x7] (Q := fun t => t.gpr .x5 = (if y = 0 then 0 else 1) ∧ t.gpr .x4 = 1 ∧
      t.gpr .x7 = 0 ∧ t.mem = t₃.mem) (by brun [h3₃, carry_one]) (by decide) (by decide) (by decide +kernel))
    fun t₄ ⟨⟨h5₄, h4₄, h7₄, m₄⟩, k₄⟩ => ?_
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = fixW y ∧ t.mem = t₄.mem) (by
    brun [(k₄.gpr .x3 (by decide)).trans h3₃, h4₄, h5₄, fixW_eq]) (by decide) (by decide) (by decide +kernel))
    fun t₅ ⟨⟨h3₅, m₅⟩, k₅⟩ => ?_
  have h16₅ : t₅.gpr .x16 = off I.B (slot (vk I.k) nM1 + 8 * (vk I.k - 1)) := by
    rw [k₅.gpr .x16 (by decide), k₄.gpr .x16 (by decide), h16₃]
  have hs₅ := hs₂'.congr ((k₃.trans k₄).trans k₅).wr
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₅.mem.writeW (off I.B (slot (vk I.k) nM1 + 8 * (vk I.k - 1)))
      (fixW y)) (by brun [h16₅, h3₅, hs₅.st haddr]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have e5 : t₅.mem = t₀.mem := by rw [m₅, m₄, m₃, m₂', m₂, m₁]
  have o := writeW_outside t₅.mem I.B (fixW y) (d := slot (vk I.k) nM1 + 8 * (vk I.k - 1)) (by omega_using [hvl, q2])
  rw [← hm] at o
  have hf : Frm I.B [(slot (vk I.k) nM1 + 8 * (vk I.k - 1), 8)] t₀.mem t.mem := by
    rw [← e5]; exact Frm.of_outside o (List.mem_singleton_self _)
  have kk := (((((((k₁.trans k₂).trans k₂').trans k₃).trans k₄).trans k₅).trans k))
  refine ⟨g₀.step (rs := [(slot (vk I.k) nM1 + 8 * (vk I.k - 1), 8)]) hf
    (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_using [q2])
    (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_using [z2]) kk (by decide), ?_, ?_, ?_⟩
  · exact (f₀.mono fun r hr => List.mem_append_left _ hr).trans (hf.mono fun r hr => List.mem_append_right _ hr)
  · rw [hm, word_writeW_self, ← hy, m₂, m₁, f₀.word_eq (fun r hr => by
      simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega_using [q2]) (by omega_using [hvl, q2])]
  · exact (k₀.trans kk).mono (by decide)




/-! ## The arithmetic of `divB` -/

theorem divB_math {D X v hi z : Nat} (hD : 2 ^ (64 * hi) ≤ D) (hD' : D < 2 ^ (64 * (hi + 1))) (hz : z + hi + 1 = v)
    (hX : X < 2 ^ (64 * v)) :
    D * 2 ^ (64 * z) < 2 ^ (64 * v) ∧ 2 ^ (64 * (v - 1)) ≤ D * 2 ^ (64 * z) ∧
      X * 2 ^ (64 * z) < 2 ^ (64 * (2 * v)) ∧
      X * 2 ^ (64 * z) / (D * 2 ^ (64 * z)) = X / D ∧
      X * 2 ^ (64 * z) % (D * 2 ^ (64 * z)) = X % D * 2 ^ (64 * z) ∧ X / D < 2 ^ (64 * v) := by
  have hp := Nat.two_pow_pos (64 * z)
  have e1 : 2 ^ (64 * (hi + 1)) * 2 ^ (64 * z) = 2 ^ (64 * v) := pow_add' (by omega_using [hz])
  have e2 : 2 ^ (64 * hi) * 2 ^ (64 * z) = 2 ^ (64 * (v - 1)) := pow_add' (by omega_using [hz])
  have e3 : 2 ^ (64 * v) * 2 ^ (64 * z) ≤ 2 ^ (64 * (2 * v)) := by
    rw [pow_add' (show 64 * v + 64 * z = 64 * (v + z) by omega_using [])]
    exact Nat.pow_le_pow_right (by decide) (by omega_using [hz])
  have hD0 : 0 < D := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hD
  refine ⟨?_, ?_, ?_, Nat.mul_div_mul_right _ _ hp, Nat.mul_mod_mul_right _ _ _, ?_⟩
  · rw [← e1]; exact Nat.mul_lt_mul_of_pos_right hD' hp
  · rw [← e2]; exact Nat.mul_le_mul_right _ hD
  · exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hX hp) e3
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hX

/-- A number whose top word is not zero. -/
theorem top_ge (m : Mem) (B : Addr) (e v : Nat) (hv : 1 ≤ v) (h : word m B (e + 8 * (v - 1)) ≠ 0) :
    2 ^ (64 * (v - 1)) ≤ wv m B e v := by
  have e1 := wv_add m B e (v - 1) 1
  rw [Nat.sub_add_cancel hv] at e1
  rw [e1]
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  have : (word m B (e + 8 * (v - 1))).toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
  calc 2 ^ (64 * (v - 1)) = 2 ^ (64 * (v - 1)) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (64 * (v - 1)) * (word m B (e + 8 * (v - 1))).toNat := Nat.mul_le_mul_left _ (by omega_using [this])
    _ ≤ _ := Nat.le_add_left _ _

/-- A number at least `2^(64 (v - 1))` has its top word not zero. -/
theorem top_ne (m : Mem) (B : Addr) (e v : Nat) (hv : 1 ≤ v) (h : 2 ^ (64 * (v - 1)) ≤ wv m B e v) :
    word m B (e + 8 * (v - 1)) ≠ 0 := by
  intro h0
  have e1 := wv_add m B e (v - 1) 1
  rw [Nat.sub_add_cancel hv] at e1
  simp only [wv, h0, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul] at e1
  have : wv m B e (v - 1) < 2 ^ (64 * (v - 1)) := wv_lt _ _ _ _
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at e1
  omega_using [h, e1, this]

theorem fixW_ne (y : BitVec 64) : fixW y ≠ 0 := by
  unfold fixW
  split
  · decide
  · assumption

theorem fixW_of_ne {y : BitVec 64} (h : y ≠ 0) : fixW y = y := by simp only [fixW, h, ↓reduceIte]

/-- What `divB` writes: the header, narrow arrays 2 to 5, wide array 5 (narrow 10 and 11) and wide
array 9 (narrow 18 and 19). -/
def rbB (v : Nat) : List (Nat × Nat) :=
  [(0, 256), (slot v 2, 32 * (v + 2)), (slot v 10, 16 * (v + 2)), (slot v 18, 16 * (v + 2))]

theorem rbB_out {B : Addr} {v : Nat} {m m' : Mem} {a n : Nat} (o : Outside B a n m m')
    (h : (a + n ≤ 256) ∨ (slot v 2 ≤ a ∧ a + n ≤ slot v 6) ∨ (slot v 10 ≤ a ∧ a + n ≤ slot v 12) ∨
      (slot v 18 ≤ a ∧ a + n ≤ slot v 20)) : Frm B (rbB v) m m' :=
  (Frm.of_outside o (List.mem_singleton_self _)).widen fun r hr => by
    rw [List.mem_singleton.mp hr]
    have q2 : slot v 6 = slot v 2 + 32 * (v + 2) := by unfold slot; omega_using []
    have q10 : slot v 12 = slot v 10 + 16 * (v + 2) := by unfold slot; omega_using []
    have q18 : slot v 20 = slot v 18 + 16 * (v + 2) := by unfold slot; omega_using []
    simp only [rbB, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    omega_using [h, q2, q10, q18]

theorem rbB_frm {B : Addr} {v : Nat} {m m' : Mem} {rs : List (Nat × Nat)} (f : Frm B rs m m')
    (h : ∀ r ∈ rs, (r.1 + r.2 ≤ 256) ∨ (slot v 2 ≤ r.1 ∧ r.1 + r.2 ≤ slot v 6) ∨
      (slot v 10 ≤ r.1 ∧ r.1 + r.2 ≤ slot v 12) ∨ (slot v 18 ≤ r.1 ∧ r.1 + r.2 ≤ slot v 20)) : Frm B (rbB v) m m' :=
  f.widen fun r hr => by
    have := h r hr
    have q2 : slot v 6 = slot v 2 + 32 * (v + 2) := by unfold slot; omega_using []
    have q10 : slot v 12 = slot v 10 + 16 * (v + 2) := by unfold slot; omega_using []
    have q18 : slot v 20 = slot v 18 + 16 * (v + 2) := by unfold slot; omega_using []
    simp only [rbB, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    omega_using [this, q2, q10, q18]

theorem hdrW_rb (r : Nat × Nat) (hr : r ∈ hdrW) : r.1 + r.2 ≤ 256 := by
  simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega_using []

theorem rbB_wv {B : Addr} {v : Nat} {m m' : Mem} (f : Frm B (rbB v) m m') {j k : Nat}
    (hj : j < 2 ∨ (6 ≤ j ∧ j < 10)) (hk : k ≤ v + 2) (hb : slot v 32 ≤ 2 ^ 64) :
    wv m' B (slot v j) k = wv m B (slot v j) k := by
  have q : ∀ i, slot v i = 256 + i * (8 * (v + 2)) := fun _ => rfl
  have q32 := q 32
  have hj' : j = 0 ∨ j = 1 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega_using [hj]
  refine f.wv_eq (fun r hr => ?_) ?_
  · simp only [rbB, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> rw [q j] <;> try rw [q]
    all_goals rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith
  · rw [q j]; rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem wpc {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa c s fun t => WP isa (seqs l) t Q) : WP isa (seqs (c :: l)) s Q := by
  cases l with
  | nil => exact absurd rfl hl
  | cons d l => exact WP.seq h

theorem wpc3 {x y z : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa (seqs [x, y, z]) s fun t => WP isa (seqs l) t Q) : WP isa (seqs (x :: y :: z :: l)) s Q :=
  wp_seqs_append (a := [x, y, z]) (by simp) hl h

/-- `divB` up to the division. -/
abbrev divBP : List (Prog isa) := [.block (setNar ++ ones), zeroA nM1, addA nM1 (2 * wA) nOne, zeroA nD,
  subA nD Public.aN (2 * wX),
  .block (ws ++ base nM1 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, mov .x14 .x12]),
  countLoop .x14 hiScan,
  .block [.sub .x .x10 .x12 .x5, .subImm .x .x10 .x10 1, sth .x10 sCnt],
  .block setWid, zeroA wM, zeroA wT, .block setNar, copyA (2 * wM) nD] ++
  (List.range 8).flatMap (fun k => [wstage nM1 false true sCnt false k, wstage wM true true sCnt false k]) ++
  [.block (setNar ++ ws ++ topAt nM1 .x16 ++ [.subImm .x .x16 .x16 8, ld .x3 .x16, movi .x4 1, movi .x7 0,
    .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7, .add .x .x3 .x3 .x4, .sub .x .x3 .x3 .x5, st .x3 .x16]),
  zeroA nRem,
  .block (ws ++ base nM1 .x9 ++ base nRem .x5 ++ setWid ++ ws ++ base wT .x6 ++ base wM .x8 ++
    [mov .x11 .x5, .subImm .x .x13 .x12 2, .lsr .x .x12 .x12 1, .subImm .x .x12 .x12 1, movi .x7 0])]

/-- `divB` after the division. -/
abbrev divBT : List (Prog isa) := [.block setNar, zeroA nD, copyA nD (2 * wM), zeroA nZ] ++ eqA nRem nZ ++
  [.block andZero]

theorem divB_eq : divB = seqs (divBP ++ divQN :: divBT) := by
  simp only [divB, divBP, divBT, List.append_assoc, List.cons_append, List.nil_append]

/-- `divB` up to the division: the divisor `D = m + 1` and `X = n - r` shifted up by the divisor's leading zero
words, the divisor's top word not zero, and `divQN`'s registers. -/
theorem divB1_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (Wk I.k) c s) (L : RpLens I) {M R N : Nat}
    (hM : wv s.mem I.B (slot (Wk I.k) wA) (Wk I.k) = M) (hR : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k + 1) = R)
    (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N)
    (one : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1) :
    WP isa (seqs divBP) s fun t => ∃ D X hi : Nat, G I m₀ (Wk I.k) c t ∧
      DQH t I.B I.Z (slot (Wk I.k) wM) (slot (vk I.k) nRem) (slot (vk I.k) nM1) (slot (Wk I.k) wT) (2 * vk I.k) (vk I.k) ∧
      (0 < D → wv t.mem I.B (slot (Wk I.k) wM) (2 * vk I.k) = X * 2 ^ (64 * (vk I.k - 1 - hi)) ∧
        wv t.mem I.B (slot (vk I.k) nM1) (vk I.k) = D * 2 ^ (64 * (vk I.k - 1 - hi)) ∧ X / D < 2 ^ (64 * vk I.k)) ∧
      (M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k) = D ∧ wsub (64 * vk I.k) N (R % 2 ^ (64 * vk I.k)) = X ∧
      Frm I.B (rbB (vk I.k)) s.mem t.mem := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hk1 := L.k1
  have hk2 := L.k2
  have hv9 : 9 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
  have hv2 : vk I.k ≤ 200 := by simp only [vk]; omega_using [hk2]
  have hb32 := hb32_of h L
  have hn := h.ws.scr.nowrap
  have hZ32 : slot (vk I.k) 32 ≤ I.Z := by have := h.ws.hZ; rw [hW, slot_wide] at this; exact this
  have q32 : slot (vk I.k) 32 = 256 + 32 * (8 * (vk I.k + 2)) := rfl
  have q0 : slot (vk I.k) 0 = 256 + 0 * (8 * (vk I.k + 2)) := rfl
  have q1 : slot (vk I.k) nOne = 256 + 1 * (8 * (vk I.k + 2)) := rfl
  have q2 : slot (vk I.k) nM1 = 256 + 2 * (8 * (vk I.k + 2)) := rfl
  have q3 : slot (vk I.k) nD = 256 + 3 * (8 * (vk I.k + 2)) := rfl
  have q4 : slot (vk I.k) nRem = 256 + 4 * (8 * (vk I.k + 2)) := rfl
  have q5 : slot (vk I.k) nZ = 256 + 5 * (8 * (vk I.k + 2)) := rfl
  have q6 : slot (vk I.k) 6 = 256 + 6 * (8 * (vk I.k + 2)) := rfl
  have q2' : slot (vk I.k) 2 = 256 + 2 * (8 * (vk I.k + 2)) := rfl
  have q3' : slot (vk I.k) 3 = 256 + 3 * (8 * (vk I.k + 2)) := rfl
  have q10 : slot (vk I.k) (2 * wM) = 256 + 10 * (8 * (vk I.k + 2)) := rfl
  have q10' : slot (vk I.k) 10 = 256 + 10 * (8 * (vk I.k + 2)) := rfl
  have q12 : slot (vk I.k) 12 = 256 + 12 * (8 * (vk I.k + 2)) := rfl
  have q14 : slot (vk I.k) (2 * wA) = 256 + 14 * (8 * (vk I.k + 2)) := rfl
  have q12x : slot (vk I.k) (2 * wX) = 256 + 12 * (8 * (vk I.k + 2)) := rfl
  have q18 : slot (vk I.k) 18 = 256 + 18 * (8 * (vk I.k + 2)) := rfl
  have q20 : slot (vk I.k) 20 = 256 + 20 * (8 * (vk I.k + 2)) := rfl
  have qM : slot (Wk I.k) wM = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  have qT : slot (Wk I.k) wT = 256 + 9 * (8 * (Wk I.k + 2)) := rfl
  have qA : slot (Wk I.k) wA = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qX : slot (Wk I.k) wX = 256 + 6 * (8 * (Wk I.k + 2)) := rfl
  have qc : 8 * sCnt = 208 := rfl
  have e14 : slot (Wk I.k) wA = slot (vk I.k) (2 * wA) := slot_wide _ _
  have e12 : slot (Wk I.k) wX = slot (vk I.k) (2 * wX) := slot_wide _ _
  have e10 : slot (Wk I.k) wM = slot (vk I.k) (2 * wM) := slot_wide _ _
  unfold divBP
  -- `m + 1` and `n - r`.
  refine wpc (by simp) ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.setNar_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_
  refine WP.mono (ones_ok s₁) fun s₂ ⟨⟨h15, _, m₂⟩, k₂⟩ => ?_
  have g₂ := g₁.same m₂ k₂ (by decide)
  have mlow : wv s₂.mem I.B (slot (vk I.k) (2 * wA)) (vk I.k) = M % 2 ^ (64 * vk I.k) := by
    rw [m₂, ← wv_mod _ _ _ (show vk I.k ≤ Wk I.k by omega_using [hW]), ← e14, Frm.hdrW_wv f₁ (slot_ge _ _) (by
      have := h.bndW L (j := wA) (k := Wk I.k) (by decide) (by omega_using []); omega_using [this]), hM]
  have rlow : wv s₂.mem I.B (slot (vk I.k) (2 * wX)) (vk I.k) = R % 2 ^ (64 * vk I.k) := by
    rw [m₂, ← wv_mod _ _ _ (show vk I.k ≤ Wk I.k + 1 by omega_using [hW]), ← e12, Frm.hdrW_wv f₁ (slot_ge _ _) (by
      have := h.bndW L (j := wX) (k := Wk I.k + 1) (by decide) (by omega_using []); omega_using [this]), hR]
  have n₂ : wv s₂.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by
    rw [m₂, Frm.hdrW_wv f₁ (slot_ge _ _) (by omega_using [hv2, q0]), hN]
  have one₂ : wv s₂.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [m₂, Frm.hdrW_wv f₁ (slot_ge _ _) (by omega_using [hv2, q1]), wv_low_of_lt (w := vk I.k + 2) (by omega_using [])
      (by rw [one]; exact Nat.one_lt_two_pow (by omega_using [hv9])), one]
  refine wpc (by simp) (WP.mono (zeroA_ok g₂.ws (j := nM1) (by decide)) fun s₃ ⟨_, o₃, _, _, _, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine wpc (by simp) (WP.mono (addA_ok g₃.ws (o := nM1) (a := 2 * wA) (b := nOne) (by decide) (by decide)
    (by decide) (by decide) (by decide) (c := true) ((k₃.gpr .x15 (by decide)).trans h15)) fun s₄ ⟨v₄, _, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega_using []) o₄ k₄ (by decide)
  simp only [↓reduceIte] at v₄
  rw [o₃.wv (by omega_using [q2, q14]) (by omega_using [hv2, q14]), mlow, o₃.wv (by omega_using [q1, q2]) (by omega_using [hv2, q1]), one₂] at v₄
  refine wpc (by simp) (WP.mono (zeroA_ok g₄.ws (j := nD) (by decide)) fun s₅ ⟨_, o₅, _, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine wpc (by simp) (WP.mono (subA_ok g₅.ws (o := nD) (a := Public.aN) (b := 2 * wX) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₆ ⟨v₆, _, _, o₆, k₆⟩ => ?_)
  have g₆ := g₅.out (by decide) (by omega_using []) o₆ k₆ (by decide)
  have rlow₅ : wv s₅.mem I.B (slot (vk I.k) (2 * wX)) (vk I.k) = R % 2 ^ (64 * vk I.k) := by
    rw [o₅.wv (by omega_using [q3, q12x]) (by omega_using [hv2, q12x]), o₄.wv (by omega_using [q2, q12x]) (by omega_using [hv2, q12x]), o₃.wv (by omega_using [q2, q12x]) (by omega_using [hv2, q12x]), rlow]
  have n₅ : wv s₅.mem I.B (slot (vk I.k) Public.aN) (vk I.k) = N := by
    rw [show slot (vk I.k) Public.aN = slot (vk I.k) 0 from rfl, o₅.wv (by omega_using [q0, q3]) (by omega_using [hv2, q0]),
      o₄.wv (by omega_using [q0, q2]) (by omega_using [hv2, q0]), o₃.wv (by omega_using [q0, q2]) (by omega_using [hv2, q0]), n₂]
  rw [rlow₅, n₅] at v₆
  generalize hX : wsub (64 * vk I.k) N (R % 2 ^ (64 * vk I.k)) = X
  generalize hD : (M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k) = D at v₄
  have hd : wv s₆.mem I.B (slot (vk I.k) nD) (vk I.k) = X := by rw [← hX]; exact sub_wsub (wv_lt _ _ _ _) v₆
  have hm1 : wv s₆.mem I.B (slot (vk I.k) nM1) (vk I.k) = D := by
    rw [o₆.wv (by omega_using [q2, q3]) (by omega_using [hv2, q2]), o₅.wv (by omega_using [q2, q3]) (by omega_using [hv2, q2]), v₄]
  have FH : Frm I.B (rbB (vk I.k)) s.mem s₆.mem :=
    ((((rbB_frm f₁ fun r hr => .inl (hdrW_rb r hr)).trans (by rw [m₂]; exact Frm.refl _ _ _)).trans
      (rbB_out o₃ (by omega_using [q2, q6, q2']))).trans (rbB_out o₄ (by omega_using [q2, q6, q2']))) |>.trans (rbB_out o₅ (by omega_using [q3, q6, q2'])) |>.trans
      (rbB_out o₆ (by omega_using [q3, q6, q2']))
  clear v₄ v₆ rlow₅ n₅ mlow rlow n₂ one₂
  -- The divisor's top nonzero word, and the count of words to shift by.
  refine wpc3 (by simp) (WP.mono (hiZ_ok g₆ L) fun s₇ ⟨g₇, f₇, hz₇, k₇⟩ => ?_)
  obtain ⟨-, hlt, -⟩ := hiOf_spec (fun j => word s₆.mem I.B (slot (vk I.k) nM1 + 8 * j)) (vk I.k)
  have hiD := wv_hi s₆.mem I.B (slot (vk I.k) nM1) (vk I.k)
  generalize hiOf (fun j => word s₆.mem I.B (slot (vk I.k) nM1 + 8 * j)) (vk I.k) = hi at hz₇ hlt hiD
  have hhi : hi < vk I.k := by omega_using [hv9, hlt]
  have F7 : Frm I.B (rbB (vk I.k)) s₆.mem s₇.mem :=
    rbB_frm f₇ (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_using [qc])
  have w7 : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv s₇.mem I.B d n = wv s₆.mem I.B d n := fun d n hd hd' =>
    f₇.wv_eq (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_using [qc, hd]) hd'
  -- `x` into wide array `wM`.
  refine wpc (by simp) (WP.mono (g₇.setWid_ok L) fun s₈ ⟨g₈, f₈, k₈⟩ => ?_)
  refine wpc (by simp) (WP.mono (zeroA_ok g₈.ws (j := wM) (by decide)) fun s₉ ⟨z₉, o₉, _, _, _, k₉⟩ => ?_)
  have g₉ := g₈.out (by decide) (Nat.le_refl _) o₉ k₉ (by decide)
  refine wpc (by simp) (WP.mono (zeroA_ok g₉.ws (j := wT) (by decide)) fun s₁₀ ⟨_, o₁₀, _, _, _, k₁₀⟩ => ?_)
  have g₁₀ := g₉.out (by decide) (Nat.le_refl _) o₁₀ k₁₀ (by decide)
  refine wpc (by simp) (WP.mono (g₁₀.setNar_ok L) fun s₁₁ ⟨g₁₁, f₁₁, k₁₁⟩ => ?_)
  refine wpc (by simp) (WP.mono (copyA_ok g₁₁.ws (o := 2 * wM) (a := nD) (by decide) (by decide) (by decide))
    fun s₁₂ ⟨v₁₂, o₁₂, _, _, k₁₂⟩ => ?_)
  have g₁₂ := g₁₁.out (by decide) (by omega_using []) o₁₂ k₁₂ (by decide)
  -- What the copies keep.
  have w12 : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → (d + 8 * n ≤ slot (vk I.k) 10 ∨ slot (vk I.k) 12 ≤ d) →
      (d + 8 * n ≤ slot (vk I.k) 18 ∨ slot (vk I.k) 20 ≤ d) → wv s₁₂.mem I.B d n = wv s₆.mem I.B d n :=
    fun d n hd hd' h1 h2 => by
      rw [o₁₂.wv (by omega_using [hv9, hv2, q10, q10', q12, q18, q20, hm1, hlt, hiD, hhi, hd, hd', h1, h2]) hd', Frm.hdrW_wv f₁₁ hd hd', o₁₀.wv (by omega_using [hW, hv9, hv2, q10', q12, q18, q20, qT, hlt, hiD, hhi, hd, hd', h1, h2]) hd', o₉.wv (by omega_using [hW, hv9, hv2, q10, q10', q12, q18, q20, qM, e10, hlt, hiD, hhi, hd, hd', h1, h2]) hd',
        Frm.hdrW_wv f₈ hd hd', w7 d n hd hd']
  have m1₁₂ : wv s₁₂.mem I.B (slot (vk I.k) nM1) (vk I.k) = D := by
    rw [w12 _ _ (by omega_using [q2]) (by omega_using [hv2, q2]) (by omega_using [q2, q10']) (by omega_using [q2, q18]), hm1]
  have x₁₂ : wv s₁₂.mem I.B (slot (Wk I.k) wM) (Wk I.k) = X := by
    have e := wv_add s₁₂.mem I.B (slot (Wk I.k) wM) (vk I.k) (vk I.k + 2)
    rw [show vk I.k + (vk I.k + 2) = Wk I.k by omega_using [hW]] at e
    have hz : wv s₁₂.mem I.B (slot (Wk I.k) wM + 8 * vk I.k) (vk I.k + 2) = 0 := by
      rw [o₁₂.wv (by omega_using [e10]) (by omega_using [hW, hv2, qM]), Frm.hdrW_wv f₁₁ (by omega_using [qM]) (by omega_using [hW, hv2, qM]), o₁₀.wv (by omega_using [hW, qM, qT]) (by omega_using [hW, hv2, qM])]
      have e9 := wv_add s₉.mem I.B (slot (Wk I.k) wM) (vk I.k) (vk I.k + 2 + 2)
      rw [show vk I.k + (vk I.k + 2 + 2) = Wk I.k + 2 by omega_using [hW], z₉] at e9
      have e9' := wv_add s₉.mem I.B (slot (Wk I.k) wM + 8 * vk I.k) (vk I.k + 2) 2
      have : 2 ^ (64 * vk I.k) * wv s₉.mem I.B (slot (Wk I.k) wM + 8 * vk I.k) (vk I.k + 2 + 2) = 0 := by omega_using [e9]
      have := (Nat.mul_eq_zero.mp this).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
      rw [e9'] at this; omega_using [this]
    rw [e, hz, Nat.mul_zero, Nat.add_zero, e10, v₁₂, Frm.hdrW_wv f₁₁ (by omega_using [q3]) (by omega_using [hv2, q3]), o₁₀.wv (by omega_using [hW, q3, qT]) (by omega_using [hv2, q3]),
      o₉.wv (by omega_using [hW, q3, qM]) (by omega_using [hv2, q3]), Frm.hdrW_wv f₈ (by omega_using [q3]) (by omega_using [hv2, q3]), w7 _ _ (by omega_using [q3]) (by omega_using [hv2, q3]), hd]
  have hz₁₂ : word s₁₂.mem I.B (8 * sCnt) = BitVec.ofNat 64 (vk I.k - 1 - hi) := by
    rw [o₁₂.word (by omega_using [q10, qc]) (by omega_using [qc]), hdr_cnt (rs := []) (f₁₁.mono fun r hr => List.mem_append_left _ hr) (by simp),
      o₁₀.word (by omega_using [qT, qc]) (by omega_using [qc]), o₉.word (by omega_using [qM, qc]) (by omega_using [qc]),
      hdr_cnt (rs := []) (f₈.mono fun r hr => List.mem_append_left _ hr) (by simp), hz₇]
  have F12 : Frm I.B (rbB (vk I.k)) s₆.mem s₁₂.mem :=
    F7.trans (rbB_frm f₈ fun r hr => .inl (hdrW_rb r hr)) |>.trans (rbB_out o₉ (by omega_using [hW, q10', q12, qM])) |>.trans
      (rbB_out o₁₀ (by omega_using [hW, q18, q20, qT])) |>.trans (rbB_frm f₁₁ fun r hr => .inl (hdrW_rb r hr)) |>.trans (rbB_out o₁₂ (by omega_using [q10, q10', q12]))
  clear w7 v₁₂ z₉
  -- The divisor and `x` shifted up by `z` words.
  refine wp_seqs_append (List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide),
    List.mem_cons_self⟩)) (by simp) (WP.mono (zStages_ok g₁₂ L (z := vk I.k - 1 - hi) hz₁₂ (by omega_using [hv9]))
    fun s₁₃ ⟨g₁₃, f₁₃, vM1₁₃, vM₁₃, k₁₃⟩ => ?_)
  rw [m1₁₂] at vM1₁₃
  rw [x₁₂] at vM₁₃
  refine wpc (by simp) (WP.mono (fixTop_ok g₁₃ L) fun s₁₄ ⟨g₁₄, f₁₄, top₁₄, k₁₄⟩ => ?_)
  have htop₁₄ : 2 ^ (64 * (vk I.k - 1)) ≤ wv s₁₄.mem I.B (slot (vk I.k) nM1) (vk I.k) :=
    top_ge _ _ _ _ (by omega_using [hv9]) (by rw [top₁₄]; exact fixW_ne _)
  have w14 : ∀ d n, d + 8 * n ≤ 2 ^ 64 → 256 ≤ d → (d + 8 * n ≤ slot (vk I.k) nM1 ∨ slot (vk I.k) 3 ≤ d) →
      wv s₁₄.mem I.B d n = wv s₁₃.mem I.B d n := fun d n hd' hd h1 =>
    f₁₄.wv_eq (fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have := hdrW_rb r hr; omega_using [hd, this]
      · dsimp only; have : slot (vk I.k) 3 = 256 + 3 * (8 * (vk I.k + 2)) := rfl; omega_using [q2, q3', h1]) hd'
  -- The remainder's array cleared, and the division's registers.
  refine wpc (by simp) (WP.mono (zeroA_ok g₁₄.ws (j := nRem) (by decide)) fun s₁₅ ⟨z₁₅, o₁₅, _, _, _, k₁₅⟩ => ?_)
  have g₁₅ := g₁₄.out (by decide) (Nat.le_refl _) o₁₅ k₁₅ (by decide)
  simp only [seqs]
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ws_ok g₁₅.ws.scr g₁₅.ws.x0 g₁₅.ws.h256 g₁₅.ws.hw g₁₅.ws.hS) fun t₁ ⟨⟨_, h11₁, m₁', _⟩, k₁'⟩ => ?_
  have x0₁ : t₁.gpr .x0 = I.B := (k₁'.gpr .x0 (by decide)).trans g₁₅.ws.x0
  refine WP.mono (base_ok nM1 .x9 x0₁ h11₁) fun t₂ ⟨⟨h9₂, m₂', _⟩, k₂'⟩ => ?_
  refine WP.mono (base_ok nRem .x5 ((k₂'.gpr .x0 (by decide)).trans x0₁) ((k₂'.gpr .x11 (by decide)).trans h11₁))
    fun t₃ ⟨⟨h5₃, m₃', _⟩, k₃'⟩ => ?_
  have g₃' := g₁₅.same (by rw [m₃', m₂', m₁']) ((k₁'.trans k₂').trans k₃') (by decide)
  refine WP.mono (g₃'.setWid_ok L) fun t₄ ⟨g₄', f₄', k₄'⟩ => ?_
  refine WP.mono (ws_ok g₄'.ws.scr g₄'.ws.x0 g₄'.ws.h256 g₄'.ws.hw g₄'.ws.hS) fun t₅ ⟨⟨h12₅, h11₅, m₅', _⟩, k₅'⟩ => ?_
  have x0₅ : t₅.gpr .x0 = I.B := (k₅'.gpr .x0 (by decide)).trans g₄'.ws.x0
  refine WP.mono (base_ok wT .x6 x0₅ h11₅) fun t₆ ⟨⟨h6₆, m₆', _⟩, k₆'⟩ => ?_
  refine WP.mono (base_ok wM .x8 ((k₆'.gpr .x0 (by decide)).trans x0₅) ((k₆'.gpr .x11 (by decide)).trans h11₅))
    fun t₇ ⟨⟨h8₇, m₇', _⟩, k₇'⟩ => ?_
  have h12₇ : t₇.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := by
    rw [k₇'.gpr .x12 (by decide), k₆'.gpr .x12 (by decide), h12₅]
  have h5₇ : t₇.gpr .x5 = off I.B (slot (vk I.k) nRem) := by
    rw [k₇'.gpr .x5 (by decide), k₆'.gpr .x5 (by decide), k₅'.gpr .x5 (by decide), k₄'.gpr .x5 (by decide), h5₃]
  have e13 : BitVec.ofNat 64 (Wk I.k) - BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 * vk I.k) := by
    rw [ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW, hv2])]; congr 1
  have eL : BitVec.ofNat 64 (Wk I.k) >>> 1 = BitVec.ofNat 64 (vk I.k + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    simp only [Wk, vk] at *; omega_using [hk2]
  have eS : BitVec.ofNat 64 (vk I.k + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (vk I.k) := by
    rw [ofNat_sub_ofNat (by omega_using []) (by omega_using [hv2])]; rfl
  refine WP.mono (WP.keep [.x7, .x11, .x12, .x13] (Q := fun t => t.gpr .x11 = off I.B (slot (vk I.k) nRem) ∧
      t.gpr .x13 = BitVec.ofNat 64 (2 * vk I.k) ∧ t.gpr .x12 = BitVec.ofNat 64 (vk I.k) ∧ t.gpr .x7 = 0 ∧
      t.mem = t₇.mem) (by brun [h5₇, h12₇, e13, eL, eS]) (by decide) (by decide) (by decide +kernel))
    fun s₁₆ ⟨⟨h11, h13, h12, h7, m₈'⟩, k₈'⟩ => ?_
  have g₁₆ : G I m₀ (Wk I.k) c s₁₆ := g₄'.same (by rw [m₈', m₇', m₆', m₅']) (((k₅'.trans k₆').trans k₇').trans k₈')
    (by decide)
  have w16 : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv s₁₆.mem I.B d n = wv s₁₅.mem I.B d n := fun d n hd hd' => by
    rw [m₈', m₇', m₆', m₅', Frm.hdrW_wv f₄' hd hd', m₃', m₂', m₁']
  have wd16 : ∀ d, 256 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁₆.mem I.B d = word s₁₅.mem I.B d := fun d hd hd' => by
    rw [m₈', m₇', m₆', m₅', Frm.hdrW_word f₄' hd hd', m₃', m₂', m₁']
  have zR : ∀ q < vk I.k + 2, word s₁₆.mem I.B (slot (vk I.k) nRem + 8 * q) = 0 := fun q hq => by
    rw [wd16 _ (by omega_using [q4]) (by omega_using [hv2, q4, hq])]; exact (wv_eq_zero_iff _ _ _ _).mp z₁₅ q hq
  have hM₁₆ : wv s₁₆.mem I.B (slot (vk I.k) nM1) (vk I.k) = wv s₁₄.mem I.B (slot (vk I.k) nM1) (vk I.k) := by
    rw [w16 _ _ (by omega_using [q2]) (by omega_using [hv2, q2]), o₁₅.wv (by omega_using [q2, q4]) (by omega_using [hv2, q2])]
  have h9₁₆ : s₁₆.gpr .x9 = off I.B (slot (vk I.k) nM1) := by
    rw [k₈'.gpr .x9 (by decide), k₇'.gpr .x9 (by decide), k₆'.gpr .x9 (by decide), k₅'.gpr .x9 (by decide),
      k₄'.gpr .x9 (by decide), k₃'.gpr .x9 (by decide), h9₂]
  -- The values when the divisor is not zero.
  have hval : 0 < D → wv s₁₆.mem I.B (slot (Wk I.k) wM) (2 * vk I.k) = X * 2 ^ (64 * (vk I.k - 1 - hi)) ∧
      wv s₁₆.mem I.B (slot (vk I.k) nM1) (vk I.k) = D * 2 ^ (64 * (vk I.k - 1 - hi)) ∧
      X / D < 2 ^ (64 * vk I.k) := by
    intro hpos
    have hD0 : wv s₆.mem I.B (slot (vk I.k) nM1) (vk I.k) ≠ 0 := by rw [hm1]; omega_using [hpos]
    obtain ⟨hlo, hhi', -⟩ := hiD hD0
    rw [hm1] at hlo hhi'
    have hXl : X < 2 ^ (64 * vk I.k) := hd ▸ wv_lt _ _ _ _
    obtain ⟨a1, a2, a3, -, -, a6⟩ := divB_math hlo hhi' (z := vk I.k - 1 - hi) (by omega_using [hv9, hlt]) hXl
    rw [Nat.mod_eq_of_lt a1] at vM1₁₃
    have hW2 : 2 ^ (64 * (2 * vk I.k)) ≤ 2 ^ (64 * Wk I.k) := Nat.pow_le_pow_right (by decide) (by omega_using [hW])
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a3 hW2)] at vM₁₃
    refine ⟨?_, ?_, a6⟩
    · rw [w16 _ _ (by omega_using [qM]) (by omega_using [hW, hv9, hv2, q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS, hD0, hlo, hhi']), o₁₅.wv (by omega_using [hW, hv9, hv2, q4, q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS, hD0, hlo, hhi']) (by omega_using [hW, hv9, hv2, q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS, hD0, hlo, hhi']), w14 _ _ (by omega_using [hW, hv9, hv2, q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS, hD0, hlo, hhi']) (by omega_using [qM]) (by omega_using [hW, hv9, hv2, q2, q3', q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS, hD0, hlo, hhi']),
        wv_low_of_lt (w := Wk I.k) (by omega_using [hW]) (by rw [vM₁₃]; exact a3), vM₁₃]
    · rw [hM₁₆, ← vM1₁₃]
      refine wv_congr fun i hi => ?_
      rcases Nat.lt_or_ge i (vk I.k - 1) with hi' | hi'
      · exact f₁₄.word_eq (fun r hr => by
          simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · have := hdrW_rb r hr; omega_using [q2, this]
          · dsimp only; omega_using [hi']) (by omega_using [hv2, q2, hi])
      · rw [show i = vk I.k - 1 by omega_using [hi, hi'], top₁₄]
        exact fixW_of_ne (top_ne _ _ _ _ (by omega_using [hv9]) (by rw [vM1₁₃]; exact a2))
  have F16 : Frm I.B hdrW s₁₅.mem s₁₆.mem := by
    rw [m₈', m₇', m₆', m₅', ← (show t₃.mem = s₁₅.mem by rw [m₃', m₂', m₁'])]; exact f₄'
  refine ⟨D, X, hi, g₁₆, ⟨g₁₆.ws.scr, g₁₆.ws.x0, by rw [k₈'.gpr .x8 (by decide), h8₇], h13, h11, h12, h9₁₆,
    by rw [k₈'.gpr .x6 (by decide), k₇'.gpr .x6 (by decide), h6₆], h7,
    by omega_using [hv9], by omega_using [], by omega_using [hv2], by omega_using [qM], by omega_using [qM, qc], by omega_using [q4, qc], by omega_using [q2, qc], by omega_using [qT, qc],
    by omega_using [hW, hv9, hv2, hb32, hn, hZ32, q32, q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS], by omega_using [hW, hv9, hv2, hb32, hn, hZ32, q32, q4, hm1, hlt, hiD, hhi, e13, eS], by omega_using [hW, hv9, hv2, hb32, hn, hZ32, q32, q2, hm1, hlt, hiD, hhi, e13, eS], by omega_using [hW, hZ32, q32, qT], by omega_using [hW, hv9, hv2, q4, q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS], by omega_using [hW, hv9, hv2, q2, q10, qM, e10, hm1, hlt, hiD, hhi, e13, eS], by omega_using [hW, hv9, hv2, q10, qM, qT, e10, hm1, hlt, hiD, hhi, e13, eS], by omega_using [q2, q4], by omega_using [hW, q4, qT], by omega_using [hW, q2, qT],
    by rw [zR _ (by omega_using [])], by rw [zR _ (by omega_using [])], by rw [hM₁₆]; exact htop₁₄⟩, hval, rfl, rfl, ?_⟩
  exact FH.trans F12 |>.trans (rbB_frm f₁₃ fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with hr | rfl | rfl
      · exact .inl (hdrW_rb r hr)
      · dsimp only; omega_using [hv9, hv2, q2, q6, q2', q10', q12, q18, q20, hlt, hiD, hhi, e13, eS]
      · dsimp only; omega_using [hW, q10', q12, qM]) |>.trans (rbB_frm f₁₄ fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact .inl (hdrW_rb r hr)
      · dsimp only; omega_using [hv9, hv2, q2, q6, q2', q10', q12, q18, q20, hlt, hiD, hhi, e13, eS]) |>.trans (rbB_out o₁₅ (by omega_using [hv9, hv2, q4, q6, q2', q10', q12, q18, q20, hlt, hiD, hhi, e13, eS])) |>.trans
      (rbB_frm F16 fun r hr => .inl (hdrW_rb r hr))

/-- `divB`: `m + 1` and `n - r`, their quotient `q` (narrow array 3) and remainder (4), and the
remainder zero and'ed into the mask. -/
theorem divB_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (Wk I.k) c s) (L : RpLens I) {M R N : Nat}
    (hM : wv s.mem I.B (slot (Wk I.k) wA) (Wk I.k) = M) (hR : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k + 1) = R)
    (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N)
    (one : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1) :
    WP isa divB s fun t => ∃ q rem : Nat,
      G I m₀ (vk I.k) (decide (rem = 0) && c) t ∧ wv t.mem I.B (slot (vk I.k) nD) (vk I.k) = q ∧
      (0 < (M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k) →
        q = wsub (64 * vk I.k) N (R % 2 ^ (64 * vk I.k)) / ((M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k)) ∧
        rem = wsub (64 * vk I.k) N (R % 2 ^ (64 * vk I.k)) % ((M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k))) ∧
      (∀ j k, (j < 2 ∨ (6 ≤ j ∧ j < 10)) → k ≤ vk I.k + 2 →
        wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hk1 := L.k1
  have hk2 := L.k2
  have hv9 : 9 ≤ vk I.k := by simp only [vk]; omega_using [hk1]
  have hv2 : vk I.k ≤ 200 := by simp only [vk]; omega_using [hk2]
  have hb32 := hb32_of h L
  have hn := h.ws.scr.nowrap
  have hZ32 : slot (vk I.k) 32 ≤ I.Z := by have := h.ws.hZ; rw [hW, slot_wide] at this; exact this
  have q32 : slot (vk I.k) 32 = 256 + 32 * (8 * (vk I.k + 2)) := rfl
  have q0 : slot (vk I.k) 0 = 256 + 0 * (8 * (vk I.k + 2)) := rfl
  have q1 : slot (vk I.k) nOne = 256 + 1 * (8 * (vk I.k + 2)) := rfl
  have q2 : slot (vk I.k) nM1 = 256 + 2 * (8 * (vk I.k + 2)) := rfl
  have q3 : slot (vk I.k) nD = 256 + 3 * (8 * (vk I.k + 2)) := rfl
  have q4 : slot (vk I.k) nRem = 256 + 4 * (8 * (vk I.k + 2)) := rfl
  have q5 : slot (vk I.k) nZ = 256 + 5 * (8 * (vk I.k + 2)) := rfl
  have q6 : slot (vk I.k) 6 = 256 + 6 * (8 * (vk I.k + 2)) := rfl
  have q2' : slot (vk I.k) 2 = 256 + 2 * (8 * (vk I.k + 2)) := rfl
  have q3' : slot (vk I.k) 3 = 256 + 3 * (8 * (vk I.k + 2)) := rfl
  have q10 : slot (vk I.k) (2 * wM) = 256 + 10 * (8 * (vk I.k + 2)) := rfl
  have q10' : slot (vk I.k) 10 = 256 + 10 * (8 * (vk I.k + 2)) := rfl
  have q12 : slot (vk I.k) 12 = 256 + 12 * (8 * (vk I.k + 2)) := rfl
  have q14 : slot (vk I.k) (2 * wA) = 256 + 14 * (8 * (vk I.k + 2)) := rfl
  have q12x : slot (vk I.k) (2 * wX) = 256 + 12 * (8 * (vk I.k + 2)) := rfl
  have q18 : slot (vk I.k) 18 = 256 + 18 * (8 * (vk I.k + 2)) := rfl
  have q20 : slot (vk I.k) 20 = 256 + 20 * (8 * (vk I.k + 2)) := rfl
  have qM : slot (Wk I.k) wM = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  have qT : slot (Wk I.k) wT = 256 + 9 * (8 * (Wk I.k + 2)) := rfl
  have qA : slot (Wk I.k) wA = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qX : slot (Wk I.k) wX = 256 + 6 * (8 * (Wk I.k + 2)) := rfl
  have qc : 8 * sCnt = 208 := rfl
  have e14 : slot (Wk I.k) wA = slot (vk I.k) (2 * wA) := slot_wide _ _
  have e12 : slot (Wk I.k) wX = slot (vk I.k) (2 * wX) := slot_wide _ _
  have e10 : slot (Wk I.k) wM = slot (vk I.k) (2 * wM) := slot_wide _ _
  rw [divB_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (divB1_ok h L hM hR hN one)
    fun s₁₆ ⟨D, X, hi, g₁₆, hh, hval, hD, hX, F16f⟩ => ?_)
  rw [hD, hX]
  -- The division.
  refine wpc (by simp) (WP.mono hh.ok fun s₁₇ ⟨hr₁₇, hq₁₇, _, f₁₇, _, k₁₇⟩ => ?_)
  rw [show 2 * vk I.k - vk I.k + 1 = vk I.k + 1 by omega_using []] at hq₁₇ f₁₇
  have g₁₇ : G I m₀ (Wk I.k) c s₁₇ := g₁₆.frmOwn (sl := sCnt) ⟨by decide, by decide, by decide⟩
    (rs := [(slot (Wk I.k) wM, 8 * (vk I.k + 1)), (slot (vk I.k) nRem, 8 * (vk I.k + 1)), (slot (Wk I.k) wT, 32)]) f₁₇
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith)
    k₁₇ (by decide)
  generalize hU : wv s₁₆.mem I.B (slot (Wk I.k) wM) (2 * vk I.k) = U at hr₁₇ hq₁₇ hval
  generalize hMM : wv s₁₆.mem I.B (slot (vk I.k) nM1) (vk I.k) = M' at hr₁₇ hq₁₇ hval
  have hM'l : M' < 2 ^ (64 * vk I.k) := hMM ▸ wv_lt _ _ _ _
  have hM'0 : 0 < M' := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (hMM ▸ hh.htop)
  -- The quotient into `nD`, and the remainder zero.
  refine wpc (by simp) (WP.mono (g₁₇.setNar_ok L) fun s₁₈ ⟨g₁₈, f₁₈, k₁₈⟩ => ?_)
  refine wpc (by simp) (WP.mono (zeroA_ok g₁₈.ws (j := nD) (by decide)) fun s₁₉ ⟨_, o₁₉, _, _, _, k₁₉⟩ => ?_)
  have g₁₉ := g₁₈.out (by decide) (Nat.le_refl _) o₁₉ k₁₉ (by decide)
  refine wpc (by simp) (WP.mono (copyA_ok g₁₉.ws (o := nD) (a := 2 * wM) (by decide) (by decide) (by decide))
    fun s₂₀ ⟨v₂₀, o₂₀, _, _, k₂₀⟩ => ?_)
  have g₂₀ := g₁₉.out (by decide) (by omega_using []) o₂₀ k₂₀ (by decide)
  refine wpc (by simp) (WP.mono (zeroA_ok g₂₀.ws (j := nZ) (by decide)) fun s₂₁ ⟨z₂₁, o₂₁, _, _, _, k₂₁⟩ => ?_)
  have g₂₁ := g₂₀.out (by decide) (Nat.le_refl _) o₂₁ k₂₁ (by decide)
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok g₂₁.ws (a := nRem) (b := nZ) (by decide)
    (by decide)) fun s₂₂ ⟨h9, m₂₂, _, _, k₂₂⟩ => ?_)
  have z₂₁' : wv s₂₁.mem I.B (slot (vk I.k) nZ) (vk I.k) = 0 := by
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega_using []) (by rw [z₂₁]; exact Nat.two_pow_pos _), z₂₁]
  rw [z₂₁'] at h9
  have g₂₂ := g₂₁.same m₂₂ k₂₂ (by decide)
  have rem₂₁ : wv s₂₁.mem I.B (slot (vk I.k) nRem) (vk I.k) = U % M' := by
    rw [o₂₁.wv (by omega_using [q4, q5]) (by omega_using [hv2, q4]), o₂₀.wv (by omega_using [q3, q4]) (by omega_using [hv2, q4]), o₁₉.wv (by omega_using [q3, q4]) (by omega_using [hv2, q4]),
      Frm.hdrW_wv f₁₈ (by omega_using [q4]) (by omega_using [hv2, q4]), wv_low_of_lt (w := vk I.k + 1) (by omega_using [])
        (by rw [hr₁₇]; exact Nat.lt_trans (Nat.mod_lt _ hM'0) hM'l), hr₁₇]
  rw [rem₂₁] at h9
  have q₂₂ : wv s₂₂.mem I.B (slot (vk I.k) nD) (vk I.k) = U / M' % 2 ^ (64 * vk I.k) := by
    rw [m₂₂, o₂₁.wv (by omega_using [q3, q5]) (by omega_using [hv2, q3]), v₂₀, o₁₉.wv (by omega_using [q3, q10]) (by omega_using [hv2, q10]), Frm.hdrW_wv f₁₈ (by omega_using [q10]) (by omega_using [hv2, q10]),
      ← e10, ← wv_mod _ _ _ (show vk I.k ≤ vk I.k + 1 by omega_using []), hq₁₇]
  have hz : s₂₂.gpr .x9 = 0 ↔ (if 0 < D then X % D else U % M') = 0 := by
    rw [h9]
    split
    · next hpos =>
      obtain ⟨hU', hM', -⟩ := hval hpos
      rw [hU', hM', Nat.mul_mod_mul_right]
      exact ⟨fun h => (Nat.mul_eq_zero.mp h).resolve_right (Nat.ne_of_gt (Nat.two_pow_pos _)),
        fun h => by rw [h, Nat.zero_mul]⟩
    · exact Iff.rfl
  -- What `divB` writes.
  have F22 : Frm I.B (rbB (vk I.k)) s.mem s₂₂.mem :=
    F16f |>.trans (rbB_frm f₁₇ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) |>.trans
      (rbB_frm f₁₈ fun r hr => .inl (hdrW_rb r hr)) |>.trans (rbB_out o₁₉ (by omega_using [q3, q6, q2'])) |>.trans
      (rbB_out o₂₀ (by omega_using [q3, q6, q2'])) |>.trans (rbB_out o₂₁ (by omega_using [q5, q6, q2'])) |>.trans (by rw [m₂₂]; exact Frm.refl _ _ _)
  refine WP.mono (andZero_ok g₂₂.ws g₂₂.msk hz) fun t ⟨⟨mt, _⟩, kt⟩ =>
    ⟨_, _, g₂₂.store mt kt (by decide), rfl, fun hpos => ?_, fun j k hj hk => ?_⟩
  · have ot : Outside I.B (8 * Public.sMask) 8 s₂₂.mem t.mem := by
      rw [mt]; exact writeW_outside s₂₂.mem I.B _ (by simp only [Public.sMask, sFn]; omega_using [])
    obtain ⟨hU', hM', hq⟩ := hval hpos
    refine ⟨?_, by simp only [hpos, ↓reduceIte]⟩
    rw [ot.wv (hd_sep (by decide)) (by omega_using [hv2, q3]), q₂₂, hU', hM', Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _),
      Nat.mod_eq_of_lt hq]
  · have ot : Outside I.B (8 * Public.sMask) 8 s₂₂.mem t.mem := by
      rw [mt]; exact writeW_outside s₂₂.mem I.B _ (by simp only [Public.sMask, sFn]; omega_using [])
    exact rbB_wv (F22.trans (rbB_out ot (by simp only [Public.sMask, sFn]; omega_using []))) hj hk hb32

end VG.Proof.Rsa.AArch64.Rd
