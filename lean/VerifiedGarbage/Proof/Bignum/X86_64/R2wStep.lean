module
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Words

import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.X86_64.R2wSub
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd

/-!
# `R² mod m` by word steps on x86-64: a step

`step`: `x := x 2^64 mod m` for `x < m` in `aR2` and `m` in `aN`, whose top
word is at least `2^63`, with the accumulator as `t` (`step_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

/-- `n + 1` words: the low `n` and the top one. -/
theorem wv_succ (m : Mem) (B : Addr) (e n : Nat) :
    wv m B e (n + 1) = wv m B e n + 2 ^ (64 * n) * (word m B (e + 8 * n)).toNat := rfl

/-- The top word of `x < m` is at most `m`'s. -/
theorem top_le {m : Mem} {B : Addr} {ex em w : Nat} (hw : 1 ≤ w)
    (h : wv m B ex w < wv m B em w) :
    (word m B (ex + 8 * (w - 1))).toNat ≤ (word m B (em + 8 * (w - 1))).toNat := by
  rw [show w = (w - 1) + 1 by omega_arith, wv_succ, wv_succ] at h
  have h1 := wv_lt m B ex (w - 1)
  have h2 := wv_lt m B em (w - 1)
  rcases Nat.lt_or_ge (word m B (em + 8 * (w - 1))).toNat (word m B (ex + 8 * (w - 1))).toNat with hl | hl
  · exfalso
    have := Nat.mul_le_mul_left (2 ^ (64 * (w - 1))) (show (word m B (em + 8 * (w - 1))).toNat + 1 ≤
      (word m B (ex + 8 * (w - 1))).toNat by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega_arith
  · exact hl

/-- The sign of `t` (`w + 1` words) in two's complement is its top word's
top bit. -/
theorem top_half (m : Mem) (B : Addr) (e w : Nat) :
    2 ^ (64 * (w + 1)) / 2 ≤ wv m B e (w + 1) ↔ 2 ^ 63 ≤ (word m B (e + 8 * w)).toNat := by
  rw [wv_succ]
  have h1 := wv_lt m B e w
  have hW : 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 := by
    rw [show 64 * (w + 1) = 64 * w + 63 + 1 by omega_arith, Nat.pow_succ, Nat.mul_div_cancel _ (by decide),
      Nat.pow_add]
  rw [hW]
  generalize 2 ^ (64 * w) = P at *
  generalize (word m B (e + 8 * w)).toNat = T
  constructor
  · intro h
    by_contra hc
    have := Nat.mul_le_mul_left P (show T + 1 ≤ 2 ^ 63 by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega_arith
  · intro h
    exact Nat.le_trans (Nat.mul_le_mul_left P h) (Nat.le_add_left _ _)

theorem addrm24 {b i p : Addr} {e j : Nat} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j) (hj : 3 ≤ j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-24) = off p (e + 8 * (j - 3)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-24) = BitVec.ofNat 64 (8 * (j - 3)) := by
    rw [show (-24 : Int) = - ((24 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 3) + 24 by omega_using [hj], BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  subst hb hi
  rw [ofNat_mul8, off, BitVec.add_assoc, BitVec.add_assoc, h8, ← BitVec.ofNat_add]

/-- `quot3`: `t = U - q̂ D` over three words (`r15`, `r14`, `r13`), with its
borrow `b`, for `q̂` in `rcx`, `x`'s top three words `U` and `m`'s top two
`D`. -/
theorem quot3_ok {t : State} {B : Addr} {Z w ex em : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 3 ≤ w) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z) :
    WP isa (.block quot3) t fun t' =>
      (∃ b < 2, (t'.gpr .r15).toNat * 2 ^ 128 + (t'.gpr .r14).toNat * 2 ^ 64 + (t'.gpr .r13).toNat +
          (t.gpr .rcx).toNat * ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 +
            (word t.mem B (em + 8 * (w - 2))).toNat) =
        (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 + (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 +
          (word t.mem B (ex + 8 * (w - 3))).toNat + 2 ^ 192 * b) ∧
      t'.mem = t.mem ∧ Keep [.rax, .rdx, .r9, .r11, .r13, .r14, .r15] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx, .r9, .r11, .r13, .r14, .r15] (Q := fun t' =>
      (∃ b < 2, (t'.gpr .r15).toNat * 2 ^ 128 + (t'.gpr .r14).toNat * 2 ^ 64 + (t'.gpr .r13).toNat +
          (t.gpr .rcx).toNat * ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 +
            (word t.mem B (em + 8 * (w - 2))).toNat) =
        (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 + (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 +
          (word t.mem B (ex + 8 * (w - 3))).toNat + 2 ^ 192 * b) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold quot3
  xrun [State.ea, ix, addrm8 h10 h12 (by omega_using [hw]), addrm16 h10 h12 (by omega_using [hw]),
    addrm8 hbx h12 (by omega_using [hw]), addrm16 hbx h12 (by omega_using [hw]), addrm24 hbx h12 hw,
    hs.ld (show em + 8 * (w - 1) + 8 ≤ Z by omega_using [hw, hM]), hs.ld (show em + 8 * (w - 2) + 8 ≤ Z by omega_using [hw, hM]),
    hs.ld (show ex + 8 * (w - 1) + 8 ≤ Z by omega_using [hw, hX]), hs.ld (show ex + 8 * (w - 2) + 8 ≤ Z by omega_using [hw, hX]),
    hs.ld (show ex + 8 * (w - 3) + 8 ≤ Z by omega_using [hw, hX]), sx0]
  dsimp only [word]
  generalize t.mem.readW (off B (ex + 8 * (w - 1))) 64 = u2
  generalize t.mem.readW (off B (ex + 8 * (w - 2))) 64 = u1
  generalize t.mem.readW (off B (ex + 8 * (w - 3))) 64 = u0
  generalize t.mem.readW (off B (em + 8 * (w - 1))) 64 = d1
  generalize t.mem.readW (off B (em + 8 * (w - 2))) 64 = d0
  generalize t.gpr .rcx = q
  have m1 := mul_toNat d1 q; have l1 := mul_le d1 q
  have m0 := mul_toNat d0 q; have l0 := mul_le d0 q
  have eq : q.toNat * (d1.toNat * 2 ^ 64 + d0.toNat) = d1.toNat * q.toNat * 2 ^ 64 + d0.toNat * q.toNat := by
    rw [Nat.mul_comm, Nat.add_mul, Nat.mul_right_comm]
  rw [eq]
  generalize d1.toNat * q.toNat = p1 at *
  generalize d0.toNat * q.toNat = p0 at *
  generalize BitVec.ofNat 64 (p1 / 2 ^ 64) = H1 at *
  generalize BitVec.ofNat 64 p1 = P1 at *
  generalize BitVec.ofNat 64 (p0 / 2 ^ 64) = H0 at *
  generalize BitVec.ofNat 64 p0 = P0 at *
  have hH0 := H0.isLt
  have a1 := addc_toNat P1 H1 H0 (by omega_using [m1, l1, hH0])
  have s0 := sbb_toNat u0 P0 false
  have s1 := sbb_toNat u1 (P1 + H0) (decide (u0.toNat < P0.toNat))
  have s2 := sbb_toNat u2 (H1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ P1.toNat + H0.toNat))).setWidth 64)
    (decide (u1.toNat < (P1 + H0).toNat + (decide (u0.toNat < P0.toNat)).toNat))
  simp only [Bool.toNat_false, Nat.add_zero, show (BitVec.ofBool false).setWidth 64 = 0#64 from rfl,
    BitVec.sub_zero] at s0
  generalize decide (u0.toNat < P0.toNat) = c0 at *
  generalize decide (2 ^ 64 ≤ P1.toNat + H0.toNat) = c1 at *
  generalize decide (u1.toNat < (P1 + H0).toNat + c0.toNat) = c2 at *
  generalize decide (u2.toNat < _ + c2.toNat) = c3 at s2
  generalize (u2 - _ - (BitVec.ofBool c2).setWidth 64) = R15 at *
  generalize (u1 - (P1 + H0) - (BitVec.ofBool c0).setWidth 64) = R14 at *
  generalize (u0 - P0) = R13 at *
  generalize (H1 + 0 + (BitVec.ofBool c1).setWidth 64) = RDX at *
  generalize (P1 + H0) = RAX at *
  exact ⟨c3.toNat, Bool.toNat_lt _, by omega_using [m1, m0, a1, s0, s1, s2]⟩

/-- The three words `r15`, `r14`, `r13` of `quot3`'s remainder. -/
abbrev rem3 (s : State) : Nat := (s.gpr .r15).toNat * 2 ^ 128 + (s.gpr .r14).toNat * 2 ^ 64 + (s.gpr .r13).toNat

/-- `fix3`: if the remainder `t` is negative (its top bit set), `q̂ := q̂ - 1`
and `t := t + D`, with its carry `c`, for `m`'s top two words `D`. -/
theorem fix3_ok {t : State} {B : Addr} {Z w em : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hM : em + 8 * w ≤ Z) :
    WP isa (.block fix3) t fun t' =>
      (∀ n, (t.gpr .rcx).toNat = n + (if 2 ^ 192 / 2 ≤ rem3 t then 1 else 0) → (t'.gpr .rcx).toNat = n) ∧
      (∃ c < 2, rem3 t' + 2 ^ 192 * c = rem3 t + if 2 ^ 192 / 2 ≤ rem3 t then
        (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat else 0) ∧
      t'.mem = t.mem ∧ Keep [.rax, .rcx, .rdx, .r11, .r13, .r14, .r15] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r11, .r13, .r14, .r15] (Q := fun t' =>
      (∀ n, (t.gpr .rcx).toNat = n + (if 2 ^ 192 / 2 ≤ rem3 t then 1 else 0) → (t'.gpr .rcx).toNat = n) ∧
      (∃ c < 2, rem3 t' + 2 ^ 192 * c = rem3 t + if 2 ^ 192 / 2 ≤ rem3 t then
        (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat else 0) ∧
      t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold fix3
  dsimp only [rem3]
  xrun [State.ea, ix, addrm8 h10 h12 (by omega_using [hw]), addrm16 h10 h12 hw,
    hs.ld (show em + 8 * (w - 1) + 8 ≤ Z by omega_using [hw, hM]), hs.ld (show em + 8 * (w - 2) + 8 ≤ Z by omega_using [hw, hM]),
    sx0, BitVec.sub_self]
  dsimp only [word]
  generalize t.mem.readW (off B (em + 8 * (w - 1))) 64 = d1
  generalize t.mem.readW (off B (em + 8 * (w - 2))) 64 = d0
  generalize t.gpr .rcx = q
  have l0 := (t.gpr .r13).isLt; have l1 := (t.gpr .r14).isLt; have l2 := (t.gpr .r15).isLt; have lq := q.isLt
  by_cases hn : 2 ^ 64 ≤ (t.gpr .r15).toNat + (t.gpr .r15).toNat
  · have hc : 2 ^ 192 / 2 ≤ (t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat := by omega_using [hn, l0, l1, l2]
    simp only [hc, ↓reduceIte, hn, decide_true]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.and_allOnes]
    have e1 := VG.Proof.Poly1305.Limbs64.addc0 (t.gpr .r13) d0
    generalize decide (2 ^ 64 ≤ (t.gpr .r13).toNat + d0.toNat) = c1 at *
    have e2 := VG.Proof.Poly1305.Limbs64.addc1 (t.gpr .r14) d1 c1
    generalize decide (2 ^ 64 ≤ (t.gpr .r14).toNat + d1.toNat + c1.toNat) = c2 at *
    have e3 := VG.Proof.Poly1305.Limbs64.addc1 (t.gpr .r15) 0 c2
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at e3
    refine ⟨fun n hq => ?_, _, Bool.toNat_lt (decide (2 ^ 64 ≤ (t.gpr .r15).toNat + 0 + c2.toNat)), ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_allOnes]; omega_using [hq, lq]
    · omega_using [e1, e2, e3]
  · have hc : ¬ 2 ^ 192 / 2 ≤ (t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat := by omega_using [hn, l0, l1, l2]
    simp only [hc, ↓reduceIte, hn, decide_false]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool false)) = 0#64 by decide,
      BitVec.and_zero, BitVec.and_zero]
    have e1 := VG.Proof.Poly1305.Limbs64.addc0 (t.gpr .r13) 0#64
    generalize decide (2 ^ 64 ≤ (t.gpr .r13).toNat + (0#64).toNat) = c1 at *
    have e2 := VG.Proof.Poly1305.Limbs64.addc1 (t.gpr .r14) 0#64 c1
    generalize decide (2 ^ 64 ≤ (t.gpr .r14).toNat + (0#64).toNat + c1.toNat) = c2 at *
    have e3 := VG.Proof.Poly1305.Limbs64.addc1 (t.gpr .r15) 0 c2
    rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at e1 e2
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at e3
    refine ⟨fun n hq => ?_, _, Bool.toNat_lt (decide (2 ^ 64 ≤ (t.gpr .r15).toNat + 0 + c2.toNat)), ?_⟩
    · rw [BitVec.add_zero]; omega_using [hq]
    · omega_using [e1, e2, e3]

/-- `refine3`: the 3-by-2 correction of the estimate `q̂` in `rcx`, `Q ≤ q̂ ≤
Q + 2`, to `Q = min(⌊U / D⌋, 2^64 - 1)`, for `x`'s top three words `U` and
`m`'s top two `D`, `U < (2^64 + 1) D`. -/
theorem refine3_ok {t : State} {B : Addr} {Z w ex em U D : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 3 ≤ w) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z)
    (hU : U = (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 + (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 +
      (word t.mem B (ex + 8 * (w - 3))).toNat)
    (hD : D = (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat)
    (hD0 : 0 < D) (hUD : U < (2 ^ 64 + 1) * D)
    (hge : min (U / D) (2 ^ 64 - 1) ≤ (t.gpr .rcx).toNat) (hle : (t.gpr .rcx).toNat ≤ min (U / D) (2 ^ 64 - 1) + 2) :
    WP isa (.block refine3) t fun t' => (t'.gpr .rcx).toNat = min (U / D) (2 ^ 64 - 1) ∧ t'.mem = t.mem ∧
      Keep [.rax, .rcx, .rdx, .r9, .r11, .r13, .r14, .r15] t t' := by
  unfold refine3
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (quot3_ok hs hbx h10 h12 hw hX hM) fun t₁ ⟨⟨b, hb, h1⟩, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have hs₁ := hs.congr k₁.2.2
  have t₁10 : t₁.gpr .r10 = off B em := (k₁.gpr (by decide)).trans h10
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have t₁cx : t₁.gpr .rcx = t.gpr .rcx := k₁.gpr (by decide)
  refine WP.mono (fix3_ok hs₁ t₁10 t₁12 (by omega_using [hw]) hM) fun t₂ ⟨hq₂, ⟨c, hc, h2⟩, hm₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have t₂10 : t₂.gpr .r10 = off B em := (k₂.gpr (by decide)).trans t₁10
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans t₁12
  refine WP.mono (fix3_ok hs₂ t₂10 t₂12 (by omega_using [hw]) hM) fun t₃ ⟨hq₃, _, hm₃, k₃⟩ => ?_
  refine ⟨?_, hm₃.trans (hm₂.trans hm₁), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [hm₁, ← hD] at h2
  rw [← hU, ← hD] at h1
  have hd1 := (word t.mem B (em + 8 * (w - 1))).isLt
  have hd0 := (word t.mem B (em + 8 * (w - 2))).isLt
  have hDW : 4 * D < 2 ^ 192 / 2 := by omega_using [hD, hd1, hd0]
  have hT1 : rem3 t₁ < 2 ^ 192 := by
    have := (t₁.gpr .r15).isLt; have := (t₁.gpr .r14).isLt; have := (t₁.gpr .r13).isLt
    dsimp only [rem3]; omega_using []
  have hT2 : rem3 t₂ < 2 ^ 192 := by
    have := (t₂.gpr .r15).isLt; have := (t₂.gpr .r14).isLt; have := (t₂.gpr .r13).isLt
    dsimp only [rem3]; omega_using []
  have hv := quot3_val (W := 2 ^ 192) (T1 := rem3 t₁) (T2 := rem3 t₂) hD0 hDW hUD hge hle (t.gpr .rcx).isLt hT1 hb
    (by rw [← t₁cx] at h1 ⊢; exact h1) hT2 hc h2
  exact hq₃ _ (hq₂ _ (by rw [t₁cx, hv, Nat.add_right_comm]))

theorem div_pow_cancel {a l K : Nat} (hl : l < 2 ^ K) : (a * 2 ^ K + l) / 2 ^ K = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos K), Nat.div_eq_of_lt hl, Nat.zero_add]

/-- The estimates of a word step from `x`'s top three words `U` and `m`'s top
two `D` (`WordStep.qhat3_norm`): `U < (2^64 + 1) D`, the 2-by-1 estimate is
`Q ≤ q̂ ≤ Q + 2` for `Q = min(⌊U / D⌋, 2^64 - 1)`, and `q ≤ Q ≤ q + 1` for `q =
⌊x 2^64 / m⌋`. -/
theorem norm3 {w X M u2 u1 u0 Xl d1 d0 ml : Nat} (hw : 3 ≤ w)
    (hX : X = u2 * 2 ^ (64 * (w - 1)) + u1 * 2 ^ (64 * (w - 2)) + u0 * 2 ^ (64 * (w - 3)) + Xl)
    (hXl : Xl < 2 ^ (64 * (w - 3)))
    (hM : M = d1 * 2 ^ (64 * (w - 1)) + d0 * 2 ^ (64 * (w - 2)) + ml) (hml : ml < 2 ^ (64 * (w - 2)))
    (hu0 : u0 < 2 ^ 64) (hd0 : d0 < 2 ^ 64) (hd : 2 ^ 63 ≤ d1) (hXM : X < M) :
    u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0 < (2 ^ 64 + 1) * (d1 * 2 ^ 64 + d0) ∧
      min ((u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0)) (2 ^ 64 - 1) ≤
        min ((u2 * 2 ^ 64 + u1) / d1) (2 ^ 64 - 1) ∧
      min ((u2 * 2 ^ 64 + u1) / d1) (2 ^ 64 - 1) ≤
        min ((u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0)) (2 ^ 64 - 1) + 2 ∧
      X * 2 ^ 64 / M ≤ min ((u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0)) (2 ^ 64 - 1) ∧
      min ((u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / (d1 * 2 ^ 64 + d0)) (2 ^ 64 - 1) ≤ X * 2 ^ 64 / M + 1 := by
  rw [show 64 * (w - 1) = 64 * (w - 3) + 64 + 64 by omega_using [hw]] at hX hM
  rw [show 64 * (w - 2) = 64 * (w - 3) + 64 by omega_using [hw]] at hX hM hml
  generalize 64 * (w - 3) = K at *
  have e128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := Nat.pow_add 2 64 64
  have hXd : X * 1 / 2 ^ K = u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0 := by
    have e : u2 * 2 ^ (K + 64 + 64) + u1 * 2 ^ (K + 64) + u0 * 2 ^ K + Xl =
        (u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) * 2 ^ K + Xl := by
      rw [Nat.pow_add, Nat.pow_add, e128]
      generalize 2 ^ K = P; generalize 2 ^ 64 = B
      grind
    rw [Nat.mul_one, hX, e, div_pow_cancel hXl]
  have hMd : M * 1 / 2 ^ (K + 64) = d1 * 2 ^ 64 + d0 := by
    have e : d1 * 2 ^ (K + 64 + 64) + d0 * 2 ^ (K + 64) + ml = (d1 * 2 ^ 64 + d0) * 2 ^ (K + 64) + ml := by
      rw [Nat.pow_add, Nat.pow_add]
      generalize 2 ^ K = P; generalize 2 ^ 64 = B
      grind
    rw [Nat.mul_one, hM, e, div_pow_cancel hml]
  have hUd : (u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0) / 2 ^ 64 = u2 * 2 ^ 64 + u1 := by
    have e : u2 * 2 ^ 128 + u1 * 2 ^ 64 + u0 = (u2 * 2 ^ 64 + u1) * 2 ^ 64 + u0 := by
      rw [e128]
      generalize 2 ^ 64 = B
      grind
    rw [e, div_pow_cancel hu0]
  have hDd : (d1 * 2 ^ 64 + d0) / 2 ^ 64 = d1 := div_pow_cancel hd0
  have h := qhat3_norm (X := X) (M := M) (P := 1) (K := K) Nat.one_pos hXM (by rw [hMd, hDd]; exact hd)
  rw [hXd, hMd, hUd, hDd] at h
  exact h

/-- `step`'s loads: the bases of `x`, `m`, the accumulator and the temporary,
and `w`. -/
theorem stepBases_ok {L : Lay} {t : State} (hg : GoodL L t) :
    WP isa (.block R2Words.bases) t fun t' =>
      t'.gpr .rbx = off L.B (slot L.w aR2) ∧ t'.gpr .r10 = off L.B (slot L.w aN) ∧
      t'.gpr .r8 = off L.B (slot L.w aAcc) ∧ t'.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t'.gpr .rbp = off L.B (slot L.w aTmp) ∧ t'.mem = t.mem ∧ Keep [.rbx, .r10, .r8, .r12, .rbp] t t' := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot L.w 8 hi; have := hg.2; omega_arith)
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .r12, .rbp] (Q := fun t' =>
      t'.gpr .rbx = off L.B (slot L.w aR2) ∧ t'.gpr .r10 = off L.B (slot L.w aN) ∧
      t'.gpr .r8 = off L.B (slot L.w aAcc) ∧ t'.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t'.gpr .rbp = off L.B (slot L.w aTmp) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩
  unfold R2Words.bases
  xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide),
    hl (sArr aAcc) (by decide), hl sW (by decide), hl (sArr aTmp) (by decide), hg.1.hdr.harr aR2 (by decide),
    hg.1.hdr.harr aN (by decide), hg.1.hdr.harr aAcc (by decide), hg.1.hdr.hw, hg.1.hdr.harr aTmp (by decide)]

/-- `x := x 2^64 mod m`, for `x < m` in `aR2` and `m` in `aN`, `m`'s top word
`d` at least `2^63`, and `v = ⌊(2^128 - 1) / d⌋ - 2^64` the first word of the
temporary; it changes only the accumulator and `x`. -/
theorem step_ok {L : Lay} {t : State} (hg : GoodL L t) (hw : 3 ≤ L.w) (hw' : L.w < 2 ^ 30)
    (hd : 2 ^ 63 ≤ (word t.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat)
    (hv : (word t.mem L.B (slot L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word t.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem L.B (slot L.w aR2) L.w < wv t.mem L.B (slot L.w aN) L.w) :
    WP isa step t fun t' => GoodL L t' ∧
      wv t'.mem L.B (slot L.w aR2) L.w = wv t.mem L.B (slot L.w aR2) L.w * 2 ^ 64 % wv t.mem L.B (slot L.w aN) L.w ∧
      Arrays L.B L.w [aAcc, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain ⟨B, Z, w, minv⟩ := L
  dsimp only at hw hw' hd hv hx ⊢
  have hs : Scr t B Z := hg.1.scr
  have hZ : slot w 8 ≤ Z := hg.2
  have hn : B.toNat + Z ≤ 2 ^ 64 := hs.nowrap
  have hsx := slot_le (w := w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := w) (show aN < 8 by decide)
  have hst := slot_le (w := w) (show aAcc < 8 by decide)
  have sXT := slot_sep (w := w) (show aR2 ≠ aAcc by decide)
  have sMT := slot_sep (w := w) (show aN ≠ aAcc by decide)
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  rw [show step = .seq (.block R2Words.bases) (.seq (.block quot) (.seq (.block refine3) (.seq mulSub
    (.seq addBack copyBack)))) from rfl]
  refine WP.seq (WP.mono (stepBases_ok (L := ⟨B, Z, w, minv⟩) hg)
    fun t₁ ⟨h1bx, h110, h18, h112, h1bp, hm₁, k₁⟩ => ?_)
  dsimp only at h1bx h110 h18 h112 h1bp
  have hs₁ := hs.congr k₁.2.2
  -- The values.
  generalize hX : wv t.mem B (slot w aR2) w = X at hx
  generalize hM : wv t.mem B (slot w aN) w = M at hx
  have hu := top_le (by omega_arith) (hX ▸ hM ▸ hx)
  rw [← hm₁] at hu hd hv
  have e1 : slot w aR2 + 8 * w ≤ Z := by omega_arith
  have e2 : slot w aN + 8 * w ≤ Z := by omega_arith
  have e3 : slot w aTmp + 8 ≤ Z := by omega_arith
  have eT : slot w aAcc + 8 * (w + 1) ≤ Z := by omega_arith
  have sX : slot w aAcc + 8 * (w + 1) ≤ slot w aR2 ∨ slot w aR2 + 8 * w ≤ slot w aAcc := by omega_arith
  have sM : slot w aAcc + 8 * (w + 1) ≤ slot w aN ∨ slot w aN + 8 * w ≤ slot w aAcc := by omega_arith
  have hw31 : w < 2 ^ 31 := by omega_arith
  have hq := quot_ok hs₁ h1bx h110 h112 h1bp (by omega_arith) e1 e2 e3 hu hd hv
  refine WP.seq (WP.mono hq fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  rw [hm₁] at h2cx
  have hs₂ := hs₁.congr k₂.2.2
  have t₂bx : t₂.gpr .rbx = off B (slot w aR2) := (k₂.gpr (by decide)).trans h1bx
  have t₂10 : t₂.gpr .r10 = off B (slot w aN) := (k₂.gpr (by decide)).trans h110
  have t₂8 : t₂.gpr .r8 = off B (slot w aAcc) := (k₂.gpr (by decide)).trans h18
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h112
  rw [hm₁] at hd
  -- The values.
  have hX' : X = (word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) +
      (word t.mem B (slot w aR2 + 8 * (w - 3))).toNat * 2 ^ (64 * (w - 3)) + wv t.mem B (slot w aR2) (w - 3) := by
    rw [← hX, show w = (w - 3) + 1 + 1 + 1 by omega_arith, wv_succ, wv_succ, wv_succ,
      show w - 3 + 1 + 1 + 1 - 1 = w - 3 + 1 + 1 by omega_arith, show w - 3 + 1 + 1 + 1 - 2 = w - 3 + 1 by omega_arith,
      show w - 3 + 1 + 1 + 1 - 3 = w - 3 by omega_arith]
    grind
  have hM' : M = (word t.mem B (slot w aN + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (slot w aN + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv t.mem B (slot w aN) (w - 2) := by
    rw [← hM, show w = (w - 2) + 1 + 1 by omega_arith, wv_succ, wv_succ, show w - 2 + 1 + 1 - 1 = w - 2 + 1 by omega_arith,
      show w - 2 + 1 + 1 - 2 = w - 2 by omega_arith]
    grind
  obtain ⟨hUD, hq1, hq2, hge, hle⟩ := norm3 hw hX' (wv_lt _ _ _ _) hM' (wv_lt _ _ _ _) (BitVec.isLt _) (BitVec.isLt _) hd hx
  have h2cx' := congrArg BitVec.toNat h2cx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))] at h2cx'
  have hD0 : 0 < (word t.mem B (slot w aN + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (slot w aN + 8 * (w - 2))).toNat := by
    omega_arith
  have hr := refine3_ok hs₂ t₂bx t₂10 t₂12 hw e1 e2 (by rw [hm₂, hm₁]) (by rw [hm₂, hm₁]) hD0 hUD
    (by rw [h2cx']; exact hq1) (by rw [h2cx']; exact hq2)
  refine WP.seq (WP.mono hr fun t₂' ⟨h2'cx, hm₂', k₂'⟩ => ?_)
  have hs₂' := hs₂.congr k₂'.2.2
  have t₂'bx : t₂'.gpr .rbx = off B (slot w aR2) := (k₂'.gpr (by decide)).trans t₂bx
  have t₂'10 : t₂'.gpr .r10 = off B (slot w aN) := (k₂'.gpr (by decide)).trans t₂10
  have t₂'8 : t₂'.gpr .r8 = off B (slot w aAcc) := (k₂'.gpr (by decide)).trans t₂8
  have t₂'12 : t₂'.gpr .r12 = BitVec.ofNat 64 w := (k₂'.gpr (by decide)).trans t₂12
  have hms := mulSub_ok hs₂' t₂'bx t₂'10 t₂'8 t₂'12 (by omega_arith) hw31 e1 e2 eT sX sM
  refine WP.seq (WP.mono hms fun t₃ ⟨b, hv₃, ho₃, k₃⟩ => ?_)
  rw [h2'cx] at hv₃
  have hs₃ := hs₂'.congr k₃.2.2
  have t₃10 : t₃.gpr .r10 = off B (slot w aN) := (k₃.gpr (by decide)).trans t₂'10
  have t₃8 : t₃.gpr .r8 = off B (slot w aAcc) := (k₃.gpr (by decide)).trans t₂'8
  have t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans t₂'12
  have hab₃ := addBack_ok hs₃ t₃10 t₃8 t₃12 (by omega_arith) hw31 e2 eT sM
  refine WP.seq (WP.mono hab₃ fun t₅ ⟨c1, hv₅, ho₅, k₅⟩ => ?_)
  have hs₅ := hs₃.congr k₅.2.2
  have t₅bx : t₅.gpr .rbx = off B (slot w aR2) :=
    (k₅.gpr (by decide)).trans ((k₃.gpr (by decide)).trans t₂'bx)
  have t₅8 : t₅.gpr .r8 = off B (slot w aAcc) := (k₅.gpr (by decide)).trans t₃8
  have t₅12 : t₅.gpr .r12 = BitVec.ofNat 64 w := (k₅.gpr (by decide)).trans t₃12
  unfold copyBack
  refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t' => t'.gpr .rsi = off B (slot w aAcc) ∧ t'.mem = t₅.mem)
    (by xrun [t₅8]) rfl) fun t₆ ⟨⟨h6si, hm₆⟩, k₆⟩ => ?_)
  have hsepw : ∀ j < w, ∀ b < 8, ofs B (off B (slot w aAcc + 8 * j) + BitVec.ofNat 64 b) < slot w aR2 ∨
      slot w aR2 + 8 * w ≤ ofs B (off B (slot w aAcc + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
    rw [ofs_off B (by omega_arith)]; omega_arith
  have hs₆ := hs₅.congr k₆.2.2
  have hrd : ∀ j < w, InRegions (t₆.rd ++ t₆.wr) (off B (slot w aAcc + 8 * j)) 8 := fun j hj => hs₆.ld (by omega_arith)
  have hwr : ∀ j < w, InRegions t₆.wr (off B (slot w aR2 + 8 * j)) 8 := fun j hj => hs₆.st (by omega_arith)
  have hcw := copyWords_ok (S := B) (D := B) h6si ((k₆.gpr (by decide)).trans t₅bx)
    ((k₆.gpr (by decide)).trans t₅12) (by omega_arith) hw31 (by omega_arith) hrd hwr hsepw
  refine WP.mono hcw fun t' ⟨hc, _, ho', k'⟩ => ?_
  -- Memory: `m` and `x` as on entry until the copy; the accumulator's changes.
  have hm₂₂ : t₂'.mem = t.mem := by rw [hm₂', hm₂, hm₁]
  have em3 : ∀ {d n}, d + 8 * n ≤ slot w aAcc ∨ slot w aAcc + 8 * (w + 2) ≤ d → d + 8 * n ≤ Z →
      wv t₃.mem B d n = wv t.mem B d n := fun h h' => by
    rw [ho₃.wv (by omega_arith) (by omega_arith), hm₂₂]
  rw [em3 (n := w) (d := slot w aN) (by omega_arith) (by omega_arith), hM] at hv₅
  rw [hm₂₂, hX, hM] at hv₃
  simp only [← top_half] at hv₅
  -- The step's value.
  have hW : 2 * M < 2 ^ (64 * (w + 1)) / 2 := by
    have := hM ▸ wv_lt t.mem B (slot w aN) w
    rw [show 64 * (w + 1) = 64 * w + 64 by omega_arith, Nat.pow_add]
    omega_arith
  have hT3 := wordStepQ1_val (by omega_arith) hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) hv₃ (wv_lt _ _ _ _)
    (Bool.toNat_lt c1) hv₅
  have hlow : wv t₅.mem B (slot w aAcc) w = wv t₅.mem B (slot w aAcc) (w + 1) := by
    have hlt : wv t₅.mem B (slot w aAcc) (w + 1) < 2 ^ (64 * w) := by
      rw [hT3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) (hM ▸ wv_lt _ _ _ _)
    rw [wv_succ] at hlt ⊢
    have : (word t₅.mem B (slot w aAcc + 8 * w)).toNat = 0 := by
      by_contra h
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤ (word t₅.mem B (slot w aAcc + 8 * w)).toNat by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero]
  have ha : Arrays B w [aAcc, aR2] t.mem t'.mem := by
    have e1 : slot w aAcc + 8 * (w + 1) ≤ slot w aAcc + 8 * (w + 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.le_succ _)) _
    have e2 : slot w aR2 + 8 * w ≤ slot w aR2 + 8 * (w + 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.le_add_right _ _)) _
    have a3 : Arrays B w [aAcc, aR2] t₂'.mem t₃.mem :=
      Arrays.of_outside (j := aAcc) (by simp) ho₃ (Nat.le_refl _) e1
    have a5 : Arrays B w [aAcc, aR2] t₃.mem t₅.mem :=
      Arrays.of_outside (j := aAcc) (by simp) ho₅ (Nat.le_refl _) e1
    have a' : Arrays B w [aAcc, aR2] t₆.mem t'.mem :=
      Arrays.of_outside (j := aR2) (by simp) ho' (Nat.le_refl _) e2
    rw [hm₆] at a'
    rw [← hm₂₂]
    exact (a3.trans a5).trans a'
  refine ⟨⟨⟨hs₅.congr (k'.2.2.trans k₆.2.2), ?_, ha.hdr hg.1.hdr⟩, hZ⟩, ?_, ha, ?_⟩
  · rw [k'.gpr (by decide), k₆.gpr (by decide), k₅.gpr (by decide), k₃.gpr (by decide), k₂'.gpr (by decide),
      k₂.gpr (by decide), k₁.gpr (by decide)]; exact hg.1.rdi
  · rw [hc, hm₆, hlow, hT3]
  · exact (((((k₁.trans k₂).trans k₂').trans k₃).trans k₅).trans (k₆.trans k')).mono (by decide)

end VG.Proof.Bignum.X86_64.R2w
