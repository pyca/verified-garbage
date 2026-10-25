module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinTable
public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinSel
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound

/-!
# Four-bit windows on PPC64LE: the power

`window_ok`: four squares of `a` (array 6) and a multiplication by `T_d`
for the digit `d` at the top of `r24`, so that `a ≡ x^c R` becomes `a ≡
x^(16 c + d) R`; `byteWin_ok`: the two windows of a byte; `powWin_ok`:
`x^d mod m` into array 4, stated as `ModExpPow.powSecret_ok` but for a
working space of 24 arrays.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Win

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.ModExp
open VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

/-- Every array but 2, 3, 5 and 6 keeps its number. -/
def Fix (B : Addr) (w : Nat) (m m' : Mem) : Prop :=
  ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 5 → j ≠ 6 → A m' B w j = A m B w j

theorem Fix.trans {B : Addr} {w : Nat} {m₁ m₂ m₃ : Mem} (a : Fix B w m₁ m₂) (b : Fix B w m₂ m₃) : Fix B w m₁ m₃ :=
  fun j hj h2 h3 h5 h6 => (b j hj h2 h3 h5 h6).trans (a j hj h2 h3 h5 h6)

/-- The registers a window writes. -/
def winRegs : List Reg := Pub.montRegs ++ selectRegs ++ [.r18, .r24]

/-- A square of `a` in the context. -/
theorem sq_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) {X c : Nat} :
    WP isa (PublicChecked.sqrOp 6 6) s fun t =>
      (WCtx t B Z w N ∧ Outs B (win w) s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        (A s.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N →
          A t.mem B w 6 % N = X ^ (c + c) * 2 ^ (64 * w) % N)) ∧ Keep Pub.montRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  exact WP.mono (h.sqr (o := 6) (a := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ha) fun t ⟨⟨ct, lt, e, v, o⟩, k⟩ =>
    ⟨⟨ct, o, fun j hj h2 h3 _ h6 => v j hj h2 h3 h6, lt, fun hA => mont_pow hR hA hA e⟩, k⟩

theorem top_nibble (x : BitVec 64) : x >>> 60 = BitVec.ofNat 64 (x.toNat / 2 ^ 60) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- `window`. -/
theorem window_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) (htab : ∀ i < 16, A s.mem B w (8 + i) < N) {X c : Nat} :
    WP isa window s fun t =>
      (WCtx t B Z w N ∧ Outs B (win w) s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        t.gpr .r24 = s.gpr .r24 <<< 4 ∧
        (A s.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N →
          (∀ i < 16, A s.mem B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N) →
          A t.mem B w 6 % N = X ^ (16 * c + (s.gpr .r24).toNat / 2 ^ 60) * 2 ^ (64 * w) % N)) ∧
        Keep winRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold window
  refine WP.seq (WP.mono (sq_ok h hodd ha (X := X) (c := c)) fun s₁ ⟨⟨c1, o1, f1, l1, e1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c1 hodd l1 (X := X) (c := c + c)) fun s₂ ⟨⟨c2, o2, f2, l2, e2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c2 hodd l2 (X := X) (c := c + c + (c + c)))
    fun s₃ ⟨⟨c3, o3, f3, l3, e3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c3 hodd l3 (X := X) (c := c + c + (c + c) + (c + c + (c + c))))
    fun s₄ ⟨⟨c4, o4, f4, l4, e4⟩, k4⟩ => ?_)
  have k14 := ((k1.trans k2).trans k3).trans k4
  have f14 := (f1.trans f2).trans (f3.trans f4)
  have hd := (s.gpr .r24).isLt
  have hd16 : (s.gpr .r24).toNat / 2 ^ 60 < 16 := by omega
  refine WP.seq (WP.mono (WP.keep [.r18] (Q := fun t =>
      t.gpr .r18 = BitVec.ofNat 64 ((s.gpr .r24).toNat / 2 ^ 60) ∧ t.mem = s₄.mem)
    (by prun [top_nibble, k14.gpr .r24 (by decide)]) (by decide)) fun s₅ ⟨⟨a18, m5⟩, k5⟩ => ?_)
  have c5 := c4.regs k5 (by decide) m5
  refine WP.seq (WP.mono (select_ok c5 a18 hd16) fun s₆ ⟨⟨a6, v6, c6, o6⟩, k6⟩ => ?_)
  have tab6 : ∀ i < 16, A s₆.mem B w (8 + i) = A s.mem B w (8 + i) := fun i hi => by
    rw [v6 _ (by omega) (by omega) (by omega), m5, f14 _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  have A6 : A s₆.mem B w 6 = A s₄.mem B w 6 := by rw [v6 6 (by decide) (by decide) (by decide), m5]
  rw [m5, f14 _ (by omega) (by omega) (by omega) (by omega) (by omega)] at a6
  refine WP.seq (WP.mono (c6.mont (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [a6]; exact htab _ hd16))
    fun s₇ ⟨⟨c7, l7, e7, v7, o7⟩, k7⟩ => ?_)
  refine WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = s₇.gpr .r24 <<< 4 ∧ t.mem = s₇.mem)
    (by prun) (by decide)) fun t ⟨⟨a24, mt⟩, kt⟩ => ⟨⟨c7.regs kt (by decide) mt, ?_, ?_, by rw [mt]; exact l7, ?_, ?_⟩,
      ?_⟩
  · rw [mt]
    exact ((((o1.trans o2).trans (o3.trans o4)).trans (by rw [← m5]; exact o6)).trans o7)
  · intro j hj h2 h3 h5 h6
    rw [mt, v7 j hj h2 h3 h6, v6 j hj h3 h5, m5]
    exact f14 j hj h2 h3 h5 h6
  · rw [a24, k7.gpr .r24 (by decide), k6.gpr .r24 (by decide), k5.gpr .r24 (by decide), k14.gpr .r24 (by decide)]
  · intro hA hT
    rw [mt, A6] at *
    rw [A6] at e7
    have := mont_pow hR (e4 (e3 (e2 (e1 hA)))) (by rw [a6]; exact hT _ hd16) e7
    rw [this, show c + c + (c + c) + (c + c + (c + c)) + (c + c + (c + c) + (c + c + (c + c))) = 16 * c by omega]
  · exact ((((k14.trans k5).trans k6).trans k7).trans kt).mono

/-! ## The exponent -/

/-- The registers `powWin` writes. -/
def powWRegs : List Reg := tabRegs ++ winRegs ++ [.r30, .r31]

/-- After the table (`t₀`), with `c` of the exponent scanned: what the
windows keep. -/
structure Run (s₀ t₀ u : State) (B : Addr) (Z w N X RR c : Nat) : Prop where
  ctx : WCtx u B Z w N
  out : Outs B (win w) s₀.mem u.mem
  fix : Fix B w t₀.mem u.mem
  lt : A u.mem B w 6 < N
  pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N
  keep : Keep powWRegs s₀ u

theorem lbz_ok {u : State} {D : Addr} {i : Nat} (h30 : u.gpr .r30 = off D i)
    (hrd : InRegions (u.rd ++ u.wr) (off D i) 1) :
    WP isa (.block [.lbz .r24 .r30 0, .lsl .r24 .r24 56, .addi .r30 .r30 1]) u fun t =>
      (t.gpr .r24 = BitVec.ofNat 64 (u.mem (off D i)).toNat <<< 56 ∧ t.gpr .r30 = off D (i + 1) ∧
        t.mem = u.mem) ∧ Keep [.r24, .r30] u t := by
  refine WP.keep _ ?_ (by decide)
  prun [h30, exec_lbz' (show Reg.r30 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd, read_byte64]

theorem nib_hi {b : Nat} (hb : b < 256) : (BitVec.ofNat 64 b <<< 56).toNat / 2 ^ 60 = b / 16 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

theorem nib_lo (b : Nat) : (BitVec.ofNat 64 b <<< 56 <<< 4).toNat / 2 ^ 60 = b % 16 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

/-- `byteWin`: the two windows of the byte `b` at `r30`, `c := 256 c + b`. -/
theorem byteWin_ok {s₀ t₀ u : State} {B D : Addr} {Z w N X RR c i : Nat} (hodd : N % 2 = 1)
    (htab : TabUpTo t₀.mem B w N X RR 16) (h : Run s₀ t₀ u B Z w N X RR c) (h30 : u.gpr .r30 = off D i)
    (hrd : InRegions (u.rd ++ u.wr) (off D i) 1) :
    WP isa byteWin u fun t =>
      Run s₀ t₀ t B Z w N X RR (256 * c + (u.mem (off D i)).toNat) ∧ t.gpr .r30 = off D (i + 1) ∧
        t.gpr .r31 = u.gpr .r31 := by
  generalize hb : (u.mem (off D i)).toNat = b
  have hb256 : b < 256 := by rw [← hb]; exact (u.mem (off D i)).isLt
  have tab : ∀ {m : Mem}, Fix B w t₀.mem m → ∀ i < 16, A m B w (8 + i) < N ∧
      (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A m B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N) :=
    fun hf i hi => by rw [hf (8 + i) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact htab i hi
  unfold byteWin
  refine WP.seq (WP.mono (lbz_ok h30 hrd) fun u₁ ⟨⟨a24, a30, m1⟩, k1⟩ => ?_)
  rw [hb] at a24
  have c1 := h.ctx.regs k1 (by decide) m1
  have f1 : Fix B w t₀.mem u₁.mem := by rw [m1]; exact h.fix
  refine WP.seq (WP.mono (window_ok c1 hodd (by rw [m1]; exact h.lt) (fun i hi => (tab f1 i hi).1)
    (X := X) (c := c)) fun u₂ ⟨⟨c2, o2, f2, l2, a24', e2⟩, k2⟩ => ?_)
  refine WP.mono (window_ok c2 hodd l2 (fun i hi => (tab (f1.trans f2) i hi).1) (X := X) (c := 16 * c + b / 16))
    fun t ⟨⟨c3, o3, f3, l3, _, e3⟩, k3⟩ => ⟨⟨c3, ?_, f1.trans (f2.trans f3), l3, fun hE => ?_, ?_⟩, ?_, ?_⟩
  · rw [m1] at o2; exact (h.out.trans o2).trans o3
  · have p1 := e2 (by rw [m1]; exact h.pw hE) (fun i hi => (tab f1 i hi).2 hE)
    rw [a24, nib_hi hb256] at p1
    have p2 := e3 p1 (fun i hi => (tab (f1.trans f2) i hi).2 hE)
    rw [a24', a24, nib_lo b] at p2
    rw [p2, show 16 * (16 * c + b / 16) + b % 16 = 256 * c + b by omega]
  · refine (h.keep.trans (k1.trans (k2.trans k3))).mono fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with h | h | h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> decide
    · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
    · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
  · rw [k3.gpr .r30 (by decide), k2.gpr .r30 (by decide), a30]
  · rw [k3.gpr .r31 (by decide), k2.gpr .r31 (by decide), k1.gpr .r31 (by decide)]

/-- `powWin`: `x^d mod m` into array 4, for `x` in array 4, `m` (odd, at least
2) in array 0, something below `m` in array 1 (if `R² mod m`, the result is
right) and the `L ≥ 1` bytes of `d` at `D` (`r30`, `r31`), apart from the
working space of 24 arrays, which is all it writes. -/
theorem powWin_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1)
    (hRRlt : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w))
    (h30 : s.gpr .r30 = off D 0) (h31 : s.gpr .r31 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa powWin s fun t =>
      ((val32 s.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) →
          val32 t.mem B (slot w 4) (2 * w) =
            val32 s.mem B (slot w 4) (2 * w) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) %
              val32 s.mem B (slot w 0) (2 * w)) ∧
        Outs B (win w) s.mem t.mem) ∧ Keep powWRegs s t := by
  have h0 : WCtx s B Z w (A s.mem B w 0) := ⟨hs, hw2, hw', hZ, h10, h29, h11, h12, hinv, rfl⟩
  have hn := h0.nw
  generalize hNd : val32 s.mem B (slot w 0) (2 * w) = N at hN hodd hRRlt ⊢
  replace h0 : WCtx s B Z w N := hNd ▸ h0
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hXd : val32 s.mem B (slot w 4) (2 * w) = X
  generalize hRRd : val32 s.mem B (slot w 1) (2 * w) = RR at hRRlt ⊢
  unfold powWin
  refine WP.seq (WP.mono (table_ok h0 hN hodd (by rw [show A s.mem B w 1 = RR from hRRd]; exact hRRlt)) fun t₀ ⟨⟨c0, o0, _, _, t7, a6, htab⟩, k0⟩ => ?_)
  rw [show A s.mem B w 4 = X from hXd, show A s.mem B w 1 = RR from hRRd] at htab
  have r0 : Run s t₀ t₀ B Z w N X RR 0 := ⟨c0, o0, fun _ _ _ _ _ _ => rfl, by rw [a6]; exact (htab 0 (by decide)).1,
    fun hE => by rw [a6]; exact (htab 0 (by decide)).2 hE, k0.mono⟩
  -- The bytes.
  let Inv : Nat → State → Prop := fun i u =>
    Run s t₀ u B Z w N X RR (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D i)) ∧ u.gpr .r30 = off D i
  refine WP.seq (WP.mono (wp_countdown (cnt := .r31) (N := L) (by omega) (by omega) Inv
    (fun i hi u ⟨hu, u30⟩ _ => ?_) ⟨by simpa [Spec.Rsa.bytesAt, Spec.Rsa.os2ip] using r0,
      by rw [k0.gpr .r30 (by decide), h30]⟩
    (by rw [k0.gpr .r31 (by decide), h31])) fun u ⟨hu, _⟩ => ?_)
  · have hb : u.mem (off D i) = s.mem (off D i) := by
      refine hu.out _ fun r hr => ?_
      rw [win, List.mem_singleton] at hr
      subst hr
      have := slot_lt (w := w) (show 1 < 24 by decide)
      have := hZ
      right
      by_contra hc
      exact hsep i hi (off D i) (by
        have e24 : slot w 24 = slot w 1 + 23 * (8 * (w + 2)) := by unfold slot; omega
        simp only [Mont.ofs, ofs] at hc ⊢; omega) rfl
    refine WP.seq (WP.mono (byteWin_ok hodd htab hu u30 (by rw [hu.keep.rd, hu.keep.wr]; exact hrd i hi))
      fun u₁ ⟨hu₁, a30, a31⟩ => ?_)
    refine WP.mono (subi_ok u₁ .r31 (by decide)) fun u₂ e => ?_
    subst e
    refine ⟨⟨⟨hu₁.ctx.regs (Keep.write _ _ _) (by decide) (by rw [mem_write]), by rw [mem_write]; exact hu₁.out,
        by rw [mem_write]; exact hu₁.fix, by rw [mem_write]; exact hu₁.lt, fun hE => ?_,
        (hu₁.keep.trans (Keep.write _ _ _)).mono⟩, by gsimp; exact a30⟩, by gsimp; rw [a31]⟩
    rw [mem_write, hu₁.pw hE, hb, VG.Proof.Bignum.PPC64LE.Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]
  -- Out of Montgomery form.
  have t7' : A u.mem B w 7 = 1 := by rw [hu.fix 7 (by decide) (by decide) (by decide) (by decide) (by decide), t7]
  refine WP.mono (hu.ctx.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t7']; omega)) fun t ⟨⟨_, lt, e, _, o⟩, k⟩ =>
    ⟨⟨fun hE => ?_, hu.out.trans o⟩, (hu.keep.trans k).mono⟩
  rw [t7', Nat.mul_one] at e
  refine (Nat.mod_eq_of_lt lt).symm.trans ?_
  exact VG.Proof.Bignum.mont_cancel hR (by rw [e, hu.pw hE])

end VG.Proof.Bignum.PPC64LE.Win
