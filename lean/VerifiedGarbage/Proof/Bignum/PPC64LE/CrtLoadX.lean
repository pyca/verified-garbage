module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: `X`'s arrays

`loadOne_ok`: a buffer, its address and length from the header, into an
array of `X`. `loadX_ok`: `M = 2^(64 w) - 1`, `n`, `p`, `q`, the input and
`qInv` into arrays 0, 1, 4, 5, 6 and 7.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- Two programs then a third, regrouped. -/
theorem wp_reassoc2 {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', hx, hq⟩ := h
  cases hx with
  | seq h1 h2 =>
    cases h1 with
    | seq ha hb => exact ⟨_, _, .seq ha (.seq hb h2), hq⟩

theorem arr_val {m m' : Mem} {B : Addr} {w i j : Nat} (h : Outside B (slot w i) (8 * (w + 1)) m m')
    (hij : i ≠ j) (hj : j < 8) (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    Mont.val32 m' B (slot w j) (2 * w) = Mont.val32 m B (slot w j) (2 * w) := by
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv]
  exact h.wv (by have := slot_sep (w := w) hij; omega_arith) (by have := slot_le (w := w) hj; omega_arith)

theorem arr_word {m m' : Mem} {B : Addr} {w i j q : Nat} (h : Outside B (slot w i) (8 * (w + 1)) m m')
    (hij : i ≠ j) (hj : j < 8) (hq : q ≤ w) (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    word m' B (slot w j + 8 * q) = word m B (slot w j + 8 * q) :=
  h.word (by have := slot_sep (w := w) hij; omega_arith) (by have := slot_le (w := w) hj; omega_arith)

/-- The address and length of a buffer from the header (words `oA`, `oL`),
then the buffer into `X`'s array `j`. -/
theorem loadOne_ok {s : State} {BX A : Addr} {Z w L j oA oL : Nat} (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z)
    (hj : j < 8) (hw' : w < 2 ^ 31) (h23 : s.gpr .r23 = BX) (h10 : s.gpr .r10 = off BX (slot w 0))
    (h21 : s.gpr .r21 = off BX (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word s.mem BX oA = off A 0) (hLw : word s.mem BX oL = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLw' : L ≤ 8 * w) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off A i) 1)
    (hsep : ∀ i < L, ∀ x, ofs BX x < Z → off A i ≠ x) :
    WP isa (.seq (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) (loadArr j)) s fun t =>
      (Mont.val32 t.mem BX (slot w j) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem A L) ∧
        word t.mem BX (slot w j + 8 * w) = 0 ∧ Outside BX (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .r10 = off BX (slot w 0)) ∧
      Keep [.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] s t := by
  have hn := hs.nowrap
  have e8 : slot w 8 = 256 + 8 * (8 * (w + 2)) := rfl
  have hA' : s.mem.readW (off BX oA) 64 = off A 0 := hA
  have hL' : s.mem.readW (off BX oL) 64 = BitVec.ofNat 64 L := hLw
  refine WP.seq (WP.mono (WP.keep [.r12, .r6] (Q := fun t => t.gpr .r12 = off A 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 L ∧ t.mem = s.mem) (by
      prun [h23, exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oA < 2 ^ 15 by omega_arith, show oA % 4 = 0 by omega_arith⟩,
        exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oL < 2 ^ 15 by omega_arith, show oL % 4 = 0 by omega_arith⟩,
        hs.ld (show oA + 8 ≤ Z by omega_arith), hs.ld (show oL + 8 ≤ Z by omega_arith), hA', hL']) rfl)
    fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  refine WP.mono (loadArr_ok (hs.congr k1.wr) hj a12 a6 ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h21) ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11)
    hL hLw' hw' hZ (fun i hi => by rw [k1.rd, k1.wr]; exact hrd i hi) hsep)
    fun t ⟨⟨v, tp, o, t10⟩, k2⟩ => ⟨⟨by rw [v, m1], tp, by rw [← m1]; exact o, t10⟩, (k1.trans k2).mono⟩

/-- The registers `loadX` writes. -/
def loadXRegs : List Reg := [.r0, .r3, .r6, .r10, .r12, .r14, .r15, .r16, .r17]

/-- A frame within the arrays is one of all of them. -/
theorem out_arrs {m m' : Mem} {B : Addr} {w o n : Nat} (h : Outside B o n m m') (ho : 256 ≤ o)
    (hn : o + n ≤ slot w 8) : Outside B 256 (slot w 8 - 256) m m' :=
  h.mono ho (by omega_arith)

/-- `loadX`, in `X` (`w` words, at `BX`, its header holding the buffers'
addresses and lengths). -/
theorem loadX_ok {s : State} {BX Na Pa Qa Ia QIa : Addr} {Z w k pL qL : Nat} (hs : Scr s BX Z)
    (hZ : slot w 8 ≤ Z) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31) (h23 : s.gpr .r23 = BX)
    (h10 : s.gpr .r10 = off BX (slot w 0)) (h21 : s.gpr .r21 = off BX (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hNa : word s.mem BX oN = off Na 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hPa : word s.mem BX oP = off Pa 0) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hQa : word s.mem BX oQ = off Qa 0) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hIa : word s.mem BX oIn = off Ia 0) (hQIa : word s.mem BX oQInv = off QIa 0)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hp : 1 ≤ pL) (hpw : pL ≤ 8 * w) (hq : 1 ≤ qL) (hqw : qL ≤ 8 * w)
    (rN : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1) (sN : ∀ i < k, ∀ x, ofs BX x < Z → off Na i ≠ x)
    (rP : ∀ i < pL, InRegions (s.rd ++ s.wr) (off Pa i) 1) (sP : ∀ i < pL, ∀ x, ofs BX x < Z → off Pa i ≠ x)
    (rQ : ∀ i < qL, InRegions (s.rd ++ s.wr) (off Qa i) 1) (sQ : ∀ i < qL, ∀ x, ofs BX x < Z → off Qa i ≠ x)
    (rI : ∀ i < k, InRegions (s.rd ++ s.wr) (off Ia i) 1) (sI : ∀ i < k, ∀ x, ofs BX x < Z → off Ia i ≠ x)
    (rQI : ∀ i < pL, InRegions (s.rd ++ s.wr) (off QIa i) 1)
    (sQI : ∀ i < pL, ∀ x, ofs BX x < Z → off QIa i ≠ x) :
    WP isa loadX s fun t =>
      (Mont.val32 t.mem BX (slot w 0) (2 * w) = 2 ^ (64 * w) - 1 ∧ word t.mem BX (slot w 0) = BitVec.allOnes 64 ∧
        Mont.val32 t.mem BX (slot w 1) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k) ∧
        Mont.val32 t.mem BX (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) ∧
        Mont.val32 t.mem BX (slot w 5) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) ∧
        Mont.val32 t.mem BX (slot w 6) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k) ∧
        Mont.val32 t.mem BX (slot w 7) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL) ∧
        word t.mem BX (slot w 1 + 8 * w) = 0 ∧ word t.mem BX (slot w 6 + 8 * w) = 0 ∧
        word t.mem BX (slot w 7 + 8 * w) = 0 ∧ Outside BX 256 (slot w 8 - 256) s.mem t.mem ∧
        t.gpr .r10 = off BX (slot w 0)) ∧ Keep loadXRegs s t := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hn8 : BX.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  have hd : ∀ {m m' : Mem}, Outside BX 256 (slot w 8 - 256) m m' → ∀ d, d + 8 ≤ 256 → word m' BX d = word m BX d :=
    fun h d hd => h.word (Or.inl hd) (by omega_arith)
  have hbz : ∀ {m m' : Mem} {A : Addr} {L : Nat}, Outside BX 256 (slot w 8 - 256) m m' →
      (∀ i < L, ∀ x, ofs BX x < Z → off A i ≠ x) → Spec.Rsa.bytesAt m' A L = Spec.Rsa.bytesAt m A L :=
    fun h hs' => bytesAt_out h (by omega_arith) hs'
  unfold loadX
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = off BX (slot w 0) ∧ t.mem = s.mem)
    (by prun [h10, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (onesWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw1 hw'
    (by omega_arith)) fun s₂ ⟨⟨h1s, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  rw [m1] at o2
  have O2 := out_arrs (w := w) o2 (by omega_arith) (by omega_arith)
  -- `n` into array 1.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 1) (A := Na) (L := k) (hs.congr k12.wr) hZ (by decide)
    hw' ((k12.gpr _ (by decide)).trans h23) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h21) ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O2 _ (by decide)]; exact hNa) (by rw [hd O2 _ (by decide)]; exact hK) hk hkw
    (fun i hi => by rw [k12.rd, k12.wr]; exact rN i hi) sN) fun s₃ ⟨⟨v1, t1, o3, b10⟩, k3⟩ => ?_))
  have k13 := k12.trans k3
  have O3 := out_arrs (w := w) o3 (by omega_arith) (by have := slot_le (w := w) (j := 1) (by decide); omega_arith)
  have O23 := O2.trans O3
  -- `p` into array 4.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 4) (A := Pa) (L := pL) (hs.congr k13.wr) hZ (by decide)
    hw' ((k13.gpr _ (by decide)).trans h23) b10
    ((k13.gpr _ (by decide)).trans h21) ((k13.gpr _ (by decide)).trans h29) ((k13.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O23 _ (by decide)]; exact hPa) (by rw [hd O23 _ (by decide)]; exact hPL)
    hp hpw (fun i hi => by rw [k13.rd, k13.wr]; exact rP i hi) sP) fun s₄ ⟨⟨v4, t4, o4, c10⟩, k4⟩ => ?_))
  have k14 := k13.trans k4
  have O4 := out_arrs (w := w) o4 (by omega_arith) (by have := slot_le (w := w) (j := 4) (by decide); omega_arith)
  have O24 := O23.trans O4
  -- `q` into array 5.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 5) (A := Qa) (L := qL) (hs.congr k14.wr) hZ (by decide)
    hw' ((k14.gpr _ (by decide)).trans h23) c10
    ((k14.gpr _ (by decide)).trans h21) ((k14.gpr _ (by decide)).trans h29) ((k14.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O24 _ (by decide)]; exact hQa) (by rw [hd O24 _ (by decide)]; exact hQL)
    hq hqw (fun i hi => by rw [k14.rd, k14.wr]; exact rQ i hi) sQ) fun s₅ ⟨⟨v5, t5, o5, d10⟩, k5⟩ => ?_))
  have k15 := k14.trans k5
  have O5 := out_arrs (w := w) o5 (by omega_arith) (by have := slot_le (w := w) (j := 5) (by decide); omega_arith)
  have O25 := O24.trans O5
  -- The input into array 6.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 6) (A := Ia) (L := k) (hs.congr k15.wr) hZ (by decide)
    hw' ((k15.gpr _ (by decide)).trans h23) d10
    ((k15.gpr _ (by decide)).trans h21) ((k15.gpr _ (by decide)).trans h29) ((k15.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O25 _ (by decide)]; exact hIa) (by rw [hd O25 _ (by decide)]; exact hK)
    hk hkw (fun i hi => by rw [k15.rd, k15.wr]; exact rI i hi) sI) fun s₆ ⟨⟨v6, t6, o6, e10⟩, k6⟩ => ?_))
  have k16 := k15.trans k6
  have O6 := out_arrs (w := w) o6 (by omega_arith) (by have := slot_le (w := w) (j := 6) (by decide); omega_arith)
  have O26 := O25.trans O6
  -- `qInv` into array 7.
  refine WP.mono (loadOne_ok (j := 7) (A := QIa) (L := pL) (hs.congr k16.wr) hZ (by decide)
    hw' ((k16.gpr _ (by decide)).trans h23) e10
    ((k16.gpr _ (by decide)).trans h21) ((k16.gpr _ (by decide)).trans h29) ((k16.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O26 _ (by decide)]; exact hQIa) (by rw [hd O26 _ (by decide)]; exact hPL)
    hp hpw (fun i hi => by rw [k16.rd, k16.wr]; exact rQI i hi) sQI) fun t ⟨⟨v7, t7, o7, t10⟩, k7⟩ => ?_
  have O7 := out_arrs (w := w) o7 (by omega_arith) (by have := slot_le (w := w) (j := 7) (by decide); omega_arith)
  have hones : Mont.val32 s₂.mem BX (slot w 0) (2 * w) = 2 ^ (64 * w) - 1 := by
    rw [Pre.val32_eq_wv]; exact wv_ones h1s
  have w0 : ∀ {m m' : Mem} {i : Nat}, Outside BX (slot w i) (8 * (w + 1)) m m' → i ≠ 0 →
      word m' BX (slot w 0) = word m BX (slot w 0) := fun h hi => by
    have := arr_word (q := 0) h hi (by decide) (by omega_arith) hn8
    simpa only [Nat.mul_zero, Nat.add_zero] using this
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, t7, O26.trans O7, t10⟩, (k16.trans k7).mono⟩
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8,
      arr_val o5 (by decide) (by decide) hn8, arr_val o4 (by decide) (by decide) hn8,
      arr_val o3 (by decide) (by decide) hn8, hones]
  · have h0 := h1s 0 hw1
    rw [Nat.mul_zero, Nat.add_zero] at h0
    rw [w0 o7 (by decide), w0 o6 (by decide), w0 o5 (by decide), w0 o4 (by decide), w0 o3 (by decide), h0]
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8,
      arr_val o5 (by decide) (by decide) hn8, arr_val o4 (by decide) (by decide) hn8, v1, hbz O2 sN]
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8,
      arr_val o5 (by decide) (by decide) hn8, v4, hbz O23 sP]
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8, v5, hbz O24 sQ]
  · rw [arr_val o7 (by decide) (by decide) hn8, v6, hbz O25 sI]
  · rw [v7, hbz O26 sQI]
  · rw [arr_word o7 (by decide) (by decide) (Nat.le_refl _) hn8, arr_word o6 (by decide) (by decide) (Nat.le_refl _) hn8,
      arr_word o5 (by decide) (by decide) (Nat.le_refl _) hn8, arr_word o4 (by decide) (by decide) (Nat.le_refl _) hn8, t1]
  · rw [arr_word o7 (by decide) (by decide) (Nat.le_refl _) hn8, t6]

end VG.Proof.Bignum.PPC64LE.Crt
