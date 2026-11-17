module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtChecks
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.PPC64LE.CrtLoadX`, which this module and modules that import it used -/

section

/-! ### `Bignum.PPC64LE.CrtLoad`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: loading

`onesWords_ok`: `w` words of all ones (`M = 2^(64 w) - 1`). `loadArr_ok`: a
buffer's bytes, most significant first, into array `j`, its word `w` zeroed.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `w` words of all ones are `2^(64 w) - 1`. -/
theorem wv_ones {m : Mem} {p : Addr} {d : Nat} : ∀ {n : Nat},
    (∀ i < n, word m p (d + 8 * i) = BitVec.allOnes 64) → wv m p d n = 2 ^ (64 * n) - 1
  | 0, _ => rfl
  | n + 1, h => by
    rw [wv, wv_ones fun i hi => h i (by omega_arith), h n (by omega_arith), BitVec.toNat_allOnes, pow64_succ]
    have := Nat.one_le_two_pow (n := 64 * n)
    rw [Nat.mul_sub, Nat.mul_one]
    have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
    omega_arith

/-- `onesWords`, `r14` at offset `d` of `B`: the `w` words there := all ones. -/
theorem onesWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B d) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : d + 8 * w ≤ Z) :
    WP isa onesWords s fun s' =>
      ((∀ i < w, word s'.mem B (d + 8 * i) = BitVec.allOnes 64) ∧ Outside B d (8 * w) s.mem s'.mem) ∧
        Keep [.r0, .r3, .r14, .r17] s s' := by
  have hnw := hs.nowrap
  unfold onesWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1, .li .r0 0, .li .r3 1, .sub .r0 .r0 .r3]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.gpr .r0 = BitVec.allOnes 64 ∧ s₁.gpr .r14 = off B d ∧
        s₁.mem = s.mem) ∧ Keep [.r0, .r3, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11, h14]
    refine ⟨?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  refine WP.mono hpre fun s₁ ⟨⟨i17, i0, i14, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (d + 8 * i) ∧ t.gpr .r0 = BitVec.allOnes 64 ∧ Outside B d (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (d + 8 * k) = BitVec.allOnes 64) ∧ Keep [.r0, .r3, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r0 .r14 0, .addi .r14 .r14 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₁.mono⟩ i17) fun t ⟨_, _, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  have hst : WP isa (.block [.store .d .r0 .r14 0, .addi .r14 .r14 8, .subi .r17 .r17 1]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off B (d + 8 * i)) (BitVec.allOnes 64) } : State).write
        .r14 (off B (d + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
    prun [j14, j0, (hs.congr jk.wr).st (show d + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := d + 8 * i) (BitVec.allOnes 64) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · exact word_writeW_self _ _ _ _
  · exact jk.trans' ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono)

/-- `loadArr j`: the `k` bytes at `X` (`r12`, `r6`), most significant first,
into array `j`, and its word `w` := 0; `r10` back to array 0 (`r21`). -/
theorem loadArr_ok {s : State} {B X : Addr} {Z w k j : Nat} (hs : Scr s B Z) (hj : j < 8)
    (h12 : s.gpr .r12 = off X 0) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off X i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off X i ≠ x) :
    WP isa (loadArr j) s fun t =>
      (Mont.val32 t.mem B (slot w j) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X k) ∧
        word t.mem B (slot w j + 8 * w) = 0 ∧ Outside B (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r10, .r14, .r15, .r16, .r17] s t := by
  have hnw := hs.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_le hj) hZ
  have hh : hdrBytes = 256 := rfl
  have h1 : 256 ≤ slot w j := by unfold slot; omega_arith
  unfold loadArr
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) h10 h29 j)
    fun s₁ ⟨⟨a10, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (loadN_ok (dA := slot w j) (hs.congr k1.wr) a10
    ((k1.gpr _ (by decide)).trans h12) ((k1.gpr _ (by decide)).trans h6) ((k1.gpr _ (by decide)).trans h11)
    hk hkw hw' (by omega_arith) (by omega_arith) (by rw [k1.rd, k1.wr]; exact hrd)
    (by intro i hi x hx; exact hsep i hi x hx)) fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  rw [m1] at hv out₃
  have k13 := k1.trans k3
  refine WP.mono (WP.keep [.r14, .r0, .r10] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64) ∧ t.gpr .r10 = off B (slot w 0))
    ?_ (by decide)) fun t ⟨⟨tm, t10⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t10⟩, (k13.trans k4).mono⟩
  · have a10' : s₃.gpr .r10 = off B (slot w j) := (k3.gpr _ (by decide)).trans a10
    have e16 : off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w j + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith)]; congr 2
    prun [a10', (k13.gpr .r29 (by decide)).trans h29, (k13.gpr .r21 (by decide)).trans h21, off_add, e16,
      BitVec.add_zero, (hs.congr k13.wr).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith)]
    rfl
  · rw [tm, Mont.Outside.val32 (fun x hx => writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith) x hx)
      (by omega_arith) (by omega_arith)]
    exact hv
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (out₃.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith)).mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.PPC64LE.Crt

end

end

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
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  obtain e8 := e 8
  have hh : hdrBytes = 256 := rfl
  obtain hn8 : BX.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  obtain hd : ∀ {m m' : Mem}, Outside BX 256 (slot w 8 - 256) m m' → ∀ d, d + 8 ≤ 256 → word m' BX d = word m BX d :=
    fun h d hd => h.word (Or.inl hd) (by omega_arith)
  obtain hbz : ∀ {m m' : Mem} {A : Addr} {L : Nat}, Outside BX 256 (slot w 8 - 256) m m' →
      (∀ i < L, ∀ x, ofs BX x < Z → off A i ≠ x) → Spec.Rsa.bytesAt m' A L = Spec.Rsa.bytesAt m A L :=
    fun h hs' => bytesAt_out h (by omega_arith) hs'
  unfold loadX
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = off BX (slot w 0) ∧ t.mem = s.mem)
    (by prun [h10, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (onesWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw1 hw'
    (by omega_arith)) fun s₂ ⟨⟨h1s, o2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  rw [m1] at o2
  obtain O2 := out_arrs (w := w) o2 (by omega_arith) (by omega_arith)
  -- `n` into array 1.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 1) (A := Na) (L := k) (hs.congr k12.wr) hZ (by decide)
    hw' ((k12.gpr _ (by decide)).trans h23) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h21) ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O2 _ (by decide)]; exact hNa) (by rw [hd O2 _ (by decide)]; exact hK) hk hkw
    (fun i hi => by rw [k12.rd, k12.wr]; exact rN i hi) sN) fun s₃ ⟨⟨v1, t1, o3, b10⟩, k3⟩ => ?_))
  obtain k13 := k12.trans k3
  obtain O3 := out_arrs (w := w) o3 (by omega_arith) (by have := slot_le (w := w) (j := 1) (by decide); omega_arith)
  obtain O23 := O2.trans O3
  -- `p` into array 4.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 4) (A := Pa) (L := pL) (hs.congr k13.wr) hZ (by decide)
    hw' ((k13.gpr _ (by decide)).trans h23) b10
    ((k13.gpr _ (by decide)).trans h21) ((k13.gpr _ (by decide)).trans h29) ((k13.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O23 _ (by decide)]; exact hPa) (by rw [hd O23 _ (by decide)]; exact hPL)
    hp hpw (fun i hi => by rw [k13.rd, k13.wr]; exact rP i hi) sP) fun s₄ ⟨⟨v4, t4, o4, c10⟩, k4⟩ => ?_))
  obtain k14 := k13.trans k4
  obtain O4 := out_arrs (w := w) o4 (by omega_arith) (by have := slot_le (w := w) (j := 4) (by decide); omega_arith)
  obtain O24 := O23.trans O4
  -- `q` into array 5.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 5) (A := Qa) (L := qL) (hs.congr k14.wr) hZ (by decide)
    hw' ((k14.gpr _ (by decide)).trans h23) c10
    ((k14.gpr _ (by decide)).trans h21) ((k14.gpr _ (by decide)).trans h29) ((k14.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O24 _ (by decide)]; exact hQa) (by rw [hd O24 _ (by decide)]; exact hQL)
    hq hqw (fun i hi => by rw [k14.rd, k14.wr]; exact rQ i hi) sQ) fun s₅ ⟨⟨v5, t5, o5, d10⟩, k5⟩ => ?_))
  obtain k15 := k14.trans k5
  obtain O5 := out_arrs (w := w) o5 (by omega_arith) (by have := slot_le (w := w) (j := 5) (by decide); omega_arith)
  obtain O25 := O24.trans O5
  -- The input into array 6.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 6) (A := Ia) (L := k) (hs.congr k15.wr) hZ (by decide)
    hw' ((k15.gpr _ (by decide)).trans h23) d10
    ((k15.gpr _ (by decide)).trans h21) ((k15.gpr _ (by decide)).trans h29) ((k15.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O25 _ (by decide)]; exact hIa) (by rw [hd O25 _ (by decide)]; exact hK)
    hk hkw (fun i hi => by rw [k15.rd, k15.wr]; exact rI i hi) sI) fun s₆ ⟨⟨v6, t6, o6, e10⟩, k6⟩ => ?_))
  obtain k16 := k15.trans k6
  obtain O6 := out_arrs (w := w) o6 (by omega_arith) (by have := slot_le (w := w) (j := 6) (by decide); omega_arith)
  obtain O26 := O25.trans O6
  -- `qInv` into array 7.
  refine WP.mono (loadOne_ok (j := 7) (A := QIa) (L := pL) (hs.congr k16.wr) hZ (by decide)
    hw' ((k16.gpr _ (by decide)).trans h23) e10
    ((k16.gpr _ (by decide)).trans h21) ((k16.gpr _ (by decide)).trans h29) ((k16.gpr _ (by decide)).trans h11)
    (by decide) (by decide) (by rw [hd O26 _ (by decide)]; exact hQIa) (by rw [hd O26 _ (by decide)]; exact hPL)
    hp hpw (fun i hi => by rw [k16.rd, k16.wr]; exact rQI i hi) sQI) fun t ⟨⟨v7, t7, o7, t10⟩, k7⟩ => ?_
  obtain O7 := out_arrs (w := w) o7 (by omega_arith) (by have := slot_le (w := w) (j := 7) (by decide); omega_arith)
  obtain hones : Mont.val32 s₂.mem BX (slot w 0) (2 * w) = 2 ^ (64 * w) - 1 := by
    rw [Pre.val32_eq_wv]; exact wv_ones h1s
  obtain w0 : ∀ {m m' : Mem} {i : Nat}, Outside BX (slot w i) (8 * (w + 1)) m m' → i ≠ 0 →
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

end

end

/-!
# The RSA private-key operation on PPC64LE: `X` loaded and checked

`phaseAWith_ok`: `loadX` and `checksWith pq`, the mask of the checks in
`r26`, `p` and `q` (or 3) and `qInv` (or 0) in `X`'s arrays 4, 5 and 7, `M`
in array 0; `phaseA_ok`, for `checks` (`pq` is `checkPQ`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The mask of the checks. -/
def crtMask (N k C P Q QI : Nat) : Bool :=
  Spec.Rsa.modulusValid N k && decide (C < N) && decide (QI < P) && decide (P * Q = N)

theorem pq_lt {P Q pL qL k w : Nat} (hP : P < 256 ^ pL) (hQ : Q < 256 ^ qL) (hp : pL < k) (hq : qL < k)
    (hw : 16 * k ≤ 64 * w) : P * Q < 2 ^ (64 * w) - 1 := by
  have h1 : P * Q < 256 ^ pL * 256 ^ qL := Nat.mul_lt_mul_of_lt_of_lt hP hQ
  rw [← Nat.pow_add, VG.Proof.Bignum.pow256_eq] at h1
  have h2 : 2 ^ (8 * (pL + qL)) * 2 ≤ 2 ^ (64 * w) := by
    rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  omega_arith

/-- `checksWith pq`, in `X` as `checksAWith_ok` and `checksB_ok` need it. -/
theorem checksWith_ok {pq : Prog isa} {s : State} {BX Na : Addr} {Z w k : Nat} {nb : List Byte}
    (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h10 : s.gpr .r10 = off BX (slot w 0)) (h21 : s.gpr .r21 = off BX (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : word s.mem BX oN = off Na 0) (hNL : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1)
    (hb : ∀ i (h : i < k), s.mem (off Na i) = nb[i]'(by omega_arith))
    (hn1 : Mont.val32 s.mem BX (slot w 1) (2 * w) = Spec.Rsa.os2ip nb)
    (h6top : word s.mem BX (slot w 6 + 8 * w) = 0) (h7top : word s.mem BX (slot w 7 + 8 * w) = 0)
    (hPQ : PQOk pq BX Z w s) :
    WP isa (checksWith pq) s fun t =>
      (t.gpr .r26 = bmask (crtMask (Spec.Rsa.os2ip nb) k (Mont.val32 s.mem BX (slot w 6) (2 * w))
          (Mont.val32 s.mem BX (slot w 4) (2 * w)) (Mont.val32 s.mem BX (slot w 5) (2 * w))
          (Mont.val32 s.mem BX (slot w 7) (2 * w))) ∧
        Mont.val32 t.mem BX (slot w 4) (2 * w) = (if crtMask (Spec.Rsa.os2ip nb) k
          (Mont.val32 s.mem BX (slot w 6) (2 * w)) (Mont.val32 s.mem BX (slot w 4) (2 * w))
          (Mont.val32 s.mem BX (slot w 5) (2 * w)) (Mont.val32 s.mem BX (slot w 7) (2 * w))
          then Mont.val32 s.mem BX (slot w 4) (2 * w) else 3) ∧
        Mont.val32 t.mem BX (slot w 5) (2 * w) = (if crtMask (Spec.Rsa.os2ip nb) k
          (Mont.val32 s.mem BX (slot w 6) (2 * w)) (Mont.val32 s.mem BX (slot w 4) (2 * w))
          (Mont.val32 s.mem BX (slot w 5) (2 * w)) (Mont.val32 s.mem BX (slot w 7) (2 * w))
          then Mont.val32 s.mem BX (slot w 5) (2 * w) else 3) ∧
        Mont.val32 t.mem BX (slot w 7) (2 * w) = (if crtMask (Spec.Rsa.os2ip nb) k
          (Mont.val32 s.mem BX (slot w 6) (2 * w)) (Mont.val32 s.mem BX (slot w 4) (2 * w))
          (Mont.val32 s.mem BX (slot w 5) (2 * w)) (Mont.val32 s.mem BX (slot w 7) (2 * w))
          then Mont.val32 s.mem BX (slot w 7) (2 * w) else 0) ∧
        Outside BX (slot w 2) (6 * (8 * (w + 2))) s.mem t.mem ∧ t.gpr .r10 = off BX (slot w 0)) ∧
      Keep (checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg)) s t := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  unfold checksWith
  refine checksAWith_ok (c := .seq (orThree 4) (.seq (orThree 5) (.seq (.block (PublicChecked.base .r14 7)) maskWords)))
    hs hZ hw2 hw' h23 h10 h21 h29 h11 hN hNL hk hk' hlen hrd hb hn1 h6top h7top hPQ
    fun t₁ t26 o2 b10 k2 => ?_
  refine WP.mono (checksB_ok (hs.congr k2.wr) hZ hw2 hw' b10
    ((k2.gpr _ (by decide)).trans h29) ((k2.gpr _ (by decide)).trans h11) t26)
    fun t ⟨⟨u4, u5, u7, o3⟩, k3⟩ => ⟨⟨(k3.gpr _ (by decide)).trans t26, ?_, ?_, ?_, ?_,
      (k3.gpr _ (by decide)).trans b10⟩, (k2.trans k3).mono⟩
  · rw [u4, o2.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)]; rfl
  · rw [u5, o2.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)]; rfl
  · rw [u7, o2.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)]; rfl
  · intro x hx
    have hx' : Mont.ofs BX x < slot w 2 ∨ slot w 2 + 6 * (8 * (w + 2)) ≤ Mont.ofs BX x := hx
    rw [o3 x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith), o2 x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)]

/-- A program, then an empty block and a second. -/
theorem wp_seq_nil {a b : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a (.seq (.block []) b)) s Q) : WP isa (.seq a b) s Q := by
  obtain ⟨t, s', hx, hq⟩ := h
  cases hx with
  | seq h1 h2 =>
    cases h2 with
    | seq h3 h4 =>
      rw [Exec.block_iff] at h3
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      exact ⟨_, _, .seq h1 h4, hq⟩

/-- `loadX`, `pre` (which writes only `r5` and `r7`) and `checksWith pq`, `pq` a
check of `p q = n` from the state after `pre` (`hPQ`), from the header's buffers (`k` bytes of `n` and the
input, `pL` of `p` and `qInv`, `qL` of `q`, apart from the working space). -/
theorem phaseAWith_ok {pre : List Instr} {pq : Prog isa} {s : State} {BX Na Pa Qa Ia QIa : Addr} {Z k pL qL : Nat}
    (hs : Scr s BX Z) (hZ : slot (2 * ((k + 7) / 8)) 8 ≤ Z) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (h23 : s.gpr .r23 = BX)
    (h10 : s.gpr .r10 = off BX (slot (2 * ((k + 7) / 8)) 0)) (h21 : s.gpr .r21 = off BX (slot (2 * ((k + 7) / 8)) 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (2 * ((k + 7) / 8))))
    (hNa : word s.mem BX oN = off Na 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hPa : word s.mem BX oP = off Pa 0) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hQa : word s.mem BX oQ = off Qa 0) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hIa : word s.mem BX oIn = off Ia 0) (hQIa : word s.mem BX oQInv = off QIa 0)
    (hp : 1 ≤ pL) (hpk : pL < k) (hq : 1 ≤ qL) (hqk : qL < k)
    (rN : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1) (sN : ∀ i < k, ∀ x, ofs BX x < Z → off Na i ≠ x)
    (rP : ∀ i < pL, InRegions (s.rd ++ s.wr) (off Pa i) 1) (sP : ∀ i < pL, ∀ x, ofs BX x < Z → off Pa i ≠ x)
    (rQ : ∀ i < qL, InRegions (s.rd ++ s.wr) (off Qa i) 1) (sQ : ∀ i < qL, ∀ x, ofs BX x < Z → off Qa i ≠ x)
    (rI : ∀ i < k, InRegions (s.rd ++ s.wr) (off Ia i) 1) (sI : ∀ i < k, ∀ x, ofs BX x < Z → off Ia i ≠ x)
    (rQI : ∀ i < pL, InRegions (s.rd ++ s.wr) (off QIa i) 1)
    (sQI : ∀ i < pL, ∀ x, ofs BX x < Z → off QIa i ≠ x)
    (hPQ : ∀ s₁, Scr s₁ BX Z → s₁.gpr .r23 = BX → (∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d) →
      Mont.val32 s₁.mem BX (slot (2 * ((k + 7) / 8)) 0) (2 * (2 * ((k + 7) / 8))) = 2 ^ (64 * (2 * ((k + 7) / 8))) - 1 →
      word s₁.mem BX (slot (2 * ((k + 7) / 8)) 0) = BitVec.allOnes 64 →
      Mont.val32 s₁.mem BX (slot (2 * ((k + 7) / 8)) 4) (2 * (2 * ((k + 7) / 8))) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) →
      Mont.val32 s₁.mem BX (slot (2 * ((k + 7) / 8)) 5) (2 * (2 * ((k + 7) / 8))) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) →
      word s₁.mem BX (slot (2 * ((k + 7) / 8)) 1 + 8 * (2 * ((k + 7) / 8))) = 0 → word s₁.mem BX (slot (2 * ((k + 7) / 8)) 6 + 8 * (2 * ((k + 7) / 8))) = 0 →
      WP isa (.block pre) s₁ fun s₂ => (s₂.mem = s₁.mem ∧ PQOk pq BX Z (2 * ((k + 7) / 8)) s₂) ∧ Keep [.r5, .r7] s₁ s₂) :
    WP isa (.seq loadX (.seq (.block pre) (checksWith pq))) s fun t =>
      (t.gpr .r26 = bmask (crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 0) (2 * (2 * ((k + 7) / 8))) =
          2 ^ (64 * (2 * ((k + 7) / 8))) - 1 ∧
        word t.mem BX (slot (2 * ((k + 7) / 8)) 0) = BitVec.allOnes 64 ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 4) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) else 3) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 5) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) else 3) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 7) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL) else 0) ∧
        Outside BX 256 (slot (2 * ((k + 7) / 8)) 8 - 256) s.mem t.mem ∧
        t.gpr .r10 = off BX (slot (2 * ((k + 7) / 8)) 0)) ∧
      Keep (loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg)) s t := by
  have hn := hs.nowrap
  have e : ∀ j, slot (2 * ((k + 7) / 8)) j = hdrBytes + j * (8 * (2 * ((k + 7) / 8) + 2)) := fun _ => rfl
  have e0 := e 0; have e2 := e 2; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq (WP.mono (loadX_ok hs hZ (by omega_arith) (by omega_arith) h23 h10 h21 h29 h11 hNa hK hPa hPL hQa hQL hIa hQIa
    (by omega_arith) (by omega_arith) hp (by omega_arith) hq (by omega_arith) rN sN rP sP rQ sQ rI sI rQI sQI)
    fun s₁ ⟨⟨v0, w0, v1, v4, v5, v6, v7, t1, t6, t7, O1, a10⟩, k1⟩ => ?_)
  have hd : ∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d := fun d hd => O1.word (Or.inl hd) (by omega_arith)
  have hQb : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) < 256 ^ qL := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem Qa qL)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hPb : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) < 256 ^ pL := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem Pa pL)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hw : 16 * k ≤ 64 * (2 * ((k + 7) / 8)) := by omega_arith
  have h23' := (k1.gpr _ (by decide)).trans h23
  refine WP.seq (WP.mono (hPQ s₁ (hs.congr k1.wr) h23' hd v0 w0 v4 v5 t1 t6) fun s₂ ⟨⟨m2, hPQ₂⟩, kp⟩ => ?_)
  have k12 := k1.trans kp
  rw [← m2] at v0 w0 v1 v4 v5 v6 v7 t1 t6 t7 hd
  rw [← m2] at O1
  refine WP.mono (checksWith_ok (nb := Spec.Rsa.bytesAt s.mem Na k) (hs.congr k12.wr) hZ (by omega_arith)
    (by omega_arith) ((kp.gpr _ (by decide)).trans h23') ((kp.gpr _ (by decide)).trans a10)
    ((k12.gpr _ (by decide)).trans h21) ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by rw [hd _ (by decide)]; exact hNa) (by rw [hd _ (by decide)]; exact hK) hk hk'
    (VG.Proof.Bignum.bytesAt_length _ _ _) (fun i hi => by rw [k12.rd, k12.wr]; exact rN i hi)
    (fun i hi => by
      rw [O1 _ (Or.inr ?_)]
      · simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      · by_contra hc
        exact sN i hi _ (by omega_arith) rfl)
    v1 t6 t7 hPQ₂)
    fun t ⟨⟨t26, u4, u5, u7, o2, t10⟩, k2⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, t10⟩, (k12.trans k2).mono⟩
  · rw [t26, v6, v4, v5, v7]
  · rw [Pre.val32_eq_wv, o2.wv (Or.inl (by omega_arith)) (by omega_arith), ← Pre.val32_eq_wv, v0]
  · rw [o2.word (Or.inl (by omega_arith)) (by omega_arith), w0]
  · rw [u4, v6, v4, v5, v7]
  · rw [u5, v6, v4, v5, v7]
  · rw [u7, v6, v4, v5, v7]
  · exact O1.trans (o2.mono (by omega_arith) (by omega_arith))

/-- `loadX` and `checks`, from the header's buffers (`k` bytes of `n` and the
input, `pL` of `p` and `qInv`, `qL` of `q`, apart from the working space). -/
theorem phaseA_ok {s : State} {BX Na Pa Qa Ia QIa : Addr} {Z k pL qL : Nat}
    (hs : Scr s BX Z) (hZ : slot (2 * ((k + 7) / 8)) 8 ≤ Z) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (h23 : s.gpr .r23 = BX)
    (h10 : s.gpr .r10 = off BX (slot (2 * ((k + 7) / 8)) 0)) (h21 : s.gpr .r21 = off BX (slot (2 * ((k + 7) / 8)) 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (2 * ((k + 7) / 8))))
    (hNa : word s.mem BX oN = off Na 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hPa : word s.mem BX oP = off Pa 0) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hQa : word s.mem BX oQ = off Qa 0) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hIa : word s.mem BX oIn = off Ia 0) (hQIa : word s.mem BX oQInv = off QIa 0)
    (hp : 1 ≤ pL) (hpk : pL < k) (hq : 1 ≤ qL) (hqk : qL < k)
    (rN : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1) (sN : ∀ i < k, ∀ x, ofs BX x < Z → off Na i ≠ x)
    (rP : ∀ i < pL, InRegions (s.rd ++ s.wr) (off Pa i) 1) (sP : ∀ i < pL, ∀ x, ofs BX x < Z → off Pa i ≠ x)
    (rQ : ∀ i < qL, InRegions (s.rd ++ s.wr) (off Qa i) 1) (sQ : ∀ i < qL, ∀ x, ofs BX x < Z → off Qa i ≠ x)
    (rI : ∀ i < k, InRegions (s.rd ++ s.wr) (off Ia i) 1) (sI : ∀ i < k, ∀ x, ofs BX x < Z → off Ia i ≠ x)
    (rQI : ∀ i < pL, InRegions (s.rd ++ s.wr) (off QIa i) 1)
    (sQI : ∀ i < pL, ∀ x, ofs BX x < Z → off QIa i ≠ x) :
    WP isa (.seq loadX checks) s fun t =>
      (t.gpr .r26 = bmask (crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 0) (2 * (2 * ((k + 7) / 8))) =
          2 ^ (64 * (2 * ((k + 7) / 8))) - 1 ∧
        word t.mem BX (slot (2 * ((k + 7) / 8)) 0) = BitVec.allOnes 64 ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 4) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) else 3) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 5) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) else 3) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 7) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL) else 0) ∧
        Outside BX 256 (slot (2 * ((k + 7) / 8)) 8 - 256) s.mem t.mem ∧
        t.gpr .r10 = off BX (slot (2 * ((k + 7) / 8)) 0)) ∧
      Keep (loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg)) s t := by
  have hn := hs.nowrap
  have hQb : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) < 256 ^ qL := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem Qa qL)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hPb : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) < 256 ^ pL := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem Pa pL)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hw : 16 * k ≤ 64 * (2 * ((k + 7) / 8)) := by omega_arith
  refine wp_seq_nil (phaseAWith_ok (pre := []) hs hZ hk hk' h23 h10 h21 h29 h11 hNa hK hPa hPL hQa hQL hIa hQIa
    hp hpk hq hqk rN sN rP sP rQ sQ rI sI rQI sQI
    fun s₁ hs₁ _ _ v0 w0 v4 v5 t1 _ => WP.block_nil ⟨⟨rfl, checkPQ_pqOk hZ (by omega_arith) (by omega_arith) v0 w0
      (by rw [v5]; have := pq_lt (P := 1) (pL := 1) (by
        rw [VG.Proof.Bignum.pow256_eq]; exact Nat.one_lt_two_pow (by omega_arith)) hQb (by omega_arith) hqk hw; omega_arith)
      (by rw [v4, v5]; exact pq_lt hPb hQb hpk hqk hw) t1⟩, Keep.refl _ _⟩)

end VG.Proof.Bignum.PPC64LE.Crt
