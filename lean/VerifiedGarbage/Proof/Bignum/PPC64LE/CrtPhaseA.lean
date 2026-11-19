module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.Code

/-! ### `Bignum.PPC64LE.CrtChecks`, which this module and modules that import it used -/

section

/-! ### `Bignum.PPC64LE.CrtMask`, which only this module used -/

section

/-!
# The RSA private-key operation on PPC64LE: masking the key

`maskWords_ok`: `w` words `&=` the mask. `orThree_ok`: an array kept under
the mask, else 3.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `maskWords`, `r14` at offset `d` of `B`: the `w` words there `&= r26`. -/
theorem maskWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B d) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : d + 8 * w ≤ Z) :
    WP isa maskWords s fun t =>
      ((∀ i < w, word t.mem B (d + 8 * i) = word s.mem B (d + 8 * i) &&& s.gpr .r26) ∧
        Outside B d (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r17] s t := by
  have hnw := hs.nowrap
  unfold maskWords
  refine WP.seq ?_
  obtain hpre : WP isa (.block [.lsr .d .r17 .r11 1]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  refine WP.mono hpre fun s₁ ⟨⟨i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (d + 8 * i) ∧ Outside B d (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (d + 8 * k) = word s.mem B (d + 8 * k) &&& s.gpr .r26) ∧
      Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr .r14 (by decide), h14]; rfl, by rw [im]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega_arith), k₁.mono⟩ i17) fun t ⟨_, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  obtain h26 : t.gpr .r26 = s.gpr .r26 := jk.gpr _ (by decide)
  refine WP.mono (WP.keep [.r0, .r14, .r17] (Q := fun t' =>
    t'.mem = t.mem.writeW (off B (d + 8 * i)) (word t.mem B (d + 8 * i) &&& s.gpr .r26) ∧
      t'.gpr .r14 = off B (d + 8 * (i + 1)) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ?_ (by decide))
    fun t' ⟨⟨a, b, c⟩, k⟩ => ⟨⟨b, ?_, ?_, jk.trans' k⟩, c⟩
  · prun [j14, h26, (hs.congr jk.wr).ld (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show d + 8 * i + 8 ≤ Z by omega_arith)]
    simp only [Mont.off, off]; congr 2
  · have hw := writeW_outside t.mem B (d := d + 8 * i) (word t.mem B (d + 8 * i) &&& s.gpr .r26) (by omega_arith)
    rw [a]; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    obtain hw := writeW_outside t.mem B (d := d + 8 * i) (word t.mem B (d + 8 * i) &&& s.gpr .r26) (by omega_arith)
    rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · rw [word_writeW_self, jout.word (Or.inr (Nat.le_refl _)) (by omega_arith)]

/-- The mask of `b`, on a word. -/
theorem and_mask (x : BitVec 64) (b : Bool) :
    x &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) = if b then x else 0 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact BitVec.and_zero
  · simp only [↓reduceIte]; exact BitVec.and_allOnes

theorem three_mask (x : BitVec 64) (b : Bool) :
    x ||| (((0#64 - 1#64) ^^^ (0#64 - BitVec.ofNat 64 (if b then 1 else 0))) &&& 3#64) =
      x ||| (if b then 0 else 3) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> congr 1

/-- `orThree j`, the mask of `b` in `r26`: array `j` (`w` words) kept if `b`,
else 3. -/
theorem orThree_ok {s : State} {B : Addr} {Z w j : Nat} {b : Bool} (hs : Scr s B Z) (hj : j < 8)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (orThree j) s fun t =>
      (Mont.val32 t.mem B (slot w j) (2 * w) = (if b then Mont.val32 s.mem B (slot w j) (2 * w) else 3) ∧
        Outside B (slot w j) (8 * w) s.mem t.mem) ∧ Keep [.r0, .r3, .r4, .r14, .r17] s t := by
  have hnw := hs.nowrap
  obtain sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_le hj) hZ
  unfold orThree
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 j)
    fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (maskWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw hw'
    (by omega_arith)) fun s₂ ⟨⟨hm, out₂⟩, k₂⟩ => ?_)
  obtain k12 := k1.trans k₂
  rw [m1, k1.gpr .r26 (by decide), h26] at hm
  rw [m1] at out₂
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) j) fun s₃ ⟨⟨b14, m3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
  refine WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun t => t.mem = s₃.mem.writeW (off B (slot w j))
    (word s₃.mem B (slot w j) ||| (if b then 0 else 3))) ?_ (by decide)) fun t ⟨tm, k4⟩ =>
    ⟨⟨?_, ?_⟩, (k13.trans k4).mono⟩
  · prun [b14, BitVec.add_zero, (k13.gpr .r26 (by decide)).trans h26, (hs.congr k13.wr).ld (show slot w j + 8 ≤ Z by omega_arith),
      (hs.congr k13.wr).st (show slot w j + 8 ≤ Z by omega_arith), three_mask]
  · rw [m3] at tm
    obtain ow := writeW_outside s₂.mem B (d := slot w j) (word s₂.mem B (slot w j) ||| (if b then 0 else 3))
      (by omega_arith)
    obtain hm0 := hm 0 (by omega_arith)
    rw [Nat.mul_zero, Nat.add_zero] at hm0
    rw [Pre.val32_eq_wv, Pre.val32_eq_wv]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [wv_single (i := 0) _ _ _ w (by omega_arith) fun q hq hne => ?_]
      · rw [tm, Nat.mul_zero, Nat.add_zero, word_writeW_self, hm0, and_mask]
        simp
      · rw [tm, ow.word (by omega_arith) (by omega_arith), hm q hq, and_mask]; rfl
    · simp only [↓reduceIte]
      refine wv_congr fun q hq => ?_
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · rw [tm, Nat.mul_zero, Nat.add_zero, word_writeW_self, hm0, and_mask]
        simp
      · rw [tm, ow.word (by omega_arith) (by omega_arith), hm q hq, and_mask]; rfl
  · rw [m3] at tm
    rw [tm]
    exact out₂.trans ((writeW_outside s₂.mem B (d := slot w j) _ (by omega_arith)).mono (Nat.le_refl _) (by omega_arith))

end VG.Proof.Bignum.PPC64LE.Crt

end

end


/-!
# The RSA private-key operation on PPC64LE: the checks

`checksAWith_ok`: the mask of the checks into `r26` (`n` valid, the input
below `n`, `qInv` below `p`, `p q = n` by a check `PQOk`, such as `checkPQ`:
`checkPQ_pqOk`). `checksB_ok`: `p` and `q` kept under the
mask, else 3, and `qInv` kept under it, else 0.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The mask of `b`. -/
abbrev bmask (b : Bool) : BitVec 64 := BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)

theorem bmask_and (a b : Bool) : bmask a &&& bmask b = bmask (a && b) := by
  cases a <;> cases b <;> decide

theorem bmask_decide (p : Prop) [Decidable p] :
    BitVec.ofNat 64 0 - BitVec.ofNat 64 (if p then 1 else 0) = bmask (decide p) := by
  by_cases h : p <;> simp [h]

/-- The registers the checks write. -/
def checkRegs : List Reg := [.r4, .r6, .r18, .r26] ++ pqRegs

/-- The registers `checkN`, `checkLt 6 1` and `checkLt 7 4` write. -/
def chk3Regs : List Reg :=
  [.r0, .r3, .r4, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r26]

/-- `pq` checks `p q = n` (arrays 4, 5 and 1 of `X` in `s`), from any state
`t` that the checks before it reach from `s`: `r26 &=` all ones if
`p q = n`, else 0, changing only arrays 2, 3 and 6. -/
def PQOk (pq : Prog isa) (BX : Addr) (Z w : Nat) (s : State) : Prop :=
  ∀ t, Scr t BX Z → t.gpr .r10 = off BX (slot w 0) → t.gpr .r21 = off BX (slot w 0) →
    t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) → t.gpr .r11 = BitVec.ofNat 64 (2 * w) → Keep chk3Regs s t →
    Mont.Outside BX (slot w 3) (8 * w) s.mem t.mem →
    WP isa pq t fun u =>
      (u.gpr .r26 = t.gpr .r26 &&& bmask (decide (val32 s.mem BX (slot w 4) (2 * w) *
          val32 s.mem BX (slot w 5) (2 * w) = val32 s.mem BX (slot w 1) (2 * w))) ∧
        Outs BX [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] t.mem u.mem ∧
        u.gpr .r10 = off BX (slot w 0)) ∧ Keep pqRegs t u

/-- `checkPQ` checks `p q = n`, with `M = 2^(64 w)-1` in array 0, `q` and
`p q` below `M`, and the top word of array 1 zero. -/
theorem checkPQ_pqOk {s : State} {BX : Addr} {Z w : Nat} (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hM : val32 s.mem BX (slot w 0) (2 * w) = 2 ^ (64 * w) - 1)
    (hM0 : word s.mem BX (slot w 0) = BitVec.allOnes 64)
    (hq : val32 s.mem BX (slot w 5) (2 * w) < 2 ^ (64 * w) - 1)
    (hpq : val32 s.mem BX (slot w 4) (2 * w) * val32 s.mem BX (slot w 5) (2 * w) < 2 ^ (64 * w) - 1)
    (h1top : word s.mem BX (slot w 1 + 8 * w) = 0) : PQOk checkPQ BX Z w s := by
  intro t ht t10 t21 t29 t11 _ to
  have hn := ht.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  obtain O : VG.Proof.Bignum.Outside BX (slot w 3) (8 * w) s.mem t.mem := fun x hx => to x hx
  obtain v : ∀ j, j ≠ 3 → j < 8 → val32 t.mem BX (slot w j) (2 * w) = val32 s.mem BX (slot w j) (2 * w) :=
    fun j h3 hj => to.val32 (by have := slot_sep (w := w) h3; omega_arith) (by have := slot_le (w := w) hj; omega_arith)
  refine WP.mono (checkPQ_ok ht hw2 hw' hZ t10 t21 t29 t11 (by rw [v 0 (by decide) (by decide), hM])
    (by rw [O.word (Or.inl (by omega_arith)) (by omega_arith), hM0])
    (by rw [v 5 (by decide) (by decide)]; exact hq)
    (by rw [v 4 (by decide) (by decide), v 5 (by decide) (by decide)]; exact hpq)
    (by rw [O.word (Or.inl (by omega_arith)) (by omega_arith)]; exact h1top))
    fun u ⟨⟨u26, uo, u10⟩, ku⟩ => ⟨⟨?_, uo, u10⟩, ku⟩
  rw [u26, v 4 (by decide) (by decide), v 5 (by decide) (by decide), v 1 (by decide) (by decide), bmask_decide]

/-- `checksWith pq`'s first part, in `X` (`n` in array 1, `p` in 4, `q` in 5,
the input in 6 and `qInv` in 7, the top words of arrays 6 and 7 zero), `pq` a
check of `p q = n` (`PQOk`): `r26 :=` the mask of the checks, changing only
arrays 2, 3 and 6. -/
theorem checksAWith_ok {pq : Prog isa} {s : State} {BX Na : Addr} {Z w k : Nat} {nb : List Byte} {c : Prog isa}
    {Q : State → Prop} (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h10 : s.gpr .r10 = off BX (slot w 0)) (h21 : s.gpr .r21 = off BX (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : word s.mem BX oN = off Na 0) (hNL : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1)
    (hb : ∀ i (h : i < k), s.mem (off Na i) = nb[i]'(by omega_arith))
    (hn1 : val32 s.mem BX (slot w 1) (2 * w) = Spec.Rsa.os2ip nb)
    (h6top : word s.mem BX (slot w 6 + 8 * w) = 0) (h7top : word s.mem BX (slot w 7 + 8 * w) = 0)
    (hPQ : PQOk pq BX Z w s)
    (hc : ∀ t, t.gpr .r26 = bmask (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k &&
        decide (val32 s.mem BX (slot w 6) (2 * w) < Spec.Rsa.os2ip nb) &&
        decide (val32 s.mem BX (slot w 7) (2 * w) < val32 s.mem BX (slot w 4) (2 * w)) &&
        decide (val32 s.mem BX (slot w 4) (2 * w) * val32 s.mem BX (slot w 5) (2 * w) = Spec.Rsa.os2ip nb)) →
      Outs BX [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem →
      t.gpr .r10 = off BX (slot w 0) → Keep checkRegs s t → WP isa c t Q) :
    WP isa (.seq checkN (.seq (checkLt 6 1) (.seq (checkLt 7 4) (.seq pq c)))) s Q := by
  have hn := hs.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  obtain e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq (WP.mono (checkN_ok hs (by omega_arith) h23 hN hNL hk hk' hlen hrd hb) fun s₁ ⟨⟨a26, m1⟩, k1⟩ => ?_)
  rw [bmask_decide] at a26
  refine WP.seq (WP.mono (checkLt_ok (a := 6) (m := 1) (hs.congr k1.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' hZ ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h21)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by rw [m1]; exact h6top))
    fun s₂ ⟨⟨b26, o2, b10⟩, k2⟩ => ?_)
  rw [m1, a26, hn1, bmask_decide, bmask_and] at b26
  obtain k12 := k1.trans k2
  rw [m1] at o2
  obtain v : ∀ j, j ≠ 3 → j < 8 → val32 s₂.mem BX (slot w j) (2 * w) = val32 s.mem BX (slot w j) (2 * w) :=
    fun j h3 hj => o2.val32 (by have := slot_sep (w := w) h3; omega_arith) (by have := slot_le (w := w) hj; omega_arith)
  obtain O2 : VG.Proof.Bignum.Outside BX (slot w 3) (8 * w) s.mem s₂.mem := fun x hx => o2 x hx
  obtain wd : ∀ j, j ≠ 3 → j < 8 → word s₂.mem BX (slot w j + 8 * w) = word s.mem BX (slot w j + 8 * w) :=
    fun j h3 hj => O2.word
      (by have := slot_sep (w := w) h3; omega_arith) (by have := slot_le (w := w) hj; omega_arith)
  refine WP.seq (WP.mono (checkLt_ok (a := 7) (m := 4) (hs.congr k12.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' hZ b10 ((k12.gpr _ (by decide)).trans h21)
    ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by rw [wd 7 (by decide) (by decide)]; exact h7top)) fun s₃ ⟨⟨c26, o3, c10⟩, k3⟩ => ?_)
  rw [b26, v 7 (by decide) (by decide), v 4 (by decide) (by decide), bmask_decide, bmask_and] at c26
  obtain k13 := k12.trans k3
  refine WP.seq (WP.mono (hPQ s₃ (hs.congr k13.wr) c10 ((k13.gpr _ (by decide)).trans h21)
    ((k13.gpr _ (by decide)).trans h29) ((k13.gpr _ (by decide)).trans h11) k13.mono
    (fun x hx => (o3 x hx).trans (o2 x hx))) fun t ⟨⟨t26, ot, t10⟩, kt⟩ => ?_)
  rw [c26, hn1, bmask_and] at t26
  refine hc t t26 (fun x hx => ?_) t10 (k13.trans kt).mono
  obtain h3 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only at h3
  rw [ot x hx, o3 x (by omega_arith), o2 x (by omega_arith)]

/-- `checks`' second part, the mask of `b` in `r26`: arrays 4 and 5 kept if
`b`, else 3, and array 7 kept if `b`, else 0. -/
theorem checksB_ok {s : State} {BX : Addr} {Z w : Nat} {b : Bool} (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (h10 : s.gpr .r10 = off BX (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h26 : s.gpr .r26 = bmask b) :
    WP isa (.seq (orThree 4) (.seq (orThree 5) (.seq (.block (PublicChecked.base .r14 7)) maskWords))) s
      fun t =>
      (val32 t.mem BX (slot w 4) (2 * w) = (if b then val32 s.mem BX (slot w 4) (2 * w) else 3) ∧
        val32 t.mem BX (slot w 5) (2 * w) = (if b then val32 s.mem BX (slot w 5) (2 * w) else 3) ∧
        val32 t.mem BX (slot w 7) (2 * w) = (if b then val32 s.mem BX (slot w 7) (2 * w) else 0) ∧
        Outs BX [(slot w 4, 8 * (w + 2)), (slot w 5, 8 * (w + 2)), (slot w 7, 8 * (w + 2))] s.mem t.mem) ∧
      Keep [.r0, .r3, .r4, .r14, .r17] s t := by
  have hn := hs.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  obtain e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq (WP.mono (orThree_ok (j := 4) hs (by decide) h10 h29 h11 (by omega_arith) hw' hZ h26)
    fun s₁ ⟨⟨v4, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (orThree_ok (j := 5) (hs.congr k1.wr) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by omega_arith) hw' hZ
    ((k1.gpr _ (by decide)).trans h26)) fun s₂ ⟨⟨v5, o2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  obtain O1 : Mont.Outside BX (slot w 4) (8 * w) s.mem s₁.mem := fun x hx => o1 x hx
  obtain O2 : Mont.Outside BX (slot w 5) (8 * w) s₁.mem s₂.mem := fun x hx => o2 x hx
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 7) fun s₃ ⟨⟨a14, m3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  refine WP.mono (maskWords_ok (hs.congr k13.wr) a14 ((k13.gpr _ (by decide)).trans h11) (by omega_arith) hw'
    (by omega_arith)) fun t ⟨⟨hm, ot⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, (k13.trans kt).mono⟩
  · have OT : Mont.Outside BX (slot w 7) (8 * w) s₃.mem t.mem := fun x hx => ot x hx
    rw [OT.val32 (Or.inl (by omega_arith)) (by omega_arith), m3, O2.val32 (Or.inl (by omega_arith)) (by omega_arith), v4]
  · have OT : Mont.Outside BX (slot w 7) (8 * w) s₃.mem t.mem := fun x hx => ot x hx
    rw [OT.val32 (Or.inl (by omega_arith)) (by omega_arith), m3, v5, O1.val32 (Or.inr (by omega_arith)) (by omega_arith)]
  · have h7 : val32 s₃.mem BX (slot w 7) (2 * w) = val32 s.mem BX (slot w 7) (2 * w) := by
      rw [m3, O2.val32 (Or.inr (by omega_arith)) (by omega_arith), O1.val32 (Or.inr (by omega_arith)) (by omega_arith)]
    rw [← h7, Pre.val32_eq_wv, Pre.val32_eq_wv]
    obtain g26 : s₃.gpr .r26 = bmask b := (k13.gpr _ (by decide)).trans h26
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine (wv_eq_zero_iff _ _ _ _).mpr fun q hq => ?_
      rw [hm q hq, g26]; exact and_mask _ false
    · simp only [↓reduceIte]
      exact wv_congr fun i hi => by rw [hm i hi, g26]; exact and_mask _ true
  · intro x hx
    obtain h4 := hx _ (List.mem_cons_self ..)
    obtain h5 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain h7 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only at h4 h5 h7
    have h4' : ofs BX x < slot w 4 ∨ slot w 4 + 8 * (w + 2) ≤ ofs BX x := h4
    have h5' : ofs BX x < slot w 5 ∨ slot w 5 + 8 * (w + 2) ≤ ofs BX x := h5
    have h7' : ofs BX x < slot w 7 ∨ slot w 7 + 8 * (w + 2) ≤ ofs BX x := h7
    rw [ot x (by omega_arith), m3, o2 x (by omega_arith), o1 x (by omega_arith)]

end VG.Proof.Bignum.PPC64LE.Crt

end

end

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
