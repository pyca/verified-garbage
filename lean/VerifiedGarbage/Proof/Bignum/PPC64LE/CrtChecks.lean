module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.Code

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
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1]) s fun s₁ =>
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
  have h26 : t.gpr .r26 = s.gpr .r26 := jk.gpr _ (by decide)
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
    have hw := writeW_outside t.mem B (d := d + 8 * i) (word t.mem B (d + 8 * i) &&& s.gpr .r26) (by omega_arith)
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
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_le hj) hZ
  unfold orThree
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 j)
    fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (maskWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw hw'
    (by omega_arith)) fun s₂ ⟨⟨hm, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [m1, k1.gpr .r26 (by decide), h26] at hm
  rw [m1] at out₂
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) j) fun s₃ ⟨⟨b14, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun t => t.mem = s₃.mem.writeW (off B (slot w j))
    (word s₃.mem B (slot w j) ||| (if b then 0 else 3))) ?_ (by decide)) fun t ⟨tm, k4⟩ =>
    ⟨⟨?_, ?_⟩, (k13.trans k4).mono⟩
  · prun [b14, BitVec.add_zero, (k13.gpr .r26 (by decide)).trans h26, (hs.congr k13.wr).ld (show slot w j + 8 ≤ Z by omega_arith),
      (hs.congr k13.wr).st (show slot w j + 8 ≤ Z by omega_arith), three_mask]
  · rw [m3] at tm
    have ow := writeW_outside s₂.mem B (d := slot w j) (word s₂.mem B (slot w j) ||| (if b then 0 else 3))
      (by omega_arith)
    have hm0 := hm 0 (by omega_arith)
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
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have O : VG.Proof.Bignum.Outside BX (slot w 3) (8 * w) s.mem t.mem := fun x hx => to x hx
  have v : ∀ j, j ≠ 3 → j < 8 → val32 t.mem BX (slot w j) (2 * w) = val32 s.mem BX (slot w j) (2 * w) :=
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
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq (WP.mono (checkN_ok hs (by omega_arith) h23 hN hNL hk hk' hlen hrd hb) fun s₁ ⟨⟨a26, m1⟩, k1⟩ => ?_)
  rw [bmask_decide] at a26
  refine WP.seq (WP.mono (checkLt_ok (a := 6) (m := 1) (hs.congr k1.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' hZ ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h21)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by rw [m1]; exact h6top))
    fun s₂ ⟨⟨b26, o2, b10⟩, k2⟩ => ?_)
  rw [m1, a26, hn1, bmask_decide, bmask_and] at b26
  have k12 := k1.trans k2
  rw [m1] at o2
  have v : ∀ j, j ≠ 3 → j < 8 → val32 s₂.mem BX (slot w j) (2 * w) = val32 s.mem BX (slot w j) (2 * w) :=
    fun j h3 hj => o2.val32 (by have := slot_sep (w := w) h3; omega_arith) (by have := slot_le (w := w) hj; omega_arith)
  have O2 : VG.Proof.Bignum.Outside BX (slot w 3) (8 * w) s.mem s₂.mem := fun x hx => o2 x hx
  have wd : ∀ j, j ≠ 3 → j < 8 → word s₂.mem BX (slot w j + 8 * w) = word s.mem BX (slot w j + 8 * w) :=
    fun j h3 hj => O2.word
      (by have := slot_sep (w := w) h3; omega_arith) (by have := slot_le (w := w) hj; omega_arith)
  refine WP.seq (WP.mono (checkLt_ok (a := 7) (m := 4) (hs.congr k12.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' hZ b10 ((k12.gpr _ (by decide)).trans h21)
    ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by rw [wd 7 (by decide) (by decide)]; exact h7top)) fun s₃ ⟨⟨c26, o3, c10⟩, k3⟩ => ?_)
  rw [b26, v 7 (by decide) (by decide), v 4 (by decide) (by decide), bmask_decide, bmask_and] at c26
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (hPQ s₃ (hs.congr k13.wr) c10 ((k13.gpr _ (by decide)).trans h21)
    ((k13.gpr _ (by decide)).trans h29) ((k13.gpr _ (by decide)).trans h11) k13.mono
    (fun x hx => (o3 x hx).trans (o2 x hx))) fun t ⟨⟨t26, ot, t10⟩, kt⟩ => ?_)
  rw [c26, hn1, bmask_and] at t26
  refine hc t t26 (fun x hx => ?_) t10 (k13.trans kt).mono
  have h3 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
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
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq (WP.mono (orThree_ok (j := 4) hs (by decide) h10 h29 h11 (by omega_arith) hw' hZ h26)
    fun s₁ ⟨⟨v4, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (orThree_ok (j := 5) (hs.congr k1.wr) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by omega_arith) hw' hZ
    ((k1.gpr _ (by decide)).trans h26)) fun s₂ ⟨⟨v5, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have O1 : Mont.Outside BX (slot w 4) (8 * w) s.mem s₁.mem := fun x hx => o1 x hx
  have O2 : Mont.Outside BX (slot w 5) (8 * w) s₁.mem s₂.mem := fun x hx => o2 x hx
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 7) fun s₃ ⟨⟨a14, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.mono (maskWords_ok (hs.congr k13.wr) a14 ((k13.gpr _ (by decide)).trans h11) (by omega_arith) hw'
    (by omega_arith)) fun t ⟨⟨hm, ot⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, (k13.trans kt).mono⟩
  · have OT : Mont.Outside BX (slot w 7) (8 * w) s₃.mem t.mem := fun x hx => ot x hx
    rw [OT.val32 (Or.inl (by omega_arith)) (by omega_arith), m3, O2.val32 (Or.inl (by omega_arith)) (by omega_arith), v4]
  · have OT : Mont.Outside BX (slot w 7) (8 * w) s₃.mem t.mem := fun x hx => ot x hx
    rw [OT.val32 (Or.inl (by omega_arith)) (by omega_arith), m3, v5, O1.val32 (Or.inr (by omega_arith)) (by omega_arith)]
  · have h7 : val32 s₃.mem BX (slot w 7) (2 * w) = val32 s.mem BX (slot w 7) (2 * w) := by
      rw [m3, O2.val32 (Or.inr (by omega_arith)) (by omega_arith), O1.val32 (Or.inr (by omega_arith)) (by omega_arith)]
    rw [← h7, Pre.val32_eq_wv, Pre.val32_eq_wv]
    have g26 : s₃.gpr .r26 = bmask b := (k13.gpr _ (by decide)).trans h26
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine (wv_eq_zero_iff _ _ _ _).mpr fun q hq => ?_
      rw [hm q hq, g26]; exact and_mask _ false
    · simp only [↓reduceIte]
      exact wv_congr fun i hi => by rw [hm i hi, g26]; exact and_mask _ true
  · intro x hx
    have h4 := hx _ (List.mem_cons_self ..)
    have h5 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h7 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only at h4 h5 h7
    have h4' : ofs BX x < slot w 4 ∨ slot w 4 + 8 * (w + 2) ≤ ofs BX x := h4
    have h5' : ofs BX x < slot w 5 ∨ slot w 5 + 8 * (w + 2) ≤ ofs BX x := h5
    have h7' : ofs BX x < slot w 7 ∨ slot w 7 + 8 * (w + 2) ≤ ofs BX x := h7
    rw [ot x (by omega_arith), m3, o2 x (by omega_arith), o1 x (by omega_arith)]

end VG.Proof.Bignum.PPC64LE.Crt
