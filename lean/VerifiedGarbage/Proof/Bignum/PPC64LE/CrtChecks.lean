module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMask
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: the checks

`checksA_ok`: the mask of the checks into `r26` (`n` valid, the input below
`n`, `qInv` below `p`, `p q = n`). `checksB_ok`: `p` and `q` kept under the
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

/-- `checks`' first part, in `X` (`M = 2^(64 w)-1` in array 0, `n` in array
1, `p` in 4, `q` in 5, the input in 6 and `qInv` in 7, the top words of
arrays 1, 6 and 7 zero): `r26 :=` the mask of the checks, changing only
arrays 2, 3 and 6. -/
theorem checksA_ok {s : State} {BX Na : Addr} {Z w k : Nat} {nb : List Byte} {c : Prog isa}
    {Q : State → Prop} (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h10 : s.gpr .r10 = off BX (slot w 0)) (h21 : s.gpr .r21 = off BX (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : word s.mem BX oN = off Na 0) (hNL : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1)
    (hb : ∀ i (h : i < k), s.mem (off Na i) = nb[i]'(by omega))
    (hM : val32 s.mem BX (slot w 0) (2 * w) = 2 ^ (64 * w) - 1)
    (hM0 : word s.mem BX (slot w 0) = BitVec.allOnes 64)
    (hn1 : val32 s.mem BX (slot w 1) (2 * w) = Spec.Rsa.os2ip nb)
    (h1top : word s.mem BX (slot w 1 + 8 * w) = 0) (h6top : word s.mem BX (slot w 6 + 8 * w) = 0)
    (h7top : word s.mem BX (slot w 7 + 8 * w) = 0)
    (hq : val32 s.mem BX (slot w 5) (2 * w) < 2 ^ (64 * w) - 1)
    (hpq : val32 s.mem BX (slot w 4) (2 * w) * val32 s.mem BX (slot w 5) (2 * w) < 2 ^ (64 * w) - 1)
    (hc : ∀ t, t.gpr .r26 = bmask (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k &&
        decide (val32 s.mem BX (slot w 6) (2 * w) < Spec.Rsa.os2ip nb) &&
        decide (val32 s.mem BX (slot w 7) (2 * w) < val32 s.mem BX (slot w 4) (2 * w)) &&
        decide (val32 s.mem BX (slot w 4) (2 * w) * val32 s.mem BX (slot w 5) (2 * w) = Spec.Rsa.os2ip nb)) →
      Outs BX [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem →
      t.gpr .r10 = off BX (slot w 0) → Keep checkRegs s t → WP isa c t Q) :
    WP isa (.seq checkN (.seq (checkLt 6 1) (.seq (checkLt 7 4) (.seq checkPQ c)))) s Q := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq (WP.mono (checkN_ok hs (by omega) h23 hN hNL hk hk' hlen hrd hb) fun s₁ ⟨⟨a26, m1⟩, k1⟩ => ?_)
  rw [bmask_decide] at a26
  refine WP.seq (WP.mono (checkLt_ok (a := 6) (m := 1) (hs.congr k1.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega) hw' hZ ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h21)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by rw [m1]; exact h6top))
    fun s₂ ⟨⟨b26, o2, b10⟩, k2⟩ => ?_)
  rw [m1, a26, hn1, bmask_decide, bmask_and] at b26
  have k12 := k1.trans k2
  rw [m1] at o2
  have v : ∀ j, j ≠ 3 → j < 8 → val32 s₂.mem BX (slot w j) (2 * w) = val32 s.mem BX (slot w j) (2 * w) :=
    fun j h3 hj => o2.val32 (by have := slot_sep (w := w) h3; omega) (by have := slot_le (w := w) hj; omega)
  have O2 : VG.Proof.Bignum.Outside BX (slot w 3) (8 * w) s.mem s₂.mem := fun x hx => o2 x hx
  have wd : ∀ j, j ≠ 3 → j < 8 → word s₂.mem BX (slot w j + 8 * w) = word s.mem BX (slot w j + 8 * w) :=
    fun j h3 hj => O2.word
      (by have := slot_sep (w := w) h3; omega) (by have := slot_le (w := w) hj; omega)
  refine WP.seq (WP.mono (checkLt_ok (a := 7) (m := 4) (hs.congr k12.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega) hw' hZ b10 ((k12.gpr _ (by decide)).trans h21)
    ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by rw [wd 7 (by decide) (by decide)]; exact h7top)) fun s₃ ⟨⟨c26, o3, c10⟩, k3⟩ => ?_)
  rw [b26, v 7 (by decide) (by decide), v 4 (by decide) (by decide), bmask_decide, bmask_and] at c26
  have k13 := k12.trans k3
  have v' : ∀ j, j ≠ 3 → j < 8 → val32 s₃.mem BX (slot w j) (2 * w) = val32 s.mem BX (slot w j) (2 * w) :=
    fun j h3 hj => (o3.val32 (by have := slot_sep (w := w) h3; omega)
      (by have := slot_le (w := w) hj; omega)).trans (v j h3 hj)
  have O3 : VG.Proof.Bignum.Outside BX (slot w 3) (8 * w) s₂.mem s₃.mem := fun x hx => o3 x hx
  have wd' : ∀ j, j ≠ 3 → j < 8 → word s₃.mem BX (slot w j + 8 * w) = word s.mem BX (slot w j + 8 * w) :=
    fun j h3 hj => (O3.word
      (by have := slot_sep (w := w) h3; omega) (by have := slot_le (w := w) hj; omega)).trans (wd j h3 hj)
  have w0 : word s₃.mem BX (slot w 0) = BitVec.allOnes 64 := by
    rw [O3.word (Or.inl (by omega)) (by omega),
      O2.word (Or.inl (by omega)) (by omega), hM0]
  refine WP.seq (WP.mono (checkPQ_ok (hs.congr k13.wr) hw2 hw' hZ c10 ((k13.gpr _ (by decide)).trans h21)
    ((k13.gpr _ (by decide)).trans h29) ((k13.gpr _ (by decide)).trans h11)
    (by rw [v' 0 (by decide) (by decide), hM]) w0 (by rw [v' 5 (by decide) (by decide)]; exact hq)
    (by rw [v' 4 (by decide) (by decide), v' 5 (by decide) (by decide)]; exact hpq)
    (by rw [wd' 1 (by decide) (by decide)]; exact h1top)) fun t ⟨⟨t26, ot, t10⟩, kt⟩ => ?_)
  rw [c26, v' 4 (by decide) (by decide), v' 5 (by decide) (by decide), v' 1 (by decide) (by decide), hn1,
    bmask_decide, bmask_and] at t26
  refine hc t t26 (fun x hx => ?_) t10 (k13.trans kt).mono
  have h3 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only at h3
  rw [ot x hx, o3 x (by omega), o2 x (by omega)]

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
  refine WP.seq (WP.mono (orThree_ok (j := 4) hs (by decide) h10 h29 h11 (by omega) hw' hZ h26)
    fun s₁ ⟨⟨v4, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (orThree_ok (j := 5) (hs.congr k1.wr) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by omega) hw' hZ
    ((k1.gpr _ (by decide)).trans h26)) fun s₂ ⟨⟨v5, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have O1 : Mont.Outside BX (slot w 4) (8 * w) s.mem s₁.mem := fun x hx => o1 x hx
  have O2 : Mont.Outside BX (slot w 5) (8 * w) s₁.mem s₂.mem := fun x hx => o2 x hx
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 7) fun s₃ ⟨⟨a14, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.mono (maskWords_ok (hs.congr k13.wr) a14 ((k13.gpr _ (by decide)).trans h11) (by omega) hw'
    (by omega)) fun t ⟨⟨hm, ot⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, (k13.trans kt).mono⟩
  · have OT : Mont.Outside BX (slot w 7) (8 * w) s₃.mem t.mem := fun x hx => ot x hx
    rw [OT.val32 (Or.inl (by omega)) (by omega), m3, O2.val32 (Or.inl (by omega)) (by omega), v4]
  · have OT : Mont.Outside BX (slot w 7) (8 * w) s₃.mem t.mem := fun x hx => ot x hx
    rw [OT.val32 (Or.inl (by omega)) (by omega), m3, v5, O1.val32 (Or.inr (by omega)) (by omega)]
  · have h7 : val32 s₃.mem BX (slot w 7) (2 * w) = val32 s.mem BX (slot w 7) (2 * w) := by
      rw [m3, O2.val32 (Or.inr (by omega)) (by omega), O1.val32 (Or.inr (by omega)) (by omega)]
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
    rw [ot x (by omega), m3, o2 x (by omega), o1 x (by omega)]

end VG.Proof.Bignum.PPC64LE.Crt
