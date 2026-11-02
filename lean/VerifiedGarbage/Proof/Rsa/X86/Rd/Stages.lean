module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Product
import VerifiedGarbage.Proof.Rsa.X86.Rd.Gcd
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFlags
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Appendix C.2 on i686: `d e - 1`, the GCD, the product and the first division

Each stage from the arrays and header words the previous one leaves, to
those the next one takes, with their values as `RecoverDet`'s model
computes them.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Rsa (b2n b2n_le sub32)

theorem sub32_wsub (w a b : Nat) : sub32 w a b = wsub (32 * w) a b := rfl

/-- `x = d e - 1` (wide), and whether `d e ≥ 2`. -/
theorem deMinus_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {de : Nat}
    (h : KS g s0 A [VG.Impl.Rsa.X86.Recover.aN] AW [VG.Impl.Rsa.X86.Recover.wM, VG.Impl.Rsa.X86.Recover.wZ] V [] s)
    (hde : AW VG.Impl.Rsa.X86.Recover.wM = de) (hz : AW VG.Impl.Rsa.X86.Recover.wZ = 0) :
    WP isa deMinus s fun t => ∃ AW',
      KS g s0 A [VG.Impl.Rsa.X86.Recover.aN] AW' [wX, VG.Impl.Rsa.X86.Recover.wZ]
        (upd V sOkDE (b2n (okDE (32 * g.W) de))) [sOkDE] t ∧
      AW' wX = deX (32 * g.W) de ∧ AW' VG.Impl.Rsa.X86.Recover.wZ = 0 := by
  have hde' : AW 3 = de := hde
  have hz' : AW 0 = 0 := hz
  unfold deMinus wideOne
  simp only [seqs]
  refine WP.seq (WP.seq (WP.mono (h.zeroWide_W (j := wOne) (by decide) (by decide)) fun u1 ⟨h1, _⟩ => ?_))
  refine WP.mono (h1.setOne_W (j := wOne) (by simp) (by decide)) fun u2 h2 => ?_
  refine WP.seq (WP.mono (h2.subWrap_W (o := wX) (a := VG.Impl.Rsa.X86.Recover.wM) (b := wOne) (by decide)
    (by simp) (by simp) (by decide) (by decide) (by decide)) fun u3 ⟨h3, b3⟩ => ?_)
  refine WP.seq (WP.mono (h3.storeSlot (d := sB0) (by decide) .ebx) fun u4 ⟨h4, _, _⟩ => ?_)
  rw [b3] at h4
  refine WP.seq (WP.mono (h4.subWrap_W (o := wT) (a := wX) (b := wOne) (by decide)
    (by simp) (by simp) (by decide) (by decide) (by decide)) fun u5 ⟨h5, b5⟩ => ?_)
  refine WP.seq (WP.mono (h5.storeSlot (d := sB1) (by decide) .ebx) fun u6 ⟨h6, _, _⟩ => ?_)
  rw [b5] at h6
  refine WP.seq (WP.mono (h6.flagOr_ok (d := sOkDE) (a := sB0) (b := sB1) (by decide) (by simp) (by simp)
    (by rw [upd_ne _ _ (show sB0 ≠ sB1 by decide), upd_self]) (by rw [upd_self])) fun u7 h7 => ?_)
  refine WP.mono (h7.flagNot_ok (d := sOkDE) (a := sOkDE) (by decide) (by simp) (by rw [upd_self])) fun t ht => ?_
  refine ⟨_, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, ?_⟩), ?_, ?_⟩
  · simp only [List.mem_singleton] at hd
    subst hd
    simp [upd, okDE, deX, sub32_wsub, hde', sOkDE, wX, wOne, VG.Impl.Rsa.X86.Recover.wM]
  · simp [upd, deX, sub32_wsub, hde', wX, wOne, wT, VG.Impl.Rsa.X86.Recover.wM]
  · simp [upd, hz', wX, wOne, wT, VG.Impl.Rsa.X86.Recover.wZ]

/-- The GCD's inputs: `u` into narrow array 8 and the halved `x` into narrow array 0. -/
theorem gcdSetD_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {u x : Nat}
    (h : KS g s0 A [aU, aX2, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sK, sOkDE] s)
    (hu : A aU = u) (hx : A aX2 = x) :
    WP isa gcdSet s fun t => ∃ A',
      KS g s0 A' [VG.Impl.Rsa.X86.Keys.aM, 0, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sOkDE] t ∧
      A' VG.Impl.Rsa.X86.Keys.aM = u ∧ A' 0 = x ∧
      A' VG.Impl.Rsa.X86.Recover.aN = A VG.Impl.Rsa.X86.Recover.aN := by
  have hu' : A 24 = u := hu
  have hx' : A 20 = x := hx
  unfold gcdSet
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := aGm) (a := aU) (by decide) (by simp) (by decide) (by decide))
    fun u1 ⟨h1, _, _⟩ => ?_)
  refine WP.mono (h1.copy_w (o := aGx) (a := aX2) (by decide) (by simp) (by decide) (by decide)) fun u2 ⟨h2, _, _⟩ => ?_
  refine ⟨_, h2.mono (live' := [VG.Impl.Rsa.X86.Keys.aM, 0, VG.Impl.Rsa.X86.Recover.aN]) (ls' := [sOkDE])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨by revert hd; revert d; decide, rfl⟩), ?_, ?_, ?_⟩
  · simp [upd, VG.Impl.Rsa.X86.Keys.aM, aGm, aGx, aU, hu']
  · simp [upd, aGx, aGm, aX2, hx']
  · simp [upd, aGx, aGm, VG.Impl.Rsa.X86.Recover.aN]

/-- The product's set-up: its sum and zero (wide) zeroed. -/
theorem aProductHead_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {g1 x3 : Nat}
    (h : KS g s0 A [1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sOkDE] s)
    (hg : A 1 = g1) (hx : AW wX3 = x3) :
    WP isa (.seq (VG.Impl.Rsa.X86.KeyRt.zeroWide wid wZ2) (VG.Impl.Rsa.X86.KeyRt.zeroWide wid wA)) s fun u =>
      KS g s0 (upd A aG g1) [1, aZero, VG.Impl.Rsa.X86.Recover.aN]
        (upd (upd (upd (upd AW wZ2 0) wA 0) wX3 x3) wA 0) [wA, wZ2, wX3] V [sOkDE] u := by
  have hx' : AW 13 = x3 := hx
  refine WP.seq (WP.mono (h.zeroWide_W (j := wZ2) (by decide) (by decide)) fun u1 ⟨h1, _⟩ => ?_)
  refine WP.mono (h1.zeroWide_W (j := wA) (by decide) (by decide)) fun u2 ⟨h2, _⟩ => ?_
  exact h2.mono (fun j hj => ⟨hj, by simp at hj; rcases hj with rfl | rfl | rfl <;> simp [upd, aG, hg, aZero,
      VG.Impl.Rsa.X86.Recover.aN]⟩)
    (fun j hj => ⟨hj, by simp at hj; rcases hj with rfl | rfl | rfl <;> simp [upd, wA, wZ2, wX3, hx']⟩)
    (fun d hd => ⟨hd, rfl⟩)

/-- The arrays the product of `aProduct` names. -/
theorem aProductIdx : ProdIdx aG wX3 wA wT wZ2 [1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wZ2, wX3] [sOkDE] :=
  ⟨by decide, by simp, by simp, by simp, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- `a`: the GCD times the doubled `x`. -/
theorem aProduct_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {g1 x3 : Nat}
    (h : KS g s0 A [1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sOkDE] s)
    (hg : A 1 = g1) (hx : AW wX3 = x3) :
    WP isa aProduct s fun t => ∃ A' AW' V',
      KS g s0 A' [aZero, VG.Impl.Rsa.X86.Recover.aN] AW' [wA, wZ2] V' [sOkDE] t ∧
      AW' wA = ((prodStep (32 * g.W))^[32 * g.w] (g1, x3, 0)).2.2 ∧ AW' wZ2 = 0 ∧ A' aZero = A aZero ∧
      A' VG.Impl.Rsa.X86.Recover.aN = A VG.Impl.Rsa.X86.Recover.aN ∧ V' sOkDE = V sOkDE := by
  unfold aProduct
  simp only [seqs]
  refine WP.assoc (WP.seq (WP.mono (aProductHead_ok h hg hx) fun u h3 =>
    WP.mono (product_ok aProductIdx (by simp [upd, wZ2, wA]) h3) fun t ht => ?_))
  unfold ProdS at ht
  refine ⟨_, _, _, ht.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), by simp [upd], by simp [upd, wA, wZ2, wX3], by simp [upd, aG, aZero],
    by simp [upd, aG, VG.Impl.Rsa.X86.Recover.aN], by simp [upd, sK, sOkDE]⟩

/-- `m = ⌊a / n⌋` and `r = a mod n`, wide, with `n` wide, and whether `m < n`. -/
theorem divA_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {a n : Nat}
    (h : KS g s0 A [aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wA, wZ2] V [sOkDE] s)
    (ha : AW wA = a) (hz : AW wZ2 = 0) (hn : A VG.Impl.Rsa.X86.Recover.aN = n) (pos : 0 < n) :
    WP isa divA s fun t => ∃ AW',
      KS g s0 A [aZero, VG.Impl.Rsa.X86.Recover.aN] AW' [wA, wR, wN, wZ2] (upd V sLt (b2n (decide (a / n < n))))
        [sLt, sOkDE] t ∧
      AW' wA = a / n ∧ AW' wR = a % n ∧ AW' wN = n ∧ AW' wZ2 = 0 := by
  unfold divA wideN
  simp only [seqs]
  refine WP.seq (WP.seq (WP.mono (h.zeroWide_W (j := wN) (by decide) (by decide)) fun u1 ⟨h1, z1⟩ => ?_))
  have h1' := h1.mono (liveW' := [wA, wZ2]) (AW' := upd AW wN 0) (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (h1'.widen (k := wN) (a := VG.Impl.Rsa.X86.RecoverDetRt.aN) (by decide) (by decide) (by decide) z1
    (by decide) (by decide)) fun u2 ⟨h2, top⟩ => ?_
  refine WP.seq (WP.mono (h2.div_W (q := wA) (r := wR) (d := wN) (t := wDt) (by simp) (by simp) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) top (by decide) (by decide)
    (by decide)) fun u3 ⟨Q, R, h3, res⟩ => ?_)
  have hn' : A VG.Impl.Rsa.X86.RecoverDetRt.aN = n := hn
  have vn : upd (upd AW wN 0) wN (A VG.Impl.Rsa.X86.RecoverDetRt.aN) wN = n := by rw [upd_self]; exact hn
  have ha' : AW 17 = a := ha
  have va : upd (upd AW wN 0) wN (A VG.Impl.Rsa.X86.RecoverDetRt.aN) wA = a := by simp [upd, wA, wN, ha']
  obtain ⟨eQ, eR⟩ := res (by rw [vn]; exact pos)
  rw [vn, va] at eQ eR
  refine WP.seq (WP.mono (h3.subWrap_W (o := wT) (a := wA) (b := wN) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun u4 ⟨h4, b4⟩ => ?_)
  refine WP.mono (h4.storeSlot (d := sLt) (by decide) .ebx) fun t ⟨ht, _, _⟩ => ?_
  rw [b4] at ht
  refine ⟨_, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, ?_⟩), ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · simp [upd, wA, wR, wN, eQ, hn']
    · simp [upd, sLt, sOkDE]
  · simp [upd, wT, wA, wR, eQ]
  · simp [upd, wT, wR, eR]
  · simp [upd, wT, wA, wR, wN, hn']
  · have hz' : AW 18 = 0 := hz
    simp [upd, wT, wA, wR, wN, wZ2, hz']

end VG.Proof.Rsa.X86.Recover
