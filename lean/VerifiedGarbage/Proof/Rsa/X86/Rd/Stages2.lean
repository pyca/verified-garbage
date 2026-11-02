module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Sqrt
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Product
import VerifiedGarbage.Proof.Rsa.X86.Rd.Count
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFlags
import VerifiedGarbage.Proof.Rsa.X86.RvDivSet
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Appendix C.2 on i686: the second division, `b² - 4 n` and the factors -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Rsa (b2n b2n_le sub32)

theorem ite_b2n (p : Prop) [Decidable p] : (if p then 1 else 0) = b2n (decide p) := by
  unfold b2n; by_cases h : p <;> simp [h]

/-- `m + 1` and `n - r`, narrow, their quotient and remainder, and whether it is zero. -/
theorem divB_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n m r : Nat}
    (h : KS g s0 A [aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wA, wR, wN, wZ2] V [sLt, sOkDE] s)
    (hz : A aZero = 0) (hn : A VG.Impl.Rsa.X86.Recover.aN = n) (hm : AW wA = m) (hr : AW wR = r)
    (hnW : AW wN = n) (hz2 : AW wZ2 = 0) :
    WP isa divB s fun t => ∃ Q R A' AW',
      KS g s0 A' [aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW' [wN, wZ2]
        (upd V sExact (b2n (decide (R = 0)))) [sExact, sLt, sOkDE] t ∧
      (0 < (m % 2 ^ (32 * g.w) + 1) % 2 ^ (32 * g.w) →
        Q = sub32 g.w n (r % 2 ^ (32 * g.w)) / ((m % 2 ^ (32 * g.w) + 1) % 2 ^ (32 * g.w)) ∧
        R = sub32 g.w n (r % 2 ^ (32 * g.w)) % ((m % 2 ^ (32 * g.w) + 1) % 2 ^ (32 * g.w))) ∧
      A' aD = Q ∧ A' aOne1 = 1 ∧ A' aZero = 0 ∧ A' VG.Impl.Rsa.X86.Recover.aN = n ∧
      AW' wN = n ∧ AW' wZ2 = 0 := by
  have hz' : A 10 = 0 := hz
  have hn' : A 32 = n := hn
  have hm' : AW 17 = m := hm
  have hr' : AW 20 = r := hr
  have hnW' : AW 19 = n := hnW
  have hz2' : AW 18 = 0 := hz2
  have h0 := (h.view (j := wA) (by simp)).view (j := wR) (by simp)
  -- The low halves, narrow.
  have c0 : KS g s0 (upd (upd (upd (upd (fun _ => 0) aZero 0) VG.Impl.Rsa.X86.Recover.aN n) aM
      (m % 2 ^ (32 * g.w))) aRlo (r % 2 ^ (32 * g.w))) [aM, aRlo, aZero, VG.Impl.Rsa.X86.Recover.aN]
      AW [wN, wZ2] V [sLt, sOkDE] s :=
    h0.mono (fun j hj => ⟨by revert hj; revert j; decide, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> simp [upd, aM, aRlo, aZero, wA, wR, hz', hn', hm', hr', VG.Impl.Rsa.X86.Recover.aN]⟩)
      (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  unfold divB
  simp only [seqs]
  refine WP.seq (WP.mono (c0.copy_w (o := aOne1) (a := aZero) (by decide) (by simp) (by decide) (by decide))
    fun u1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.setOne_w (j := aOne1) (by simp) (by decide)) fun u2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.subWrap (o := aD) (a := VG.Impl.Rsa.X86.RecoverDetRt.aN) (b := aRlo) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun u3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.add_w (o := aM1) (a := aM) (b := aOne1) (by decide) (by decide) (by simp)
    (by decide)) fun u4 ⟨h4, _⟩ => ?_)
  -- `m + 1`, `n - r` and one.
  have c4 : KS g s0 (upd (upd (upd (upd (upd (fun _ => 0) aZero 0) VG.Impl.Rsa.X86.Recover.aN n) aD
      (sub32 g.w n (r % 2 ^ (32 * g.w)))) aM1 ((m % 2 ^ (32 * g.w) + 1) % 2 ^ (32 * g.w))) aOne1 1)
      [aM1, aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wN, wZ2] V [sLt, sOkDE] u4 :=
    h4.mono (fun j hj => ⟨by revert hj; revert j; decide, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [upd, aM, aRlo, aZero, aD, aM1, aOne1, VG.Impl.Rsa.X86.Recover.aN,
          VG.Impl.Rsa.X86.RecoverDetRt.aN]⟩)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (zeroAbove_ok c4.rt (j := aM1) (by decide)) fun u5 ⟨_, k5, e5, top5, r5⟩ => ?_)
  rw [kw_nar] at k5 e5 top5
  have h5 := c4.write_w k5 (by decide) (by simp) (r5.mono (by decide)) (e5.trans (c4.arrs aM1 (by simp)))
    (by decide) (by simp)
  rw [upd_noop rfl] at h5
  refine WP.seq (WP.mono (h5.div_w (q := aD) (r := aRem) (d := aM1) (t := aDt) (by simp) (by simp) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) top5 (by decide)
    (by decide) (by decide)) fun u6 ⟨Q, R, h6, res⟩ => ?_)
  refine WP.mono (h6.eq_w (d := sExact) (a := aRem) (b := aZero) (by simp) (by simp) (by decide)) fun t ht => ?_
  refine ⟨Q, R, _, _, ht.mono (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨by revert hd; revert d; decide, ?_⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · simp [upd, aRem, aZero, aD, aM1, aOne1, ite_b2n, VG.Impl.Rsa.X86.Recover.aN]
    · simp [upd, sLt, sExact]
    · simp [upd, sOkDE, sExact]
  · intro pos
    obtain ⟨e1, e2⟩ := res (by simpa [upd, aM1, aD, aOne1] using pos)
    simp only [upd, aM1, aD, aOne1, ↓reduceIte] at e1 e2
    exact ⟨by simpa using e1, by simpa using e2⟩
  · simp [upd, aRem, aD]
  · simp [upd, aRem, aD, aOne1]
  · simp [upd, aRem, aD, aOne1, aZero, aM1, VG.Impl.Rsa.X86.Recover.aN]
  · simp [upd, aRem, aD, aOne1, aM1, VG.Impl.Rsa.X86.Recover.aN]
  · exact hnW
  · exact hz2

/-- The square's set-up: `b = q + 1` narrow in `aD` and `aBy` and wide in `wB`, and the sum zeroed. -/
theorem squareHead_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n q : Nat}
    (h : KS g s0 A [aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wN, wZ2] V [sExact, sLt, sOkDE] s)
    (hq : A aD = q) (h1 : A aOne1 = 1) (hz : A aZero = 0) (hnW : AW wN = n) (hz2 : AW wZ2 = 0) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.chain nar .adc aD aD aOne1 false, VG.Impl.Rsa.X86.KeyRt.copy nar aBy aD,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid wB, VG.Impl.Rsa.X86.KeyRt.copy nar (2 * wB) aD,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid wA]) s fun u => ∃ A' AW',
      KS g s0 A' [aBy, aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW' [wA, wB, wN, wZ2] V
        [sExact, sLt, sOkDE] u ∧
      A' aBy = (q + 1) % 2 ^ (32 * g.w) ∧ AW' wB = (q + 1) % 2 ^ (32 * g.w) ∧ AW' wA = 0 ∧ AW' wZ2 = 0 ∧
      A' aD = (q + 1) % 2 ^ (32 * g.w) ∧ A' aZero = 0 ∧ AW' wN = n := by
  have hq' : A 30 = q := hq
  have hz' : A 10 = 0 := hz
  have hnW' : AW 19 = n := hnW
  have hz2' : AW 18 = 0 := hz2
  simp only [seqs]
  refine WP.seq (WP.mono (h.add_w (o := aD) (a := aD) (b := aOne1) (by decide) (by simp) (by simp) (by decide))
    fun u1 ⟨k1, _⟩ => ?_)
  refine WP.seq (WP.mono (k1.copy_w (o := aBy) (a := aD) (by decide) (by simp) (by decide) (by decide))
    fun u2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.zeroWide_W (j := wB) (by decide) (by decide)) fun u3 ⟨h3, z3⟩ => ?_)
  have h3' := h3.mono (liveW' := [wN, wZ2]) (AW' := upd AW wB 0) (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h3'.widen (k := wB) (a := aD) (by decide) (by simp) (by decide) z3 (by decide)
    (by decide)) fun u4 ⟨h4, _⟩ => ?_)
  refine WP.mono (h4.zeroWide_W (j := wA) (by decide) (by decide)) fun u5 ⟨h5, _⟩ => ?_
  exact ⟨_, _, h5.mono (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩), by simp [upd, aBy, aD, hq', h1], by simp [upd, wA, wB, aD, hq', h1], by simp [upd],
    by simp [upd, wZ2, wA, wB, hz2'], by simp [upd, aBy, aD, hq', h1], by simp [upd, aBy, aZero, aD, hz'],
    by simp [upd, wN, wA, wB, hnW']⟩

/-- The arrays the product of `square` names. -/
theorem squareIdx : ProdIdx aBy wB wA wT wZ2 [aBy, aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN]
    [wA, wB, wN, wZ2] [sExact, sLt, sOkDE] :=
  ⟨by simp, by simp, by simp, by simp, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- `b = q + 1`, and `b²` (wide). -/
theorem square_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n q : Nat}
    (h : KS g s0 A [aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wN, wZ2] V [sExact, sLt, sOkDE] s)
    (hq : A aD = q) (h1 : A aOne1 = 1) (hz : A aZero = 0) (hnW : AW wN = n) (hz2 : AW wZ2 = 0) :
    WP isa square s fun t => ∃ A' AW' V',
      KS g s0 A' [aD, aZero] AW' [wA, wN] V' [sK, sExact, sLt, sOkDE] t ∧
      A' aD = (q + 1) % 2 ^ (32 * g.w) ∧ A' aZero = 0 ∧
      AW' wA = ((prodStep (32 * g.W))^[32 * g.w] ((q + 1) % 2 ^ (32 * g.w), (q + 1) % 2 ^ (32 * g.w), 0)).2.2 ∧
      AW' wN = n ∧ V' sExact = V sExact ∧ V' sLt = V sLt ∧ V' sOkDE = V sOkDE := by
  unfold square
  refine wp_seqs_snoc (WP.mono (squareHead_ok h hq h1 hz hnW hz2)
    fun u ⟨A5, AW5, h5, y5, x5, a5, z5, d5, zz5, n5⟩ => ?_)
  refine WP.mono (product_ok' squareIdx z5 h5 y5 x5 a5) fun t ht => ?_
  unfold ProdS at ht
  refine ⟨_, _, _, ht.mono (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun d hd => ⟨by revert hd; revert d; decide, rfl⟩),
    by rw [upd_ne _ _ (show aD ≠ aBy by decide)]; exact d5,
    by rw [upd_ne _ _ (show aZero ≠ aBy by decide)]; exact zz5, by simp [upd],
    by rw [upd_ne _ _ (show wN ≠ wA by decide), upd_ne _ _ (show wN ≠ wB by decide)]; exact n5,
    by simp [upd, sK, sExact], by simp [upd, sK, sLt], by simp [upd, sK, sOkDE]⟩

/-- `b² - 4 n` (wide) and whether `b² > 4 n`. -/
theorem minus4n_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n sq : Nat}
    (h : KS g s0 A [aD, aZero] AW [wA, wN] V [sK, sExact, sLt, sOkDE] s)
    (hs : AW wA = sq) (hn : AW wN = n) :
    WP isa minus4n s fun t => ∃ AW',
      KS g s0 A [aD, aZero] AW' [wR] (upd V sOk4 (b2n (!(decide (sq < ((n + n) % 2 ^ (32 * g.W) +
          (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) ||
        decide (sub32 g.W sq (((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) < 1)))))
        sqSlots t ∧
      AW' wR = sub32 g.W sq (((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) := by
  have hs' : AW 17 = sq := hs
  have hn' : AW 19 = n := hn
  unfold minus4n wideOne
  simp only [seqs]
  refine WP.seq (WP.mono (h.add_W (o := wN) (a := wN) (b := wN) (by decide) (by simp) (by simp) (by decide))
    fun u1 ⟨h1, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.add_W (o := wN) (a := wN) (b := wN) (by decide) (by simp) (by simp) (by decide))
    fun u2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (h2.zeroWide_W (j := wOne2) (by decide) (by decide)) fun u3 ⟨h3, _⟩ => ?_))
  refine WP.mono (h3.setOne_W (j := wOne2) (by simp) (by decide)) fun u4 h4 => ?_
  refine WP.seq (WP.mono (h4.subWrap_W (o := wR) (a := wA) (b := wN) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun u5 ⟨h5, b5⟩ => ?_)
  refine WP.seq (WP.mono (h5.storeSlot (d := sC1) (by decide) .ebx) fun u6 ⟨h6, _, _⟩ => ?_)
  rw [b5] at h6
  refine WP.seq (WP.mono (h6.subWrap_W (o := wT) (a := wR) (b := wOne2) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun u7 ⟨h7, b7⟩ => ?_)
  refine WP.seq (WP.mono (h7.storeSlot (d := sC2) (by decide) .ebx) fun u8 ⟨h8, _, _⟩ => ?_)
  rw [b7] at h8
  refine WP.seq (WP.mono (h8.flagOr_ok (d := sOk4) (a := sC1) (b := sC2) (by decide) (by simp) (by simp)
    (by rw [upd_ne _ _ (show sC1 ≠ sC2 by decide), upd_self]) (by rw [upd_self])) fun u9 h9 => ?_)
  refine WP.mono (h9.flagNot_ok (d := sOk4) (a := sOk4) (by decide) (by simp) (by rw [upd_self])) fun t ht => ?_
  refine ⟨_, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨by revert hd; revert d; decide, ?_⟩), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upd, wR, wA, wN, wOne2, hs', hn', sC1, sC2, sOk4, sK, sExact, sLt, sOkDE]
  · simp [upd, wR, wA, wN, wT, wOne2, hs', hn']

/-- The factors `(b + y) / 2` and `(b - y) / 2` into narrow arrays 5 and 6, and the mask of every
check into `sMask`. -/
theorem factorsD_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {b y : Nat} {okde lt ex ok4 ok5 : Bool}
    (h : KS g s0 A [aY, aD, aZero] AW [] V (sOk5 :: sqSlots) s)
    (hy : A aY = y) (hb : A aD = b) (hz : A aZero = 0) (v1 : V sOkDE = b2n okde) (v2 : V sLt = b2n lt)
    (v3 : V sExact = b2n ex) (v4 : V sOk4 = b2n ok4) (v5 : V sOk5 = b2n ok5) :
    WP isa factors s fun t => ∃ A' V',
      KS g s0 A' [5, 6, aZero] AW [] V' [VG.Impl.Rsa.X86.Recover.sMask] t ∧
      A' 5 = (b + y) % 2 ^ (32 * g.w) / 2 ∧ A' 6 = sub32 g.w b y / 2 ∧ A' aZero = 0 ∧
      V' VG.Impl.Rsa.X86.Recover.sMask = b2n ((((okde && lt) && ex) && ok4) && ok5) := by
  have hy' : A 4 = y := hy
  have hb' : A 30 = b := hb
  have hz' : A 10 = 0 := hz
  unfold factors
  simp only [seqs]
  refine WP.seq (WP.mono (h.add_w (o := 5) (a := aD) (b := aY) (by decide) (by simp) (by simp) (by simp))
    fun u1 ⟨h1, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun u2 U _ => WP.block_nil ?_)
  have h2 := h1.of_rest U.keeps (by decide) U.mem
  refine WP.seq (WP.mono (h2.half_w (j := 5) (by simp) (by rw [U.gpr]; rfl) (by simp)) fun u3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.subWrap (o := 6) (a := aD) (b := aY) (by decide) (by simp) (by simp) (by decide)
    (by decide) (by simp)) fun u4 ⟨h4, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun u5 U5 _ => WP.block_nil ?_)
  have h5 := h4.of_rest U5.keeps (by decide) U5.mem
  refine WP.seq (WP.mono (h5.half_w (j := 6) (by simp) (by rw [U5.gpr]; rfl) (by simp)) fun u6 ⟨h6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.flagAnd_ok (d := VG.Impl.Rsa.X86.Recover.sMask) (a := sOkDE) (b := sLt) (by decide)
    (by simp) (by simp) v1 v2) fun u7 h7 => ?_)
  refine WP.seq (WP.mono (h7.flagAnd_ok (d := VG.Impl.Rsa.X86.Recover.sMask) (a := VG.Impl.Rsa.X86.Recover.sMask)
    (b := sExact) (by decide) (by simp) (by simp) (by rw [upd_self]) (by rw [upd_ne _ _ (show sExact ≠ VG.Impl.Rsa.X86.Recover.sMask by decide)]; exact v3)) fun u8 h8 => ?_)
  refine WP.seq (WP.mono (h8.flagAnd_ok (d := VG.Impl.Rsa.X86.Recover.sMask) (a := VG.Impl.Rsa.X86.Recover.sMask)
    (b := sOk4) (by decide) (by simp) (by simp) (by rw [upd_self]) (by rw [upd_ne _ _ (show sOk4 ≠ VG.Impl.Rsa.X86.Recover.sMask by decide)]; exact v4)) fun u9 h9 => ?_)
  refine WP.mono (h9.flagAnd_ok (d := VG.Impl.Rsa.X86.Recover.sMask) (a := VG.Impl.Rsa.X86.Recover.sMask)
    (b := sOk5) (by decide) (by simp) (by simp) (by rw [upd_self]) (by rw [upd_ne _ _ (show sOk5 ≠ VG.Impl.Rsa.X86.Recover.sMask by decide)]; exact v5)) fun t ht => ?_
  refine ⟨_, _, ht.mono (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨by revert hd; revert d; decide, rfl⟩), ?_, ?_, ?_, by simp [upd]⟩
  · simp [upd, aD, aY, hy', hb']
  · simp [upd, aD, aY, hy', hb']
  · simp [upd, aZero, hz']

end VG.Proof.Rsa.X86.Recover
