module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.Sub32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Appendix C.2 by words on i686: `d e - 1`, the GCD's inputs and the factors

The pieces of `det` around the word-level ones, as `RecoverDet`'s model computes them.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
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
theorem gcdSetW_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {u x : Nat}
    (h : KS g s0 A [aU, aX2, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sOkDE] s)
    (hu : A aU = u) (hx : A aX2 = x) :
    WP isa gcdSet s fun t => ∃ A',
      KS g s0 A' [aGm, aGx, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sOkDE] t ∧
      A' aGm = u ∧ A' aGx = x ∧
      A' VG.Impl.Rsa.X86.Recover.aN = A VG.Impl.Rsa.X86.Recover.aN := by
  have hu' : A 24 = u := hu
  have hx' : A 20 = x := hx
  unfold gcdSet
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := aGm) (a := aU) (by decide) (by simp) (by decide) (by decide))
    fun u1 ⟨h1, _, _⟩ => ?_)
  refine WP.mono (h1.copy_w (o := aGx) (a := aX2) (by decide) (by simp) (by decide) (by decide)) fun u2 ⟨h2, _, _⟩ => ?_
  refine ⟨_, h2.mono (live' := [aGm, aGx, VG.Impl.Rsa.X86.Recover.aN]) (ls' := [sOkDE])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨by revert hd; revert d; decide, rfl⟩), ?_, ?_, ?_⟩
  · simp [upd, aGm, aGx, aU, hu']
  · simp [upd, aGx, aGm, aX2, hx']
  · simp [upd, aGx, aGm, VG.Impl.Rsa.X86.Recover.aN]

theorem ite_b2n (p : Prop) [Decidable p] : (if p then 1 else 0) = b2n (decide p) := by
  unfold b2n; by_cases h : p <;> simp [h]

/-- The factors `(b + y) / 2` and `(b - y) / 2` into narrow arrays 5 and 6, and the mask of every
check into `sMask`. -/
theorem factorsW_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {b y : Nat} {okde lt ex ok4 ok5 : Bool}
    (h : KS g s0 A [aY, aD, aZero] AW [] V (sOk5 :: sqSlotsW) s)
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
