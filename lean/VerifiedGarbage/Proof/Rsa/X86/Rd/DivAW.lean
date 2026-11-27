module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Proof.Bignum.ShiftStages
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.Sub32
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.TwosW
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivQ
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivBW
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Rsa.X86.Rd.ProdW`, which the modules that import this one used -/

section

/-! ### `Rsa.X86.Rd.DetPartsW`, which the modules that import this one used -/

section

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
  refine ⟨_, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], ?_⟩), ?_, ?_⟩
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

end

end

/-! # Prime recovery's products on i686

`RecoverDetRt.aProduct`: `a = (2^k x) gcd(u, x)` modulo `2^(32 W)` by word rows of `W + 1` words;
`square`: `b = q + 1` and `b²` over `2 w` words (`WordModRt.mulWide`), the wide array's words above
zero; `minus4n`: `b² - 4 n` and whether `b² > 4 n`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa (b2n sub32)
open VG.Impl.Mont.X86 (sc at_)

/-! ## `b² - 4 n` -/

/-- `b² - 4 n` (wide) and whether `b² > 4 n`. -/
theorem minus4n_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n sq : Nat}
    (h : KS g s0 A [aD, aZero] AW [wA, wN] V [sExact, sLt, sOkDE] s) (hs : AW wA = sq) (hn : AW wN = n) :
    WP isa minus4n s fun t => ∃ AW' V',
      KS g s0 A [aD, aZero] AW' [wR] V' [sOkDE, sLt, sExact, sOk4] t ∧
      V' sOk4 = b2n (!(decide (sq < ((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) ||
        decide (sub32 g.W sq (((n + n) % 2 ^ (32 * g.W) + (n + n) % 2 ^ (32 * g.W)) % 2 ^ (32 * g.W)) < 1))) ∧
      V' sOkDE = V sOkDE ∧ V' sLt = V sLt ∧ V' sExact = V sExact ∧
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
  refine ⟨_, _, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨by revert hd; revert d; decide, rfl⟩),
    by simp [upd, wR, wA, wN, wOne2, hs', hn', sOk4],
    by simp [upd, sC1, sC2, sOk4, sOkDE], by simp [upd, sC1, sC2, sOk4, sLt],
    by simp [upd, sC1, sC2, sOk4, sExact], ?_⟩
  simp [upd, wR, wA, wN, wT, wOne2, hs', hn']


/-! ## `b²` -/

section
open VG.Proof.Rsa.X86.WordRt
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Impl.Rsa.X86.KeyRt (Lay zeroWide)
open VG.Impl.Rsa.X86.WordModRt (oJ)
variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- Words `2 w` and `2 w + 1` of `[o]` (in array `o + 1`) zero. -/
abbrev TopZ (B : Addr) (len o : Nat) (u : State) : Prop :=
  w32 u.mem B (arr (kw len) o + 4 * (2 * kw len)) = 0 ∧ w32 u.mem B (arr (kw len) o + 4 * (2 * kw len + 1)) = 0

/-- `mulWide`'s start clears words `2 w` and `2 w + 1` of `[o]`. -/
theorem topZ_init {s : State} (h : RtWs L s B Z len N) {o : Nat} (ho : o + 1 < N) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.seqs [zeroWide L o, zeroWide L (o + 1),
      .block [.mov .eax (.imm 0), .store (sc oJ) .eax]]) s (TopZ B len o) := by
  have hdr := h.ws.hdr_le
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h (j := o) (by omega_using [ho])) fun u₁ ⟨h₁, _, _, _⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h₁ (j := o + 1) ho) fun u₂ ⟨h₂, _, z₂, _⟩ => ?_)
  refine wp_movS rfl fun u₃ U₃ _ => ?_
  obtain h₃ := h₂.keep U₃.keeps (by decide) (by decide) (by rw [U₃.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlotZ_ok h₃ (d := oJ) (by decide) .eax) fun u₄ ⟨_, k₄, _, _, _⟩ => ?_
  rw [U₃.mem] at k₄
  obtain fit := h.ws.fit64 (j := o + 1) ho
  have kwe : kw len = 2 * Spec.Rsa.modulusWords len := rfl
  have wpos := h.kw_pos
  obtain e : ∀ i, i < kw len + 1 → w32 u₄.mem B (arr (kw len) (o + 1) + 4 * i) = 0 := fun i hi => by
    rw [k₄.word (j := o + 1) (i := i) (by simp only [S]; omega_using [hi]) (by simp) (by decide) fit]
    exact w32_of_val32_zero z₂ hi
  obtain ea : arr (kw len) (o + 1) = arr (kw len) o + 4 * (kw len + 2) := arr_succ ..
  obtain e1 := e (kw len - 2) (by omega_using [])
  obtain e2 := e (kw len - 1) (by omega_using [])
  rw [ea, Nat.add_assoc, ← Nat.mul_add, show kw len + 2 + (kw len - 2) = 2 * kw len by omega_using [kwe, wpos]] at e1
  rw [ea, Nat.add_assoc, ← Nat.mul_add, show kw len + 2 + (kw len - 1) = 2 * kw len + 1 by omega_using [wpos]] at e2
  exact ⟨e1, e2⟩

/-- `mulWide` leaves words `2 w` and `2 w + 1` of `[o]` zero. -/
theorem mulWideTop_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat}
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulWide L o a b) s (TopZ B len o) := by
  obtain init := WP.and (rowsInit_ok h (a := a) (b := b) ho) (topZ_init h ho)
  have wpos := h.kw_pos
  unfold VG.Impl.Rsa.X86.WordModRt.mulWide
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs] at init ⊢
  rw [WP.seq_iff] at init
  refine WP.seq (WP.mono init fun u₁ w₁ => ?_)
  rw [WP.seq_iff] at w₁
  refine WP.seq (WP.mono w₁ fun u₂ w₂ => ?_)
  refine WP.seq (WP.mono w₂ fun u₄ ⟨I₀, Z₀⟩ => ?_)
  refine WP.loop (M := isa) (fun n u => ∃ j, n = kw len - j ∧ j < kw len ∧
    RowsI L s B Z len N o a b j false u ∧ TopZ B len o u) ?_ _ u₄ ⟨0, rfl, wpos, I₀, Z₀⟩
  rintro n u ⟨j, rfl, hj, I, Zu⟩
  refine WP.mono (WP.and (rowsStep_ok h (rows := none) (half := false) (by simp) (by simp [VG.Proof.Rsa.X86.WordRt.rowsN, VG.Proof.Rsa.X86.WordRt.rowW])
    ho ha hb hao hao1 hbo hbo1 (by simpa [VG.Proof.Rsa.X86.WordRt.rowsN, VG.Proof.Rsa.X86.WordRt.rowW] using hj) I)
    (mulRow_ok I.ws (rows := none) (half := false) ho ha hb hao hao1 I.cnt hj (by simp)))
    fun v ⟨⟨zv, I'⟩, ⟨_, _, _, wv, _⟩⟩ => ?_
  simp only [VG.Proof.Rsa.X86.WordRt.rowsN, VG.Proof.Rsa.X86.WordRt.rowW] at zv wv
  obtain Z' : TopZ B len o v :=
    ⟨by rw [wv _ (.inr (by omega_using [hj])) (by omega_using [])]; exact Zu.1, by rw [wv _ (.inr (by omega_using [hj])) (by omega_using [])]; exact Zu.2⟩
  by_cases e : j + 1 = kw len
  · exact .inl ⟨by simp only [eval, zv, e, decide_true, Option.map_some, Bool.not_true], Z'⟩
  · exact .inr ⟨by simp only [eval, zv, e, decide_false, Option.map_some, Bool.not_false], kw len - (j + 1),
      by omega_using [hj], j + 1, rfl, by omega_using [hj, e], I', Z'⟩

end

/-- `b = q + 1` (narrow) and `b²` (wide, its words above `2 w` zero). -/
theorem square_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n q : Nat}
    (h : KS g s0 A [aD, aOne1, aZero, aN] AW [wN] V [sExact, sLt, sOkDE] s)
    (hq : A aD = q) (one : A aOne1 = 1) (z : A aZero = 0) (hnW : AW wN = n) :
    WP isa square s fun t => ∃ A' AW',
      KS g s0 A' [aD, aZero] AW' [wA, wN] V [sExact, sLt, sOkDE] t ∧
      A' aD = (q + 1) % 2 ^ (32 * g.w) ∧ A' aZero = 0 ∧
      AW' wA = (q + 1) % 2 ^ (32 * g.w) * ((q + 1) % 2 ^ (32 * g.w)) ∧ AW' wN = n := by
  unfold square
  simp only [seqs]
  refine WP.seq (WP.mono (h.add_w (o := aD) (a := aD) (b := aOne1) (by decide) (by simp) (by simp) (by decide))
    fun u ⟨h₁, _⟩ => ?_)
  rw [hq, one] at h₁
  have nw := h₁.ws.workspace.nowrap
  obtain f34 := h₁.ws.arr_fit (j := 34) (by decide)
  obtain f35 := h₁.ws.arr_fit (j := 35) (by decide)
  simp only [S] at f34 f35
  refine WP.mono (WP.and (VG.Proof.Rsa.X86.WordRt.mulWide_ok h₁.rt (o := 2 * wA) (a := aD) (b := aD)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (mulWideTop_ok h₁.rt (o := 2 * wA) (a := aD) (b := aD)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    fun t ⟨⟨_, k, e, r⟩, z1, z2⟩ => ?_
  rw [kw_nar] at k e z1 z2
  have k' : Keep g.B g.w [34, 35] [VG.Impl.Rsa.X86.WordModRt.oJ] u.mem t.mem := k
  obtain bD := h₁.arrs aD (by simp)
  rw [upd_self] at bD
  rw [bD] at e
  change w32 t.mem g.B (arr g.w 34 + 4 * (2 * g.w)) = 0 at z1
  change w32 t.mem g.B (arr g.w 34 + 4 * (2 * g.w + 1)) = 0 at z2
  change val32 t.mem g.B (arr g.w 34) (2 * g.w) = _ at e
  obtain value : num t.mem g.B g.W wA = (q + 1) % 2 ^ (32 * g.w) * ((q + 1) % 2 ^ (32 * g.w)) := by
    change val32 t.mem g.B (arr g.W 17) (2 * g.w + 1 + 1) = _
    rw [arr_W' g 17, show (2 * 17 : Nat) = 34 from rfl, val32_succ, val32_succ, z1, z2, e]
    simp
  obtain ds : ∀ d ∈ [VG.Impl.Rsa.X86.WordModRt.oJ], SlotOk d := by decide
  obtain aw := h₁.arrs_w k' (by decide) ds
  obtain awW := h₁.arrsW_w k' (by decide) ds
  refine ⟨_, upd AW wA ((q + 1) % 2 ^ (32 * g.w) * ((q + 1) % 2 ^ (32 * g.w))),
    h₁.core k' (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h₁.ws.arr_fit (by decide)
      · exact h₁.ws.arr_fit (by decide)) ds (r.mono (by decide))
      (fun j hj => aw j (by simp at hj ⊢; omega_using [hj])) (by decide)
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · rw [upd_self]; exact value
        · rw [upd_ne _ _ (by decide)]; exact awW _ (by simp))
      (by decide) (h₁.sl_keep k' (by decide)) h₁.ls_ok, upd_self .., ?_, upd_self .., ?_⟩
  · rw [upd_ne _ _ (by decide)]; exact z
  · rw [upd_ne _ _ (by decide)]; exact hnW


/-! ## `a`'s rows -/

section
open VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc bytesB_ok)
open VG.Proof.Rsa.X86.WordRt (RowI rowLoop_ok RowsI keep_of_two oJ_val)
open VG.Impl.Rsa.X86.WordModRt (oJ)
variable {B : Addr} {Z len N len' N' : Nat}

/-- Row `j` of `aProduct` (at `oJ`): `[o]` from word `j`, `W + 1` words (`W` of the wide layout),
becomes its words `j, …, j + W - 1` plus `a b_j`; the count `j + 1`, compared with `w` (the narrow
layout's). -/
theorem rowWRow_ok {s : State} (h : RtWs wid s B Z len N) (hn : RtWs nar s B Z len' N') {o a b j : Nat}
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1)
    (hj : slot s.mem B oJ = j) (hjw : j < kw len) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.rowW o a b) s fun v => RtWs wid v B Z len N ∧
      RtWs nar v B Z len' N' ∧ Keep B (kw len) [o, o + 1] [oJ] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) o + 4 * j) (kw len + 1) =
        val32 s.mem B (arr (kw len) a) (kw len) * w32 s.mem B (arr (kw len) b + 4 * j) +
          val32 s.mem B (arr (kw len) o + 4 * j) (kw len) ∧
      (∀ i, (i < j ∨ j + kw len + 1 ≤ i) → i < 2 * (kw len + 2) →
        w32 v.mem B (arr (kw len) o + 4 * i) = w32 s.mem B (arr (kw len) o + 4 * i)) ∧
      slot v.mem B oJ = j + 1 ∧ v.zf = some (decide (j + 1 = kw len')) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  obtain fo := h.ws.arr_fit ho
  obtain fa := h.ws.arr_fit ha
  obtain fb := h.ws.arr_fit hb
  have hdr := h.ws.hdr_le
  obtain hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  obtain hkw' := VG.Proof.Rsa.X86.KeyRt.kw_bound hn.lenLe
  have wpos := h.kw_pos
  simp only [S] at fo fa fb
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  obtain eo1 : arr (kw len) (o + 1) = arr (kw len) o + 4 * (kw len + 2) := by
    rw [VG.Proof.Rsa.X86.Keys.arr_succ]
  obtain gsep : arr (kw len) a + 4 * kw len ≤ arr (kw len) o + 4 * j ∨
      arr (kw len) o + 4 * j + 4 * (kw len + 1) ≤ arr (kw len) a := by
    rcases Nat.lt_or_gt_of_ne hao with hlt | hgt
    · have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hlt; simp only [S] at this; omega_using [this]
    · have h2 : o + 1 < a := by omega_using [hao1, hgt]
      have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) h2; simp only [S] at this; omega_using [hjw, eo1, this]
  have ws := h.rt
  unfold VG.Impl.Rsa.X86.RecoverDetRt.rowW
  simp only [VG.Impl.Rsa.X86.Keys.seqs, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebx) (t := .edx) (j := b) (by decide) (by decide)
    (by omega_using [nw, fb]) fun u₁ K₁ m₁ p₁ _ => ?_)
  obtain h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sc h₁.ws.workspace (d := oJ) (by rw [oJ_val]; omega_using [hdr])) fun u₂ U₂ _ =>
    wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => ?_
  obtain e₄ : (u₄.gpr .eax).toNat = 4 * j := by
    rw [U₄.gpr, BitVec.toNat_add, U₃.gpr, BitVec.toNat_add, U₂.gpr, m₁]
    change (((w32 s.mem B oJ) + w32 s.mem B oJ) % 2 ^ 32 + ((w32 s.mem B oJ) + w32 s.mem B oJ) % 2 ^ 32) % 2 ^ 32 = _
    rw [show w32 s.mem B oJ = j from hj]; omega_using [hjw, hkw]
  obtain p₅ : PtrAt u₅ B .ebx (arr (kw len) b + 4 * j) := by
    rw [PtrAt, U₅.gpr, BitVec.toNat_add, U₄.other .ebx (by decide), U₃.other .ebx (by decide),
      U₂.other .ebx (by decide), p₁, e₄]
    have := B.isLt; omega_using []
  obtain K₅ : Keeps [.eax, .ebx, .edx] s u₅ := (K₁.mono (by decide)).trans
    (((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide))).trans
      ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))))
  obtain m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  refine wp_movS (readSrc_ptr (ws.of_keeps K₅) p₅ (d := 0) (by omega_using [hjw, fb])) fun u₆ U₆ _ => ?_
  obtain K₆ : Keeps [.eax, .ebx, .ecx, .edx] s u₆ := (K₅.mono (by decide)).trans (U₆.keeps.mono (by decide))
  obtain h₆ := h.keep K₆ (by decide) (by decide) (by rw [U₆.mem, m₅]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₆) h₆.lenLe h₆.edi (r := .ebp) (t := .edx) (j := o) (by decide) (by decide)
    (by omega_using [nw, fo, eo1]) fun u₇ K₇ m₇ p₇ _ => wp_addS rfl fun u₈ U₈ _ => ?_
  obtain p₈ : PtrAt u₈ B .ebp (arr (kw len) o + 4 * j) := by
    rw [PtrAt, U₈.gpr, BitVec.toNat_add, p₇, K₇.1 .eax (by decide), U₆.other .eax (by decide), U₅.other .eax (by decide), e₄]
    have := B.isLt; omega_using []
  obtain K₈ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₈ := (K₆.mono (by decide)).trans
    ((K₇.mono (by decide)).trans (U₈.keeps.mono (by decide)))
  obtain h₈ := h.keep K₈ (by decide) (by decide) (by rw [U₈.mem, m₇, U₆.mem, m₅]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₈) h₈.lenLe h₈.edi (r := .esi) (t := .edx) (j := a) (by decide) (by decide)
    (by omega_using [nw, fa]) fun u₉ K₉ m₉ p₉ _ => bytesB_ok ((lenSrc h₈).keep K₉ (by decide) m₉) h.lenLe fun u₁₀ K₁₀ m₁₀ e₁₀ =>
      wp_movS rfl fun u₁₁ U₁₁ _ => WP.block_nil ?_
  obtain m₁₁ : u₁₁.mem = s.mem := by rw [U₁₁.mem, m₁₀, m₉, U₈.mem, m₇, U₆.mem, m₅]
  obtain bj : (u₁₁.gpr .ecx).toNat = w32 s.mem B (arr (kw len) b + 4 * j) := by
    rw [U₁₁.other _ (by decide), K₁₀.1 _ (by decide), K₉.1 _ (by decide), U₈.other _ (by decide),
      K₇.1 _ (by decide), U₆.gpr, m₅, Nat.add_zero]
  obtain K₁₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u₁₁ := (K₈.mono (by decide)).trans
    (((K₉.mono (by decide)).trans (K₁₀.mono (by decide))).trans (U₁₁.keeps.mono (by decide)))
  obtain I₀ : RowI u₁₁ B (arr (kw len) a) (arr (kw len) o + 4 * j) (kw len) 0 u₁₁ :=
    ⟨by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₁.other _ (by decide), K₁₀.1 _ (by decide)]; exact p₉,
      by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₁.other _ (by decide), K₁₀.1 _ (by decide),
        K₉.1 _ (by decide)]; exact p₈,
      by apply BitVec.eq_of_toNat_eq
         rw [U₁₁.other _ (by decide), e₁₀, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hkw])],
      rfl, Keeps.refl _ _, Outside.refl _ _ _ _, by rw [U₁₁.gpr]; simp [val32]⟩
  refine WP.seq (WP.mono (rowLoop_ok (ws.of_keeps K₁₁) nw (by omega_arith) (by omega_arith) (by omega_using [gsep]) (by omega_using [hkw]) wpos I₀)
    fun u I => ?_)
  -- The carry, `edi`, and the count.
  obtain wsu : Ws u B Z := (ws.of_keeps K₁₁).of_wr I.keep.2.2
  refine wp_storeS (ea_ptr wsu I.bp (d := 0) (by omega_arith)) (ws_write wsu (by omega_arith)) fun t₁ M₁ => ?_
  obtain O₁ := writeW32_outside u.mem B (d := arr (kw len) o + 4 * j + 4 * kw len + 0) (u.gpr .ebx) (by omega_arith)
  rw [← M₁.mem] at O₁
  obtain Orow : Outside B (arr (kw len) o + 4 * j) (4 * (kw len + 1)) s.mem t₁.mem := by
    rw [← m₁₁]; exact (I.out.mono (by omega_using []) (by omega_using [])).trans (O₁.mono (by omega_using []) (by omega_using []))
  obtain K₁ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t₁ :=
    K₁₁.trans ((I.keep.mono (by decide)).trans (M₁.keeps _))
  obtain ca := h.wsArg.keep K₁ₜ (by decide) (Orow.mono (Nat.zero_le _) (by omega_arith))
  simp only [restoreEdi, List.cons_append, List.nil_append]
  refine wp_movS ca.readSrc fun t₂ T₂ _ => ?_
  obtain K₂ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₂ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi])
      ((K₁ₜ.trans (T₂.keeps.mono (by decide))).mono (by decide)) (T₂.gpr.trans h.edi_eq.symm)
  obtain Z₂ : Outside B 0 Z s.mem t₂.mem := by rw [T₂.mem]; exact Orow.mono (Nat.zero_le _) (by omega_arith)
  obtain h₂ : RtWs wid t₂ B Z len N := h.keep K₂ₜ (by decide) (by decide) Z₂
  obtain hn₂ : RtWs nar t₂ B Z len' N' := hn.keep K₂ₜ (by decide) (by decide) Z₂
  obtain hoJ : oJ + 4 ≤ arr (kw len) o + 4 * j := by rw [oJ_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega_using []
  obtain oj₂ : slot t₂.mem B oJ = j := by
    rw [slot, T₂.mem, Orow.w32 (.inl hoJ) (by rw [oJ_val]; omega_using [])]; exact hj
  refine wp_movS (readSrc_sc h₂.ws.workspace (d := oJ) (by rw [oJ_val]; omega_using [hdr])) fun t₃ T₃ _ =>
    wp_addS rfl fun t₄ T₄ _ => ?_
  obtain e₄' : (t₄.gpr .eax).toNat = j + 1 := by
    rw [T₄.gpr, BitVec.toNat_add, T₃.gpr]
    change (w32 t₂.mem B oJ + 1) % 2 ^ 32 = _
    rw [show w32 t₂.mem B oJ = j from oj₂]; omega_using [e₄]
  obtain K₄ₜ : Keeps [.eax] t₂ t₄ := (T₃.keeps.mono (by decide)).trans (T₄.keeps.mono (by decide))
  obtain m₄₂ : t₄.mem = t₂.mem := by rw [T₄.mem, T₃.mem]
  obtain h₄ := h₂.keep K₄ₜ (by decide) (by decide) (by rw [m₄₂]; exact Outside.refl _ _ _ _)
  obtain hn₄ := hn₂.keep K₄ₜ (by decide) (by decide) (by rw [m₄₂]; exact Outside.refl _ _ _ _)
  refine wp_storeS (h₄.ws.workspace.ea (by rw [oJ_val]; omega_using [hdr])) (h₄.ws.workspace.write (by rw [oJ_val]; omega_using [hdr]))
    fun t₅ M₅ => ?_
  obtain O₅ := writeW32_outside t₄.mem B (d := oJ) (t₄.gpr .eax) (by rw [oJ_val]; omega_using [])
  rw [← M₅.mem] at O₅
  obtain h₅ : RtWs wid t₅ B Z len N := h₄.keep (M₅.keeps []) (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by rw [oJ_val]; omega_using [hdr]))
  obtain hn₅ : RtWs nar t₅ B Z len' N' := hn₄.keep (M₅.keeps []) (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by rw [oJ_val]; omega_using [hdr]))
  obtain K₅ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₅ := K₂ₜ.trans ((K₄ₜ.mono (by decide)).trans (M₅.keeps _))
  obtain m₁ : t₁.mem = u.mem.writeW (off B (arr (kw len) o + 4 * j + 4 * kw len)) (u.gpr .ebx) := by
    rw [M₁.mem, Nat.add_zero]
  obtain m₁₄ : t₁.mem = t₄.mem := by rw [m₄₂, T₂.mem]
  obtain kk : Keep B (kw len) [o, o + 1] [oJ] s.mem t₁.mem :=
    keep_of_two (w := kw len) (o := o) Orow (by omega_using []) (by simp only [S]; omega_arith) (by simp) (by simp)
  obtain ax₅ : (t₅.gpr .eax).toNat = j + 1 := by rw [M₅.gpr]; exact e₄'
  refine bytesB_ok (lenSrc hn₅) hn.lenLe fun t₆ K₆ m₆ e₆ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t₇ U₇ => wp_cmp fun v F _ z => WP.block_nil ?_
  obtain Fk : Keeps [] t₇ v := ⟨fun r _ => by rw [F.gpr], F.rd, F.wr⟩
  obtain K₇ : Keeps [.ecx] t₅ v := (K₆.trans (U₇.keeps.mono (by decide))).trans (Fk.mono (by simp))
  obtain mv : v.mem = t₅.mem := by rw [F.mem, U₇.mem, m₆]
  obtain ecx : (t₇.gpr .ecx).toNat = kw len' := by
    have kwe : kw len' = 2 * Spec.Rsa.modulusWords len' := rfl
    rw [U₇.gpr, BitVec.toNat_ushiftRight, e₆, Nat.shiftRight_eq_div_pow]; omega_using []
  obtain eax : (t₇.gpr .eax).toNat = j + 1 := by
    rw [U₇.other _ (by decide), K₆.1 _ (by decide)]; exact ax₅
  refine ⟨h₅.keep K₇ (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _),
    hn₅.keep K₇ (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _), ?_, ?_, ?_, ?_, ?_,
    (K₅ₜ.trans (K₇.mono (by decide))).mono (by decide)⟩
  · rw [mv]; refine kk.trans ?_; rw [m₁₄]; exact Keep.of_slot O₅ (by simp)
  · have hv : val32 v.mem B (arr (kw len) o + 4 * j) (kw len + 1) =
        val32 u.mem B (arr (kw len) o + 4 * j) (kw len) + 2 ^ (32 * kw len) * (u.gpr .ebx).toNat := by
      rw [mv, O₅.val32 (.inr hoJ) (by omega_arith), ← m₁₄, val32_succ, m₁, w32_write_self,
        (writeW32_outside u.mem B (d := arr (kw len) o + 4 * j + 4 * kw len) (u.gpr .ebx) (by omega_arith)).val32
          (.inl (by omega_using [])) (by omega_arith)]
    rw [hv, I.val, bj, m₁₁]
  · intro i hi1 hi2
    obtain hoJ0 : oJ + 4 ≤ arr (kw len) o := by rw [oJ_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega_using []
    rw [mv, O₅.w32 (.inr (by omega_using [hoJ0])) (by omega_arith), ← m₁₄]
    exact Orow.w32 (by omega_arith) (by omega_arith)
  · rw [slot, mv, M₅.mem, w32_write_self, e₄']
  · rw [z]
    congr 1
    by_cases e : j + 1 = kw len'
    · rw [decide_eq_true e, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, eax, ecx, e, show BitVec.toNat (0 : BitVec 32) = 0 from rfl]; omega_using [hkw']
    · rw [decide_eq_false e, beq_eq_false_iff_ne]
      intro hc; have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_sub, eax, ecx] at this; simp at this; omega_arith


/-- A row of `aProduct`: `RowsI` of one more row, and whether it was the last (the `w`th). -/
theorem rowsStepW_ok {s u : State} (h : RtWs wid s B Z len N) {o a b j : Nat}
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) (hw : kw len' ≤ kw len) (hj : j < kw len')
    (I : RowsI wid s B Z len N o a b j false u) (In : RtWs nar u B Z len' N') :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.rowW o a b) u fun v =>
      v.zf = some (decide (j + 1 = kw len')) ∧ RowsI wid s B Z len N o a b (j + 1) false v ∧
      RtWs nar v B Z len' N' := by
  obtain fitb := h.ws.fit64 hb
  obtain fita := h.ws.fit64 ha
  obtain fo := h.ws.arr_fit ho
  simp only [S] at fo
  have Iv := I.val
  simp only [VG.Proof.Rsa.X86.WordRt.rowW] at Iv
  refine WP.mono (rowWRow_ok I.ws In ho ha hb hao hao1 I.cnt (by omega_using [hw, hj]))
    fun v ⟨hv, hnv, kv, ev, wv, cv, zv, Kv⟩ => ⟨zv, ?_, hnv⟩
  obtain Ia : val32 u.mem B (arr (kw len) a) (kw len) = val32 s.mem B (arr (kw len) a) (kw len) :=
    val32_congr fun i hi => I.keep.word (j := a) (i := i) (by simp only [S]; omega_using [hi]) (by simp; omega_using [hao, hao1]) (by decide) fita
  obtain Ibj : w32 u.mem B (arr (kw len) b + 4 * j) = w32 s.mem B (arr (kw len) b + 4 * j) :=
    I.keep.word (j := b) (i := j) (by simp only [S]; omega_using [hw, hj]) (by simp; omega_using [hbo, hbo1]) (by decide) fitb
  refine ⟨hv, I.keep.trans kv, I.rest.trans Kv, cv, ?_, fun hh => nomatch hh⟩
  obtain hlow : val32 v.mem B (arr (kw len) o) j = val32 u.mem B (arr (kw len) o) j :=
    val32_congr fun i hi => wv i (.inl hi) (by omega_using [hw, hj, hi])
  show val32 v.mem B (arr (kw len) o) (j + 1 + kw len) =
    val32 s.mem B (arr (kw len) a) (kw len) * val32 s.mem B (arr (kw len) b) (j + 1)
  rw [show j + 1 + kw len = j + (kw len + 1) by omega_using [], val32_append, hlow, ev, Ia, Ibj]
  rw [val32_append] at Iv
  rw [val32_succ s.mem B (arr (kw len) b) j]
  generalize val32 s.mem B (arr (kw len) a) (kw len) = A at *
  grind

/-- `aProduct`'s rows: `RowsI` of none to `RowsI` of `w`. -/
theorem rowsLoopW_ok {s u : State} (h : RtWs wid s B Z len N) {o a b : Nat}
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) (hw : kw len' ≤ kw len) (hw1 : 1 ≤ kw len')
    (I₀ : RowsI wid s B Z len N o a b 0 false u) (In : RtWs nar u B Z len' N') :
    WP isa (.loop (VG.Impl.Rsa.X86.RecoverDetRt.rowW o a b) .ne) u fun v =>
      RowsI wid s B Z len N o a b (kw len') false v ∧ RtWs nar v B Z len' N' := by
  refine WP.loop (M := isa) (fun n u => ∃ j, n = kw len' - j ∧ j < kw len' ∧
    RowsI wid s B Z len N o a b j false u ∧ RtWs nar u B Z len' N') ?_ _ u ⟨0, rfl, by omega_using [hw1], I₀, In⟩
  rintro n u ⟨j, rfl, hj, I, In⟩
  refine WP.mono (rowsStepW_ok h ho ha hb hao hao1 hbo hbo1 hw hj I In) fun v ⟨zv, I', In'⟩ => ?_
  by_cases e : j + 1 = kw len'
  · exact .inl ⟨by simp only [eval, zv, e, decide_true, Option.map_some, Bool.not_true], e ▸ I', In'⟩
  · exact .inr ⟨by simp only [eval, zv, e, decide_false, Option.map_some, Bool.not_false], kw len' - (j + 1),
      by omega_using [hj], j + 1, rfl, by omega_using [hj, e], I', In'⟩

end

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr ptr_add ea_ptr ws_write)

/-- `aProduct`'s end: words `W` and `W + 1` of `[wA]` cleared. -/
theorem KS.clearTop (h : KS g s0 A live AW liveW V ls s) (hA : wA ∈ liveW) (hl : ∀ j ∈ live, j / 2 ≠ wA) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.arrPtr wid .eax wA .edx ++ VG.Impl.Rsa.X86.KeyRt.bytesB wid .ecx ++
      ([.alu .add .eax (.reg .ecx), .mov .ecx (.imm 0), .store (at_ .eax 0) .ecx, .store (at_ .eax 4) .ecx] :
        List Instr))) s fun t =>
      KS g s0 A live (upd AW wA (AW wA)) (wA :: liveW) V ls t ∧ w32 t.mem g.B (arr g.W wA + 4 * g.W) = 0 := by
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  obtain fa := h.wsW.arr_fit (j := wA) (by decide)
  simp only [S] at fa
  rw [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW) hW.lenLe hW.edi
    (r := .eax) (t := .edx) (j := wA) (by decide) (by decide) (by rw [kw_wid]; change arr g.W wA < 2 ^ 32; omega_using [nw, fa])
    fun u₁ U₁ m₁ p₁ _ => ?_
  obtain hW₁ := hW.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW₁) hW₁.lenLe (r := .ecx)
    fun u₂ U₂ m₂ e₂ => ?_
  rw [kw_wid] at p₁ e₂
  change PtrAt u₁ g.B .eax (arr g.W wA) at p₁
  change (u₂.gpr .ecx).toNat = 4 * g.W at e₂
  refine wp_addS rfl fun u₃ U₃ _ => wp_movS (v := 0) rfl fun u₄ U₄ _ => ?_
  obtain p₃ : PtrAt u₃ g.B .eax (arr g.W wA + 4 * g.W) := by
    rw [PtrAt, U₃.gpr, BitVec.toNat_add, U₂.1 _ (by decide), p₁, e₂]
    have := g.B.isLt; omega_using []
  obtain p₄ : PtrAt u₄ g.B .eax (arr g.W wA + 4 * g.W) := by rw [PtrAt, U₄.other _ (by decide)]; exact p₃
  obtain ws₄ := ((h.rt.rt.of_wr U₁.2.2).of_wr U₂.2.2).of_wr (U₄.wr.trans U₃.wr)
  refine wp_storeS (ea_ptr ws₄ p₄ (d := 0) (by omega_using [fa])) (ws_write ws₄ (by omega_using [fa])) fun t₁ M₁ => ?_
  obtain p₁' : PtrAt t₁ g.B .eax (arr g.W wA + 4 * g.W) := by rw [PtrAt, M₁.gpr]; exact p₄
  obtain ws₁ := ws₄.of_wr M₁.wr
  refine wp_storeS (ea_ptr ws₁ p₁' (d := 4) (by omega_using [fa])) (ws_write ws₁ (by omega_using [fa])) fun t₂ M₂ => WP.block_nil ?_
  have c₄ : u₄.gpr .ecx = 0 := U₄.gpr
  obtain O₁ := writeW32_outside u₄.mem g.B (d := arr g.W wA + 4 * g.W + 0) (u₄.gpr .ecx) (by omega_using [nw, fa])
  rw [← M₁.mem] at O₁
  obtain O₂ := writeW32_outside t₁.mem g.B (d := arr g.W wA + 4 * g.W + 4) (t₁.gpr .ecx) (by omega_using [nw, fa])
  rw [← M₂.mem] at O₂
  obtain m₄ : u₄.mem = s.mem := by rw [U₄.mem, U₃.mem, m₂, m₁]
  obtain O : Outside g.B (arr g.W wA + 4 * g.W) 8 s.mem t₂.mem := by
    rw [← m₄]; exact (O₁.mono (by omega_using []) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))
  obtain k : Keep g.B g.W [wA] [] s.mem t₂.mem := Keep.of_arr (d := 4 * g.W) O (by simp only [S]; omega_using []) (by simp)
  obtain r : Keeps opRegs s t₂ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans
      ((M₁.keeps _).trans (M₂.keeps _)))))
  obtain e : num t₂.mem g.B g.W wA = AW wA := by
    rw [← h.arrsW wA hA]
    exact O.val32 (.inl (by omega_using [])) (by omega_using [nw, fa])
  refine ⟨h.write_W k (by decide) (by simp) r e hl (by simp), ?_⟩
  rw [O₂.w32 (.inl (by omega_using [])) (by omega_using [nw, fa]), M₁.mem, Nat.add_zero, w32_write_self, c₄]
  rfl

end


/-- `a = g₁ x₃` modulo `2^(32 W)` (`[wA]`, its extra word zero), by `w` rows of `W + 1` words. -/
theorem aProduct_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {g1 x3 : Nat}
    (h : KS g s0 A [aG, aZero, aN] AW [wX3] V [sOkDE] s) (hg : A aG = g1) (hx : AW wX3 = x3) :
    WP isa aProduct s fun t => ∃ A' AW' V',
      KS g s0 A' [aZero, aN] AW' [wA] V' [sOkDE] t ∧
      AW' wA = g1 * x3 % 2 ^ (32 * g.W) ∧ VG.Proof.Mont.w32 t.mem g.B (arr g.W wA + 4 * g.W) = 0 ∧
      A' aZero = A aZero ∧ A' aN = A aN ∧ V' sOkDE = V sOkDE := by
  obtain g1lt : g1 < 2 ^ (32 * g.w) := by rw [← hg, ← h.arrs aG (by simp)]; exact val32_lt _ _ _ _
  obtain kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  obtain kwN : VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8) = g.w := kw_nar _
  obtain w18 : 18 ≤ g.w := by have := h.lower; simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega_using [this]
  have wW : g.W = 2 * g.w + 2 := rfl
  unfold aProduct
  simp only [seqs]
  refine WP.seq (WP.mono (h.zeroWide_W (j := wT) (by decide) (by decide)) fun u₁ ⟨h₁, z₁⟩ => ?_)
  obtain h₁' : KS g s0 A [aG, aZero, aN] (upd AW wT 0) [wX3] V [sOkDE] u₁ :=
    h₁.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h₁'.widen (k := wT) (a := aG) (by decide) (by simp) (by decide) z₁ (by decide)
    (by decide)) fun u₂ ⟨h₂, _⟩ => ?_)
  refine WP.seq (WP.mono (h₂.zeroWide_W (j := wA) (by decide) (by decide)) fun u₃ ⟨h₃, _⟩ => ?_)
  refine WP.seq (WP.mono (h₃.zeroWide_W (j := wA + 1) (by decide) (by decide)) fun u₄ ⟨h₄, _⟩ => ?_)
  refine WP.seq (wp_movS (v := 0) rfl fun u₅ U₅ _ => ?_)
  obtain h₅ := h₄.of_rest U₅.keeps (by decide) U₅.mem
  refine WP.mono (h₅.storeSlot (d := VG.Impl.Rsa.X86.WordModRt.oJ) (by decide) .eax) fun u₆ ⟨h₆, _, _⟩ => ?_
  rw [U₅.gpr] at h₆
  -- The rows.
  obtain I₀ : VG.Proof.Rsa.X86.WordRt.RowsI wid u₆ g.B g.Z (16 * g.n + 24) 22 wA wX3 wT 0 false u₆ := by
    refine ⟨h₆.rtW, Keep.refl _ _ _ _ _, Keeps.refl _ _, ?_, ?_, fun hh => nomatch hh⟩
    · rw [h₆.sl _ (by simp), upd_self]; rfl
    · simp only [VG.Proof.Rsa.X86.WordRt.rowW, Nat.zero_add, kwW]
      change num u₆.mem g.B g.W wA = _
      rw [h₆.arrsW wA (by simp)]
      simp [upd, val32]
  refine WP.seq (WP.mono (rowsLoopW_ok h₆.rtW (o := wA) (a := wX3) (b := wT) (len' := 8 * g.n + 8) (N' := 44)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [kwW, kwN]; omega_using [wW]) (by rw [kwN]; omega_using [w18]) I₀ h₆.rt) fun v ⟨I, _⟩ => ?_)
  have Iv := I.val
  simp only [VG.Proof.Rsa.X86.WordRt.rowW, kwW, kwN] at Iv
  obtain ex : val32 u₆.mem g.B (arr g.W wX3) g.W = x3 := by
    change num u₆.mem g.B g.W wX3 = x3
    rw [h₆.arrsW wX3 (by simp)]
    simp only [upd, show wX3 ≠ wA + 1 by decide, show wX3 ≠ wA by decide, show wX3 ≠ wT by decide,
      ↓reduceIte, hx]
  obtain eg : val32 u₆.mem g.B (arr g.W wT) g.w = g1 := by
    obtain e := h₆.arrsW wT (by simp)
    simp only [upd, show wT ≠ wA + 1 by decide, show wT ≠ wA by decide, ↓reduceIte, hg] at e
    rw [← Nat.mod_eq_of_lt g1lt, ← e]
    change val32 u₆.mem g.B (arr g.W wT) g.w = val32 u₆.mem g.B (arr g.W wT) (2 * g.w + 2) % 2 ^ (32 * g.w)
    rw [show 2 * g.w + 2 = g.w + (g.w + 2) by omega_using [], val32_mod]
  rw [ex, eg] at Iv
  obtain P : num v.mem g.B g.W wA = x3 * g1 % 2 ^ (32 * g.W) := by
    change val32 v.mem g.B (arr g.W wA) g.W = _
    rw [← val32_mod (k := g.w), Nat.add_comm, Iv]
  obtain k : Keep g.B g.W [wA, wA + 1] [VG.Impl.Rsa.X86.WordModRt.oJ] u₆.mem v.mem := by
    have := I.keep; rw [kwW] at this; exact this
  obtain ds : ∀ d ∈ [VG.Impl.Rsa.X86.WordModRt.oJ], SlotOk d := by decide
  obtain h₆m := h₆.mono (ls' := [sOkDE]) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
  obtain aw := h₆m.arrs_W k (by decide) ds
  obtain h₇ : KS g s0 A [aZero, aN] (upd (upd (upd (upd (upd AW wT 0) wT (A aG)) wA 0) (wA + 1) 0) wA
      (x3 * g1 % 2 ^ (32 * g.W))) [wA] (upd V VG.Impl.Rsa.X86.WordModRt.oJ 0) [sOkDE] v :=
    h₆m.core k (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact h₆m.wsW.arr_fit (by decide)
        · exact h₆m.wsW.arr_fit (by decide)) ds (I.rest.mono (by decide))
      (fun j hj => aw j (by simp at hj ⊢; omega_using [hj])) (by decide)
      (fun j hj => by simp at hj; subst hj; rw [upd_self]; exact P) (by decide)
      (h₆m.sl_keep k (by decide)) h₆m.ls_ok
  refine WP.seq (WP.mono (h₇.zeroWide_W (j := wA + 1) (by decide) (by decide)) fun v₂ ⟨h₈, _⟩ => ?_)
  refine WP.mono (h₈.clearTop (by simp) (by decide)) fun t ⟨h₉, top⟩ => ?_
  refine ⟨_, _, _, h₉.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], rfl⟩), ?_, top, rfl, rfl, ?_⟩
  · simp only [upd_self, upd_ne _ _ (show wA ≠ wA + 1 by decide)]
    rw [Nat.mul_comm]
  · rw [upd_ne _ _ (by decide)]

end VG.Proof.Rsa.X86.Recover

end

end

/-! # `m = ⌊a / n⌋` and `r = a mod n` on i686

`RecoverDetRt.divA`: `n` widened (`wideN`), `n` and the dividend `a` (`W + 1` words) doubled until
`n`'s word `W' - 1` has its top bit set (`normA`, `z` times, counted in `sZ`), then divided by words
(`wordDivQ … true`): the quotient `⌊a 2^z / n 2^z⌋ = ⌊a / n⌋` in `wA`'s low words, the rest of them
cleared (`clearQTop`), and the remainder `(a mod n) 2^z` halved back `z` times (`unnormA`); then `n`
widened again and whether `m < n`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa (b2n sub32)
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr ptr_add)
open VG.Proof.Rsa.X86.WordRt (MLen wq)

/-! ## Helpers -/

/-- `test d, imm`: ZF is `d &&& v = 0`. -/
theorem wp_testI {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.imm v) :: is)) s Q :=
  VG.X86.Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

/-- A word's top bit clear. -/
theorem topBit_clear (x : BitVec 32) :
    (x &&& BitVec.ofNat 32 0x80000000 == 0) = decide (x.toNat < 2 ^ 31) := by
  have hx := x.isLt
  obtain key : x.toNat &&& 2 ^ 31 = x.toNat / 2 ^ 31 % 2 * 2 ^ 31 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ 31) with e | e
    · rw [e, Nat.zero_mul, Nat.zero_testBit]
      by_cases hi : 31 = i
      · subst hi; simp [Nat.testBit_eq_decide_div_mod_eq, e]
      · simp [hi]
    · rw [e, Nat.one_mul, Nat.testBit_two_pow]
      by_cases hi : 31 = i
      · subst hi; simp [Nat.testBit_eq_decide_div_mod_eq, e]
      · simp [hi]
  obtain e : (x &&& BitVec.ofNat 32 0x80000000).toNat = x.toNat / 2 ^ 31 % 2 * 2 ^ 31 := by
    rw [BitVec.toNat_and, show (BitVec.ofNat 32 0x80000000).toNat = 2 ^ 31 from rfl, key]
  by_cases h : x.toNat < 2 ^ 31
  · have z : x.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt h
    rw [z] at e
    simp only [h, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [e]; rfl)
  · have z : x.toNat / 2 ^ 31 = 1 := by omega_using [h]
    rw [z] at e
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro c; rw [c] at e; simp at e

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `wideN`: `n` (narrow `aN`) into the wide `wN`, its extra word zero; `wA`'s extra word kept. -/
theorem KS.wideN_ok (h : KS g s0 A live AW liveW V ls s) (hN : aN ∈ live) (hl : ∀ i ∈ live, i / 2 ≠ wN)
    (hlW : ∀ j ∈ liveW, j ≠ wN) :
    WP isa wideN s fun t =>
      KS g s0 A live (upd (upd AW wN 0) wN (A aN)) (wN :: liveW) V ls t ∧
      w32 t.mem g.B (arr g.W wN + 4 * g.W) = 0 ∧
      w32 t.mem g.B (arr g.W wA + 4 * g.W) = w32 s.mem g.B (arr g.W wA + 4 * g.W) := by
  obtain fA := h.wsW.fit64 (j := wA) (by decide)
  obtain e17 := arr_end (w := g.W) (show wA < wN by decide)
  obtain e19 : arr g.W wN = arr g.w (2 * wN) := arr_W' g wN
  have wW : g.W = 2 * g.w + 2 := rfl
  simp only [S] at e17
  unfold wideN
  refine WP.seq (WP.mono (WP.and (h.zeroWide_W (j := wN) (by decide) hl)
    (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h.rtW (j := wN) (by decide))) fun u ⟨⟨hu, z⟩, ⟨_, ku, _, _⟩⟩ => ?_)
  rw [kw_wid] at ku
  obtain hu' := hu.mono (liveW' := liveW) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (WP.and (hu'.widen (k := wN) (a := aN) (by decide) hN (by decide) z hl hlW)
    (copyOut_ok hu'.rt (o := 2 * wN) (a := aN) (by decide) (hu'.live_lt aN hN) (by decide)))
    fun v ⟨⟨hv, top⟩, ⟨_, Ov, _, _⟩⟩ => ⟨hv, top, ?_⟩
  rw [kw_nar] at Ov
  change Outside g.B (arr g.w (2 * wN)) (4 * g.w) u.mem v.mem at Ov
  obtain dj : arr g.W wA + 4 * g.W + 4 ≤ arr g.w (2 * wN) := by rw [← e19]; omega_using [e17]
  rw [Ov.w32 (.inl dj) (by simp only [S] at fA; omega_using [fA])]
  obtain e := ku.word (j := wA) (i := g.W) (by show 4 * g.W + 4 ≤ 4 * (g.W + 2); omega_using []) (by decide) (by simp) fA
  exact e

/-- `topBit`: ZF set exactly where the top bit of `n`'s word `W' - 1` is clear. -/
theorem KS.topBit_ok {a : Nat} {is : List Instr} {Q : State → Prop} (h : KS g s0 A live AW liveW V ls s)
    (hm : MLen s g.B g.Z VG.Impl.Rsa.X86.RecoverDetRt.nl a) (hN : wN ∈ liveW) (hw1 : 1 ≤ wq a)
    (hw : wq a ≤ g.w)
    (k : ∀ t, KS g s0 A live AW liveW V ls t → t.mem = s.mem →
      t.zf = some (decide (AW wN % 2 ^ (32 * wq a) / 2 ^ (32 * (wq a - 1)) < 2 ^ 31)) →
      WP isa (.block is) t Q) :
    WP isa (.block (topBit ++ is)) s Q := by
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  obtain fa := h.wsW.arr_fit (j := wN) (by decide)
  have wW : g.W = 2 * g.w + 2 := rfl
  simp only [S] at fa
  unfold topBit
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine VG.Proof.Rsa.X86.WordRt.topPtr_ok hW hm (j := wN) (i := 1) (r := .ebx) (t := .ecx)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw1 (by rw [kw_wid]; change wq a ≤ g.W + 2; omega_using [hw, wW])
    fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kw_wid] at p₁
  change PtrAt u₁ g.B .ebx (arr g.W wN + 4 * wq a - 4 * 1) at p₁
  refine wp_movS (readSrc_ptr (h.rt.rt.of_wr U₁.2.2) p₁ (d := 0) (by omega_using [hw, fa, wW])) fun u₂ U₂ _ =>
    wp_testI fun u₃ F₃ z₃ => k u₃ ?_ (by rw [F₃.mem, U₂.mem, m₁]) ?_
  · exact h.of_rest (rs := opRegs) ((U₁.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
      ⟨fun r _ => by rw [F₃.gpr], F₃.rd, F₃.wr⟩)) (fun x hx => hx) (by rw [F₃.mem, U₂.mem, m₁])
  · rw [z₃, topBit_clear, U₂.gpr, m₁, Nat.add_zero,
      show arr g.W wN + 4 * wq a - 4 * 1 = arr g.W wN + 4 * (wq a - 1) by omega_using [hw1]]
    change some (decide (w32 s.mem g.B (arr g.W wN + 4 * (wq a - 1)) < 2 ^ 31)) = _
    obtain e := val32_top (m := s.mem) (B := g.B) (d := arr g.W wN) (K := g.W - wq a) hw1
    rw [show wq a + (g.W - wq a) = g.W by omega_using [hw, wW]] at e
    rw [← h.arrsW wN hN]
    change _ = some (decide (val32 s.mem g.B (arr g.W wN) g.W % _ / _ < _))
    rw [e]


/-- `[wA]` doubled over its `W + 1` words (the extra word too). -/
theorem KS.dblX (h : KS g s0 A live AW liveW V ls s) (hA : wA ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ wA)
    {X : Nat} (hX : val32 s.mem g.B (arr g.W wA) (g.W + 1) = X) (hX2 : 2 * X < 2 ^ (32 * (g.W + 1))) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.chain wid .adc wA wA wA true) s fun t =>
      KS g s0 A live (upd AW wA (2 * X % 2 ^ (32 * g.W))) (wA :: liveW) V ls t ∧
      val32 t.mem g.B (arr g.W wA) (g.W + 1) = 2 * X := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.chainAdd_ok h.rtW (o := wA) (a := wA) (b := wA)
    (h.liveW_lt wA hA) (h.liveW_lt wA hA) (h.liveW_lt wA hA) true) fun t ⟨_, k, ⟨c, _, v⟩, r⟩ => ?_
  simp only [VG.Proof.Rsa.X86.KeyRt.kk, Bool.toNat_true] at v
  rw [kw_wid] at k v
  change val32 t.mem g.B (arr g.W wA) (g.W + 1) + _ = val32 s.mem g.B (arr g.W wA) (g.W + 1) +
    val32 s.mem g.B (arr g.W wA) (g.W + 1) at v
  rw [hX] at v
  obtain ⟨xv, _⟩ := sum_carry (val32_lt _ _ _ _) v
  obtain e2 : val32 t.mem g.B (arr g.W wA) (g.W + 1) = 2 * X := by rw [xv, ← Nat.two_mul, Nat.mod_eq_of_lt hX2]
  refine ⟨h.write_W k (h.liveW_lt wA hA) (by simp) (r.mono (by decide)) ?_ hl (by simp), e2⟩
  change val32 t.mem g.B (arr g.W wA) g.W = _
  rw [← val32_mod (k := 1), e2]

end

/-! ## `normA` -/

/-- `normA`'s state after `z` doublings. -/
def NS (g : Geo) (s0 : State) (A : Nat → Nat) (ok n x z : Nat) (t : State) : Prop :=
  ∃ AW V, KS g s0 A [aZero, aN] AW [wN, wA] V [sZ, sOkDE] t ∧ V sZ = z ∧ V sOkDE = ok ∧
    AW wN = n * 2 ^ z ∧ AW wA = x * 2 ^ z % 2 ^ (32 * g.W) ∧
    val32 t.mem g.B (arr g.W wA) (g.W + 1) = x * 2 ^ z

/-- A word below `2^(32 W')`: its word `W' - 1` is below `2^31` exactly when it is below
`2^(32 W' - 1)`. -/
theorem top_lt_iff {v W' : Nat} (hv : v < 2 ^ (32 * W')) (hW : 1 ≤ W') :
    v % 2 ^ (32 * W') / 2 ^ (32 * (W' - 1)) < 2 ^ 31 ↔ v < 2 ^ (32 * W' - 1) := by
  rw [Nat.mod_eq_of_lt hv, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
    show 31 + 32 * (W' - 1) = 32 * W' - 1 by omega_using [hW]]

section
variable {g : Geo} {s0 : State} {A : Nat → Nat}

/-- A doubling of `normA`'s loop, and its test of `n`'s top bit. -/
theorem normStep_ok {ok n x z a : Nat} {t : State} (h : NS g s0 A ok n x z t)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha1 : a ≤ 1024)
    (hw1 : 1 ≤ wq a) (hw : wq a ≤ g.w) (hx : x < 2 ^ (32 * g.W)) (hz : z < 31)
    (hn : n * 2 ^ (z + 1) < 2 ^ (32 * wq a)) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.chain wid .adc wN wN wN false,
      VG.Impl.Rsa.X86.KeyRt.chain wid .adc wA wA wA true,
      .block (([.mov .eax (.mem (sc sZ)), .alu .add .eax (.imm 1), .store (sc sZ) .eax] : List Instr) ++ topBit)])
      t fun u =>
      NS g s0 A ok n x (z + 1) u ∧
        u.zf = some (decide (n * 2 ^ (z + 1) < 2 ^ (32 * wq a - 1))) := by
  obtain ⟨AW, V, h, hzV, hok, hN, hA, hX⟩ := h
  obtain pw : 2 ^ (32 * wq a) ≤ 2 ^ (32 * g.W) := Nat.pow_le_pow_right (by decide)
    (by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at hw; omega_using [hw])
  obtain fA := h.wsW.fit64 (j := wA) (by decide)
  simp only [seqs]
  -- `n` doubled.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.chainAdd_ok h.rtW (o := wN) (a := wN) (b := wN)
    (by decide) (by decide) (by decide) false) fun t₁ ⟨_, k₁, ⟨c₁, _, v₁⟩, r₁⟩ => ?_)
  simp only [VG.Proof.Rsa.X86.KeyRt.kk, Bool.toNat_false, Nat.add_zero] at v₁
  rw [kw_wid] at k₁ v₁
  change num t₁.mem g.B g.W wN + _ = num t.mem g.B g.W wN + num t.mem g.B g.W wN at v₁
  rw [h.arrsW wN (by simp), hN] at v₁
  obtain ⟨xv₁, _⟩ := sum_carry (val32_lt _ _ _ _) v₁
  obtain e₁ : num t₁.mem g.B g.W wN = n * 2 ^ (z + 1) := by
    change val32 t₁.mem g.B (arr g.W wN) g.W = _
    rw [xv₁, ← Nat.two_mul, Nat.mul_left_comm, ← Nat.pow_succ']; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn pw)
  obtain h₁ := h.write_W k₁ (by decide) (by simp) (r₁.mono (by decide)) e₁ (by decide) (by simp)
  obtain X₁ : val32 t₁.mem g.B (arr g.W wA) (g.W + 1) = x * 2 ^ z := by
    rw [← hX]
    exact val32_congr fun i hi => k₁.word (j := wA) (i := i) (by show 4 * i + 4 ≤ 4 * (g.W + 2); omega_using [hi]) (by decide) (by simp) fA
  -- `a` doubled over `W + 1` words.
  obtain X2 : 2 * (x * 2 ^ z) < 2 ^ (32 * (g.W + 1)) := by
    obtain e : 2 * (x * 2 ^ z) = x * 2 ^ (z + 1) := by rw [Nat.mul_left_comm, ← Nat.pow_succ']
    rw [e]
    calc x * 2 ^ (z + 1) < 2 ^ (32 * g.W) * 2 ^ (z + 1) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
      _ = 2 ^ (32 * g.W + (z + 1)) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (32 * (g.W + 1)) := Nat.pow_le_pow_right (by decide) (by omega_using [hz])
  refine WP.seq (WP.mono (h₁.dblX (by simp) (by decide) X₁ X2) fun t₂ ⟨h₂, X₂⟩ => ?_)
  -- `sZ := z + 1`, then the test.
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (h₂.readSlot (d := sZ) (by simp)) fun u₁ U₁ _ => wp_addS rfl fun u₂ U₂ _ => ?_
  obtain h₂' := h₂.of_rest (rs := opRegs) ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide)))
    (fun x hx => hx) (by rw [U₂.mem, U₁.mem])
  obtain ez : (u₂.gpr .eax).toNat = z + 1 := by
    rw [U₂.gpr, U₁.gpr, BitVec.toNat_add, hzV, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (show z < 2 ^ 32 by omega_using [hz]), Nat.mod_eq_of_lt (show z + 1 < 2 ^ 32 by omega_using [hz])]
  refine storeHdr h₂'.ws (d := sZ) (by decide) .eax fun u₃ K₃ e₃ k₃ _ _ => ?_
  rw [ez] at e₃
  obtain h₃ := (h₂'.slot1 K₃ (by decide) (k₃.mono (by decide)) e₃).mono (ls' := [sZ, sOkDE])
    (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
  rw [show topBit = topBit ++ [] from (List.append_nil _).symm]
  refine KS.topBit_ok h₃ (h₃.mlen ha ha1) (by simp) hw1 hw fun u₄ h₄ m₄ zf₄ => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨_, _, h₄.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
      (fun d hd => ⟨hd, rfl⟩),
      upd_self .., by rw [upd_ne _ _ (by decide), hok], ?_, ?_, ?_⟩
    · rw [upd_ne _ _ (by decide), upd_self]
    · rw [upd_self, Nat.mul_left_comm, ← Nat.pow_succ']
    · have X₄ : val32 u₄.mem g.B (arr g.W wA) (g.W + 1) = val32 t₂.mem g.B (arr g.W wA) (g.W + 1) := by
        rw [m₄, show t₂.mem = u₂.mem by rw [U₂.mem, U₁.mem]]
        exact val32_congr fun i hi => K₃.toW.word (j := wA) (i := i)
          (by show 4 * i + 4 ≤ 4 * (2 * g.w + 2 + 2); have : g.W = 2 * g.w + 2 := rfl; omega_using [hi, this]) (by simp)
          (by decide) fA
      rw [X₄, X₂, Nat.mul_left_comm, ← Nat.pow_succ']
  · rw [zf₄, upd_ne _ _ (by decide), upd_self]
    simp only [top_lt_iff hn hw1]


theorem z_bound {n y W' : Nat} (hW : 1 ≤ W') (hn0 : 2 ^ (32 * (W' - 1)) ≤ n)
    (c : n * 2 ^ y < 2 ^ (32 * W' - 1)) : y < 31 := by
  have : 2 ^ (32 * (W' - 1) + y) < 2 ^ (32 * (W' - 1) + 31) :=
    calc 2 ^ (32 * (W' - 1) + y) = 2 ^ (32 * (W' - 1)) * 2 ^ y := Nat.pow_add _ _ _
      _ ≤ n * 2 ^ y := Nat.mul_le_mul_right _ hn0
      _ < 2 ^ (32 * W' - 1) := c
      _ = 2 ^ (32 * (W' - 1) + 31) := by rw [show 32 * W' - 1 = 32 * (W' - 1) + 31 by omega_using [hW]]
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
  omega_using [this]

/-- `normA`: `n` and `a` doubled `z` times, until `n`'s word `W' - 1` has its top bit set. -/
theorem normA_ok {V AW : Nat → Nat} {n x a : Nat} {t : State}
    (h : KS g s0 A [aZero, aN] AW [wN, wA] V [sOkDE] t) (hN : AW wN = n) (hA : AW wA = x)
    (hxt : w32 t.mem g.B (arr g.W wA + 4 * g.W) = 0)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha1 : a ≤ 1024)
    (hw1 : 1 ≤ wq a) (hw : wq a ≤ g.w) (hx : x < 2 ^ (32 * g.W))
    (hn0 : 2 ^ (32 * (wq a - 1)) ≤ n) (hn' : n < 2 ^ (32 * wq a)) :
    WP isa normA t fun u => ∃ z, z ≤ 31 ∧ NS g s0 A (V sOkDE) n x z u ∧
      2 ^ (32 * wq a - 1) ≤ n * 2 ^ z ∧ n * 2 ^ z < 2 ^ (32 * wq a) := by
  obtain fA := h.wsW.fit64 (j := wA) (by decide)
  unfold normA
  simp only [seqs, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_)
  obtain h₁ := h.of_rest U₁.keeps (by decide) U₁.mem
  refine storeHdr h₁.ws (d := sZ) (by decide) .eax fun u₂ K₂ e₂ k₂ _ _ => ?_
  obtain h₂ := h₁.slot1 K₂ (by decide) (k₂.mono (by decide)) e₂
  rw [show topBit = topBit ++ [] from (List.append_nil _).symm]
  refine KS.topBit_ok h₂ (h₂.mlen ha ha1) (by simp) hw1 hw fun u₃ h₃ m₃ zf₃ => WP.block_nil ?_
  obtain X₃ : val32 u₃.mem g.B (arr g.W wA) (g.W + 1) = x := by
    rw [m₃, val32_succ]
    have k₂W := K₂.toW
    rw [U₁.mem] at k₂W
    obtain e := k₂W.word (j := wA) (i := g.W) (by show 4 * g.W + 4 ≤ 4 * (g.W + 2); omega_using []) (by simp) (by decide) fA
    change w32 u₂.mem g.B (arr g.W wA + 4 * g.W) = w32 t.mem g.B (arr g.W wA + 4 * g.W) at e
    rw [e, hxt]
    change val32 u₂.mem g.B (arr g.W wA) g.W + 0 = x
    rw [Nat.add_zero, ← hA, ← h₂.arrsW wA (by simp)]
  obtain P₀ : NS g s0 A (V sOkDE) n x 0 u₃ :=
    ⟨_, _, h₃, by rw [upd_self, U₁.gpr]; rfl, by rw [upd_ne _ _ (by decide)], by rw [hN, Nat.pow_zero, Nat.mul_one],
      by rw [hA, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx], by rw [X₃, Nat.pow_zero, Nat.mul_one]⟩
  simp only [hN, top_lt_iff hn' hw1] at zf₃
  refine WP.ite (!decide (n < 2 ^ (32 * wq a - 1))) (by simp only [eval, zf₃, Option.map_some]) (fun hb => ?_)
    (fun hb => ?_)
  · refine WP.block_nil ⟨0, by omega_using [], P₀, ?_, by simpa using hn'⟩
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    simpa using hb
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.loop (M := isa) (fun k u => ∃ z, k = 31 - z ∧ z < 31 ∧ NS g s0 A (V sOkDE) n x z u ∧
      n * 2 ^ z < 2 ^ (32 * wq a - 1)) ?_ (31 - 0) u₃ ⟨0, rfl, by decide, P₀, by simpa using hb⟩
    rintro k u ⟨z, rfl, hz, P, hlt⟩
    obtain hn2 : n * 2 ^ (z + 1) < 2 ^ (32 * wq a) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      have : 2 ^ (32 * wq a) = 2 ^ (32 * wq a - 1) * 2 := by
        rw [← Nat.pow_succ]; exact congrArg (2 ^ ·) (by omega_using [hw1])
      omega_using [hlt, this]
    refine WP.mono (normStep_ok P ha ha1 hw1 hw hx hz hn2) fun u' ⟨P', zf'⟩ => ?_
    by_cases c : n * 2 ^ (z + 1) < 2 ^ (32 * wq a - 1)
    · refine .inr ⟨by simp only [eval, zf', c, decide_true], 31 - (z + 1), by omega_using [hz], z + 1, rfl,
        z_bound hw1 hn0 c, P', c⟩
    · refine .inl ⟨by simp only [eval, zf', c, decide_false], z + 1, by omega_using [hz], P', by omega_using [c], hn2⟩

end

/-! ## `clearQTop` -/

section
open VG.Proof.Mont.X86.Rt (ea_ptr ws_write)

/-- After words `0, …, j - 1` of `K` cleared from `d`. -/
structure ZI (s : State) (B : Addr) (d K j : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (d + 4 * j)
  dx : (u.gpr .edx).toNat = 4 * (K - j)
  keep : Keeps [.eax, .edx, .esi] s u
  out : Outside B d (4 * j) s.mem u.mem
  zero : ∀ i < j, w32 u.mem B (d + 4 * i) = 0

theorem zeroStep_ok {B : Addr} {s u : State} {bytes d K j : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (nw : B.toNat + bytes ≤ 2 ^ 32) (hd : d + 4 * K ≤ bytes) (hj : j < K) (I : ZI s B d K j u) :
    WP isa (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)])
      u fun u' => u'.zf = some (decide (j + 1 = K)) ∧ ZI s B d K (j + 1) u' := by
  obtain wsu := ws.of_wr I.keep.2.2
  refine wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_
  obtain ws₁ := wsu.of_wr U₁.wr
  obtain p₁ : PtrAt u₁ B .esi (d + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.si
  refine wp_storeS (ea_ptr ws₁ p₁ (d := 0) (by omega_using [hd, hj])) (ws_write ws₁ (by omega_using [hd, hj])) fun u₂ M₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => VG.Proof.Mont.X86.Rt.wp_subZ rfl fun u₄ U₄ z₄ => WP.block_nil ?_
  obtain hc := VG.Proof.Mont.X86.Rt.count_zf (N := K) (x := u.gpr .edx) I.dx hj
  obtain dx₃ : u₃.gpr .edx = u.gpr .edx := by
    rw [U₃.other _ (by decide), M₂.gpr, U₁.other _ (by decide)]
  obtain m₄ : u₄.mem = u.mem.writeW (off B (d + 4 * j)) (0 : BitVec 32) := by
    rw [U₄.mem, U₃.mem, M₂.mem, U₁.mem, U₁.gpr, Nat.add_zero]
  obtain O := writeW32_outside u.mem B (d := d + 4 * j) (0 : BitVec 32) (by omega_using [nw, hd, hj])
  rw [← m₄] at O
  refine ⟨by rw [z₄, dx₃, hc.2], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₄.other _ (by decide), U₃.gpr, ptr_add (s := u₂) (x := d + 4 * j)
      (by rw [PtrAt, M₂.gpr]; exact p₁)]
    congr 2
  · rw [U₄.gpr, dx₃, hc.1]
  · exact I.keep.trans ((U₁.keeps.mono (by decide)).trans ((M₂.keeps _).trans
      ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))))
  · exact (I.out.mono (by omega_using []) (by omega_using [])).trans (O.mono (by omega_using []) (by omega_using []))
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [O.w32 (.inl (by omega_using [hi])) (by omega_arith)]; exact I.zero i hi
    · rw [m₄, w32_write_self]; rfl

theorem zeroLoop_ok {B : Addr} {s u : State} {bytes d K : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (nw : B.toNat + bytes ≤ 2 ^ 32) (hd : d + 4 * K ≤ bytes) (hK : 0 < K) (I : ZI s B d K 0 u) :
    WP isa (.loop (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4),
      .alu .sub .edx (.imm 4)]) .ne) u (ZI s B d K K) := by
  refine WP.loop (M := isa) (fun n v => ∃ j, n = K - j ∧ j < K ∧ ZI s B d K j v) ?_ _ u ⟨0, rfl, hK, I⟩
  rintro n v ⟨j, rfl, hj, J⟩
  refine WP.mono (zeroStep_ok ws nw hd hj J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : j + 1 = K
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ J'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], K - (j + 1),
      by omega_using [hj], j + 1, rfl, by omega_using [hj, e], J'⟩

variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `clearQTop`: `[wA]`'s words `W - W' + 2, …, W + 1` cleared, so it holds its low `W - W' + 2`. -/
theorem KS.clearQTop_ok {a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hm : MLen s g.B g.Z VG.Impl.Rsa.X86.RecoverDetRt.nl a) (hl : ∀ j ∈ live, j / 2 ≠ wA)
    (hw2 : 2 ≤ wq a) (hw : wq a ≤ g.w) :
    WP isa clearQTop s fun t =>
      KS g s0 A live (upd AW wA (val32 s.mem g.B (arr g.W wA) (g.W - wq a + 2))) (wA :: liveW) V ls t := by
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  obtain fa := h.wsW.arr_fit (j := wA) (by decide)
  have wW : g.W = 2 * g.w + 2 := rfl
  obtain wb : g.w ≤ 258 := by
    have := h.upper; simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega_using [this]
  simp only [S] at fa
  unfold clearQTop
  simp only [seqs]
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW) hW.lenLe hW.edi
    (r := .esi) (t := .edx) (j := wA) (by decide) (by decide) (by rw [kw_wid]; change arr g.W wA < 2 ^ 32; omega_using [nw, fa])
    fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kw_wid] at p₁
  change PtrAt u₁ g.B .esi (arr g.W wA) at p₁
  obtain hW₁ := hW.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW₁) hW₁.lenLe (r := .eax)
    fun u₂ U₂ m₂ e₂ => ?_
  rw [kw_wid] at e₂
  change (u₂.gpr .eax).toNat = 4 * g.W at e₂
  simp only [List.cons_append, List.nil_append]
  refine wp_addS rfl fun u₃ U₃ _ => ?_
  obtain m₃ : u₃.mem = s.mem := by rw [U₃.mem, m₂, m₁]
  refine VG.Proof.Rsa.X86.WordRt.width4_ok (hm.keep (((U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    (U₃.keeps.mono (by decide)))) : Keeps [.eax, .edx, .esi] s u₃) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _))
    (r := .edx) fun u₄ U₄ m₄ e₄ => ?_
  obtain w4 : 4 * wq a < 2 ^ 32 := by omega_using [hw, wb]
  refine wp_subS rfl fun u₅ U₅ _ => wp_addS rfl fun u₆ U₆ _ => WP.block_nil ?_
  obtain e₃ : (u₃.gpr .esi).toNat = g.B.toNat + arr g.W wA + 4 * g.W := by
    rw [U₃.gpr, BitVec.toNat_add, U₂.1 .esi (by decide), p₁, e₂]
    have := g.B.isLt; omega_using [nw, fa]
  obtain p₆ : PtrAt u₆ g.B .esi (arr g.W wA + 4 * (g.W - wq a + 2)) := by
    rw [PtrAt, U₆.gpr, BitVec.toNat_add, U₅.gpr, BitVec.toNat_sub, U₄.1 .esi (by decide), e₃,
      e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w4, show (8 : BitVec 32).toNat = 8 from rfl]
    omega_using [hw, nw, fa, wW]
  obtain K₆ : Keeps [.eax, .edx, .esi] s u₆ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans
      (U₆.keeps.mono (by decide))))))
  obtain m₆ : u₆.mem = s.mem := by rw [U₆.mem, U₅.mem, m₄, m₃]
  obtain I₀ : ZI u₆ g.B (arr g.W wA + 4 * (g.W - wq a + 2)) (wq a) 0 u₆ := by
    refine ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact p₆, ?_, Keeps.refl _ _, Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    rw [U₆.other _ (by decide), U₅.other _ (by decide), e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w4, Nat.sub_zero]
  refine WP.mono (zeroLoop_ok (h.rt.rt.of_keeps K₆) nw (by omega_using [hw, fa, wW]) (by omega_using [hw2]) I₀) fun t I => ?_
  obtain O : Outside g.B (arr g.W wA + 4 * (g.W - wq a + 2)) (4 * wq a) s.mem t.mem := by rw [← m₆]; exact I.out
  obtain k : Keep g.B g.W [wA] [] s.mem t.mem :=
    Keep.of_arr (d := 4 * (g.W - wq a + 2)) O (by simp only [S]; omega_using [hw, wW]) (by simp)
  refine h.write_W k (by decide) (by simp) ((K₆.trans I.keep).mono (by decide)) ?_ hl (by simp)
  change val32 t.mem g.B (arr g.W wA) g.W = _
  obtain e := val32_append t.mem g.B (arr g.W wA) (g.W - wq a + 2) (wq a - 2)
  rw [show g.W - wq a + 2 + (wq a - 2) = g.W by omega_using [hw2, hw, wW]] at e
  obtain lowEq : val32 t.mem g.B (arr g.W wA) (g.W - wq a + 2) =
      val32 s.mem g.B (arr g.W wA) (g.W - wq a + 2) := by
    rw [← m₆]; exact I.out.val32 (.inl (Nat.le_refl _)) (by omega_using [e₃])
  obtain hiZ : val32 t.mem g.B (arr g.W wA + 4 * (g.W - wq a + 2)) (wq a - 2) = 0 :=
    VG.Proof.Rsa.X86.WordRt.val32_eq_zero fun i hi => I.zero i (by omega_using [hi])
  rw [e, lowEq, hiZ, Nat.mul_zero, Nat.add_zero]

end

/-! ## `unnormA` -/

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem ofNat_beq_zero {z : Nat} (hz : z < 2 ^ 32) : (BitVec.ofNat 32 z == 0) = decide (z = 0) := by
  by_cases h : z = 0
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro c; have := congrArg BitVec.toNat c; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz] at this
    exact h this

/-- `unnormA`: `[wR] = R 2^z` halved `z` times (`z` in `sZ`). -/
theorem KS.unnormA_ok {z R : Nat} (h : KS g s0 A live AW liveW V ls s) (hS : sZ ∈ ls) (hVS : V sZ = z)
    (hR : wR ∈ liveW) (hRv : AW wR = R * 2 ^ z) (hz : z < 2 ^ 32) (hl : ∀ j ∈ live, j / 2 ≠ wR) :
    WP isa unnormA s fun t => ∃ V', KS g s0 A live (upd AW wR R) (wR :: liveW) V' (sZ :: ls) t ∧
      ∀ d, d ≠ sZ → V' d = V d := by
  unfold unnormA
  simp only [seqs]
  refine WP.seq (wp_movS (h.readSlot hS) fun u₁ U₁ _ => VG.X86.Wp.wp_test fun u₂ F₂ z₂ => WP.block_nil ?_)
  obtain h₂ := h.of_rest (rs := opRegs) ((U₁.keeps.mono (by decide)).trans ⟨fun r _ => by rw [F₂.gpr], F₂.rd, F₂.wr⟩)
    (fun x hx => hx) (by rw [F₂.mem, U₁.mem])
  rw [U₁.gpr, BitVec.and_self, hVS, ofNat_beq_zero hz] at z₂
  refine WP.ite (decide (z = 0)) (by simp only [eval, z₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨V, h₂.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨?_, rfl⟩),
      fun _ _ => rfl⟩
    · exact (List.mem_cons.mp hj).elim (fun e => e ▸ hR) id
    · by_cases e : j = wR
      · subst e; rw [upd_self, hRv, Nat.pow_zero, Nat.mul_one]
      · rw [upd_ne _ _ e]
    · exact (List.mem_cons.mp hd).elim (fun e => e ▸ hS) id
  simp only [decide_eq_false_iff_not] at hb
  obtain I₀ : KS g s0 A live (upd AW wR (R * 2 ^ (z - 0))) (wR :: liveW) (upd V sZ (z - 0)) (sZ :: ls) u₂ := by
    refine h₂.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
    · exact (List.mem_cons.mp hj).elim (fun e => e ▸ hR) id
    · by_cases e : j = wR
      · subst e; rw [upd_self, hRv, Nat.sub_zero]
      · rw [upd_ne _ _ e]
    · exact (List.mem_cons.mp hd).elim (fun e => e ▸ hS) id
    · by_cases e : d = sZ
      · subst e; rw [upd_self, hVS, Nat.sub_zero]
      · rw [upd_ne _ _ e]
  refine WP.loop (M := isa) (fun k u => ∃ i, k = z - i ∧ i < z ∧
    KS g s0 A live (upd AW wR (R * 2 ^ (z - i))) (wR :: liveW) (upd V sZ (z - i)) (sZ :: ls) u) ?_ (z - 0) u₂
    ⟨0, rfl, by omega_using [hb], I₀⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.seq (wp_movS rfl fun u₁ U₁' _ => WP.block_nil ?_)
  obtain P₁ := P.of_rest U₁'.keeps (by decide) U₁'.mem
  refine WP.seq (WP.mono (P₁.half_W (j := wR) (by simp) (by rw [U₁'.gpr]; rfl) hl) fun u₂ ⟨P₂, _⟩ => ?_)
  refine wp_movS (P₂.readSlot (d := sZ) (by simp)) fun u₃ U₃ _ =>
    VG.Proof.Mont.X86.Rt.wp_subZ (v := 1) rfl fun u₄ U₄ z₄ => ?_
  obtain P₄ := P₂.of_rest (rs := opRegs) ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))
    (fun x hx => hx) (by rw [U₄.mem, U₃.mem])
  refine WP.mono (P₄.storeSlot (d := sZ) (by decide) .eax) fun t ⟨P₅, zf₅, _⟩ => ?_
  obtain ev : (u₄.gpr .eax).toNat = z - (i + 1) := by
    rw [U₄.gpr, U₃.gpr, upd_self, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z - i < 2 ^ 32 by omega_using [hz]),
      show (1 : BitVec 32).toNat = 1 from rfl]
    omega_using [hz, hi]
  rw [ev] at P₅
  obtain e2 : R * 2 ^ (z - i) / 2 = R * 2 ^ (z - (i + 1)) := by
    rw [show z - i = z - (i + 1) + 1 by omega_using [hi], Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
  obtain P₆ : KS g s0 A live (upd AW wR (R * 2 ^ (z - (i + 1)))) (wR :: liveW) (upd V sZ (z - (i + 1))) (sZ :: ls) t :=
    P₅.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, by rw [upd_upd, upd_self, e2]⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ hd, by rw [upd_upd]⟩)
  obtain zz : (u₃.gpr .eax - 1 == 0) = decide (i + 1 = z) := by
    rw [U₃.gpr, upd_self]
    by_cases e : i + 1 = z
    · simp only [e, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z - i < 2 ^ 32 by omega_using [hz])]; simp; omega_using [e]
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro c; have := congrArg BitVec.toNat c
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z - i < 2 ^ 32 by omega_using [hz])] at this; simp at this; omega_using [hz, e, this]
  rw [zz] at z₄
  by_cases e : i + 1 = z
  · refine .inl ⟨by simp only [eval, zf₅, z₄, e, decide_true, Option.map_some, Bool.not_true], upd V sZ 0, ?_,
      fun d hd => by rw [upd_ne _ _ hd]⟩
    rw [← e, Nat.sub_self] at P₆
    rw [Nat.pow_zero, Nat.mul_one] at P₆
    exact P₆
  · exact .inr ⟨by simp only [eval, zf₅, z₄, e, decide_false, Option.map_some, Bool.not_false], z - (i + 1),
      by omega_using [hi], i + 1, rfl, by omega_using [hi, e], P₆⟩

end

/-! ## `divA` -/

section
open VG.Proof.Rsa.X86.WordRt (mw)

/-- `divA`: `m = ⌊a / n⌋` (`wA`) and `r = a mod n` (`wR`), `n` wide again, and whether `m < n`. -/
theorem divA_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n x a : Nat}
    (h : KS g s0 A [aZero, aN] AW [wA] V [sOkDE] s)
    (_hz : A aZero = 0) (hn : A aN = n) (hx : AW wA = x)
    (hxt : VG.Proof.Mont.w32 s.mem g.B (arr g.W wA + 4 * g.W) = 0)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w)
    (hn0 : 2 ^ (32 * (VG.Proof.Rsa.X86.WordRt.wq a - 1)) ≤ n)
    (hn' : n < 2 ^ (32 * VG.Proof.Rsa.X86.WordRt.wq a)) :
    WP isa divA s fun t => ∃ AW' V',
      KS g s0 A [aZero, aN] AW' [wA, wR, wN] V' [sLt, sOkDE] t ∧
      AW' wA = x / n ∧ AW' wR = x % n ∧ AW' wN = n ∧
      V' sLt = b2n (decide (x / n < n)) ∧ V' sOkDE = V sOkDE := by
  obtain hw1 : 16 ≤ wq a := by simp only [wq]; omega_using [ha0]
  obtain hwq : wq a ≤ 256 := by simp only [wq]; omega_using [ha1]
  have wW : g.W = 2 * g.w + 2 := rfl
  obtain pw : 2 ^ (32 * wq a) ≤ 2 ^ (32 * g.w) := Nat.pow_le_pow_right (by decide) (by omega_using [haw])
  obtain pwW : 2 ^ (32 * g.w) ≤ 2 ^ (32 * g.W) := Nat.pow_le_pow_right (by decide) (by omega_using [wW])
  obtain kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  obtain xlt : x < 2 ^ (32 * g.W) := by rw [← hx, ← h.arrsW wA (by simp)]; exact val32_lt _ _ _ _
  obtain n0 : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hn0
  unfold divA
  simp only [seqs]
  -- `n` wide.
  refine WP.seq (WP.mono (h.wideN_ok (by simp) (by decide) (by decide)) fun t₁ ⟨h₁, _, ex₁⟩ => ?_)
  -- `n` and `a` normalized.
  refine WP.seq (WP.mono (normA_ok h₁ (by rw [upd_self, hn]) (by rw [upd_ne _ _ (by decide),
    upd_ne _ _ (by decide), hx]) (by rw [ex₁]; exact hxt) ha ha1 (by omega_using [hw1]) haw xlt hn0 hn')
    fun t₂ ⟨z, hz31, P₂, top₂, lt₂⟩ => ?_)
  obtain ⟨AW₂, V₂, h₂, hz₂, hok₂, hN₂, hA₂, hX₂⟩ := P₂
  -- The division.
  refine WP.seq (WP.mono (wordDivQ_ok h₂.rtW (h₂.mlen ha ha1) (x := wA) (r := wR) (m := wN) (t := wDt)
    (extra := true) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [hw1]) (by rw [kwW]; omega_using [haw, wW]))
    fun t₃ ⟨_, k₃, mw₃, mt₃, rem₃, quo₃, _, K₃⟩ => ?_)
  rw [kwW] at k₃ mw₃ mt₃ rem₃ quo₃
  simp only [xn, kwW, Bool.toNat_true] at rem₃ quo₃
  obtain eN2 : num t₂.mem g.B g.W wN = n * 2 ^ z := by rw [h₂.arrsW wN (by simp), hN₂]
  obtain low2 : val32 t₂.mem g.B (arr g.W wN) (wq a) = n * 2 ^ z := by
    obtain e := val32_mod (m := t₂.mem) (B := g.B) (arr g.W wN) (wq a) (g.W - wq a)
    rw [show wq a + (g.W - wq a) = g.W by omega_using [haw, wW]] at e
    rw [← e]; change num t₂.mem g.B g.W wN % _ = _; rw [eN2, Nat.mod_eq_of_lt lt₂]
  obtain topw : 2 ^ 31 ≤ w32 t₂.mem g.B (arr g.W wN + 4 * (wq a - 1)) := by
    obtain e := val32_top (m := t₂.mem) (B := g.B) (d := arr g.W wN) (W' := wq a) (K := 0) (by omega_using [hw1])
    rw [Nat.add_zero, low2, Nat.mod_eq_of_lt lt₂] at e
    rw [← e, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add,
      show 31 + 32 * (wq a - 1) = 32 * wq a - 1 by omega_using [hw1]]
    exact top₂
  obtain low3 : val32 t₃.mem g.B (arr g.W wN) (wq a) = n * 2 ^ z := by
    rw [← low2]
    apply val32_congr
    intro j hj
    by_cases ej : j = wq a - 1
    · subst ej
      obtain lt32 := (t₂.mem.readW (off g.B (arr g.W wN + 4 * (wq a - 1))) 32).isLt
      have e := mt₃
      simp only [mw] at e
      change w32 t₃.mem g.B (arr g.W wN + 4 * (wq a - 1)) = w32 t₂.mem g.B (arr g.W wN + 4 * (wq a - 1))
      rw [e]
      have : w32 t₂.mem g.B (arr g.W wN + 4 * (wq a - 1)) < 2 ^ 32 := lt32
      omega_using [topw, this]
    · exact mw₃ j (by omega_using [haw, wW, hj]) ej
  rw [hX₂, low3, Nat.mul_mod_mul_right] at rem₃
  rw [hX₂, low3, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _),
    show g.W + 1 - wq a + 1 = g.W - wq a + 2 by omega_using [haw, wW]] at quo₃
  -- Back to the stage's arrays.
  obtain h₂m := h₂.mono (AW' := AW₂) (liveW' := []) (fun j hj => ⟨hj, rfl⟩) (fun j hj => by simp at hj)
    (fun d hd => ⟨hd, rfl⟩)
  obtain h₃ : KS g s0 A [aZero, aN] (upd (upd AW₂ wA (num t₃.mem g.B g.W wA)) wR (num t₃.mem g.B g.W wR))
      [wA, wR] V₂ [sZ, sOkDE] t₃ :=
    h₂m.core k₃ (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact h₂m.wsW.arr_fit (by decide)) (by decide)
      (K₃.mono (by decide)) (h₂m.arrs_W k₃ (by decide) (by decide)) (by decide)
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · rw [upd_ne _ _ (by decide), upd_self]
        · rw [upd_self])
      (by decide) (h₂m.sl_keep k₃ (by decide)) h₂m.ls_ok
  -- The quotient's top words cleared.
  refine WP.seq (WP.mono (h₃.clearQTop_ok (h₃.mlen ha ha1) (by decide) (by omega_using [hw1]) haw) fun t₄ h₄ => ?_)
  rw [quo₃] at h₄
  -- The remainder halved back.
  refine WP.seq (WP.mono (h₄.unnormA_ok (z := z) (R := x % n) (by simp) hz₂ (by simp)
    (by rw [upd_ne _ _ (by decide), upd_self, rem₃]) (by omega_using [hz31]) (by decide)) fun t₅ ⟨V₅, h₅, hV₅⟩ => ?_)
  -- `n` wide again.
  refine WP.seq (WP.mono (h₅.wideN_ok (by simp) (by decide) (by decide)) fun t₆ ⟨h₆, _, _⟩ => ?_)
  -- `m < n`.
  refine WP.seq (WP.mono (h₆.subWrap_W (o := wT) (a := wA) (b := wN) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun t₇ ⟨h₇, b₇⟩ => ?_)
  refine WP.mono (h₇.storeSlot (d := sLt) (by decide) .ebx) fun t ⟨h₈, _, _⟩ => ?_
  rw [b₇] at h₈
  have hn₀ : A 32 = n := hn
  refine ⟨_, _, h₈.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], rfl⟩), ?_, ?_, ?_, ?_, ?_⟩
  · simp [upd, wA, wR, wN, wT]
  · simp [upd, wR, wN, wT]
  · simp [upd, wN, wT, aN, hn₀]
  · simp [upd, wA, wR, wN, aN, hn₀, sLt]
  · have h144 : V₅ 144 = V 144 := by rw [hV₅ 144 (by decide)]; exact hok₂
    simp [upd, sLt, sOkDE, h144]

end
end VG.Proof.Rsa.X86.Recover
