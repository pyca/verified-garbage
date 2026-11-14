module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Proof.Bignum.ShiftStages
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.Sub32
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Framework.Omega

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
  have h₃ := h₂.keep U₃.keeps (by decide) (by decide) (by rw [U₃.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlotZ_ok h₃ (d := oJ) (by decide) .eax) fun u₄ ⟨_, k₄, _, _, _⟩ => ?_
  rw [U₃.mem] at k₄
  have fit := h.ws.fit64 (j := o + 1) ho
  have kwe : kw len = 2 * Spec.Rsa.modulusWords len := rfl
  have wpos := h.kw_pos
  have e : ∀ i, i < kw len + 1 → w32 u₄.mem B (arr (kw len) (o + 1) + 4 * i) = 0 := fun i hi => by
    rw [k₄.word (j := o + 1) (i := i) (by simp only [S]; omega_using [hi]) (by simp) (by decide) fit]
    exact w32_of_val32_zero z₂ hi
  have ea : arr (kw len) (o + 1) = arr (kw len) o + 4 * (kw len + 2) := arr_succ ..
  have e1 := e (kw len - 2) (by omega_using [])
  have e2 := e (kw len - 1) (by omega_using [])
  rw [ea, Nat.add_assoc, ← Nat.mul_add, show kw len + 2 + (kw len - 2) = 2 * kw len by omega_using [kwe, wpos]] at e1
  rw [ea, Nat.add_assoc, ← Nat.mul_add, show kw len + 2 + (kw len - 1) = 2 * kw len + 1 by omega_using [wpos]] at e2
  exact ⟨e1, e2⟩

/-- `mulWide` leaves words `2 w` and `2 w + 1` of `[o]` zero. -/
theorem mulWideTop_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat}
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulWide L o a b) s (TopZ B len o) := by
  have init := WP.and (rowsInit_ok h (a := a) (b := b) ho) (topZ_init h ho)
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
  have Z' : TopZ B len o v :=
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
  have f34 := h₁.ws.arr_fit (j := 34) (by decide)
  have f35 := h₁.ws.arr_fit (j := 35) (by decide)
  simp only [S] at f34 f35
  refine WP.mono (WP.and (VG.Proof.Rsa.X86.WordRt.mulWide_ok h₁.rt (o := 2 * wA) (a := aD) (b := aD)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (mulWideTop_ok h₁.rt (o := 2 * wA) (a := aD) (b := aD)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    fun t ⟨⟨_, k, e, r⟩, z1, z2⟩ => ?_
  rw [kw_nar] at k e z1 z2
  have k' : Keep g.B g.w [34, 35] [VG.Impl.Rsa.X86.WordModRt.oJ] u.mem t.mem := k
  have bD := h₁.arrs aD (by simp)
  rw [upd_self] at bD
  rw [bD] at e
  change w32 t.mem g.B (arr g.w 34 + 4 * (2 * g.w)) = 0 at z1
  change w32 t.mem g.B (arr g.w 34 + 4 * (2 * g.w + 1)) = 0 at z2
  change val32 t.mem g.B (arr g.w 34) (2 * g.w) = _ at e
  have value : num t.mem g.B g.W wA = (q + 1) % 2 ^ (32 * g.w) * ((q + 1) % 2 ^ (32 * g.w)) := by
    change val32 t.mem g.B (arr g.W 17) (2 * g.w + 1 + 1) = _
    rw [arr_W' g 17, show (2 * 17 : Nat) = 34 from rfl, val32_succ, val32_succ, z1, z2, e]
    simp
  have ds : ∀ d ∈ [VG.Impl.Rsa.X86.WordModRt.oJ], SlotOk d := by decide
  have aw := h₁.arrs_w k' (by decide) ds
  have awW := h₁.arrsW_w k' (by decide) ds
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
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  have hkw' := VG.Proof.Rsa.X86.KeyRt.kw_bound hn.lenLe
  have wpos := h.kw_pos
  simp only [S] at fo fa fb
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have eo1 : arr (kw len) (o + 1) = arr (kw len) o + 4 * (kw len + 2) := by
    rw [VG.Proof.Rsa.X86.Keys.arr_succ]
  have gsep : arr (kw len) a + 4 * kw len ≤ arr (kw len) o + 4 * j ∨
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
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sc h₁.ws.workspace (d := oJ) (by rw [oJ_val]; omega_using [hdr])) fun u₂ U₂ _ =>
    wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => ?_
  have e₄ : (u₄.gpr .eax).toNat = 4 * j := by
    rw [U₄.gpr, BitVec.toNat_add, U₃.gpr, BitVec.toNat_add, U₂.gpr, m₁]
    change (((w32 s.mem B oJ) + w32 s.mem B oJ) % 2 ^ 32 + ((w32 s.mem B oJ) + w32 s.mem B oJ) % 2 ^ 32) % 2 ^ 32 = _
    rw [show w32 s.mem B oJ = j from hj]; omega_using [hjw, hkw]
  have p₅ : PtrAt u₅ B .ebx (arr (kw len) b + 4 * j) := by
    rw [PtrAt, U₅.gpr, BitVec.toNat_add, U₄.other .ebx (by decide), U₃.other .ebx (by decide),
      U₂.other .ebx (by decide), p₁, e₄]
    have := B.isLt; omega_using []
  have K₅ : Keeps [.eax, .ebx, .edx] s u₅ := (K₁.mono (by decide)).trans
    (((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide))).trans
      ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))))
  have m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  refine wp_movS (readSrc_ptr (ws.of_keeps K₅) p₅ (d := 0) (by omega_using [hjw, fb])) fun u₆ U₆ _ => ?_
  have K₆ : Keeps [.eax, .ebx, .ecx, .edx] s u₆ := (K₅.mono (by decide)).trans (U₆.keeps.mono (by decide))
  have h₆ := h.keep K₆ (by decide) (by decide) (by rw [U₆.mem, m₅]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₆) h₆.lenLe h₆.edi (r := .ebp) (t := .edx) (j := o) (by decide) (by decide)
    (by omega_using [nw, fo, eo1]) fun u₇ K₇ m₇ p₇ _ => wp_addS rfl fun u₈ U₈ _ => ?_
  have p₈ : PtrAt u₈ B .ebp (arr (kw len) o + 4 * j) := by
    rw [PtrAt, U₈.gpr, BitVec.toNat_add, p₇, K₇.1 .eax (by decide), U₆.other .eax (by decide), U₅.other .eax (by decide), e₄]
    have := B.isLt; omega_using []
  have K₈ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₈ := (K₆.mono (by decide)).trans
    ((K₇.mono (by decide)).trans (U₈.keeps.mono (by decide)))
  have h₈ := h.keep K₈ (by decide) (by decide) (by rw [U₈.mem, m₇, U₆.mem, m₅]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₈) h₈.lenLe h₈.edi (r := .esi) (t := .edx) (j := a) (by decide) (by decide)
    (by omega_using [nw, fa]) fun u₉ K₉ m₉ p₉ _ => bytesB_ok ((lenSrc h₈).keep K₉ (by decide) m₉) h.lenLe fun u₁₀ K₁₀ m₁₀ e₁₀ =>
      wp_movS rfl fun u₁₁ U₁₁ _ => WP.block_nil ?_
  have m₁₁ : u₁₁.mem = s.mem := by rw [U₁₁.mem, m₁₀, m₉, U₈.mem, m₇, U₆.mem, m₅]
  have bj : (u₁₁.gpr .ecx).toNat = w32 s.mem B (arr (kw len) b + 4 * j) := by
    rw [U₁₁.other _ (by decide), K₁₀.1 _ (by decide), K₉.1 _ (by decide), U₈.other _ (by decide),
      K₇.1 _ (by decide), U₆.gpr, m₅, Nat.add_zero]
  have K₁₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u₁₁ := (K₈.mono (by decide)).trans
    (((K₉.mono (by decide)).trans (K₁₀.mono (by decide))).trans (U₁₁.keeps.mono (by decide)))
  have I₀ : RowI u₁₁ B (arr (kw len) a) (arr (kw len) o + 4 * j) (kw len) 0 u₁₁ :=
    ⟨by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₁.other _ (by decide), K₁₀.1 _ (by decide)]; exact p₉,
      by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₁.other _ (by decide), K₁₀.1 _ (by decide),
        K₉.1 _ (by decide)]; exact p₈,
      by apply BitVec.eq_of_toNat_eq
         rw [U₁₁.other _ (by decide), e₁₀, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hkw])],
      rfl, Keeps.refl _ _, Outside.refl _ _ _ _, by rw [U₁₁.gpr]; simp [val32]⟩
  refine WP.seq (WP.mono (rowLoop_ok (ws.of_keeps K₁₁) nw (by omega_arith) (by omega_arith) (by omega_using [gsep]) (by omega_using [hkw]) wpos I₀)
    fun u I => ?_)
  -- The carry, `edi`, and the count.
  have wsu : Ws u B Z := (ws.of_keeps K₁₁).of_wr I.keep.2.2
  refine wp_storeS (ea_ptr wsu I.bp (d := 0) (by omega_arith)) (ws_write wsu (by omega_arith)) fun t₁ M₁ => ?_
  have O₁ := writeW32_outside u.mem B (d := arr (kw len) o + 4 * j + 4 * kw len + 0) (u.gpr .ebx) (by omega_arith)
  rw [← M₁.mem] at O₁
  have Orow : Outside B (arr (kw len) o + 4 * j) (4 * (kw len + 1)) s.mem t₁.mem := by
    rw [← m₁₁]; exact (I.out.mono (by omega_using []) (by omega_using [])).trans (O₁.mono (by omega_using []) (by omega_using []))
  have K₁ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t₁ :=
    K₁₁.trans ((I.keep.mono (by decide)).trans (M₁.keeps _))
  have ca := h.wsArg.keep K₁ₜ (by decide) (Orow.mono (Nat.zero_le _) (by omega_arith))
  simp only [restoreEdi, List.cons_append, List.nil_append]
  refine wp_movS ca.readSrc fun t₂ T₂ _ => ?_
  have K₂ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₂ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi])
      ((K₁ₜ.trans (T₂.keeps.mono (by decide))).mono (by decide)) (T₂.gpr.trans h.edi_eq.symm)
  have Z₂ : Outside B 0 Z s.mem t₂.mem := by rw [T₂.mem]; exact Orow.mono (Nat.zero_le _) (by omega_arith)
  have h₂ : RtWs wid t₂ B Z len N := h.keep K₂ₜ (by decide) (by decide) Z₂
  have hn₂ : RtWs nar t₂ B Z len' N' := hn.keep K₂ₜ (by decide) (by decide) Z₂
  have hoJ : oJ + 4 ≤ arr (kw len) o + 4 * j := by rw [oJ_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega_using []
  have oj₂ : slot t₂.mem B oJ = j := by
    rw [slot, T₂.mem, Orow.w32 (.inl hoJ) (by rw [oJ_val]; omega_using [])]; exact hj
  refine wp_movS (readSrc_sc h₂.ws.workspace (d := oJ) (by rw [oJ_val]; omega_using [hdr])) fun t₃ T₃ _ =>
    wp_addS rfl fun t₄ T₄ _ => ?_
  have e₄' : (t₄.gpr .eax).toNat = j + 1 := by
    rw [T₄.gpr, BitVec.toNat_add, T₃.gpr]
    change (w32 t₂.mem B oJ + 1) % 2 ^ 32 = _
    rw [show w32 t₂.mem B oJ = j from oj₂]; omega_using [e₄]
  have K₄ₜ : Keeps [.eax] t₂ t₄ := (T₃.keeps.mono (by decide)).trans (T₄.keeps.mono (by decide))
  have m₄₂ : t₄.mem = t₂.mem := by rw [T₄.mem, T₃.mem]
  have h₄ := h₂.keep K₄ₜ (by decide) (by decide) (by rw [m₄₂]; exact Outside.refl _ _ _ _)
  have hn₄ := hn₂.keep K₄ₜ (by decide) (by decide) (by rw [m₄₂]; exact Outside.refl _ _ _ _)
  refine wp_storeS (h₄.ws.workspace.ea (by rw [oJ_val]; omega_using [hdr])) (h₄.ws.workspace.write (by rw [oJ_val]; omega_using [hdr]))
    fun t₅ M₅ => ?_
  have O₅ := writeW32_outside t₄.mem B (d := oJ) (t₄.gpr .eax) (by rw [oJ_val]; omega_using [])
  rw [← M₅.mem] at O₅
  have h₅ : RtWs wid t₅ B Z len N := h₄.keep (M₅.keeps []) (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by rw [oJ_val]; omega_using [hdr]))
  have hn₅ : RtWs nar t₅ B Z len' N' := hn₄.keep (M₅.keeps []) (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by rw [oJ_val]; omega_using [hdr]))
  have K₅ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₅ := K₂ₜ.trans ((K₄ₜ.mono (by decide)).trans (M₅.keeps _))
  have m₁ : t₁.mem = u.mem.writeW (off B (arr (kw len) o + 4 * j + 4 * kw len)) (u.gpr .ebx) := by
    rw [M₁.mem, Nat.add_zero]
  have m₁₄ : t₁.mem = t₄.mem := by rw [m₄₂, T₂.mem]
  have kk : Keep B (kw len) [o, o + 1] [oJ] s.mem t₁.mem :=
    keep_of_two (w := kw len) (o := o) Orow (by omega_using []) (by simp only [S]; omega_arith) (by simp) (by simp)
  have ax₅ : (t₅.gpr .eax).toNat = j + 1 := by rw [M₅.gpr]; exact e₄'
  refine bytesB_ok (lenSrc hn₅) hn.lenLe fun t₆ K₆ m₆ e₆ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t₇ U₇ => wp_cmp fun v F _ z => WP.block_nil ?_
  have Fk : Keeps [] t₇ v := ⟨fun r _ => by rw [F.gpr], F.rd, F.wr⟩
  have K₇ : Keeps [.ecx] t₅ v := (K₆.trans (U₇.keeps.mono (by decide))).trans (Fk.mono (by simp))
  have mv : v.mem = t₅.mem := by rw [F.mem, U₇.mem, m₆]
  have ecx : (t₇.gpr .ecx).toNat = kw len' := by
    have kwe : kw len' = 2 * Spec.Rsa.modulusWords len' := rfl
    rw [U₇.gpr, BitVec.toNat_ushiftRight, e₆, Nat.shiftRight_eq_div_pow]; omega_using []
  have eax : (t₇.gpr .eax).toNat = j + 1 := by
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
    have hoJ0 : oJ + 4 ≤ arr (kw len) o := by rw [oJ_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega_using []
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
  have fitb := h.ws.fit64 hb
  have fita := h.ws.fit64 ha
  have fo := h.ws.arr_fit ho
  simp only [S] at fo
  have Iv := I.val
  simp only [VG.Proof.Rsa.X86.WordRt.rowW] at Iv
  refine WP.mono (rowWRow_ok I.ws In ho ha hb hao hao1 I.cnt (by omega_using [hw, hj]))
    fun v ⟨hv, hnv, kv, ev, wv, cv, zv, Kv⟩ => ⟨zv, ?_, hnv⟩
  have Ia : val32 u.mem B (arr (kw len) a) (kw len) = val32 s.mem B (arr (kw len) a) (kw len) :=
    val32_congr fun i hi => I.keep.word (j := a) (i := i) (by simp only [S]; omega_using [hi]) (by simp; omega_using [hao, hao1]) (by decide) fita
  have Ibj : w32 u.mem B (arr (kw len) b + 4 * j) = w32 s.mem B (arr (kw len) b + 4 * j) :=
    I.keep.word (j := b) (i := j) (by simp only [S]; omega_using [hw, hj]) (by simp; omega_using [hbo, hbo1]) (by decide) fitb
  refine ⟨hv, I.keep.trans kv, I.rest.trans Kv, cv, ?_, fun hh => nomatch hh⟩
  have hlow : val32 v.mem B (arr (kw len) o) j = val32 u.mem B (arr (kw len) o) j :=
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
  have fa := h.wsW.arr_fit (j := wA) (by decide)
  simp only [S] at fa
  rw [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW) hW.lenLe hW.edi
    (r := .eax) (t := .edx) (j := wA) (by decide) (by decide) (by rw [kw_wid]; change arr g.W wA < 2 ^ 32; omega_using [nw, fa])
    fun u₁ U₁ m₁ p₁ _ => ?_
  have hW₁ := hW.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW₁) hW₁.lenLe (r := .ecx)
    fun u₂ U₂ m₂ e₂ => ?_
  rw [kw_wid] at p₁ e₂
  change PtrAt u₁ g.B .eax (arr g.W wA) at p₁
  change (u₂.gpr .ecx).toNat = 4 * g.W at e₂
  refine wp_addS rfl fun u₃ U₃ _ => wp_movS (v := 0) rfl fun u₄ U₄ _ => ?_
  have p₃ : PtrAt u₃ g.B .eax (arr g.W wA + 4 * g.W) := by
    rw [PtrAt, U₃.gpr, BitVec.toNat_add, U₂.1 _ (by decide), p₁, e₂]
    have := g.B.isLt; omega_using []
  have p₄ : PtrAt u₄ g.B .eax (arr g.W wA + 4 * g.W) := by rw [PtrAt, U₄.other _ (by decide)]; exact p₃
  have ws₄ := ((h.rt.rt.of_wr U₁.2.2).of_wr U₂.2.2).of_wr (U₄.wr.trans U₃.wr)
  refine wp_storeS (ea_ptr ws₄ p₄ (d := 0) (by omega_using [fa])) (ws_write ws₄ (by omega_using [fa])) fun t₁ M₁ => ?_
  have p₁' : PtrAt t₁ g.B .eax (arr g.W wA + 4 * g.W) := by rw [PtrAt, M₁.gpr]; exact p₄
  have ws₁ := ws₄.of_wr M₁.wr
  refine wp_storeS (ea_ptr ws₁ p₁' (d := 4) (by omega_using [fa])) (ws_write ws₁ (by omega_using [fa])) fun t₂ M₂ => WP.block_nil ?_
  have c₄ : u₄.gpr .ecx = 0 := U₄.gpr
  have O₁ := writeW32_outside u₄.mem g.B (d := arr g.W wA + 4 * g.W + 0) (u₄.gpr .ecx) (by omega_using [nw, fa])
  rw [← M₁.mem] at O₁
  have O₂ := writeW32_outside t₁.mem g.B (d := arr g.W wA + 4 * g.W + 4) (t₁.gpr .ecx) (by omega_using [nw, fa])
  rw [← M₂.mem] at O₂
  have m₄ : u₄.mem = s.mem := by rw [U₄.mem, U₃.mem, m₂, m₁]
  have O : Outside g.B (arr g.W wA + 4 * g.W) 8 s.mem t₂.mem := by
    rw [← m₄]; exact (O₁.mono (by omega_using []) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))
  have k : Keep g.B g.W [wA] [] s.mem t₂.mem := Keep.of_arr (d := 4 * g.W) O (by simp only [S]; omega_using []) (by simp)
  have r : Keeps opRegs s t₂ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans
      ((M₁.keeps _).trans (M₂.keeps _)))))
  have e : num t₂.mem g.B g.W wA = AW wA := by
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
  have g1lt : g1 < 2 ^ (32 * g.w) := by rw [← hg, ← h.arrs aG (by simp)]; exact val32_lt _ _ _ _
  have kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  have kwN : VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8) = g.w := kw_nar _
  have w18 : 18 ≤ g.w := by have := h.lower; simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega_using [this]
  have wW : g.W = 2 * g.w + 2 := rfl
  unfold aProduct
  simp only [seqs]
  refine WP.seq (WP.mono (h.zeroWide_W (j := wT) (by decide) (by decide)) fun u₁ ⟨h₁, z₁⟩ => ?_)
  have h₁' : KS g s0 A [aG, aZero, aN] (upd AW wT 0) [wX3] V [sOkDE] u₁ :=
    h₁.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h₁'.widen (k := wT) (a := aG) (by decide) (by simp) (by decide) z₁ (by decide)
    (by decide)) fun u₂ ⟨h₂, _⟩ => ?_)
  refine WP.seq (WP.mono (h₂.zeroWide_W (j := wA) (by decide) (by decide)) fun u₃ ⟨h₃, _⟩ => ?_)
  refine WP.seq (WP.mono (h₃.zeroWide_W (j := wA + 1) (by decide) (by decide)) fun u₄ ⟨h₄, _⟩ => ?_)
  refine WP.seq (wp_movS (v := 0) rfl fun u₅ U₅ _ => ?_)
  have h₅ := h₄.of_rest U₅.keeps (by decide) U₅.mem
  refine WP.mono (h₅.storeSlot (d := VG.Impl.Rsa.X86.WordModRt.oJ) (by decide) .eax) fun u₆ ⟨h₆, _, _⟩ => ?_
  rw [U₅.gpr] at h₆
  -- The rows.
  have I₀ : VG.Proof.Rsa.X86.WordRt.RowsI wid u₆ g.B g.Z (16 * g.n + 24) 22 wA wX3 wT 0 false u₆ := by
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
  have ex : val32 u₆.mem g.B (arr g.W wX3) g.W = x3 := by
    change num u₆.mem g.B g.W wX3 = x3
    rw [h₆.arrsW wX3 (by simp)]
    simp only [upd, show wX3 ≠ wA + 1 by decide, show wX3 ≠ wA by decide, show wX3 ≠ wT by decide,
      ↓reduceIte, hx]
  have eg : val32 u₆.mem g.B (arr g.W wT) g.w = g1 := by
    have e := h₆.arrsW wT (by simp)
    simp only [upd, show wT ≠ wA + 1 by decide, show wT ≠ wA by decide, ↓reduceIte, hg] at e
    rw [← Nat.mod_eq_of_lt g1lt, ← e]
    change val32 u₆.mem g.B (arr g.W wT) g.w = val32 u₆.mem g.B (arr g.W wT) (2 * g.w + 2) % 2 ^ (32 * g.w)
    rw [show 2 * g.w + 2 = g.w + (g.w + 2) by omega_using [], val32_mod]
  rw [ex, eg] at Iv
  have P : num v.mem g.B g.W wA = x3 * g1 % 2 ^ (32 * g.W) := by
    change val32 v.mem g.B (arr g.W wA) g.W = _
    rw [← val32_mod (k := g.w), Nat.add_comm, Iv]
  have k : Keep g.B g.W [wA, wA + 1] [VG.Impl.Rsa.X86.WordModRt.oJ] u₆.mem v.mem := by
    have := I.keep; rw [kwW] at this; exact this
  have ds : ∀ d ∈ [VG.Impl.Rsa.X86.WordModRt.oJ], SlotOk d := by decide
  have h₆m := h₆.mono (ls' := [sOkDE]) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
  have aw := h₆m.arrs_W k (by decide) ds
  have h₇ : KS g s0 A [aZero, aN] (upd (upd (upd (upd (upd AW wT 0) wT (A aG)) wA 0) (wA + 1) 0) wA
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
