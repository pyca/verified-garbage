module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# FFDH on x86-64: an exponentiation

`pow bp bl ep el` in the inner workspace for a modulus `X`, with `R² mod X`
in `aR2`: the base (pointer and length in the outer slots `bp`, `bl`) into
`aXm`; the accumulator `R mod X` and the base in Montgomery form; `R²` kept
in `aX` while the base takes `aXc` (array `aR2`); RSA's fixed-window
exponentiation over every octet of the exponent (slots `ep`, `el`); the
result out of Montgomery form; `R²` back (`pow_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The inner workspace for the modulus `X`, `-X⁻¹`, the number 1 and
`R² mod X`. -/
structure ModCtx (t : State) (B : Addr) (Z o w : Nat) (mi : BitVec 64) (X : Nat) : Prop where
  sub : SubCtx t B Z o w w mi
  xv : XVals t B o w mi X
  r2l : wv t.mem (off B o) (slot w aR2) w < X
  r2 : wv t.mem (off B o) (slot w aR2) w % X = 2 ^ (64 * w) * 2 ^ (64 * w) % X
  odd : X % 2 = 1
  x1 : 1 < X
  wide : o + slot w 8 + tabBytes w 32 ≤ Z
  w2 : 2 ≤ w
  w28 : w < 2 ^ 28

/-- What `pow` changes in the inner workspace. -/
def powRanges (w : Nat) : List (Nat × Nat) :=
  (slot w aX, 8 * (w + 2)) :: (slot w aR2, 8 * (w + 2)) :: (slot w aXm, 8 * (w + 2)) :: crtExpRanges5 w

theorem powRanges_ok (w : Nat) : ∀ r ∈ powRanges w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 + tabBytes w 32 := by
  intro r hr
  simp only [powRanges, List.mem_cons] at hr
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have s0 := slot_le (w := w) (show aX < 8 by decide)
  have s1 := slot_le (w := w) (show aR2 < 8 by decide)
  have s2 := slot_le (w := w) (show aXm < 8 by decide)
  have g1 := slot_le (w := w) (show 0 < 8 by decide)
  have e0 : slot w 0 = 256 := by unfold slot hdrBytes; omega_arith
  rcases hr with rfl | rfl | rfl | hr
  · have := hdr_lt_slot w aX (show 31 < 32 by decide); simp only; unfold tabBytes; omega_arith
  · have := hdr_lt_slot w aR2 (show 31 < 32 by decide); simp only; unfold tabBytes; omega_arith
  · have := hdr_lt_slot w aXm (show 31 < 32 by decide); simp only; unfold tabBytes; omega_arith
  · exact crtExpRanges5_ok w r hr

/-- `XVals` after a change of memory outside the modulus, the number 1 and the
header's first 17 slots. -/
theorem _root_.VG.Proof.Bignum.X86_64.XVals.of_frmA {s t : State} {B : Addr} {o w : Nat} {mi : BitVec 64} {X : Nat} {rs : List (Nat × Nat)}
    (h : XVals s B o w mi X) (hn : (off B o).toNat + slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w)
    (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, (r.1 + r.2 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ r.1) ∧
      (r.1 + r.2 ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ r.1)) : XVals t B o w mi X := by
  have sN := slot_le (w := w) (show aN < 8 by decide)
  have sO := slot_le (w := w) (show aOne < 8 by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [hf.wv_eq (fun r hr' => by have := (hr r hr').1; omega_arith) (by omega_arith)]; exact h.n
  · rw [hf.word_eq (fun r hr' => by have := (hr r hr').1; omega_arith) (by omega_arith)]; exact h.inv
  · rw [hf.wv_eq (fun r hr' => by have := (hr r hr').2; omega_arith) (by omega_arith)]; exact h.one

/-- The ranges of arrays other than the modulus and the number 1. -/
theorem arr_off (w : Nat) {j : Nat} (h0 : j ≠ aN) (h7 : j ≠ aOne) :
    ((slot w j + 8 * (w + 2) ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ slot w j) ∧
      (slot w j + 8 * (w + 2) ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ slot w j)) :=
  ⟨slot_sep (w := w) h0, slot_sep (w := w) h7⟩

/-- A change of the inner workspace (with its table) keeps the outer header,
and memory past the inner workspace. -/
theorem child_frm {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (hc : SubCtx s B Z o w w mi) (hwide : o + slot w 8 + tabBytes w 32 ≤ Z) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ slot w 8 + tabBytes w 32) :
    (∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i)) ∧ InScr B Z s.mem t.mem := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hL : o + (slot w 8 + tabBytes w 32) ≤ 2 ^ 64 := by omega_arith
  have h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  refine ⟨fun i hi => hf.word_below hr hL (by unfold slot hdrBytes at hL; omega_arith)
    (by have := hdr_lt_slot w 8 hi; omega_arith), ?_⟩
  refine InScr.of_frm (hf.rebase (by omega_arith) fun r hr' => by have := hr r hr'; omega_arith) fun r hr' => ?_
  simp only [shiftRanges, List.mem_map] at hr'
  obtain ⟨r', hr'', rfl⟩ := hr'
  have := hr r' hr''
  simp only
  omega_arith

theorem pow_ok (M : Mont) (E : CrtExpL M) {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {X : Nat}
    (hc : ModCtx s B Z o w mi X)
    {bp bl ep el : Nat} (hbp : bp < 32) (hbl : bl < 32) (hep : ep < 32) (hel : el < 32)
    {pb pe : Addr} {bb eb : List Byte}
    (hpb : word s.mem B (8 * bp) = pb) (hlb : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : (bb.length + 7) / 8 ≤ w)
    (hpe : word s.mem B (8 * ep) = pe) (hle : word s.mem B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src s B Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (seqs (pow M.mm E.code bp bl ep el)) s fun t => ModCtx t B Z o w mi X ∧
      wv t.mem (off B o) (slot w aY) w = Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % X ∧
      Frm (off B o) (powRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw2 := hc.w2
  have hw28 := hc.w28
  have hn := hc.sub.scr.nowrap
  have hGn : (off B o).toNat + slot w 8 ≤ 2 ^ 64 := hc.sub.good.scr.nowrap
  have hlo := hc.sub.lo
  have hwide := hc.wide
  have hR : Nat.Coprime (2 ^ (64 * w)) X := VG.Proof.Bignum.coprime_pow2 hc.odd _
  have hX0 : 0 < X := by have := hc.x1; omega_arith
  have h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have sXa := slot_le (w := w) (show aX < 8 by decide)
  have sR := slot_le (w := w) (show aR2 < 8 by decide)
  have sXm := slot_le (w := w) (show aXm < 8 by decide)
  have sY := slot_le (w := w) (show aY < 8 by decide)
  -- Arrays of the steps' ranges, all at least `8 * 17` and below `slot w 8`.
  have hA : ∀ j < 8, 8 * 17 ≤ slot w j := fun j hj => by have := hdr_lt_slot w j (show 31 < 32 by decide); omega_arith
  unfold pow
  simp only [List.append_assoc]
  -- The base into `aXm`.
  refine wp_seqs_append (by simp [loadArr]) (by simp) (WP.mono (primeLoad_ok hc.sub hw2 (Nat.le_refl _) (by omega_arith)
    (show aXm < 8 by decide) hbp hbl hpb hlb hsb hb1 (by omega_arith) hb2) fun s₁ ⟨hs₁, hb₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (off B o) [(slot w aXm, 8 * (w + 2))] s.mem s₁.mem := Frm.of_outside ho₁ (by simp)
  have hv₁ : XVals s₁ B o w mi X := hc.xv.of_frmA hGn (by omega_arith) f₁ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  have hr2₁ : wv s₁.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w :=
    f₁.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) (show aR2 ≠ aXm by decide); omega_arith) (by omega_arith)
  have hg₁ := hs₁.good
  have hinv₁ := hv₁.inv
  -- `Y := R` (`R² · 1`).
  simp only [List.cons_append, List.nil_append]
  refine wp_seqs_cons (by simp) (WP.mono (M.mm_ok hg₁ (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := aR2) (b := aOne)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hinv₁
    (by rw [hv₁.one, hv₁.n]; exact hc.x1)) fun s₂ ⟨hg₂, hYl₂, hYv₂, ha₂, k₂⟩ => ?_)
  simp only [hv₁.n, hv₁.one, Nat.mul_one] at hYl₂ hYv₂
  have f₂ : Frm (off B o) [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]
      s₁.mem s₂.mem := Frm.of_arrays ha₂ (by simp)
  have rng₂ : ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))],
      8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
  have hs₂ := hs₁.of_frm f₂ rng₂ k₂.2.2 (k₂.gpr (by decide))
  have hv₂ := hv₁.of_frmA hGn (by omega_arith) f₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact arr_off w (by decide) (by decide))
  have nY : ∀ {j}, j < 8 → j ≠ aAcc → j ≠ aTmp → j ≠ aY → wv s₂.mem (off B o) (slot w j) w = wv s₁.mem (off B o) (slot w j) w :=
    fun hj h1 h2 h3 => ha₂.wv_of_not_mem hj (by simp [h1, h2, h3]) hGn
  have hR2₂ : wv s₂.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w := by
    rw [nY (by decide) (by decide) (by decide) (by decide), hr2₁]
  have hXm₂ : wv s₂.mem (off B o) (slot w aXm) w = Spec.Rsa.os2ip bb := by
    rw [nY (by decide) (by decide) (by decide) (by decide), hb₁]
  have hYR : wv s₂.mem (off B o) (slot w aY) w % X = 2 ^ (64 * w) % X := by
    apply mont_cancel hR
    rw [hYv₂, hr2₁, hc.r2]
  -- `Xm := b R`.
  refine wp_seqs_cons (by simp) (WP.mono (M.mm_ok hs₂.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aXm) (a := aXm)
    (b := aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv₂.inv
    (by rw [hR2₂, hv₂.n]; exact hc.r2l)) fun s₃ ⟨_, hXl₃, hXv₃, ha₃, k₃⟩ => ?_)
  simp only [hv₂.n, hXm₂, hR2₂] at hXv₃ hXl₃
  have f₃ : Frm (off B o) [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]
      s₂.mem s₃.mem := Frm.of_arrays ha₃ (by simp)
  have hs₃ := hs₂.of_frm f₃ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₃.2.2 (k₃.gpr (by decide))
  have hv₃ := hv₂.of_frmA hGn (by omega_arith) f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact arr_off w (by decide) (by decide))
  have nXm : ∀ {j}, j < 8 → j ≠ aAcc → j ≠ aTmp → j ≠ aXm →
      wv s₃.mem (off B o) (slot w j) w = wv s₂.mem (off B o) (slot w j) w :=
    fun hj h1 h2 h3 => ha₃.wv_of_not_mem hj (by simp [h1, h2, h3]) hGn
  have hXb : wv s₃.mem (off B o) (slot w aXm) w % X = Spec.Rsa.os2ip bb * 2 ^ (64 * w) % X := by
    apply mont_cancel hR
    rw [hXv₃, Nat.mul_mod, hc.r2, ← Nat.mul_mod, Nat.mul_assoc]
  -- `aX := R²`, `aXc := b R`.
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hs₃.good (Nat.le_refl _) (by omega_arith)
    (by omega_arith) (show aX < 8 by decide) (show aR2 < 8 by decide) (by decide)) fun s₄ ⟨hX₄, ho₄, k₄⟩ => ?_)
  have f₄ : Frm (off B o) [(slot w aX, 8 * (w + 2))] s₃.mem s₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot w aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hs₄ := hs₃.of_frm f₄ (by
    simp only [List.mem_singleton, forall_eq]; exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₄.2.2 (k₄.gpr (by decide))
  have hv₄ := hv₃.of_frmA hGn (by omega_arith) f₄ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  have n₄ : ∀ {j}, j < 8 → j ≠ aX → wv s₄.mem (off B o) (slot w j) w = wv s₃.mem (off B o) (slot w j) w :=
    fun hj h1 => f₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) h1; omega_arith)
      (by have := slot_le (w := w) hj; omega_arith)
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hs₄.good (Nat.le_refl _) (by omega_arith)
    (by omega_arith) (show Crt.aXc < 8 by decide) (show aXm < 8 by decide) (by decide)) fun s₅ ⟨hX₅, ho₅, k₅⟩ => ?_)
  have eXc : Crt.aXc = aR2 := rfl
  rw [eXc] at hX₅ ho₅
  have f₅ : Frm (off B o) [(slot w aR2, 8 * (w + 2))] s₄.mem s₅.mem :=
    Frm.of_outside (ho₅.mono (o' := slot w aR2) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hs₅ := hs₄.of_frm f₅ (by
    simp only [List.mem_singleton, forall_eq]; exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₅.2.2 (k₅.gpr (by decide))
  have hv₅ := hv₄.of_frmA hGn (by omega_arith) f₅ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  have n₅ : ∀ {j}, j < 8 → j ≠ aR2 → wv s₅.mem (off B o) (slot w j) w = wv s₄.mem (off B o) (slot w j) w :=
    fun hj h1 => f₅.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) h1; omega_arith)
      (by have := slot_le (w := w) hj; omega_arith)
  -- Values before the exponentiation.
  have hXc₅ : wv s₅.mem (off B o) (slot w Crt.aXc) w = wv s₃.mem (off B o) (slot w aXm) w := by
    rw [eXc, hX₅, n₄ (by decide) (by decide)]
  have hY₅ : wv s₅.mem (off B o) (slot w aY) w = wv s₂.mem (off B o) (slot w aY) w := by
    rw [n₅ (by decide) (by decide), n₄ (by decide) (by decide), nXm (by decide) (by decide) (by decide) (by decide)]
  have hXa₅ : wv s₅.mem (off B o) (slot w aX) w = wv s.mem (off B o) (slot w aR2) w := by
    rw [n₅ (by decide) (by decide), hX₄, nXm (by decide) (by decide) (by decide) (by decide)]; exact hR2₂
  -- The exponentiation.
  have F₅ : Frm (off B o) ([(slot w aXm, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
      (slot w aY, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++
      [(slot w aX, 8 * (w + 2))] ++ [(slot w aR2, 8 * (w + 2))]) s.mem s₅.mem :=
    (((f₁.append f₂).append f₃).append f₄).append f₅
  have rF₅ : ∀ r ∈ ([(slot w aXm, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
      (slot w aY, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++
      [(slot w aX, 8 * (w + 2))] ++ [(slot w aR2, 8 * (w + 2))]), r ∈ powRanges w := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [powRanges, crtExpRanges5, crtExpRanges, crtWinRanges, List.mem_cons]
    rcases hr with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  obtain ⟨hb₅, hi₅⟩ := child_frm hc.sub hwide F₅ (fun r hr => (powRanges_ok w r (rF₅ r hr)).2)
  have K₅ := keep_trans (keep_trans (keep_trans (keep_trans k₁ k₂) k₃) k₄) k₅
  refine wp_seqs_append (E.ne ep el) (by simp) (WP.mono (E.ok (Q := True) (x := Spec.Rsa.os2ip bb) (ep := pe) (eb := eb) hs₅ (by simpa [wsTab] using hwide) hw2
    (Nat.le_refl _) (by omega_arith) hv₅.n hv₅.inv hc.odd (by rw [hXc₅]; exact hXl₃) (fun _ => by rw [hXc₅]; exact hXb)
    (by rw [hY₅]; exact hYl₂) (fun _ => by rw [hY₅]; exact hYR) hep hel (by rw [hb₅ _ hep]; exact hpe)
    (by rw [hb₅ _ hel]; exact hle) he1 he2 (hse.congrK hi₅ K₅)) fun s₆ ⟨hs₆, hYl₆, hYv₆, f₆, k₆⟩ => ?_)
  have hYv₆' := hYv₆ trivial
  have hv₆ := hv₅.of_frmA hGn (by omega_arith) f₆ (fun r hr => by
    have := crtExpRanges5_ok w r hr
    simp only [crtExpRanges5, crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    have s8 := hdr_lt_slot w aN (show 31 < 32 by decide)
    have s7 := hdr_lt_slot w aOne (show 31 < 32 by decide)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold slot hdrBytes; simp only [aN, aOne, aAcc, aTmp, aY, Crt.aT, Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sTab,
      Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, Crt.sPow, sFn, tabBytes]; omega_arith))
  have hX₆ : wv s₆.mem (off B o) (slot w aX) w = wv s₅.mem (off B o) (slot w aX) w := by
    refine f₆.wv_eq (fun r hr => ?_) (by omega_arith)
    simp only [crtExpRanges5, crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold slot hdrBytes; simp only [aX, aAcc, aTmp, aY, Crt.aT, Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sTab,
      Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, Crt.sPow, sFn, tabBytes]; omega_arith)
  -- `Y := Y R⁻¹`, out of Montgomery form.
  refine wp_seqs_cons (by simp [copyArr]) (WP.mono (M.mm_ok hs₆.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := aY)
    (b := aOne) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv₆.inv
    (by rw [hv₆.one, hv₆.n]; exact hc.x1)) fun s₇ ⟨_, hYl₇, hYv₇, ha₇, k₇⟩ => ?_)
  simp only [hv₆.n, hv₆.one, Nat.mul_one] at hYl₇ hYv₇
  have hY₇ : wv s₇.mem (off B o) (slot w aY) w = Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % X := by
    rw [← Nat.mod_eq_of_lt hYl₇]
    exact mont_cancel hR (by rw [hYv₇, hYv₆'])
  have f₇ : Frm (off B o) [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]
      s₆.mem s₇.mem := Frm.of_arrays ha₇ (by simp)
  have hs₇ := hs₆.of_frm f₇ rng₂ k₇.2.2 (k₇.gpr (by decide))
  have hv₇ := hv₆.of_frmA hGn (by omega_arith) f₇ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact arr_off w (by decide) (by decide))
  have hX₇ : wv s₇.mem (off B o) (slot w aX) w = wv s.mem (off B o) (slot w aR2) w := by
    rw [ha₇.wv_of_not_mem (by decide) (by decide) hGn, hX₆, hXa₅]
  -- `R²` back.
  refine WP.mono (copyArr_ok hs₇.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show aR2 < 8 by decide)
    (show aX < 8 by decide) (by decide)) fun t ⟨hR₈, ho₈, k₈⟩ => ?_
  have f₈ : Frm (off B o) [(slot w aR2, 8 * (w + 2))] s₇.mem t.mem :=
    Frm.of_outside (ho₈.mono (o' := slot w aR2) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hs₈ := hs₇.of_frm f₈ (by
    simp only [List.mem_singleton, forall_eq]; exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₈.2.2 (k₈.gpr (by decide))
  have hv₈ := hv₇.of_frmA hGn (by omega_arith) f₈ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  have hY₈ : wv t.mem (off B o) (slot w aY) w = wv s₇.mem (off B o) (slot w aY) w :=
    f₈.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) (show aY ≠ aR2 by decide); omega_arith)
      (by omega_arith)
  refine ⟨⟨hs₈, hv₈, by rw [hR₈, hX₇]; exact hc.r2l, by rw [hR₈, hX₇]; exact hc.r2, hc.odd, hc.x1, hwide, hw2, hw28⟩,
    by rw [hY₈, hY₇], ?_, ?_⟩
  · have g₆ : Frm (off B o) (powRanges w) s₅.mem s₆.mem := f₆.mono fun r hr => by
      simp only [powRanges, List.mem_cons]; exact Or.inr (Or.inr (Or.inr hr))
    have g₇ : Frm (off B o) (powRanges w) s₆.mem s₇.mem := f₇.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [powRanges, crtExpRanges5, crtExpRanges, crtWinRanges, List.mem_cons]
      rcases hr with h | h | h <;> subst h <;> simp
    have g₈ : Frm (off B o) (powRanges w) s₇.mem t.mem := f₈.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp [powRanges]
    exact (((F₅.mono rF₅).trans g₆).trans g₇).trans g₈
  · exact keep_trans (keep_trans (keep_trans K₅ k₆) k₇) k₈

end VG.Proof.Ffdh.X86_64
