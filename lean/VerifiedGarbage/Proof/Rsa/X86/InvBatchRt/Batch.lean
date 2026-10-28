module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Update
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Divstep.Word32
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Monoid
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Divstep.Batch

/-! # A batch at a run-time width

`start_ok` and `words_ok`: the low words, the identity matrix and thirty word divsteps in the
header's window; `countedBatch_ok`: then the update, and the batch count down by one.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob wordState atWord)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem low_cong {m : Mem} {base : Addr} {d n : Nat} {x : Int}
    (h : (val32 m base d (n + 1) : Int) % 2 ^ (32 * (n + 1)) = x % 2 ^ (32 * (n + 1))) :
    ((m.readW (off base d) 32).toNat : Int) % 2 ^ 32 = x % 2 ^ 32 := by
  have D : (2 : Int) ^ 32 ∣ 2 ^ (32 * (n + 1)) := pow_dvd_pow 2 (by omega)
  have E : (w32 m base d : Int) % 2 ^ 32 = (val32 m base d (n + 1) : Int) % 2 ^ 32 := by
    rw [val32]; push_cast; exact (Int.add_mul_emod_self_left _ _ _).symm
  rw [E, ← Int.emod_emod_of_dvd _ D, h, Int.emod_emod_of_dvd _ D]

/-- The window's low words and identity matrix (`GcdBatch.start_ok`). -/
theorem start_ok {s : State} (h : Bx L s B Z len N) :
    WP isa (.block (start L)) s fun u =>
      Bx L u B Z len N ∧
      wordState u.mem B win =
        ⟨s.mem.readW (off B win) 32, s.mem.readW (off B (rv (kw len) (a 4))) 32,
          s.mem.readW (off B (rv (kw len) (a 5))) 32, 1, 0, 0, 1⟩ ∧
      Keeps wordClob s u ∧ Outside B (win + 4) 24 s.mem u.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have e16 : win = 16 := rfl
  have r4 := rv_a len 4; have r5 := rv_a len 5
  unfold start
  simp only [List.append_assoc]
  -- `[win + 4] = [a 4]`.
  refine ptr_ok h.ws h.slots hZ (r := .ebx) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) (by omega) fun s₁ K₁ m₁ p₁ => ?_
  simp only [List.cons_append, List.nil_append]
  have H₁ : Bx L s₁ B Z len N := h.keep K₁ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₁]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  refine wp_movS (readSrc_ptr H₁.ws.rt p₁ (d := 0) (by omega)) fun s₂ U₂ _ => ?_
  have hs₂ := H₁.ws.ws.workspace.of_keeps U₂.keeps (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write (d := win + 4) (n := 4) (by omega)) fun s₃ U₃ => ?_
  have K₃ : Keeps [.eax, .ebx, .edx] s s₃ :=
    ((K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps _)
  have O₃ : Outside B (win + 4) 4 s.mem s₃.mem := by
    rw [U₃.mem, U₂.mem, m₁]; exact writeW32_outside _ _ _ (by omega)
  have H₃ : Bx L s₃ B Z len N := h.keepLow K₃ (by decide) (by decide) O₃ (by decide)
  have F₃ : w32 s₃.mem B (win + 4) = w32 s.mem B (rv (kw len) (a 4)) := by
    rw [U₃.mem, w32_write_self, U₂.gpr, m₁, Nat.add_zero]
  -- `[win + 8] = [a 5]`.
  refine ptr_ok H₃.ws H₃.slots hZ (r := .ebx) (t := .edx) (x := a 5) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega) fun s₄ K₄ m₄ p₄ => ?_
  have H₄ : Bx L s₄ B Z len N := H₃.keep K₄ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₄]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  refine wp_movS (readSrc_ptr H₄.ws.rt p₄ (d := 0) (by omega)) fun s₅ U₅ _ => ?_
  have hs₅ := H₄.ws.ws.workspace.of_keeps U₅.keeps (by decide)
  refine wp_storeS (hs₅.ea (by omega)) (hs₅.write (d := win + 8) (n := 4) (by omega)) fun s₆ U₆ => ?_
  have K₆ : Keeps [.eax, .ebx, .edx] s₃ s₆ :=
    ((K₄.mono (by decide)).trans (U₅.keeps.mono (by decide))).trans (U₆.keeps _)
  have O₆ : Outside B (win + 8) 4 s₃.mem s₆.mem := by
    rw [U₆.mem, U₅.mem, m₄]; exact writeW32_outside _ _ _ (by omega)
  have H₆ : Bx L s₆ B Z len N := H₃.keepLow K₆ (by decide) (by decide) O₆ (by decide)
  have G₆ : w32 s₆.mem B (win + 8) = w32 s.mem B (rv (kw len) (a 5)) := by
    rw [U₆.mem, w32_write_self, U₅.gpr, m₄, Nat.add_zero, ← O₃.w32 (d := rv (kw len) (a 5)) (by omega) (by omega)]
  -- The identity matrix.
  refine WP.mono (VG.Proof.Weierstrass.X86.Inv.setMatrix_ok H₆.ws.ws.workspace (dst := win + 12) (by omega))
    fun u ⟨U, V, Q, R, K₇, O₇⟩ => ?_
  have H₇ : Bx L u B Z len N := H₆.keepLow K₇ (by decide) (by decide) O₇ (by decide)
  refine ⟨H₇, ?_, ((K₃.trans K₆).trans (K₇.mono (by decide))).mono (by decide), ?_⟩
  · have D : w32 u.mem B win = w32 s.mem B win := by
      rw [O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), O₃.w32 (by omega) (by omega)]
    have F : w32 u.mem B (win + 4) = w32 s.mem B (rv (kw len) (a 4)) := by
      rw [O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), F₃]
    have G : w32 u.mem B (win + 8) = w32 s.mem B (rv (kw len) (a 5)) := by
      rw [O₇.w32 (by omega) (by omega), G₆]
    simp only [wordState, atWord, Divstep.W32.WSt.mk.injEq, Nat.reduceMul, Nat.add_zero]
    refine ⟨BitVec.eq_of_toNat_eq D, BitVec.eq_of_toNat_eq F, BitVec.eq_of_toNat_eq G,
      BitVec.eq_of_toNat_eq U, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 16) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using V
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 20) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Q
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem B (win + 24) = 1
      simpa only [Nat.add_assoc, Nat.reduceAdd] using R
  · intro x hx
    rw [O₇ x (by omega), O₆ x (by omega), O₃ x (by omega)]

/-- The window's thirty word divsteps (`GcdBatch.words_ok`). -/
theorem words_ok {s : State} (h : Bx L s B Z len N) {d f g : Int}
    (hd : s.mem.readW (off B win) 32 = BitVec.ofInt 32 d)
    (hf : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      f % 2 ^ (32 * (nw len + 1)))
    (hg : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      g % 2 ^ (32 * (nw len + 1)))
    (hdb : |d| + 64 < 2 ^ 30) (hfo : f % 2 = 1) :
    WP isa (.seq (.block (start L)) (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)) s fun z =>
      Bx L z B Z len N ∧ MatrixAt B (Divstep.msteps 30 (Divstep.MSt.init d f g)) z ∧
      Keeps wordClob s z ∧ Outside B win 28 s.mem z.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have e16 : win = 16 := rfl
  have e96 : halfSlot = 96 := rfl
  refine WP.seq (WP.mono (start_ok h) fun s₁ ⟨H₁, V₁, K₁, O₁⟩ => ?_)
  have rel : (wordState s₁.mem B win).rel (Divstep.MSt.init d f g) 32 := by
    rw [V₁]
    exact ⟨hd, rfl, rfl, rfl, rfl, low_cong hf, low_cong hg⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hdb hfo 30 (by decide)
  refine WP.mono (VG.Proof.Weierstrass.X86.Inv.wordSteps_ok H₁.ws.ws.workspace (t := win) (by omega)
    (by decide) (by decide)) fun z ⟨V₂, K₂, O₂⟩ => ⟨H₁.keepLow K₂ (by decide) (by decide) O₂ (by decide), ?_,
      (K₁.mono (by decide)).trans K₂, ?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D, U, V, Q, R, _, _⟩ := matrix
    exact ⟨D, U, V, Q, R⟩
  · intro x hx
    rw [O₂ x hx, O₁ x (by omega)]

/-- The state survives writes apart from it. -/
theorem StateAt.keep {s t : State} {p iv : Nat} {st : Divstep.W32.IState} (hs : StateAt len B p iv st s)
    (h : Bx L s B Z len N) {o c : Nat} (O : Outside B o c s.mem t.mem)
    (ho : win + 32 ≤ o ∧ o + c ≤ rv (kw len) (a 2) ∨ rv (kw len) (a 8) ≤ o ∧ o + c ≤ Z) :
    StateAt len B p iv st t := by
  have hn := h.nowrap
  have hf := h.fits16
  have e16 : win = 16 := rfl
  have r2 := rv_a len 2; have r4 := rv_a len 4; have r5 := rv_a len 5; have r6 := rv_a len 6
  have r7 := rv_a len 7; have r8 := rv_a len 8
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Weierstrass.X86.Inv.read32_unch O.unch (by
      intro r hr; rw [List.mem_singleton.mp hr]; omega) (by omega)]
    exact hs.d
  · rw [O.val32 (by omega) (by omega)]; exact hs.modulus
  · rw [O.w32 (by omega) (by omega)]; exact hs.inverse
  · rw [O.val32 (by omega) (by omega)]; exact hs.f
  · rw [O.val32 (by omega) (by omega)]; exact hs.g
  · rw [O.val32 (by omega) (by omega)]; exact hs.ca
  · rw [O.val32 (by omega) (by omega)]; exact hs.cb
  · rw [O.w32 (by omega) (by omega)]; exact hs.aTop
  · rw [O.w32 (by omega) (by omega)]; exact hs.bTop

/-- What a counted batch writes. -/
def countedWrites (len : Nat) : List (Nat × Nat) := (100, 4) :: (win, 28) :: updateWrites len

/-- A counted batch. -/
theorem countedBatch_ok {s : State} (h : Bx L s B Z len N) (he : nw len % 2 = 0) {p iv cap j : Nat}
    {st : Divstep.W32.IState} (hst : StateAt len B p iv st s) (hp : 0 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (hd : |st.d| + 64 < 2 ^ 30) (odd : st.f % 2 = 1)
    (hf : |st.f| ≤ cap) (hg : |st.g| ≤ cap) (capBound : cap < 2 ^ (32 * nw len + 1))
    (ha : |st.a| ≤ p) (hb : |st.b| ≤ p) (jp : 1 ≤ j) (jl : j < 2 ^ 32) (counter : w32 s.mem B 100 = j) :
    WP isa (.seq (.block (start L)) (.seq (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30) (.seq (update L)
      (.block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter])))) s fun z =>
      Bx L z B Z len N ∧ StateAt len B p iv (Divstep.W32.batch 30 p iv st) z ∧
      w32 z.mem B 100 = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps wordClob s z ∧ Unch B (countedWrites len) s.mem z.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have e16 : win = 16 := rfl
  have e48 : signSlot = 48 := rfl
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r4 := rv_a len 4; have r5 := rv_a len 5
  have r6 := rv_a len 6; have r7 := rv_a len 7; have r11 := rv_a len 11
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  generalize hT : Divstep.msteps 30 (Divstep.MSt.init st.d st.f st.g) = T
  have mat := Divstep.msteps_mat (d := st.d) (g := st.g) odd 30
  have bound := Divstep.msteps_bnd st.d st.f st.g 30
  rw [hT] at mat bound
  change 2 ^ 30 * T.f = T.u * st.f + T.v * st.g ∧ 2 ^ 30 * T.g = T.q * st.f + T.r * st.g at mat
  change |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30 at bound
  refine seq_assoc (WP.seq (WP.mono (words_ok h hst.d hst.f hst.g hd odd) fun u ⟨Hu, M, K, O⟩ => ?_))
  rw [hT] at M
  have input : RowInput len B p iv T st u := by
    refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [O.val32 (by omega) (by omega)]; exact hst.modulus
    · rw [O.w32 (by omega) (by omega)]; exact hst.inverse
    · rw [O.val32 (by omega) (by omega)]; exact hst.f
    · rw [O.val32 (by omega) (by omega)]; exact hst.g
    · rw [O.val32 (by omega) (by omega)]; exact hst.ca
    · rw [O.val32 (by omega) (by omega)]; exact hst.cb
  have topA : w32 u.mem B (rv (kw len) (a 6) + 4 * nw len) = 0 := by
    rw [O.w32 (by omega) (by omega)]; exact hst.aTop
  have topB : w32 u.mem B (rv (kw len) (a 7) + 4 * nw len) = 0 := by
    rw [O.w32 (by omega) (by omega)]; exact hst.bTop
  refine WP.seq (WP.mono (update_ok Hu he input hp hinv bound.1 bound.2 hf hg capBound
    ⟨T.f, mat.1.symm⟩ ⟨T.g, mat.2.symm⟩ ha hb topA topB) fun v ⟨Hv, I, K', O'⟩ => ?_)
  have cv : w32 v.mem B 100 = j := by
    rw [VG.Proof.Weierstrass.X86.Inv.word_unch O' (by
      intro r hr
      simp only [updateWrites, rowWrites, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl <;> simp only <;> omega) (by omega),
      O.w32 (by omega) (by omega), counter]
  refine WP.mono (VG.Proof.Rsa.X86.GcdBatch.countDown_ok Hv.ws.ws.workspace (d := 100) (by omega) jp jl cv)
    fun z ⟨c, zf, K'', O''⟩ => ?_
  refine ⟨Hv.keepHigh K'' (by decide) (by decide) O'' (by decide) (by omega), ?_, c, zf,
    (K.trans K').trans (K''.mono (by decide)), ?_⟩
  · have I' := I.keep Hv O'' (.inl ⟨by omega, by omega⟩)
    unfold Divstep.W32.batch
    rw [hT]
    exact I'
  · intro x hx
    rw [O'' x (hx (100, 4) (by simp [countedWrites])), O' x fun r hr => hx r (by
      simp only [countedWrites, List.mem_cons]; exact .inr (.inr hr)), O x (hx (win, 28) (by simp [countedWrites]))]

end VG.Proof.Rsa.X86.InvBatchRt
