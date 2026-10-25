module

import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedWindow
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowStep
import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
public import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowPowers

/-! # The padded scan with a continuation for the captured root -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aXm aAcc aTmp sMask sCnt)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (powMod)

def scanArrays : List Nat := [aXm, aAcc, aTmp, aX, aRoot, aY]
def scanHeaders : List Nat := [sMask, sC1, sC2, sC3]

structure ScanInv (s₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64)
    (N el E sigma g k : Nat) (R : Option Nat) (u : State) : Prop where
  cst : Cst u B Z w minv N el E sigma
  powers : RecoveryWindow.Powers u.mem B w N g
  frm : Frm B (rg w scanArrays scanHeaders) s₀.mem u.mem
  keep : Keep mmRegs s₀ u
  y : wv u.mem B (slot w aY) w = powMod g (E / 4 ^ k) N * 2 ^ (64 * w) % N
  track : ∃ v, TrackRep u.mem B w N v ∧
    VG.Proof.Rsa.RecoveryFolded.result (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N) (VG.Proof.Rsa.RecoveryFolded.scan N g E k v)) = R

structure WordInv (s₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64)
    (N el E sigma g q : Nat) (R : Option Nat) (u : State) : Prop extends
    ScanInv s₀ B Z w minv N el E sigma g (32 * q) R u where
  c1 : word u.mem B (8 * sC1) = BitVec.ofNat 64 q

structure BitInv (s₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64)
    (N el E sigma g q j : Nat) (R : Option Nat) (u : State) : Prop extends
    ScanInv s₀ B Z w minv N el E sigma g (32 * q - j) R u where
  c1 : word u.mem B (8 * sC1) = BitVec.ofNat 64 q
  c2 : word u.mem B (8 * sC2) =
    BitVec.ofNat 64 (E / 2 ^ (64 * (q - 1)) % 2 ^ 64 * 2 ^ (2 * j) % 2 ^ 64)
  c3 : word u.mem B (8 * sC3) = BitVec.ofNat 64 (64 - 2 * j)

theorem digit {E q j : Nat} (hq : 1 ≤ q) (hj : j < 32) :
    (E / 2 ^ (64 * (q - 1)) % 2 ^ 64 * 2 ^ (2 * j) % 2 ^ 64) / 2 ^ 62 =
      E / 4 ^ (32 * q - j - 1) % 4 := by
  rw [RecoveryWindow.top_digit (by omega), RecoveryWindow.low_digit (E / 2 ^ (64 * (q - 1))) (by omega),
    Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 64 * (q - 1) + (62 - 2 * j) = 2 * (32 * q - j - 1) by omega, Nat.pow_mul]

theorem prefix_step (E k : Nat) : E / 4 ^ k = 4 * (E / 4 ^ (k + 1)) + E / 4 ^ k % 4 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- Consume two bits, preserving the result of all remaining work. -/
theorem body_ok (M : Mont) {s₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g q j : Nat} {R : Option Nat} (hq : 1 ≤ q) (hj : j < 32)
    (hi : BitInv s₀ B Z w minv N el E sigma g q j R u) :
    WP isa (Folded.window M.mm) u fun u' => u'.zf = some (decide (j + 1 = 32)) ∧
      BitInv s₀ B Z w minv N el E sigma g q (j + 1) R u' := by
  have hz := hi.cst.hZ16
  let V := E / 2 ^ (64 * (q - 1)) % 2 ^ 64 * 2 ^ (2 * j) % 2 ^ 64
  have hVlt : V < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hd : (BitVec.ofNat 64 V).toNat / 2 ^ 62 = E / 4 ^ (32 * q - j - 1) % 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hVlt]; exact digit hq hj
  have hk : 32 * q - j - 1 + 1 = 32 * q - j := by omega
  have hpref : 4 * (E / 4 ^ (32 * q - j)) + (BitVec.ofNat 64 V).toNat / 2 ^ 62 =
      E / 4 ^ (32 * q - j - 1) := by
    rw [hd]
    have h := prefix_step E (32 * q - j - 1)
    rw [hk] at h
    exact h.symm
  obtain ⟨v, hv, hcont⟩ := hi.track
  unfold Folded.window
  refine WP.seq (WP.mono (arithmetic_ok M hi.cst hi.powers hv hi.y hi.c2)
    fun u₁ ⟨hc₁, ht₁, hy₁, f₁, k₁⟩ => ?_)
  rw [hpref] at ht₁ hy₁
  have ht₁' : TrackRep u₁.mem B w N (VG.Proof.Rsa.RecoveryFolded.window N g E (32 * q - j - 1) v) := by
    change TrackRep u₁.mem B w N (resetTrack ((BitVec.ofNat 64 V).toNat / 2 ^ 62) N
      (powMod g (E / 4 ^ (32 * q - j - 1)) N)
      (VG.Proof.Rsa.RecoveryFolded.run N 2 (powMod g (E / 4 ^ (32 * q - j)) N) v)) at ht₁
    rw [hd] at ht₁
    simpa only [VG.Proof.Rsa.RecoveryFolded.window, resetTrack, hk] using ht₁
  have hcont₁ : VG.Proof.Rsa.RecoveryFolded.result (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N)
      (VG.Proof.Rsa.RecoveryFolded.scan N g E (32 * q - j - 1) (VG.Proof.Rsa.RecoveryFolded.window N g E (32 * q - j - 1) v))) = R := by
    rw [← hk, VG.Proof.Rsa.RecoveryFolded.scan] at hcont
    exact hcont
  have hc1₁ : word u₁.mem B (8 * sC1) = BitVec.ofNat 64 q := by
    rw [f₁.rg_word (by decide) (by decide)]; exact hi.c1
  have hc2₁ : word u₁.mem B (8 * sC2) = BitVec.ofNat 64 V := by
    rw [f₁.rg_word (by decide) (by decide)]; exact hi.c2
  have hc3₁ : word u₁.mem B (8 * sC3) = BitVec.ofNat 64 (64 - 2 * j) := by
    rw [f₁.rg_word (by decide) (by decide)]; exact hi.c3
  refine WP.mono (RecoveryWindow.next_ok hc₁.ws hc2₁ hc3₁ hj) fun u' ⟨hcond, hm, k₂⟩ => ⟨hcond, ?_⟩
  have f₂ : Frm B (rg w [] [sC2, sC3]) u₁.mem u'.mem := by
    rw [hm]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
      (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
        (by decide))
  have heq : 32 * q - (j + 1) = 32 * q - j - 1 := by omega
  refine ⟨⟨hc₁.congr f₂ (by decide) (by decide) k₂ (by decide),
    hi.powers.congr (f₁.rg_trans f₂) hz (by decide) (by decide) (by decide) (by decide),
    ((hi.frm.rg_trans f₁).rg_trans f₂).rg_mono (by decide) (by decide),
    ((hi.keep.trans k₁).trans k₂).mono (by decide), ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [f₂.rg_wv hz (by decide) (by decide) (by decide) (by omega), heq]; exact hy₁
  · exact ⟨_, ht₁'.congr f₂ hz (by decide) (by decide), by rw [heq]; exact hcont₁⟩
  · rw [f₂.rg_word (by decide) (by decide)]; exact hc1₁
  · rw [hm, (writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
      (d := 8 * sC2) (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega),
      word_writeW_self]
    congr 1
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.pow_add, ← Nat.mul_assoc, Nat.mod_mul_mod]
  · rw [hm, word_writeW_self]

theorem ScanInv.headers {s₀ u u' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g k : Nat} {R : Option Nat}
    (hi : ScanInv s₀ B Z w minv N el E sigma g k R u) {hs : List Nat} {rs : List Reg}
    (hf : Frm B (rg w [] hs) u.mem u'.mem) (hk : Keep rs u u')
    (hhs : hs ⊆ scanHeaders) (hkeep : rs ⊆ mmRegs) :
    ScanInv s₀ B Z w minv N el E sigma g k R u' := by
  have hz := hi.cst.hZ16
  have hh : ∀ i ∈ hs, i < 32 := fun i h => by have := hhs h; simp only [scanHeaders, List.mem_cons, List.not_mem_nil, or_false] at this; rcases this with rfl | rfl | rfl | rfl <;> decide
  have hother : ∀ i ∈ hs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by
    intro i h; have := hhs h
    simp only [scanHeaders, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl <;> decide
  refine ⟨hi.cst.congr hf (by decide) hother (hk.mono hkeep) (by decide),
    hi.powers.congr hf hz hh (by decide) (by decide) (by decide),
    (hi.frm.rg_trans hf).rg_mono (by decide) (fun i h => (List.mem_append.mp h).elim id (fun h => hhs h)),
    (hi.keep.trans hk).mono ?_, ?_, ?_⟩
  · intro r h; rcases List.mem_append.mp h with h | h
    · exact h
    · exact hkeep h
  · rw [hf.rg_wv hz hh (by decide) (by decide) (by omega)]; exact hi.y
  · obtain ⟨v, hv, hc⟩ := hi.track
    exact ⟨v, hv.congr hf hz hh (by decide), hc⟩

theorem head_ok {s₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g q : Nat} {R : Option Nat}
    (hq : 1 ≤ q) (hqb : q ≤ w + (el + 7) / 8)
    (hi : WordInv s₀ B Z w minv N el E sigma g q R u) :
    WP isa (.block wordHead) u fun u' => BitInv s₀ B Z w minv N el E sigma g q 0 R u' := by
  have hc := hi.cst
  have hz := hc.hZ16
  have he2 := hc.e2
  have hw2 := hc.ws.w2
  have hBw : w + (el + 7) / 8 ≤ 2 * (w + 2) := by omega
  have hq' : q = (q - 1) + 1 := by omega
  have hc1 := hi.c1
  rw [hq'] at hc1
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by simp only [slot, hdrBytes, aM]; omega
  have hZ := hc.ws.hZ
  refine WP.mono (wordHead_ok hc.ws hc1 (by omega) (by omega))
    fun u₁ ⟨m₁, k₁⟩ => ?_
  have hW : (word u.mem B (slot w aM + 8 * (q - 1))).toNat = E / 2 ^ (64 * (q - 1)) % 2 ^ 64 := by
    have := word_of_wv u.mem B (slot w aM) (w + (el + 7) / 8) (q := q - 1) (by omega)
    rwa [hc.hm] at this
  have f₁ : Frm B (rg w [] [sC2, sC3]) u.mem u₁.mem := by
    rw [m₁]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
      (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3] (by decide))
  have hs₁ := hi.toScanInv.headers f₁ k₁ (by decide) (by decide)
  have hW' : word u.mem B (slot w aM + 8 * (q - 1)) = BitVec.ofNat 64 (E / 2 ^ (64 * (q - 1)) % 2 ^ 64) := by
    rw [← hW, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hb0 : BitInv s₀ B Z w minv N el E sigma g q 0 R u₁ := by
    refine ⟨by simpa only [Nat.sub_zero] using hs₁, ?_, ?_, ?_⟩
    · rw [f₁.rg_word (by decide) (by decide)]; exact hi.c1
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_mod]
      rw [m₁, (writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), word_writeW_self, hW']
    · rw [m₁, word_writeW_self]
  exact hb0

/-- Load a public word, execute its 32 windows, then advance the word counter. -/
theorem word_ok (M : Mont) {s₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g q : Nat} {R : Option Nat}
    (hq : 1 ≤ q) (hqb : q ≤ w + (el + 7) / 8)
    (hi : WordInv s₀ B Z w minv N el E sigma g q R u) :
    WP isa (.seq (.block wordHead) (.seq (.loop (Folded.window M.mm) .ne) (.block wordNext))) u fun u' =>
      u'.zf = some (decide (q - 1 = 0)) ∧ WordInv s₀ B Z w minv N el E sigma g (q - 1) R u' := by
  have hc := hi.cst
  have hz := hc.hZ16
  have he2 := hc.e2
  have hw2 := hc.ws.w2
  have hBw : w + (el + 7) / 8 ≤ 2 * (w + 2) := by omega
  have hq' : q = (q - 1) + 1 := by omega
  have hc1 := hi.c1
  rw [hq'] at hc1
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by simp only [slot, hdrBytes, aM]; omega
  have hZ := hc.ws.hZ
  refine WP.seq (WP.mono (wordHead_ok hc.ws hc1 (by omega) (by omega))
    fun u₁ ⟨m₁, k₁⟩ => ?_)
  have hW : (word u.mem B (slot w aM + 8 * (q - 1))).toNat = E / 2 ^ (64 * (q - 1)) % 2 ^ 64 := by
    have := word_of_wv u.mem B (slot w aM) (w + (el + 7) / 8) (q := q - 1) (by omega)
    rwa [hc.hm] at this
  have f₁ : Frm B (rg w [] [sC2, sC3]) u.mem u₁.mem := by
    rw [m₁]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
      (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3] (by decide))
  have hs₁ := hi.toScanInv.headers f₁ k₁ (by decide) (by decide)
  have hW' : word u.mem B (slot w aM + 8 * (q - 1)) = BitVec.ofNat 64 (E / 2 ^ (64 * (q - 1)) % 2 ^ 64) := by
    rw [← hW, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hb0 : BitInv s₀ B Z w minv N el E sigma g q 0 R u₁ := by
    refine ⟨by simpa only [Nat.sub_zero] using hs₁, ?_, ?_, ?_⟩
    · rw [f₁.rg_word (by decide) (by decide)]; exact hi.c1
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_mod]
      rw [m₁, (writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), word_writeW_self, hW']
    · rw [m₁, word_writeW_self]
  refine WP.seq (wp_upto (a := 0) (N := 32) (by decide)
    (fun j v => BitInv s₀ B Z w minv N el E sigma g q j R v)
    (fun j _ hj v hv => body_ok M hq hj hv) (fun v hv => ?_) hb0)
  refine WP.mono (ctrDec_ok hv.cst.ws (i := sC1) (by decide) (by decide)
    hv.c1 hq (by omega)) fun u' ⟨hz', m₂, k₂⟩ => ⟨by rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega), ?_⟩
  have f₂ : Frm B (rg w [] [sC1]) v.mem u'.mem := by
    rw [m₂]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _ (List.mem_singleton_self _)
  have hs₂ := hv.toScanInv.headers f₂ k₂ (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · simpa only [show 32 * q - 32 = 32 * (q - 1) by omega] using hs₂
  · rw [m₂, word_writeW_self]

/-- The public padded exponent loop preserves the remaining-work continuation. -/
theorem init_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g : Nat} {R : Option Nat} {v : Track}
    (hc : Cst s B Z w minv N el E sigma) (hp : RecoveryWindow.Powers s.mem B w N g)
    (hv : TrackRep s.mem B w N v)
    (hcont : VG.Proof.Rsa.RecoveryFolded.result (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N)
      (VG.Proof.Rsa.RecoveryFolded.scan N g E (32 * (w + (el + 7) / 8)) v)) = R)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % N) :
    WP isa (.block expInit) s fun u =>
      WordInv s B Z w minv N el E sigma g (w + (el + 7) / 8) R u := by
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  unfold expInit
  refine WP.mono (Q := fun (u : State) => u.mem = s.mem.writeW (off B (8 * sC1))
      (BitVec.ofNat 64 (w + (el + 7) / 8)) ∧ Keep mmRegs s u)
    (WP.block_append_iff.mpr (WP.mono (bw_ok hc.ws hc.hel (by omega)) fun s₁ ⟨hax, m₁, k₁⟩ => ?_))
    fun s₁ ⟨m₁, k₁⟩ => ?_
  · have hs₁ := hc.ws.scr.congr k₁.2.2
    have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hc.ws.rdi
    refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off B (8 * sC1))
        (BitVec.ofNat 64 (w + (el + 7) / 8))) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hax, m₁])
      rfl) fun u ⟨mu, k₂⟩ => ⟨mu, (k₁.trans k₂).mono (by decide)⟩
  have f₁ : Frm B (rg w [] [sC1]) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hE : E < 4 ^ (32 * (w + (el + 7) / 8)) := by
    rw [show 4 ^ (32 * (w + (el + 7) / 8)) = 2 ^ (64 * (w + (el + 7) / 8)) by rw [show 4 = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega]
    exact hc.hm ▸ wv_lt _ _ _ _
  have hi : ScanInv s B Z w minv N el E sigma g (32 * (w + (el + 7) / 8)) R s := by
    refine ⟨hc, hp, Frm.refl _ _ _, Keep.refl _ _, ?_, ⟨v, hv, hcont⟩⟩
    rw [Nat.div_eq_of_lt hE, powMod_eq, Nat.pow_zero, Nat.mod_mul_mod, Nat.one_mul]; exact hY
  have h0 : WordInv s B Z w minv N el E sigma g (w + (el + 7) / 8) R s₁ :=
    ⟨hi.headers f₁ k₁ (by decide) (by decide), by rw [m₁, word_writeW_self]⟩
  exact h0

theorem loop_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g : Nat} {R : Option Nat} {v : Track}
    (hc : Cst s B Z w minv N el E sigma) (hp : RecoveryWindow.Powers s.mem B w N g)
    (hv : TrackRep s.mem B w N v)
    (hcont : VG.Proof.Rsa.RecoveryFolded.result (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N)
      (VG.Proof.Rsa.RecoveryFolded.scan N g E (32 * (w + (el + 7) / 8)) v)) = R)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % N) :
    WP isa (paddedScan M.mm) s fun u => ScanInv s B Z w minv N el E sigma g 0 R u := by
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  unfold paddedScan expInit
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = s.mem.writeW (off B (8 * sC1))
      (BitVec.ofNat 64 (w + (el + 7) / 8)) ∧ Keep mmRegs s u)
    (WP.block_append_iff.mpr (WP.mono (bw_ok hc.ws hc.hel (by omega)) fun s₁ ⟨hax, m₁, k₁⟩ => ?_))
    fun s₁ ⟨m₁, k₁⟩ => ?_)
  · have hs₁ := hc.ws.scr.congr k₁.2.2
    have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hc.ws.rdi
    refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off B (8 * sC1))
        (BitVec.ofNat 64 (w + (el + 7) / 8))) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hax, m₁])
      rfl) fun u ⟨mu, k₂⟩ => ⟨mu, (k₁.trans k₂).mono (by decide)⟩
  have f₁ : Frm B (rg w [] [sC1]) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hE : E < 4 ^ (32 * (w + (el + 7) / 8)) := by
    rw [show 4 ^ (32 * (w + (el + 7) / 8)) = 2 ^ (64 * (w + (el + 7) / 8)) by rw [show 4 = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega]
    exact hc.hm ▸ wv_lt _ _ _ _
  have hi : ScanInv s B Z w minv N el E sigma g (32 * (w + (el + 7) / 8)) R s := by
    refine ⟨hc, hp, Frm.refl _ _ _, Keep.refl _ _, ?_, ⟨v, hv, hcont⟩⟩
    rw [Nat.div_eq_of_lt hE, powMod_eq, Nat.pow_zero, Nat.mod_mul_mod, Nat.one_mul]; exact hY
  have h0 : WordInv s B Z w minv N el E sigma g (w + (el + 7) / 8) R s₁ :=
    ⟨hi.headers f₁ k₁ (by decide) (by decide), by rw [m₁, word_writeW_self]⟩
  refine wp_upto (a := 0) (N := w + (el + 7) / 8) (by omega)
    (fun k u => WordInv s B Z w minv N el E sigma g (w + (el + 7) / 8 - k) R u)
    (fun k _ hk u hu => ?_) (fun u hu => ?_) (by simpa only [Nat.sub_zero] using h0)
  · refine WP.mono (word_ok M (by omega) (by omega) hu) fun u' ⟨hz, hi⟩ => ?_
    have he : w + (el + 7) / 8 - k - 1 = w + (el + 7) / 8 - (k + 1) := by omega
    rw [he] at hz hi
    have hz' : (w + (el + 7) / 8 - (k + 1) = 0) ↔ (k + 1 = w + (el + 7) / 8) := by omega
    exact ⟨by simpa only [hz'] using hz, hi⟩
  · simpa only [Nat.sub_self, Nat.mul_zero] using hu.toScanInv

end VG.Proof.Rsa.X86_64.RecoveryFolded
