module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedLoop
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedSquare

/-! # The folded scan, its fixed suffix, and root extraction -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aXm aAcc aTmp sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (powMod)

def initial : Track := ⟨0, true, false⟩

theorem zeroRoot_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g : Nat}
    (hc : Cst s B Z w minv N el E sigma) (hp : RecoveryWindow.Powers s.mem B w N g)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % N) :
    WP isa (zeroA aRoot) s fun u =>
      Cst u B Z w minv N el E sigma ∧ RecoveryWindow.Powers u.mem B w N g ∧ TrackRep u.mem B w N initial ∧
      wv u.mem B (slot w aY) w = 2 ^ (64 * w) % N ∧
      Frm B (rg w [aRoot] []) s.mem u.mem ∧ Keep mmRegs s u := by
  have hz := hc.hZ16
  have hN : 0 < N := by have := hc.n1; omega_arith
  refine WP.mono (zeroA_ok hc.ws (j := aRoot) (by decide)) fun s₁ ⟨hzero, o₁, k₁⟩ => ?_
  have f₁ : Frm B (rg w [aRoot] []) s.mem s₁.mem := Frm.rg_of_out o₁ (by omega_arith) _ _ (by decide)
  have hc₁ := hc.congr f₁ (by decide) (by simp) k₁ (by decide)
  have hp₁ := hp.congr f₁ hz (by simp) (by decide) (by decide) (by decide)
  have hzw := (wv_eq_zero_iff _ _ _ _).mp hzero
  have hv : TrackRep s₁.mem B w N initial := by
    refine ⟨?_, hN, ?_, ?_⟩
    · change wv s₁.mem B (slot w aRoot) w = 0 * 2 ^ (64 * w) % N
      rw [Nat.zero_mul, Nat.zero_mod]; exact wv_zero fun q hq => hzw q (by omega_arith)
    · exact hzw w (by omega_arith)
    · have he : flagsAt w + 8 = slot w aRoot + 8 * (w + 1) := by unfold flagsAt; omega_arith
      change word s₁.mem B (flagsAt w + 8) = 0
      rw [he]; exact hzw (w + 1) (by omega_arith)
  have hY₁ : wv s₁.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega_arith)]; exact hY
  exact ⟨hc₁, hp₁, hv, hY₁, f₁, k₁.mono (by decide)⟩

theorem windows_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g : Nat} {R : Option Nat}
    (hc : Cst s B Z w minv N el E sigma) (hp : RecoveryWindow.Powers s.mem B w N g)
    (hcont : VG.Proof.Rsa.RecoveryFolded.result (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N)
      (VG.Proof.Rsa.RecoveryFolded.scan N g E (32 * (w + (el + 7) / 8)) initial)) = R)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % N) :
    WP isa (windows M.mm) s fun u => ScanInv s B Z w minv N el E sigma g 0 R u := by
  have hz := hc.hZ16
  have hN : 0 < N := by have := hc.n1; omega_arith
  unfold windows
  refine WP.seq (WP.mono (zeroA_ok hc.ws (j := aRoot) (by decide)) fun s₁ ⟨hzero, o₁, k₁⟩ => ?_)
  have f₁ : Frm B (rg w [aRoot] []) s.mem s₁.mem := Frm.rg_of_out o₁ (by omega_arith) _ _ (by decide)
  have hc₁ := hc.congr f₁ (by decide) (by simp) k₁ (by decide)
  have hp₁ := hp.congr f₁ hz (by simp) (by decide) (by decide) (by decide)
  have hzw := (wv_eq_zero_iff _ _ _ _).mp hzero
  have hv : TrackRep s₁.mem B w N initial := by
    refine ⟨?_, hN, ?_, ?_⟩
    · change wv s₁.mem B (slot w aRoot) w = 0 * 2 ^ (64 * w) % N
      rw [Nat.zero_mul, Nat.zero_mod]; exact wv_zero fun q hq => hzw q (by omega_arith)
    · exact hzw w (by omega_arith)
    · have he : flagsAt w + 8 = slot w aRoot + 8 * (w + 1) := by unfold flagsAt; omega_arith
      change word s₁.mem B (flagsAt w + 8) = 0
      rw [he]; exact hzw (w + 1) (by omega_arith)
  have hY₁ : wv s₁.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega_arith)]; exact hY
  refine WP.mono (loop_ok M hc₁ hp₁ hv hcont hY₁) fun u hu => ?_
  exact ⟨hu.cst, hu.powers, (f₁.rg_trans hu.frm).rg_mono (by decide) (by decide),
    (k₁.trans hu.keep).mono (by decide), hu.y, hu.track⟩

/-- Two physical squares implement either one or two tracking steps. -/
theorem suffix_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma y : Nat} {v : Track}
    (hc : Cst s B Z w minv N el E sigma) (hsigma : sigma ≤ 2)
    (hv : TrackRep s.mem B w N v) (hy : y < N)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % N) :
    WP isa (.seq (Folded.square M.mm none) (Folded.square M.mm (some 1))) s fun u =>
      Cst u B Z w minv N el E sigma ∧
      TrackRep u.mem B w N (VG.Proof.Rsa.RecoveryFolded.run N sigma y v) ∧
      Frm B (rg w [aAcc, aTmp, aX, aRoot, aY] [sMask]) s.mem u.mem ∧ Keep mmRegs s u := by
  have hN : 0 < N := by have := hc.n1; omega_arith
  refine WP.seq (WP.mono (square_ok M hc (j := none) (Or.inl rfl) hv hy hY)
    fun s₁ ⟨hc₁, ht₁, hy₁, f₁, k₁⟩ => ?_)
  refine WP.mono (square_ok M hc₁ (j := some 1) (Or.inr rfl) ht₁ (Nat.mod_lt _ hN) hy₁)
    fun u ⟨hcu, htu, _, f₂, k₂⟩ => ?_
  refine ⟨hcu, ?_, (f₁.rg_trans f₂).rg_mono (by decide) (by decide), (k₁.trans k₂).mono (by decide)⟩
  have ht := hc.t1
  rcases (by omega_arith : sigma = 1 ∨ sigma = 2) with rfl | rfl <;> exact htu

/-- Root extraction exposes only the found mask and the captured Montgomery root. -/
theorem finish_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma : Nat} {v : Track}
    (hc : Cst s B Z w minv N el E sigma) (hv : TrackRep s.mem B w N v) :
    WP isa finish s fun u =>
      Cst u B Z w minv N el E sigma ∧
      word u.mem B (8 * sC3) = mask v.found ∧
      wv u.mem B (slot w aY) w = v.root * 2 ^ (64 * w) % N ∧
      Frm B (rg w [aY] [sC3]) s.mem u.mem ∧ Keep mmRegs s u := by
  have hz := hc.hZ16
  unfold finish
  refine WP.seq (WP.mono (copyA_ok hc.ws (o := aY) (a := aRoot) (by decide) (by decide) (by decide))
    fun s₁ ⟨hy₁, o₁, k₁⟩ => ?_)
  have f₁ : Frm B (rg w [aY] []) s.mem s₁.mem := Frm.rg_of_out o₁ (by omega_arith) _ _ (by decide)
  have hc₁ := hc.congr f₁ (by decide) (by simp) k₁ (by decide)
  have hv₁ := hv.congr f₁ hz (by simp) (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hc₁.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aRoot (r := .r8) (by decide) ((k₂.gpr (by decide)).trans hc₁.ws.rdi) h9)
    fun s₃ ⟨h8, m₃, k₃⟩ => ?_
  have hdi : s₃.gpr .rdi = B := (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hc₁.ws.rdi)
  have h12' : s₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans h12
  have hs := hc₁.ws.scr.congr (k₂.trans k₃).2.2
  have haddr : off B (slot w aRoot) + BitVec.ofNat 64 w * 8#64 + 8#64 = off B (flagsAt w + 8) := by
    simpa only [State.ea, found, ix, h8, h12', show BitVec.ofInt 64 8 = 8#64 from rfl] using found_ea h8 h12'

  have h256 := hc₁.ws.h256
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s₁.mem.writeW (off B (8 * sC3)) (mask v.found)) (by
    xrun [found, ix, h8, h12', show BitVec.ofInt 64 8 = 8#64 from rfl, haddr, hs.ld (d := flagsAt w + 8) (by unfold flagsAt at *; have hZ := hc₁.ws.hZ; unfold slot aRoot at *; omega_arith),
      State.ea, hdr, hdi, hdrOff, hs.st (d := 8 * sC3) (by simp only [sC3, sFn]; omega_arith),
      m₃, m₂, hv₁.found]) rfl) fun u ⟨mu, k₄⟩ => ?_
  have f₂ : Frm B (rg w [] [sC3]) s₁.mem u.mem := by
    rw [mu]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega_arith)) _ _ (by decide)
  have kk := ((k₂.trans k₃).trans k₄).mono (show ∀ r ∈ [.r12, .r9] ++ [.r8] ++ [.rax], r ∈ mmRegs by decide)
  refine ⟨hc₁.congr f₂ (by decide) (by decide) kk (by decide), by rw [mu, word_writeW_self], ?_,
    (f₁.rg_trans f₂).rg_mono (by decide) (by decide), (k₁.trans kk).mono (by decide)⟩
  rw [f₂.rg_wv hz (by decide) (by decide) (by decide) (by omega_arith), hy₁, hv.root]

/-- Folded exponentiation has exactly the existing root-search result. -/
theorem exp_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g r a : Nat}
    (hc : Cst s B Z w minv N el E sigma) (hsigma : sigma ≤ 2)
    (hE : E = r * 4 ^ a) (hr : r % 2 = 1)
    (hGlt : wv s.mem B (slot w aG) w < N)
    (hG : wv s.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) :
    WP isa (exponentiate M.mm) s fun u =>
      Cst u B Z w minv N el E sigma ∧
      word u.mem B (8 * sC3) = mask (VG.Spec.Rsa.recoverStep N (2 * a + sigma) r g).isSome ∧
      (∀ y, VG.Spec.Rsa.recoverStep N (2 * a + sigma) r g = some y →
        wv u.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N) ∧
      Frm B (rg w [aE, aD, aXm, aAcc, aTmp, aX, aRoot, aY] scanHeaders) s.mem u.mem ∧ Keep mmRegs s u := by
  have hN : 0 < N := by have := hc.n1; omega_arith
  have hEbound : E < 4 ^ (32 * (w + (el + 7) / 8)) := by
    rw [show 4 ^ (32 * (w + (el + 7) / 8)) = 2 ^ (64 * (w + (el + 7) / 8)) by
      rw [show 4 = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega_arith]
    exact hc.hm ▸ wv_lt _ _ _ _
  have ha : a < 32 * (w + (el + 7) / 8) := by
    have hle : 4 ^ a ≤ E := by rw [hE]; exact Nat.le_mul_of_pos_left _ (by omega_arith)
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt hle hEbound)
  have hcont : VG.Proof.Rsa.RecoveryFolded.result (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N)
      (VG.Proof.Rsa.RecoveryFolded.scan N g E (32 * (w + (el + 7) / 8)) initial)) =
        VG.Spec.Rsa.recoverStep N (2 * a + sigma) r g := by
    rw [hE, VG.Proof.Rsa.RecoveryFolded.powMod_four N g r a (by omega_arith)]
    exact VG.Proof.Rsa.RecoveryFolded.scan_result hr ha hc.t1 initial
  simp only [exponentiate, seqs]
  refine WP.seq (WP.mono (RecoveryWindow.powers_ok M hc hGlt hG)
    fun s₁ ⟨hc₁, f₁, k₁, hp₁, hy₁⟩ => ?_)
  refine WP.seq (WP.mono (windows_ok M hc₁ hp₁ hcont hy₁) fun s₂ hi => ?_)
  obtain ⟨v, hv, hcresult⟩ := hi.track
  simp only [VG.Proof.Rsa.RecoveryFolded.scan] at hcresult
  have hy₂ : wv s₂.mem B (slot w aY) w = powMod g E N * 2 ^ (64 * w) % N := by
    simpa only [Nat.pow_zero, Nat.div_one] using hi.y
  refine WP.seq (WP.mono (suffix_ok M hi.cst hsigma hv (by rw [powMod_eq]; exact Nat.mod_lt _ hN) hy₂)
    fun s₃ ⟨hc₃, hv₃, f₃, k₃⟩ => ?_)
  refine WP.mono (finish_ok hc₃ hv₃) fun u ⟨hcu, hok, hyu, f₄, k₄⟩ => ?_
  refine ⟨hcu, ?_, ?_, (((f₁.rg_trans hi.frm).rg_trans f₃).rg_trans f₄).rg_mono (by decide) (by decide),
    (((k₁.trans hi.keep).trans k₃).trans k₄).mono (by decide)⟩
  · rw [hok, ← hcresult]
    cases hfound : (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N) v).found <;>
      simp [VG.Proof.Rsa.RecoveryFolded.result, hfound]
  · intro y hy
    rw [← hcresult, VG.Proof.Rsa.RecoveryFolded.result] at hy
    split at hy
    · cases hy; exact ⟨hyu, hv₃.rootlt⟩
    · cases hy

end VG.Proof.Rsa.X86_64.RecoveryFolded
