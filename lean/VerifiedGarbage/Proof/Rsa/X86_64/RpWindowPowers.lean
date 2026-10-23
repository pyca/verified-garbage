module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.RecoverMath

/-! # Recovery windows: the four powers and their selection -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

namespace RecoveryWindow

/-- The three nonzero powers, in Montgomery form. -/
structure Powers (m : Mem) (B : Addr) (w N g : Nat) : Prop where
  g1lt : wv m B (slot w aG) w < N
  g1 : wv m B (slot w aG) w % N = g * 2 ^ (64 * w) % N
  g2lt : wv m B (slot w aE) w < N
  g2 : wv m B (slot w aE) w % N = g ^ 2 * 2 ^ (64 * w) % N
  g3lt : wv m B (slot w aD) w < N
  g3 : wv m B (slot w aD) w % N = g ^ 3 * 2 ^ (64 * w) % N

theorem Powers.congr {m m' : Mem} {B : Addr} {w N g : Nat} (h : Powers m B w N g)
    {js hs : List Nat} (hf : Frm B (rg w js hs) m m') (hZ : slot w 16 ≤ 2 ^ 64)
    (hh : ∀ i ∈ hs, i < 32) (hg : aG ∉ js) (he : aE ∉ js) (hd : aD ∉ js) : Powers m' B w N g := by
  have e1 := hf.rg_wv hZ hh (j := aG) (by decide) hg (n := w) (by omega)
  have e2 := hf.rg_wv hZ hh (j := aE) (by decide) he (n := w) (by omega)
  have e3 := hf.rg_wv hZ hh (j := aD) (by decide) hd (n := w) (by omega)
  exact ⟨by rw [e1]; exact h.g1lt, by rw [e1]; exact h.g1,
    by rw [e2]; exact h.g2lt, by rw [e2]; exact h.g2,
    by rw [e3]; exact h.g3lt, by rw [e3]; exact h.g3⟩

/-- The table is built in arrays no longer used for the input exponents. -/
theorem powers_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g : Nat}
    (hc : Cst s B Z w minv N el r t) (hGlt : wv s.mem B (slot w aG) w < N)
    (hG : wv s.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) :
    WP isa (windowPowers M.mm) s fun u => Cst u B Z w minv N el r t ∧
      Frm B (rg w [aAcc, aTmp, aXm, aY, aE, aD] []) s.mem u.mem ∧ Keep mmRegs s u ∧
      Powers u.mem B w N g ∧ wv u.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
  have hz := hc.hZ16
  have hR := hc.coprime
  simp only [windowPowers, seqs]
  refine WP.seq (WP.mono (copy_ok hc (o := aXm) (a := aG) (by decide) (by decide) (by decide) (by decide))
    fun s₁ ⟨hc₁, f₁, k₁, hx₁⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok hc₁ (o := aY) (a := aG) (by decide) (by decide) (by decide) (by decide))
    fun s₂ ⟨hc₂, f₂, k₂, hy₂⟩ => ?_)
  have hg₂ : wv s₂.mem B (slot w aY) w = wv s.mem B (slot w aG) w := by
    rw [hy₂, f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega)]
  refine WP.seq (WP.mono (mul_ok M hc₂ (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hg₂]; exact hGlt))
    fun s₃ ⟨hc₃, f₃, k₃, hlt₃, hy₃⟩ => ?_)
  have hy₃' := mont_sq hR (x := g) (E := 1) (by rw [hg₂]; simpa only [Nat.pow_one] using hG) hy₃
  have hy₃'' : wv s₃.mem B (slot w aY) w % N = g ^ 2 * 2 ^ (64 * w) % N := by
    simpa only [Nat.mul_one] using hy₃'
  refine WP.seq (WP.mono (copy_ok hc₃ (o := aE) (a := aY) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨hc₄, f₄, k₄, he₄⟩ => ?_)
  have hx₄ : wv s₄.mem B (slot w aXm) w = wv s.mem B (slot w aG) w := by
    rw [f₄.rg_wv hz (by simp) (by decide) (by decide) (by omega),
      f₃.rg_wv hz (by simp) (by decide) (by decide) (by omega),
      f₂.rg_wv hz (by simp) (by decide) (by decide) (by omega), hx₁]
  refine WP.seq (WP.mono (mul_ok M hc₄ (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hx₄]; exact hGlt))
    fun s₅ ⟨hc₅, f₅, k₅, hlt₅, hy₅⟩ => ?_)
  have hy₅' := mont_mulp hR (E := 2) (b := 1) (by
    rw [f₄.rg_wv hz (by simp) (by decide) (by decide) (by omega)]; exact hy₃'')
    (by rw [hx₄]; simpa only [Nat.pow_one] using hG) hy₅
  have hy₅'' : wv s₅.mem B (slot w aY) w % N = g ^ 3 * 2 ^ (64 * w) % N := by
    simpa only [Nat.reduceAdd] using hy₅'
  refine WP.seq (WP.mono (copy_ok hc₅ (o := aD) (a := aY) (by decide) (by decide) (by decide) (by decide))
    fun s₆ ⟨hc₆, f₆, k₆, hd₆⟩ => ?_)
  refine WP.mono (copy_ok hc₆ (o := aY) (a := aO) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hcu, f₇, k₇, hy₇⟩ => ?_
  have fe := f₅.rg_trans f₆ |>.rg_trans f₇
  have fg := f₁.rg_trans f₂ |>.rg_trans f₃ |>.rg_trans f₄ |>.rg_trans f₅ |>.rg_trans f₆ |>.rg_trans f₇
  refine ⟨hcu, fg.rg_mono (by decide) (by simp),
    ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).mono (by decide), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fg.rg_wv hz (by simp) (by decide) (by decide) (by omega)]; exact hGlt
    · rw [fg.rg_wv hz (by simp) (by decide) (by decide) (by omega)]; exact hG
    · rw [fe.rg_wv hz (by simp) (by decide) (by decide) (by omega), he₄]; exact hlt₃
    · rw [fe.rg_wv hz (by simp) (by decide) (by decide) (by omega), he₄]; exact hy₃''
    · rw [f₇.rg_wv hz (by simp) (by decide) (by decide) (by omega), hd₆]; exact hlt₅
    · rw [f₇.rg_wv hz (by simp) (by decide) (by decide) (by omega), hd₆]; exact hy₅''
  · rw [hy₇, hc₆.ho]

/-- The masked four-entry selection returns the power of the top two bits. -/
theorem select_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g V : Nat}
    (hc : Cst s B Z w minv N el r t) (hp : Powers s.mem B w N g)
    (hv : word s.mem B (8 * sC2) = BitVec.ofNat 64 V) (hV : V < 2 ^ 64) :
    WP isa windowSelect s fun u => Cst u B Z w minv N el r t ∧
      Frm B (rg w [aXm] []) s.mem u.mem ∧ Keep mmRegs s u ∧
      wv u.mem B (slot w aXm) w < N ∧
      wv u.mem B (slot w aXm) w % N = g ^ (V / 2 ^ 62) * 2 ^ (64 * w) % N := by
  have hz := hc.hZ16
  have hn : 0 < N := by have := hc.n1; omega
  simp only [windowSelect, seqs]
  refine WP.seq (WP.mono (copy_ok hc (o := aXm) (a := aO) (by decide) (by decide) (by decide) (by decide))
    fun s₁ ⟨hc₁, f₁, k₁, hx₁⟩ => ?_)
  refine WP.seq (WP.mono (pick_ok hc₁.ws (a := aG) (j := 1) (by decide) (by decide) (by decide)
    (by rw [f₁.rg_word (by decide) (by simp)]; exact hv) hV) fun s₂ ⟨f₂, k₂, hx₂⟩ => ?_)
  have hc₂ := hc₁.congr f₂ (by decide) (by simp) k₂ (by decide)
  refine WP.seq (WP.mono (pick_ok hc₂.ws (a := aE) (j := 2) (by decide) (by decide) (by decide)
    (by rw [f₂.rg_word (by decide) (by simp), f₁.rg_word (by decide) (by simp)]; exact hv) hV)
    fun s₃ ⟨f₃, k₃, hx₃⟩ => ?_)
  have hc₃ := hc₂.congr f₃ (by decide) (by simp) k₃ (by decide)
  refine WP.mono (pick_ok hc₃.ws (a := aD) (j := 3) (by decide) (by decide) (by decide)
    (by rw [f₃.rg_word (by decide) (by simp), f₂.rg_word (by decide) (by simp),
      f₁.rg_word (by decide) (by simp)]; exact hv) hV) fun u ⟨f₄, k₄, hx₄⟩ => ?_
  have ff := f₁.rg_trans f₂ |>.rg_trans f₃ |>.rg_trans f₄
  have h1 : wv s₁.mem B (slot w aG) w = wv s.mem B (slot w aG) w :=
    f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega)
  have h2 : wv s₂.mem B (slot w aE) w = wv s.mem B (slot w aE) w :=
    (f₁.rg_trans f₂).rg_wv hz (by simp) (by decide) (by decide) (by omega)
  have h3 : wv s₃.mem B (slot w aD) w = wv s.mem B (slot w aD) w :=
    ((f₁.rg_trans f₂).rg_trans f₃).rg_wv hz (by simp) (by decide) (by decide) (by omega)
  refine ⟨hc₃.congr f₄ (by decide) (by simp) k₄ (by decide), ff.rg_mono (by decide) (by simp),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide), ?_, ?_⟩
  all_goals rw [hx₄, hx₃, hx₂, hx₁, h1, h2, h3, hc.ho]
  all_goals have hd : V / 2 ^ 62 < 4 := by omega
  all_goals rcases (by omega : V / 2 ^ 62 = 0 ∨ V / 2 ^ 62 = 1 ∨ V / 2 ^ 62 = 2 ∨ V / 2 ^ 62 = 3) with h0 | h0 | h0 | h0
  all_goals simp only [h0, Nat.reduceEqDiff, ne_eq, not_false_eq_true, not_true_eq_false,
    ↓reduceIte, Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mod_mod]
  · exact Nat.mod_lt _ hn
  · exact hp.g1lt
  · exact hp.g2lt
  · exact hp.g3lt
  · exact hp.g1
  · exact hp.g2
  · exact hp.g3

end RecoveryWindow
end VG.Proof.Rsa.X86_64
