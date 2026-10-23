module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedSquare
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedReset
public import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowPowers
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math

/-! # The arithmetic and tracker transition of one folded window -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aXm aAcc aTmp sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (powMod)

theorem powMod_win2 (g p d N : Nat) :
    powMod g (4 * p + d) N = VG.Proof.RsaKeyGen.sqIter N (powMod g p N) 2 * powMod g d N % N := by
  rw [VG.Proof.RsaKeyGen.sqIter_pow N _ 2 (by decide), powMod_eq, powMod_eq, powMod_eq,
    ← Nat.pow_mod, ← Nat.mul_mod, ← Nat.pow_mul, ← Nat.pow_add, show 4 * p = p * 2 ^ 2 by omega]

theorem arithmetic_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma g p : Nat} {v : Track} {V : BitVec 64}
    (hc : Cst s B Z w minv N el E sigma) (hp : RecoveryWindow.Powers s.mem B w N g)
    (hv : TrackRep s.mem B w N v)
    (hY : wv s.mem B (slot w aY) w = powMod g p N * 2 ^ (64 * w) % N)
    (hV : word s.mem B (8 * sC2) = V) :
    WP isa (windowArithmetic M.mm) s fun u =>
      Cst u B Z w minv N el E sigma ∧
      TrackRep u.mem B w N
        (resetTrack (V.toNat / 2 ^ 62) N (powMod g (4 * p + V.toNat / 2 ^ 62) N)
          (VG.Proof.Rsa.RecoveryFolded.run N 2 (powMod g p N) v)) ∧
      wv u.mem B (slot w aY) w = powMod g (4 * p + V.toNat / 2 ^ 62) N * 2 ^ (64 * w) % N ∧
      Frm B (rg w [aXm, aAcc, aTmp, aX, aRoot, aY] [sMask]) s.mem u.mem ∧ Keep mmRegs s u := by
  have hz := hc.hZ16
  have hR := hc.coprime
  have hN0 : 0 < N := by have := hc.n1; omega
  let y := powMod g p N
  have hy : y < N := by dsimp [y]; rw [powMod_eq]; exact Nat.mod_lt _ hN0
  have hy1 : y * y % N < N := Nat.mod_lt _ hN0
  let d := V.toNat / 2 ^ 62
  simp only [windowArithmetic, seqs]
  refine WP.seq (WP.mono (RecoveryWindow.select_ok hc hp (by rw [BitVec.ofNat_toNat]; exact hV) V.isLt)
    fun s₁ ⟨hc₁, f₁, k₁, hXm₁lt, hXm₁⟩ => ?_)
  have ht₁ := hv.congr f₁ hz (by simp) (by decide)
  have hy₁ : wv s₁.mem B (slot w aY) w = y * 2 ^ (64 * w) % N := by
    rw [f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega)]; exact hY
  refine WP.seq (WP.mono (square_ok M hc₁ (j := none) (Or.inl rfl) ht₁ hy hy₁)
    fun s₂ ⟨hc₂, ht₂, hy₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (square_ok M hc₂ (j := none) (Or.inl rfl) ht₂ hy1 hy₂)
    fun s₃ ⟨hc₃, ht₃, hy₃, f₃, k₃⟩ => ?_)
  have ht₃' : TrackRep s₃.mem B w N (VG.Proof.Rsa.RecoveryFolded.run N 2 y v) := ht₃
  have f13 := f₂.rg_trans f₃
  have hx₃ : wv s₃.mem B (slot w aXm) w = wv s₁.mem B (slot w aXm) w :=
    f13.rg_wv hz (by decide) (by decide) (by decide) (by omega)
  have hXm₁' : wv s₁.mem B (slot w aXm) w = g ^ d * 2 ^ (64 * w) % N := by
    rw [Nat.mod_eq_of_lt hXm₁lt] at hXm₁
    exact hXm₁
  have hx₃' : wv s₃.mem B (slot w aXm) w = powMod g d N * 2 ^ (64 * w) % N := by
    rw [hx₃, hXm₁', powMod_eq, Nat.mod_mul_mod]
  refine WP.seq (WP.mono (RecoveryWindow.mul_ok M hc₃ (a := aY) (b := aXm)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hx₃]; exact hXm₁lt)) fun s₄ ⟨hc₄, f₄, k₄, hy₄lt, hy₄⟩ => ?_)
  have hy₄' := VG.Proof.RsaKeyGen.mont_val hR hy₄lt hy₄ hy₃ hx₃'
  have hwin : (y * y % N * (y * y % N) % N) * powMod g d N % N = powMod g (4 * p + d) N :=
    (powMod_win2 g p d N).symm
  rw [hwin] at hy₄'
  have ht₄ := ht₃'.congr f₄ hz (by simp) (by decide)
  have ff := ((f₁.rg_trans f₂).rg_trans f₃).rg_trans f₄
  have hV₄ : word s₄.mem B (8 * sC2) = V := by
    rw [ff.rg_word (by decide) (by decide)]; exact hV
  have hyp : powMod g (4 * p + d) N < N := by rw [powMod_eq]; exact Nat.mod_lt _ hN0
  refine WP.mono (reset_ok hc₄ ht₄ hyp hy₄' hV₄) fun u ⟨hcu, htu, f₅, k₅⟩ => ?_
  refine ⟨hcu, htu, ?_, (ff.rg_trans f₅).rg_mono (by decide) (by decide),
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  rw [f₅.rg_wv hz (by decide) (by decide) (by decide) (by omega)]
  exact hy₄'

end VG.Proof.Rsa.X86_64.RecoveryFolded
