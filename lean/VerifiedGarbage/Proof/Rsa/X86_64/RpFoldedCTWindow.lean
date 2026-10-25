module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTSquare
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTPieces
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTSquare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTPieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCompare
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedMasks
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedReset
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedSquare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCompare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedReset
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedSquare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
public import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowPowers
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTPieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTPieces
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase

/-! # Constant time of a folded two-bit window -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aXm sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (powMod)
open Rp

def WQ (selected : Bool) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N E sigma g y x : Nat) (v : Track),
    Cst s p.B p.Z (wk p.k) minv N p.el E sigma ∧ RecoveryWindow.Powers s.mem p.B (wk p.k) N g ∧
    TrackRep s.mem p.B (wk p.k) N v ∧ y < N ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = y * 2 ^ (64 * wk p.k) % N ∧
    (selected = true → x < N ∧ wv s.mem p.B (slot (wk p.k) aXm) (wk p.k) = x * 2 ^ (64 * wk p.k) % N)

theorem WQ.ws {sel : Bool} {p : RpP} {s : State} (h : WQ sel p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc.ws

theorem WQ.sq {sel : Bool} {p : RpP} {s : State} (h : WQ sel p s) : SQ 0 p s := by
  obtain ⟨minv, N, E, sigma, g, y, x, v, hc, _, hv, hy, hY, _⟩ := h
  exact ⟨minv, N, E, sigma, y, v, hc, hv, hy, hY, fun h => by omega, fun h => by omega⟩

theorem select_ct : RelCT isa (Two (WQ false)) windowSelect (Two (WQ true)) := by
  refine two_post (two_map (Φ' := RecoveryWindow.WT false) id (fun p s h => ?_) (RecoveryWindow.select_ct.mono (fun _ _ h => h) (fun _ _ _ => trivial)))
    fun p s ⟨minv, N, E, sigma, g, y, x, v, hc, hp, hv, hy, hY, _⟩ => ?_
  · obtain ⟨minv, N, E, sigma, g, y, x, v, hc, hp, hv, hy, hY, _⟩ := h
    have hN : 0 < N := by have := hc.n1; omega
    exact ⟨minv, N, E, sigma, g, hc, hp, by dsimp only [id]; rw [hY]; exact Nat.mod_lt _ hN, fun h => by cases h⟩
  have hN : 0 < N := by have := hc.n1; omega
  let V := (word s.mem p.B (8 * sC2)).toNat
  refine WP.mono (RecoveryWindow.select_ok hc hp (V := V) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (BitVec.isLt _)) fun u ⟨hc', f, k, hxlt, hx⟩ => ?_
  let d := V / 2 ^ 62
  have hx' : wv u.mem p.B (slot (wk p.k) aXm) (wk p.k) = powMod g d N * 2 ^ (64 * wk p.k) % N := by
    rw [Nat.mod_eq_of_lt hxlt] at hx
    rw [hx, powMod_eq, Nat.mod_mul_mod]
  exact ⟨minv, N, E, sigma, g, y, powMod g d N, v, hc',
    hp.congr f hc.hZ16 (by simp) (by decide) (by decide) (by decide), hv.congr f hc.hZ16 (by simp) (by decide), hy,
    by rw [f.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hY,
    fun _ => ⟨by rw [powMod_eq]; exact Nat.mod_lt _ hN, hx'⟩⟩

theorem windowSquare_ct (M : Mont) : RelCT isa (Two (WQ true)) (Folded.square M.mm none) (Two (WQ true)) := by
  refine two_post (two_map id (fun _ _ h => h.sq) (square_ct M none (Or.inl rfl)))
    fun p s ⟨minv, N, E, sigma, g, y, x, v, hc, hp, hv, hy, hY, hx⟩ => ?_
  have hN : 0 < N := by have := hc.n1; omega
  refine WP.mono (square_ok M hc (Or.inl rfl) hv hy hY) fun u ⟨hc', hv', hy', f, k⟩ => ?_
  exact ⟨minv, N, E, sigma, g, y * y % N, x, _, hc',
    hp.congr f hc.hZ16 (by decide) (by decide) (by decide) (by decide), hv', Nat.mod_lt _ hN, hy',
    fun _ => ⟨(hx rfl).1, by rw [f.rg_wv hc.hZ16 (by decide) (by decide) (by decide) (by omega)]; exact (hx rfl).2⟩⟩

theorem windowMul_ct (M : Mont) : RelCT isa (Two (WQ true)) (M.mm aY aY aXm) (Two (WQ true)) := by
  refine mm_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) M (by unfold MmUse; decide)
    fun p s ⟨minv, N, E, sigma, g, y, x, v, hc, hp, hv, hy, hY, hx⟩ => ?_
  have hN : 0 < N := by have := hc.n1; omega
  refine WP.mono (RecoveryWindow.mul_ok M hc (a := aY) (b := aXm) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [(hx rfl).2]; exact Nat.mod_lt _ hN))
    fun u ⟨hc', f, k, hlt, hm⟩ => ?_
  exact ⟨minv, N, E, sigma, g, y * x % N, x, v, hc',
    hp.congr f hc.hZ16 (by simp) (by decide) (by decide) (by decide), hv.congr f hc.hZ16 (by simp) (by decide),
    Nat.mod_lt _ hN, VG.Proof.RsaKeyGen.mont_val hc.coprime hlt hm hY (hx rfl).2,
    fun _ => ⟨(hx rfl).1, by rw [f.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact (hx rfl).2⟩⟩

theorem windowReset_ct : RelCT isa (Two (WQ true)) reset (Two (WQ true)) := by
  refine reset_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ?_ ?_
  · intro p s ⟨minv, N, E, sigma, g, y, x, v, hc, hp, hv, hy, hY, hx⟩
    exact WP.mono (comparisons_ok hc (a := aY) (by decide) hy hY) fun _ ⟨hc', _⟩ => hc'.ws
  · intro p s ⟨minv, N, E, sigma, g, y, x, v, hc, hp, hv, hy, hY, hx⟩
    refine WP.mono (reset_ok hc hv hy hY rfl) fun u ⟨hc', hv', f, k⟩ => ?_
    exact ⟨minv, N, E, sigma, g, y, x, _, hc',
      hp.congr f hc.hZ16 (by decide) (by decide) (by decide) (by decide), hv', hy,
      by rw [f.rg_wv hc.hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hY,
      fun _ => ⟨(hx rfl).1, by rw [f.rg_wv hc.hZ16 (by decide) (by decide) (by decide) (by omega)]; exact (hx rfl).2⟩⟩

theorem body_ct (M : Mont) : RelCT isa (Two (WQ false)) (Folded.window M.mm) fun _ _ => True := by
  unfold Folded.window
  refine RelCT.seq (R := Two (WQ true)) ?_ ?_
  · simp only [windowArithmetic, seqs]
    exact RelCT.seq select_ct (RelCT.seq (windowSquare_ct M) (RelCT.seq (windowSquare_ct M)
      (RelCT.seq (windowMul_ct M) windowReset_ct)))
  · exact two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]) (by taint_decide)

end VG.Proof.Rsa.X86_64.RecoveryFolded
