module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTLoop
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTPrepare
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT7
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTPrepare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT7
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedExp
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedLoop
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedMasks
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedSquare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedExp
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedSquare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTSquare
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTSquare
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase

/-! # Constant time of the padded folded exponentiation and its fixed suffix -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aXm sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (powMod)
open Rp

def EX0 (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N E sigma g : Nat), Cst s p.B p.Z (wk p.k) minv N p.el E sigma ∧
    RecoveryWindow.Powers s.mem p.B (wk p.k) N g ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = 2 ^ (64 * wk p.k) % N

def EX (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N E sigma g : Nat) (v : Track), Cst s p.B p.Z (wk p.k) minv N p.el E sigma ∧
    RecoveryWindow.Powers s.mem p.B (wk p.k) N g ∧ TrackRep s.mem p.B (wk p.k) N v ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = 2 ^ (64 * wk p.k) % N

theorem paddedScan_ct (M : Mont) : RelCT isa (Two EX) (paddedScan M.mm) (Two fun p s => WI p (bW p) s) := by
  unfold paddedScan
  refine RelCT.seq (blk_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ ⟨_, _, _, _, _, _, hc, _⟩ => hc.ws)
    (by taint_decide) ?_) (wordLoop_ct M)
  intro p s ⟨minv, N, E, sigma, g, v, hc, hp, hv, hY⟩
  have hN : 0 < bW p := by have := hc.ws.w1; unfold bW; omega
  let R := VG.Proof.Rsa.RecoveryFolded.result (VG.Proof.Rsa.RecoveryFolded.run N sigma (powMod g E N)
    (VG.Proof.Rsa.RecoveryFolded.scan N g E (32 * bW p) v))
  exact WP.mono (init_ok hc hp hv (R := R) rfl hY) fun u hi =>
    ⟨hN, s, minv, N, E, sigma, g, R, by simpa only [Nat.sub_zero] using hi⟩

theorem windows_ct (M : Mont) : RelCT isa (Two EX0) (windows M.mm) (Two fun p s => WI p (bW p) s) := by
  unfold windows
  refine RelCT.seq (zeroA_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) ?_) (paddedScan_ct M)
  intro p s ⟨minv, N, E, sigma, g, hc, hp, hY⟩
  exact WP.mono (zeroRoot_ok hc hp hY) fun u ⟨hc', hp', hv', hy', _, _⟩ =>
    ⟨minv, N, E, sigma, g, initial, hc', hp', hv', hy'⟩

theorem squareStep_ct (M : Mont) (j : Option Nat) (hj : j = none ∨ j = some 1) :
    RelCT isa (Two (SQ 0)) (Folded.square M.mm j) (Two (SQ 0)) := by
  refine two_post (square_ct M j hj) fun p s ⟨minv, N, E, sigma, y, v, hc, hv, hy, hY, _, _⟩ => ?_
  have hN : 0 < N := by have := hc.n1; omega
  exact WP.mono (square_ok M hc hj hv hy hY) fun u ⟨hc', hv', hy', _, _⟩ =>
    ⟨minv, N, E, sigma, y * y % N, _, hc', hv', Nat.mod_lt _ hN, hy', fun h => by omega, fun h => by omega⟩

theorem finish_ct : RelCT isa (Two (SQ 0)) finish fun _ _ => True := by
  unfold finish
  have e : ws ++ base aRoot .r8 ++ ([.mov .rax (.mem found), .store (hdr sC3) .rax] : List Instr) =
      ws ++ (base aRoot .r8 ++ [.mov .rax (.mem found), .store (hdr sC3) .rax]) := List.append_assoc _ _ _
  rw [e]
  let F (p : RpP) (u : State) := Ws u p.B p.Z (wk p.k) ∧
    WP isa (.block (ws ++ (base aRoot .r8 ++ [.mov .rax (.mem found), .store (hdr sC3) .rax]))) u (fun _ => True)
  refine (RelCT.seq (R := Two F) (copyA_gct (Ψ := F) RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ h => h.ws) (by taint_decide) ?_)
    (ws_block_ct (Ψ := fun _ _ => True) RpP.B RpP.Z (fun p => wk p.k)
      (fun _ _ h => h.1) (by taint_decide) (fun _ _ h => h.2))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  intro p s ⟨minv, N, E, sigma, y, v, hc, hv, hy, hY, _, _⟩
  have hw := WP.seq_iff.mp (WP.mono (finish_ok hc hv) fun _ _ => trivial)
  rw [e] at hw
  apply WP.and ?_ hw
  exact WP.mono (RecoveryWindow.copy_ok hc (o := aY) (a := aRoot) (by decide) (by decide) (by decide) (by decide))
    fun _ ⟨hc', _⟩ => hc'.ws

/-- The scan plus suffix discloses no exponent bits or alignment shift. -/
theorem exp_ct (M : Mont) : RelCT isa (Two Rp.EX) (exponentiate M.mm) fun _ _ => True := by
  simp only [exponentiate, seqs]
  refine RelCT.seq (two_post (RecoveryWindow.prepare_ct M) ?_) (RelCT.seq (windows_ct M) ?_)
  · intro p s ⟨minv, N, E, sigma, g, hc, hGlt, hG, _⟩
    exact WP.mono (RecoveryWindow.powers_ok M hc hGlt hG) fun _ ⟨hc', _, _, hp', hY'⟩ =>
      ⟨minv, N, E, sigma, g, hc', hp', hY'⟩
  · refine RelCT.seq (R := Two (SQ 0)) ?_ finish_ct
    unfold suffix
    apply two_map (Φ' := SQ 0) id ?_ (RelCT.seq (squareStep_ct M none (Or.inl rfl)) (squareStep_ct M (some 1) (Or.inr rfl)))
    intro p s ⟨s₀, minv, N, E, sigma, g, R, hi⟩
    obtain ⟨v, hv, _⟩ := hi.track
    have hN : 0 < N := by have := hi.cst.n1; omega
    refine ⟨minv, N, E, sigma, powMod g E N, v, hi.cst, hv,
      by rw [powMod_eq]; exact Nat.mod_lt _ hN, ?_, fun h => by omega, fun h => by omega⟩
    simpa only [id, bW, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] using hi.y

end VG.Proof.Rsa.X86_64.RecoveryFolded
