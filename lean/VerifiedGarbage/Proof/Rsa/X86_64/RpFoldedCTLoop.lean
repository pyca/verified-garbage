module

import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTWindow
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTLoop
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedLoop
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedTrack
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4

/-! # Public loop counts for the folded scan -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aXm aAcc aTmp sMask sCnt)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (powMod)
open Rp

def BI (q : RpP × Nat) (j : Nat) (u : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (N E sigma g : Nat) (R : Option Nat),
    1 ≤ q.2 ∧ q.2 ≤ bW q.1 ∧ BitInv s₀ q.1.B q.1.Z (wk q.1.k) minv N q.1.el E sigma g q.2 j R u

theorem bitLoop_ct (M : Mont) : RelCT isa (Two fun q s => 0 < 32 ∧ BI q 0 s)
    (.loop (Folded.window M.mm) .ne) (Two fun q s => BI q 32 s) := by
  refine two_loop (fun _ => 32) (two_map (fun q => q.1.1) (fun q s h => ?_) (body_ct M)) ?_
  · obtain ⟨_, s₀, minv, N, E, sigma, g, R, _, _, hi⟩ := h
    obtain ⟨v, hv, _⟩ := hi.track
    have hN : 0 < N := by have := hi.cst.n1; omega
    exact ⟨minv, N, E, sigma, g, powMod g (E / 4 ^ (32 * q.1.2 - q.2)) N, 0, v,
      hi.cst, hi.powers, hv, by rw [powMod_eq]; exact Nat.mod_lt _ hN, hi.y, fun h => by cases h⟩
  · intro q j s hj ⟨s₀, minv, N, E, sigma, g, R, hq, hqb, hi⟩
    exact WP.mono (body_ok M hq hj hi) fun u ⟨hz, hi'⟩ =>
      ⟨eval_ne_count hj hz, fun _ => ⟨s₀, minv, N, E, sigma, g, R, hq, hqb, hi'⟩,
        fun h => h ▸ ⟨s₀, minv, N, E, sigma, g, R, hq, hqb, hi'⟩⟩

def WI (p : RpP) (k : Nat) (u : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (N E sigma g : Nat) (R : Option Nat),
    WordInv s₀ p.B p.Z (wk p.k) minv N p.el E sigma g (bW p - k) R u

def headVal (q : RpP × Nat) : Reg → BitVec 64
  | .rdi => q.1.B
  | .rbx => off q.1.B (slot (wk q.1.k) aM)
  | .rax => BitVec.ofNat 64 (bW q.1 - q.2 - 1)
  | _ => 0

theorem wordHead_ct : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < bW q.1 ∧ WI q.1 q.2 s) (.block wordHead)
    (Two fun (q : RpP × Nat) s => 0 < 32 ∧ BI (q.1, bW q.1 - q.2) 0 s) := by
  rw [RecoveryWindow.window_wordHead_eq]
  refine RelCT.block_append (ws_pin_ct (fun q : RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun q s ⟨_, _, _, _, _, _, _, _, hi⟩ => hi.cst.ws) (by taint_decide)
    [.rdi, .rbx, .rax] headVal (fun q s h => ?_) (by taint_decide) fun q s h => ?_)
  · obtain ⟨hk, s₀, minv, N, E, sigma, g, R, hi⟩ := h
    have hc := hi.cst
    have h256 := hc.ws.h256
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    rw [WP.block_append_iff]
    refine WP.mono hc.ws.ws_ok fun u₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aM (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hc.ws.rdi) h9)
      fun u₂ ⟨hbx, m₂, k₂⟩ => ?_
    have k12 := k₁.trans k₂
    have hs₂ := hc.ws.scr.congr k12.2.2
    have hdi₂ : u₂.gpr .rdi = q.1.B := (k12.gpr (by decide)).trans hc.ws.rdi
    have e1 : BitVec.ofNat 64 (bW q.1 - q.2) - 1 = BitVec.ofNat 64 (bW q.1 - q.2 - 1) :=
      ofNat64_pred (by omega) (by simp only [bW]; unfold wk at *; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 (bW q.1 - q.2 - 1)) (by
      xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega),
        m₂, m₁, hi.c1, e1]) rfl) fun u ⟨hax, k₃⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k₃.gpr (by decide)).trans hdi₂
    · exact (k₃.gpr (by decide)).trans hbx
    · exact hax
  · obtain ⟨hk, s₀, minv, N, E, sigma, g, R, hi⟩ := h
    have hw : WP isa (.block wordHead) s fun u => 0 < 32 ∧ BI (q.1, bW q.1 - q.2) 0 u :=
      WP.mono (head_ok (by omega) (by simp only [bW]; omega) hi) fun u hi' =>
        ⟨by decide, s₀, minv, N, E, sigma, g, R, by omega, by change bW q.1 - q.2 ≤ bW q.1; omega, hi'⟩
    rw [RecoveryWindow.window_wordHead_eq] at hw
    exact WP.seq_iff.mpr (WP.block_append_iff.mp hw)

/-- A word's data-dependent work has a fixed public number of windows. -/
theorem wordBody_ct (M : Mont) : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < bW q.1 ∧ WI q.1 q.2 s)
    (.seq (.block wordHead) (.seq (.loop (Folded.window M.mm) .ne) (.block wordNext))) fun _ _ => True := by
  refine RelCT.seq wordHead_ct (RelCT.seq (two_map (fun q => (q.1, bW q.1 - q.2)) (fun _ _ h => h) (bitLoop_ct M)) ?_)
  exact two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    obtain ⟨_, _, _, _, _, _, _, _, _, hi₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, hi₂⟩ := h₂
    simp only [List.mem_singleton] at hr; subst hr; rw [hi₁.cst.ws.rdi, hi₂.cst.ws.rdi]) (by taint_decide)

/-- The outer loop consumes exactly the padded public exponent width. -/
theorem wordLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < bW p ∧ WI p 0 s)
    (.loop (.seq (.block wordHead) (.seq (.loop (Folded.window M.mm) .ne) (.block wordNext))) .ne)
    (Two fun p s => WI p (bW p) s) := by
  refine two_loop bW (wordBody_ct M) ?_
  intro p k s hk ⟨s₀, minv, N, E, sigma, g, R, hi⟩
  refine WP.mono (word_ok M (by omega) (by simp only [bW]; omega) hi) fun u ⟨hz, hi'⟩ => ?_
  have he : bW p - k - 1 = bW p - (k + 1) := by omega
  rw [he] at hz hi'
  have he' : (bW p - (k + 1) = 0) ↔ (k + 1 = bW p) := by omega
  have hz' : u.zf = some (decide (k + 1 = bW p)) := by simpa only [he'] using hz
  exact ⟨eval_ne_count hk hz', fun _ => ⟨s₀, minv, N, E, sigma, g, R, hi'⟩,
    fun h => h ▸ ⟨s₀, minv, N, E, sigma, g, R, hi'⟩⟩

end VG.Proof.Rsa.X86_64.RecoveryFolded
