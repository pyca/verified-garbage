module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvCount
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # One binary-exponentiation step in prime recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev liveExp : List Nat := [mY, mG, mR2, mBase, aO, aNg, aZ, aOne, aN]
abbrev slotsExp : List Nat := [sInv, sCnt, sTc, sCand]

theorem expBody_step {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m : Nat}
    (h : KS g s0 A liveExp AW [wRc, wR] V slotsExp s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0)
    (hy : A mY < m) (hg : A mG < m) (ho : A aO < m)
    (lo : 1 ≤ V sCnt) (hi : V sCnt < 2 ^ 32) :
    WP isa (expBody g.n) s fun t => ∃ Y G,
      KS g s0 (upd (upd A mY Y) mG G) liveExp (upd AW wRc (AW wRc / 2)) [wRc, wR]
        (upd V sCnt (V sCnt - 1)) slotsExp t ∧
      Y < m ∧ G < m ∧
      Y * 2 ^ (64 * g.n) % m = A mY * (if AW wRc % 2 = 0 then A aO else A mG) % m ∧
      G * 2 ^ (64 * g.n) % m = A mG * A mG % m ∧
      t.zf = some (decide (V sCnt - 1 = 0)) := by
  unfold expBody
  simp only [seqs]
  refine WP.seq (WP.block_append (WP.mono (h.bitOf_W (j := wRc) (sl := sBit)
    (by simp) (by decide)) fun s1 ⟨h1, _⟩ => ?_))
  refine wp_movS rfl fun s2 U _ => WP.block_nil ?_
  have h2 := h1.of_rest U.keeps (by decide) U.mem
  refine WP.seq (WP.mono (h2.half_W (j := wRc) (by simp) (by rw [U.gpr]; rfl)
    (by decide)) fun s3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.sel_w (o := mXm) (a := aO) (b := mG) (sl := sBit)
    (by decide) (by simp [liveExp]) (by simp [liveExp]) (by simp)
    (by rw [upd_self]; omega) (by decide)) fun s4 ⟨h4, _⟩ => ?_)
  simp only [upd_self] at h4
  have mr4 := h4.montReady (m := m) (by simp [liveExp]) (by simp [slotsExp])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mXm)] using value) bound
    (by simpa only [upd_ne _ _ (by decide : sInv ≠ sBit)] using inverse)
  have selLt : (if AW wRc % 2 = 0 then A aO else A mG) < m := by split <;> with_reducible assumption
  refine WP.seq (WP.mono (h4.mmul mr4 (o := mY) (a := mY) (b := mXm)
    (by decide) (by decide) (by decide) (by decide) (by simp [liveExp]) (by simp)
    (by simpa only [upd_ne _ _ (by decide : mY ≠ mXm)] using hy)
    (by simpa only [upd_self] using selLt) (by decide) (by decide))
    fun s5 ⟨Y, h5, mr5, _, ylt, yv⟩ => ?_)
  refine WP.seq (WP.mono (h5.mmul mr5 (o := mG) (a := mG) (b := mG)
    (by decide) (by decide) (by decide) (by decide) (by simp [liveExp]) (by simp [liveExp])
    (by simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_ne _ _ (by decide : mG ≠ mXm)] using hg)
    (by simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_ne _ _ (by decide : mG ≠ mXm)] using hg)
    (by decide) (by decide)) fun s6 ⟨G, h6, _, _, glt, gv⟩ => ?_)
  refine WP.mono (h6.cntNext_ok (by simp [slotsExp])
    (by simpa only [upd_ne _ _ (by decide : sCnt ≠ sBit)] using lo)
    (by simpa only [upd_ne _ _ (by decide : sCnt ≠ sBit)] using hi)) fun t ⟨ht, zt⟩ => ?_
  refine ⟨Y, G, ht.mono ?_ ?_ ?_, ylt, glt, ?_, ?_, ?_⟩
  · intro j hj
    simp only [liveExp, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [liveExp, upd, mY, mG, mXm, mR2, mBase, aO, aNg, aZ, aOne, aN]
  · simp
  · intro d hd
    simp only [slotsExp, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [slotsExp, upd, sInv, sCnt, sTc, sCand, sBit]
  · simpa only [upd_self, upd_ne _ _ (by decide : mY ≠ mXm)] using yv
  · simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_ne _ _ (by decide : mG ≠ mXm)] using gv
  · simpa only [upd_ne _ _ (by decide : sCnt ≠ sBit)] using zt

end VG.Proof.Rsa.X86.Recover
