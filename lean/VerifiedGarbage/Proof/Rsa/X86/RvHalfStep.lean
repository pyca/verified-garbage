module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Rsa.RecoverMath

import VerifiedGarbage.Proof.Rsa.RecoverHalving
import VerifiedGarbage.Proof.Rsa.X86.RvCount
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.KeyBits32
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.Set
/-! # One fixed-schedule halving iteration -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvHalfBit.lean`, which only this module imported.
section

/-! # Recording whether the current exponent is even and counting its halvings -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Rsa.KeyBits32

def Vhalf (V : Nat → Nat) (R : Nat) : Nat → Nat :=
  upd (upd (upd V sBit (R % 2)) sBit (1 - R % 2)) sTc (V sTc + (1 - R % 2))

theorem KS.halfBit_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) (hr : wR ∈ liveW) (hc : sTc ∈ ls)
    (bound : V sTc ≤ 16384) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverRt.halfBit) s fun t =>
      KS g s0 A live AW liveW (Vhalf V (AW wR)) (sTc :: sBit :: sBit :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.halfBit
  refine WP.block_append (WP.mono (h.bitOf_W hr (by decide)) fun u ⟨hu, _⟩ => ?_)
  refine WP.block_append (WP.mono (hu.loadSlot (d := sBit) (by simp) (r := .eax) (by decide))
    fun v ⟨hv, vx, _⟩ => ?_)
  refine wp_logicS (.inr rfl) rfl fun w W => ?_
  have hw := hv.of_rest W.keeps (by decide) W.mem
  have even : (w.gpr .eax).toNat = 1 - AW wR % 2 := by
    rw [W.gpr, ite_eq_right (by decide), vx, upd_self]
    rw [bv_xor_bits (by rw [BitVec.toNat_ofNat]; omega) (by decide), BitVec.toNat_ofNat]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine WP.block_append (WP.mono (hw.storeSlot (d := sBit) (by decide) .eax)
    fun x ⟨hx, _, rx⟩ => ?_)
  rw [even] at hx
  refine WP.block_append (WP.mono (hx.loadSlot (d := sTc) (by simp [hc]) (r := .edx) (by decide))
    fun y ⟨hy, yt, ry⟩ => ?_)
  refine wp_addS rfl fun z Z _ => ?_
  have hz := hy.of_rest Z.keeps (by decide) Z.mem
  have total : (z.gpr .edx).toNat = V sTc + (1 - AW wR % 2) := by
    rw [Z.gpr, yt, ry.1 .eax (by decide), rx.1 .eax (by decide),
      upd_ne _ _ (by decide : sTc ≠ sBit), upd_ne _ _ (by decide : sTc ≠ sBit),
      BitVec.toNat_add, BitVec.toNat_ofNat, even]
    omega
  refine WP.mono (hz.storeSlot (d := sTc) (by decide) .edx) fun t ⟨ht, _, _⟩ => ?_
  rw [total] at ht
  exact ht

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (halveStep)

abbrev hvs (m k : Nat) : Nat × Nat := halveStep^[k] (m, 0)
def AWh (m k : Nat) : Nat → Nat := fun _ => (hvs m k).1
def Vh (c m k : Nat) : Nat → Nat := upd (upd (fun _ => 0) sTc (hvs m k).2) sCnt (c - k)
def HI (g : Geo) (s0 : State) (A : Nat → Nat) (m c k : Nat) (s : State) : Prop :=
  KS g s0 A [aN] (AWh m k) [wR] (Vh c m k) [sTc, sCnt] s

theorem halfBody_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {m c k : Nat}
    (h : HI g s0 A m c k s) (hk : k < c) (hc : c ≤ 16384) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.halfBody s fun t => HI g s0 A m c (k + 1) t ∧
      t.zf = some (decide (c - (k + 1) = 0)) := by
  have countBound := VG.Proof.Rsa.halve_count_le m k
  generalize eR : (hvs m k).1 = R at *
  generalize eT : (hvs m k).2 = T at *
  have aW : AWh m k = fun _ => R := funext fun _ => eR
  have vT : Vh c m k sTc = T := by simp [Vh, upd, sTc, sCnt, eT]
  have vC : Vh c m k sCnt = c - k := by simp [Vh, upd]
  change KS _ _ _ _ _ _ _ _ _ at h
  rw [aW] at h
  unfold VG.Impl.Rsa.X86.RecoverRt.halfBody
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_W (o := wH) (a := wR) (by decide) (by simp) (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s2 ⟨h2, _⟩ => ?_)
  rw [upd_noop rfl] at h2
  refine WP.seq (wp_movS rfl fun s3 U _ => WP.block_nil ?_)
  have h3 := h2.of_rest U.keeps (by decide) U.mem
  refine WP.seq (WP.mono (h3.half_W (j := wH) (by simp) (by rw [U.gpr]; rfl)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s4 ⟨h4, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.halfBit_ok (by simp) (by simp) (by rw [vT]; omega))
    fun s5 h5 => ?_)
  have bitR : upd (fun _ => R) wH (R / 2) wR = R := rfl
  rw [bitR] at h5
  have bitValue : Vhalf (Vh c m k) R sBit = 1 - R % 2 := rfl
  refine WP.seq (WP.mono (h5.sel_W (o := wR) (a := wR) (b := wH) (sl := sBit)
    (by decide) (by simp) (by simp) (by simp) (by rw [bitValue]; omega) (.inr (by decide))
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s6 ⟨h6, _⟩ => ?_)
  have count : Vhalf (Vh c m k) R sCnt = c - k := by
    unfold Vhalf
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), vC]
  refine WP.mono (h6.cntNext_ok (by simp) (by rw [count]; omega) (by rw [count]; omega))
    fun t ⟨ht, zt⟩ => ⟨?_, ?_⟩
  · have hs : hvs m (k + 1) = halveStep (R, T) := by
      rw [hvs, Function.iterate_succ_apply']
      congr 1
      exact Prod.ext eR eT
    refine ht.mono (fun j hj => ⟨by simpa using hj, rfl⟩) (fun j hj => ?_) (fun d hd => ?_)
    · simp only [List.mem_singleton] at hj; subst j
      refine ⟨by simp, ?_⟩
      simp only [AWh, hs, halveStep]
      rw [upd_self, bitValue, upd_ne (fun _ => R) (R / 2) (show wR ≠ wH by decide), upd_self]
      by_cases even : R % 2 = 0
      · simp only [even, ite_true]; split <;> omega
      · simp only [even, ite_false]; split <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨by simp, ?_⟩
        rw [upd_ne _ _ (by decide)]
        change Vh c m k sTc + (1 - R % 2) = _
        rw [vT]
        simp only [Vh, hs, halveStep]
        rw [upd_ne _ _ (by decide), upd_self]
        by_cases even : R % 2 = 0
        · simp only [even, ite_true]
        · simp only [even, ite_false]; omega
      · refine ⟨by simp, ?_⟩
        rw [upd_self, count]
        simp only [Vh, upd_self]
        omega
  · rw [zt, count]
    congr 2

end VG.Proof.Rsa.X86.Recover

