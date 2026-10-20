module
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyTop
public import VerifiedGarbage.Proof.Rsa.AArch64.CkCT

import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyTop
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# Constant-time bounded RSA reduction on AArch64

Each block of `reduceTop` reads its workspace width and quotient count
from public data. The full and CRT checkers instantiate this proof with
their respective public length bounds.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sP sPlen sQ sQlen sQI aX aR aM aA aRem aT aOne aE ltA mulE mulXR)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ hiTail loTail cntTail reduceTop topE topQ modOne modChecks)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The registers `blkHi`'s copy uses, from the public data. -/
def hiVal (C : CkP → Nat) (p : CkP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wW p.cap) aA + 8 * C p)
  | .x17 => off p.B (slot (wW p.cap) aRem)
  | .x12 => BitVec.ofNat 64 (wW p.cap - C p)
  | _ => 0

/-- The registers `blkLo`'s copy uses. -/
def loVal (C : CkP → Nat) (p : CkP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wW p.cap) aA)
  | .x17 => off p.B (slot (wW p.cap) aQ + 8 * (wW p.cap - C p))
  | .x12 => BitVec.ofNat 64 (C p)
  | _ => 0

/-- The registers the loop uses. -/
def cntVal (C : CkP → Nat) (p : CkP) : Reg → BitVec 64
  | .x0 => p.B
  | .x12 => BitVec.ofNat 64 (wW p.cap)
  | .x11 => BitVec.ofNat 64 (8 * (wW p.cap + 2))
  | .x6 => BitVec.ofNat 64 (64 * C p)
  | _ => 0

/-- `reduceTop top` leaks the same in two runs with the same public data,
for a count `C p` of words that `top` sets. -/
theorem reduceTop_ckct {top : List Instr} (C : CkP → Nat)
    (hT : ∀ p s, GK p s → TopOk top p.B p.Z s.mem (C p)) (hC : ∀ p s, GK p s → 1 ≤ C p ∧ C p < wW p.cap)
    {h₁ h₂ h₃ h₄ h₅ h₆ h₇ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tR : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aRem .x8 ++ [movi .x7 0])) zeroAcc)
      h₁).isSome = true)
    (tQ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aQ .x8 ++ [movi .x7 0])) zeroAcc)
      h₂).isSome = true)
    (tHi : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ base aA .x16 ++ base aRem .x17 ++ hiTail)) h₃).isSome = true)
    (tLo : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ base aA .x16 ++ base aQ .x17 ++ loTail)) h₄).isSome = true)
    (tCnt : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ cntTail)) h₅).isSome = true)
    (tCopy : (taint.check (Taint.ofRegs [.x0, .x16, .x17, .x12]) copyWords h₆).isSome = true)
    (tLoop : (taint.check (Taint.ofRegs [.x0, .x12, .x11, .x6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep aQ aRem aM aT) (.nonzero .x .x6)) h₇).isSome = true) :
    RelCT isa (Two GK) (seqs (reduceTop top)) (Two GK) := by
  -- The facts about the layout `Ws` gives.
  have lay : ∀ {p : CkP} {s : State}, GK p s → slot (wW p.cap) 16 ≤ p.Z ∧ 1 ≤ wW p.cap ∧ wW p.cap < 2 ^ 24 ∧
      p.B.toNat + p.Z ≤ 2 ^ 64 := fun h => ⟨h.ws.hZ, by have := h.ws.w1; omega_using [this], h.ws.w2, h.ws.scr.nowrap⟩
  have hct : RelCT isa (Two GK) (seqs (reduceTop top)) fun _ _ => True := by
    refine (ct_cons (by simp) (zeroA_ckct (by decide) tR) (ct_cons (by simp) (zeroA_ckct (by decide) tQ)
      (ct_cons (Ψ := GK) (by simp) ?_ (ct_cons (Ψ := GK) (by simp) ?_
      (ct_one (Ψ := fun (_ : CkP) (_ : State) => True) ?_))))).mono (fun _ _ h => h) fun _ _ _ => trivial
    -- The words from `c` up into `[aRem]`.
    · refine pin_seq [.x0, .x16, .x17, .x12] (hiVal C) (two_taint [.x0] pins_GK tHi) (fun p s h => ?_) tCopy
        (fun p s h => ?_)
      · refine WP.mono (blkHi_ok h.ws (hT p s h) (hC p s h).2) fun t ⟨⟨e16, e17, e12, _⟩, k⟩ r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (k.gpr .x0 (by decide)).trans h.ws.x0
        · exact e16
        · exact e17
        · exact e12
      · obtain ⟨hZ, hw1, hw, hn⟩ := lay h
        have hc := (hC p s h).2
        have sA := Nat.le_trans (slot_lt (w := wW p.cap) (show aA < 16 by decide)) hZ
        have sR := Nat.le_trans (slot_lt (w := wW p.cap) (show aRem < 16 by decide)) hZ
        have pAR := slot_sep (w := wW p.cap) (show aA ≠ aRem by decide)
        refine WP.seq (WP.mono (blkHi_ok h.ws (hT p s h) hc) fun t ⟨⟨e16, e17, e12, m⟩, k⟩ => ?_)
        have hs := h.ws.scr.congr k.wr
        refine WP.mono (copyWords_ok e16 e17 e12 (by omega_using [hc]) (by omega_using [hw]) (by omega_using [hn, sR])
          (fun i hi => hs.ld (by omega_using [sA, hi])) (fun i hi => hs.st (by omega_using [sR, hi]))
          (fun i hi b hb => by rw [ofs_off p.B (by omega_using [hn, sA, hi, hb])]; omega_using [pAR, hi, hb])) fun u ⟨_, _, o, _, _, k'⟩ => ?_
        rw [m] at o
        exact h.arr (show aRem < 16 by decide) (Nat.le_refl _) (o.mono (by omega_using []) (by omega_using [])) (k.trans k')
          (by decide)
    -- The low words into the top of `[aQ]`.
    · refine pin_seq [.x0, .x16, .x17, .x12] (loVal C) (two_taint [.x0] pins_GK tLo) (fun p s h => ?_) tCopy
        (fun p s h => ?_)
      · refine WP.mono (blkLo_ok h.ws (hT p s h) (hC p s h).2) fun t ⟨⟨e16, e17, e12, _⟩, k⟩ r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (k.gpr .x0 (by decide)).trans h.ws.x0
        · exact e16
        · exact e17
        · exact e12
      · obtain ⟨hZ, hw1, hw, hn⟩ := lay h
        have hc := (hC p s h).2
        have hc1 := (hC p s h).1
        have sA := Nat.le_trans (slot_lt (w := wW p.cap) (show aA < 16 by decide)) hZ
        have sQ := Nat.le_trans (slot_lt (w := wW p.cap) (show aQ < 16 by decide)) hZ
        have pAQ := slot_sep (w := wW p.cap) (show aA ≠ aQ by decide)
        refine WP.seq (WP.mono (blkLo_ok h.ws (hT p s h) hc) fun t ⟨⟨e16, e17, e12, m⟩, k⟩ => ?_)
        have hs := h.ws.scr.congr k.wr
        refine WP.mono (copyWords_ok e16 e17 e12 hc1 (by omega_using [hw, hc]) (by omega_using [hn, hc, sQ])
          (fun i hi => hs.ld (by omega_using [hc, sA, hi])) (fun i hi => hs.st (by omega_using [hc, sQ, hi]))
          (fun i hi b hb => by rw [ofs_off p.B (by omega_using [hn, hc, sA, hi, hb])]; omega_using [hc, pAQ, hi, hb])) fun u ⟨_, _, o, _, _, k'⟩ => ?_
        rw [m] at o
        exact h.arr (show aQ < 16 by decide) (Nat.le_refl _) (o.mono (by omega_using []) (by omega_using [hc])) (k.trans k')
          (by decide)
    -- The count, and the loop.
    · refine pin_seq (Ψ := fun (_ : CkP) (_ : State) => True) [.x0, .x12, .x11, .x6] (cntVal C) (two_taint [.x0] pins_GK tCnt)
        (fun p s h => ?_) tLoop (fun p s h => ?_)
      · refine WP.mono (blkCnt_ok h.ws (hT p s h) (hC p s h).2) fun t ⟨⟨e6, e12, e11, _⟩, k⟩ r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (k.gpr .x0 (by decide)).trans h.ws.x0
        · exact e12
        · exact e11
        · exact e6
      · obtain ⟨hZ, hw1, hw, -⟩ := lay h
        exact WP.seq (WP.mono (blkCnt_ok h.ws (hT p s h) (hC p s h).2) fun t ⟨⟨e6, e12, e11, _⟩, k⟩ =>
          WP.mono (stepsTop_ok (h.ws.scr.congr k.wr) ((k.gpr .x0 (by decide)).trans h.ws.x0) e12 e11 hw1 hw hZ
            (hC p s h).1 (hC p s h).2 e6) fun _ _ => trivial)
  refine two_post hct fun p s h => ?_
  obtain ⟨I, m₀, c, rfl, hs, L, hm⟩ := id h
  exact WP.mono (ckReduceTop_ok hs (hT _ s h) (hC _ s h).1 (hC _ s h).2) fun t ⟨ht, mt, _, _⟩ =>
    ⟨I, m₀, c, rfl, ht, L, mt.trans hm⟩

/-- `modOne top`. -/
theorem modOneTop_ckct {top : List Instr} (C : CkP → Nat)
    (hT : ∀ p s, GK p s → TopOk top p.B p.Z s.mem (C p)) (hC : ∀ p s, GK p s → 1 ≤ C p ∧ C p < wW p.cap)
    {h₃ h₄ h₅ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tHi : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ base aA .x16 ++ base aRem .x17 ++ hiTail)) h₃).isSome = true)
    (tLo : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ base aA .x16 ++ base aQ .x17 ++ loTail)) h₄).isSome = true)
    (tCnt : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ cntTail)) h₅).isSome = true) :
    RelCT isa (Two GK) (seqs (modOne top)) (Two GK) := by
  unfold modOne
  rw [List.append_assoc]
  exact ct_app (by simp [reduceTop]) (by simp [eqA]) (reduceTop_ckct C hT hC (by taint_decide)
    (by taint_decide) tHi tLo tCnt (by taint_decide) (by taint_decide))
    (ct_app (by simp [eqA]) (by simp) (eqA_ckct (a := aRem) (b := aOne) (by decide) (by decide)
      (by taint_decide)) (ct_one andZero_ckct))


end VG.Proof.Rsa.AArch64
