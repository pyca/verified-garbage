module
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyTop
public import VerifiedGarbage.Proof.Rsa.AArch64.CkCT

import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
public import VerifiedGarbage.Proof.Rsa.AArch64.WDivCT
public import VerifiedGarbage.Proof.Rsa.AArch64.WDiv
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
meta import VerifiedGarbage.Proof.Rsa.AArch64.WDivCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.WDiv
meta import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
open VG.Impl.Rsa.AArch64.CheckKey (sP sPlen sQ sQlen sQI aX aR aM aA aRem aT aOne aE ltA mulE wmodOne wM aBase)
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

/-! ## `wmodOne` -/

/-- `n`'s first byte, as `wordGuard` reads it. -/
def ckGbyte (p : CkP) : BitVec (8 * 1) := Mem.read (fun _ => p.nb[0]?.getD 0) 0 1

/-- After `wordGuard`: its value, pinned. -/
def GKW (p : CkP) (s : State) : Prop := GK p s ∧ s.gpr .x9 = guardVal p.k p.pl p.ql (ckGbyte p)

/-- The registers `wordGuard` reads `n` through. -/
def ckGwVal (p : CkP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => p.pN
  | _ => 0

theorem ckGuard_ct : RelCT isa (Two GK) (.block (wordGuard sPlen sQlen)) (Two GKW) := by
  rw [wordGuard_eq]
  refine RelCT.block_append (pin_ct [.x0] [.x0, .x16] ckGwVal pins_GK (by taint_decide) (fun p s h => ?_)
    (by taint_decide) fun p s h => ?_)
  all_goals obtain ⟨I, m₀, c, rfl, h', L, hm⟩ := id h
  · have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi =>
      h'.ws.scr.ld (by have := h'.ws.h256; omega_using [hi, this])
    refine WP.mono (WP.keep [.x13, .x14, .x15, .x16] (Q := fun t => t.gpr .x16 = I.pN) (by
      brun [h'.ws.x0, hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hdr_enc (show sPlen < 32 by decide), hdr_enc (show sQlen < 32 by decide), hl Public.sN (by decide),
        hl Public.sK (by decide), hl sPlen (by decide), hl sQlen (by decide), h'.args.n]) (by decide) (by decide)
      (by decide +kernel)) fun t ⟨h16, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans h'.ws.x0
    · exact h16
  · have hn0 : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega_using [this]
    have hb : s.mem.read I.pN 1 = ckGbyte I.pub := by
      refine read1_eq ?_
      have := h'.n.val 0 hn0
      rw [show I.pN + BitVec.ofNat 64 0 = I.pN by simp] at this
      rw [this]
      dsimp only [CkIn.pub]
      rw [List.getElem?_eq_getElem hn0]; rfl
    refine WP.seq_iff.mpr (WP.block_append_iff.mp ?_)
    rw [← wordGuard_eq sPlen sQlen]
    exact WP.mono (wordGuard_ok h'.ws.scr h'.ws.x0 h'.ws.h256 (by decide) (by decide) h'.args.k h'.args.pl h'.args.ql
      h'.args.n hb (by simpa using h'.n.rd 0 hn0)) fun t ⟨⟨h9, mt⟩, kt⟩ =>
        ⟨h.same mt kt (by decide), h9⟩

/-- `wmodOne top lenL`, for a count `C p` of words that `top` sets and `[aA]`
of `Ln p` words (`lenL`). -/
theorem wmodOne_ckct {top lenL : List Instr} (C Ln : CkP → Nat)
    (hT : ∀ p s, GK p s → TopOk top p.B p.Z s.mem (C p)) (hC : ∀ p s, GK p s → 1 ≤ C p ∧ C p < wW p.cap)
    (hL : ∀ p s, GK p s → LenOk lenL (wW p.cap) (Ln p) ∧ Ln p ≤ wW p.cap ∧ wk p.k / 2 ≤ Ln p)
    {h₀ h₃ h₄ h₅ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tW : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aRem .x8 ++ [movi .x7 0]))
      (wdivRest aA aM aRem aT wM lenL aBase)) h₀).isSome = true)
    (tHi : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ base aA .x16 ++ base aRem .x17 ++ hiTail)) h₃).isSome = true)
    (tLo : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ base aA .x16 ++ base aQ .x17 ++ loTail)) h₄).isSome = true)
    (tCnt : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ top ++ cntTail)) h₅).isSome = true) :
    RelCT isa (Two GK) (seqs (wmodOne top lenL)) (Two GK) := by
  unfold wmodOne
  rw [List.append_assoc]
  refine ct_app (by simp) (by simp [eqA]) (ct_one ?_) (ct_app (by simp [eqA]) (by simp)
    (eqA_ckct (a := aRem) (b := aOne) (by decide) (by decide) (by taint_decide)) (ct_one andZero_ckct))
  refine RelCT.seq ckGuard_ct (two_ite (fun p s₁ s₂ h₁ h₂ => by
    obtain ⟨-, e₁⟩ := h₁
    obtain ⟨-, e₂⟩ := h₂
    rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero, e₁, e₂]) ?_ ?_)
  · -- The guard passes: `wdiv`.
    refine wdiv_ct CkP.B CkP.Z (fun p => wW p.cap) (fun _ _ h => h.1.1.ws) tW fun p s ⟨⟨h, h9⟩, he⟩ => ?_
    obtain ⟨I, m₀, c, rfl, h', L, hm⟩ := id h
    have hg : guardVal I.k I.pl I.ql (ckGbyte I.pub) = 0 := by
      rw [VG.Proof.MlKem.AArch64.eval_zero, h9] at he; simpa [CkIn.pub] using he
    have hk1 := L.k1
    have hk2 := L.k2
    have pl2 := L.pl2
    have ql2 := L.ql2
    obtain ⟨g16, -, -, -⟩ := guard_zero (k := I.k) (pl := I.pl) (ql := I.ql) (by omega_using [hk2]) (by omega_using [hk2, pl2]) (by omega_using [hk2, ql2]) hg
    have eW : wW I.cap = 2 * wk I.k + 2 := by rw [L.capk]
    have hw8 : 8 ≤ wk I.k := by unfold wk; omega_using [hk1]
    have hwm : (wW I.cap - 2) / 4 = wk I.k / 2 := by rw [eW]; unfold wk; omega_using []
    have hW := ckWm_ok (wW I.cap) (by omega_using [eW]) (by rw [eW]; unfold wk; omega_using [hk2])
    have hxb := ckXb_ok I.B (wW I.cap) (by rw [eW]; unfold wk; omega_using [g16]) (by rw [eW]; unfold wk; omega_using [hk2])
    rw [hwm] at hW hxb
    obtain ⟨hL', l1, l2⟩ := hL _ s h
    dsimp only [CkIn.pub] at hL' l1 l2
    exact WP.mono (wdiv_ok h'.ws (iX := aA) (iM := aM) (iR := aRem) (iT := aT) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hW hL' hxb (by omega_using [hw8]) (by omega_using [eW])
      (by omega_using [l1]) l2) fun t ⟨_, ft, kt, _⟩ => ⟨I, m₀, c, rfl, h'.step ft (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> exact h'.ws.sl (by decide)) kt (by decide), L, by
        show word t.mem I.B (8 * Public.sMask) = _
        rw [ft.word_eq (fun r hr => by
          simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> dsimp only <;>
            exact .inl (hdr_lt_slot _ _ (show Public.sMask < 32 by decide))) (by unfold Public.sMask sFn; omega_using [])]
        exact hm⟩
  · -- `reduceTop`.
    exact (reduceTop_ckct C hT hC (by taint_decide) (by taint_decide) tHi tLo tCnt (by taint_decide)
      (by taint_decide)).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h

end VG.Proof.Rsa.AArch64
