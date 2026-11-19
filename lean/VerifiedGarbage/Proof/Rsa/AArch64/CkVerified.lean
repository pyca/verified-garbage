module

public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.AArch64.CkCT
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Rsa.AArch64.CkMain
public import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.AArch64.CvTail
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvTail
meta import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy

/-! ### `Rsa.AArch64.CkCTCode`, which only this module used -/

section

/-! ### `Rsa.AArch64.CkCTMain`, which only this module used -/

section

/-! ### `Rsa.AArch64.CrtKeyCT`, which only this module used -/

section

/-! ### `Rsa.AArch64.CkCTPieces`, which this module and modules that import it used -/

section

/-!
# Shared constant-time pieces for RSA key validation on AArch64

Compositions of `CkCT.lean` used by both the full and CRT checkers:
loads, comparisons, product checks, and the final mask return.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem toGKb {α : Type} {Φ : α → State → Prop} {c : Prog isa} {js js' : List Nat}
    (h : RelCT isa (Two Φ) c (Two (GKb js))) (hj : ∀ j ∈ js', j ∈ js) : RelCT isa (Two Φ) c (Two (GKb js')) :=
  h.mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.mono hj) h

theorem toGK {α : Type} {Φ : α → State → Prop} {c : Prog isa} {js : List Nat}
    (h : RelCT isa (Two Φ) c (Two (GKb js))) : RelCT isa (Two Φ) c (Two GK) :=
  h.mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.1) h

theorem ofGK {Ψ : CkP → State → Prop} {c : Prog isa} (h : RelCT isa (Two (GKb [])) c (Two Ψ)) :
    RelCT isa (Two GK) c (Two Ψ) :=
  h.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h, by simp⟩) h) fun _ _ h => h

/-- The loads of `main`, from `GK`. -/
theorem ld_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CkP → Addr)
    (len : CkP → Nat) {js : List Nat} (hjs : ∀ i ∈ js, i ≠ j ∧ i < 16)
    (hA : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧
      (∃ bs, Src s I.B I.Z (ptr I.pub) bs ∧ bs.length = len I.pub) ∧ 1 ≤ len I.pub ∧ len I.pub ≤ I.cap)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (GKb js)) (seqs (loadA j sPtr sLen)) (Two (GKb (j :: js))) :=
  loadA_ckct hj hP hL hjs ptr len (fun p s h => by
    obtain ⟨I, m₀, c, rfl, hs, L, -⟩ := h
    exact hA I m₀ s hs L) ht₁ ht₂ ht₃

theorem ldWide_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CkP → Addr)
    (len : CkP → Nat) {js : List Nat} (hjs : ∀ i ∈ js, i ≠ j ∧ i < 16)
    (hA : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧
      (∃ bs, Src s I.B I.Z (ptr I.pub) bs ∧ bs.length = len I.pub) ∧ 1 ≤ len I.pub ∧ len I.pub ≤ I.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (GKb js)) (seqs (loadA j sPtr sLen)) (Two (GKb js)) :=
  loadA_wide_ckct hj hP hL hjs ptr len (fun p s h => by
    obtain ⟨I, m₀, c, rfl, hs, L, -⟩ := h
    exact hA I m₀ s hs L) ht₁ ht₂ ht₃

/-! ## The phases -/

theorem ckPQ_ct : RelCT isa (Two GK) (seqs (loadA aX sP sPlen ++ (loadA aR sQ sQlen ++
    (mulPQ ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa))))))) (Two GK) := by
  refine ofGK (ct_app (by simp [loadA]) (by simp [loadA]) (ld_ct (by decide) (by decide) (by decide) CkP.pP CkP.pl
    (by simp) (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, L.pcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA]) (by simp [mulPQ])
    (ld_ct (by decide) (by decide) (by decide) CkP.pQ CkP.ql (by decide)
      (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, L.qcap⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [mulPQ]) (by simp [eqA]) (mulPQ_ckct (by taint_decide) |>.mono
      (fun _ _ h => two_mono (fun _ _ h => h.mono (by simp)) h) fun _ _ h => h)
      (ct_app (by simp [eqA]) (by simp) (eqA_ckct (by decide) (by decide) (by taint_decide))
        (ct_one andZero_ckct)))))

theorem ckDN_ct : RelCT isa (Two GK) (seqs (loadA aX sD sDlen ++ ltA aX 0)) (Two GK) :=
  toGK (ofGK (ct_app (by simp [loadA]) (by simp [ltA]) (ld_ct (by decide) (by decide) (by decide) CkP.pD CkP.dl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.d, hs.args.dl, ⟨_, hs.d, L.dbl⟩, L.dl1, L.dcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
    (ltA_ckct (by decide) (by decide) (by decide) (by taint_decide))))


theorem retMaskK_ct : RelCT isa (Two GK) (.block retMask) (Two fun (_ : CkP) (_ : State) => True) :=
  two_post (two_taint [.x0] pins_GK (by taint_decide)) fun _ _ h => by
    obtain ⟨I, m₀, c, rfl, hs, -, hm⟩ := h
    exact WP.mono (cvExit_ok hs.ws hm) fun _ _ => trivial

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.CrtKeyCTReduce`, which this module and modules that import it used -/

section

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

end

end

/-!
# `vg_rsa_check_crt_key` on AArch64: constant time

Compose the shared pieces from `CkCTPieces.lean` and bounded reductions
from `CrtKeyCTReduce.lean` into the CRT checks and their main routine.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sP sPlen sQ sQlen sQI aX aR aM aA aRem aT aOne aE ltA mulE mulPQ wmodOne lenQ)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ hiTail loTail cntTail reduceTop topE topQ modChecks)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `qInv < p` and `q qInv ≡ 1 (mod p)`. -/
theorem ckQIC_ct : RelCT isa (Two GK) (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++
    (loadA aR sQ sQlen ++ (mulPQ ++ wmodOne topQ lenQ)))))) (Two GK) :=
  ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pP CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, L.pcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))))
  (ofGK (ct_app (by simp [loadA]) (by simp [ltA]) (ld_ct (by decide) (by decide) (by decide) CkP.pQi CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.qi, hs.args.pl, ⟨_, hs.qi, L.qibl⟩, L.pl1, L.pcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
  (ct_app (by simp [ltA]) (by simp [loadA]) (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide) (by decide)
    (by decide) (by taint_decide))
  (ct_app (by simp [loadA]) (by simp [mulPQ]) (toGKb (ld_ct (by decide) (by decide) (by decide) CkP.pQ CkP.ql
    (js := [aX]) (by decide) (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, L.qcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) (js' := [aX, aR]) (by decide))
  (ct_app (by simp [mulPQ]) (by simp [wmodOne]) (mulPQ_ckct (by taint_decide))
    (wmodOne_ckct (fun p => (p.ql + 7) / 8) (fun p => (wW p.cap - 2) / 2) (fun p s h => by
        obtain ⟨I, m₀, c, rfl, hs, L, -⟩ := h
        exact topQ_ok hs.args.ql (by simp only [CkIn.pub]; have := L.ql2; have := L.k2; omega_arith)
          (by simp only [CkIn.pub]; have := hs.ws.h256; omega_using [this]))
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, -, L, -⟩ := h
        have := L.ql1; have := L.qcap
        exact ⟨by simp only [CkIn.pub]; omega_arith, by simp only [CkIn.pub, wW, wk]; omega_using [this]⟩)
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, -, L, -⟩ := h
        have := L.k2
        dsimp only [CkIn.pub]
        rw [L.capk]
        exact ⟨ckLenQ_ok _ (by unfold wW wk; omega_using []) (by unfold wW wk; omega_using [this]), by omega_using [], by unfold wW wk; omega_using []⟩)
      (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)))))))

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_check_key` on AArch64: constant time, `main`

The pieces of `CkCT.lean` in sequence: the phases of the checks
(`ckPQ_ct`, `ckMod_ct`, `ckQIC_ct`), and `main` (`ckMain_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG.Impl.Rsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The checks modulo `X - 1`. -/
theorem ckMod_ct {sX sXlen sDX sYlen : Nat} (hsX : sX < 32) (hsL : sXlen < 32) (hsD : sDX < 32) (pX pDX : CkP → Addr)
    (xl : CkP → Nat)
    (hX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sX) = pX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.cap)
    (hDX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sDX) = pDX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pDX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.cap)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aM .x8 ++ [ldh .x1 sX, ldh .x2 sXlen]))
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htDX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aX .x8 ++ [ldh .x1 sDX, ldh .x2 sXlen]))
      hc₂).isSome = true)
    (hsY : sYlen < 32) (yl : CkP → Nat)
    (hY : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I →
      word s.mem I.B (8 * sYlen) = BitVec.ofNat 64 (yl I.pub) ∧ yl I.pub ≤ I.cap)
    {h₃ h₄ h₅ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tHi : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ topD sYlen ++ base aA .x16 ++ base aRem .x17 ++ CheckCrtKey.hiTail)) h₃).isSome = true)
    (tLo : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ topD sYlen ++ base aA .x16 ++ base CheckCrtKey.aQ .x17 ++ CheckCrtKey.loTail)) h₄).isSome = true)
    (tCnt : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ topD sYlen ++ CheckCrtKey.cntTail)) h₅).isSome = true) :
    RelCT isa (Two GK) (seqs (modChecks sX sXlen sDX sYlen)) (Two GK) := by
  rw [modChecks_eq]
  have ldX := toGK (ofGK (ld_ct (j := aM) (by decide) hsX hsL pX xl (by decide) hX (by taint_decide) htX (by taint_decide)))
  have ldDX := ofGK (ld_ct (j := aX) (by decide) hsD hsL pDX xl (by decide) hDX (by taint_decide) htDX (by taint_decide))
  have ldD := ofGK (ld_ct (j := aX) (by decide) (by decide) (by decide) CkP.pD CkP.dl (by decide)
    (fun I m₀ s hs L => ⟨hs.args.d, hs.args.dl, ⟨_, hs.d, L.dbl⟩, L.dl1, L.dcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
  have mE := mulE_ckct (by taint_decide) (by taint_decide)
  have rD : RelCT isa (Two GK) (seqs (wmodOne (topD sYlen) lenD)) (Two GK) :=
    wmodOne_ckct (fun p => (yl p + 7) / 8 + 1) (fun p => wW p.cap / 2)
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, hs, L, _⟩ := h
        obtain ⟨a, b⟩ := hY I m₀ s hs L
        exact topD_ok hsY a (by have := L.cap2; have := L.k2; omega_arith) hs.ws.h256)
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, hs, L, _⟩ := h
        have := (hY I m₀ s hs L).2
        have := L.cap1
        change 1 ≤ (yl I.pub + 7) / 8 + 1 ∧ (yl I.pub + 7) / 8 + 1 < wW I.cap
        unfold wW wk; omega_arith)
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, -, L, -⟩ := h
        have := L.k2
        dsimp only [CkIn.pub]
        rw [L.capk]
        exact ⟨ckLenD_ok _ (by unfold wW wk; omega_using [this]), by omega_using [], by unfold wW wk; omega_using []⟩)
      (by taint_decide) tHi tLo tCnt
  have rE : RelCT isa (Two GK) (seqs (wmodOne CheckCrtKey.topE lenE)) (Two GK) :=
    wmodOne_ckct (fun _ => 1) (fun p => (wW p.cap - 2) / 4 + 1) (fun p s _ => topE_ok p.B p.Z s.mem)
      (fun p s h => by obtain ⟨I, m₀, c, rfl, hs, L, _⟩ := h; simp only [CkIn.pub, wW]; omega_arith)
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, -, L, -⟩ := h
        have := L.k2
        have := L.k1
        dsimp only [CkIn.pub]
        rw [L.capk]
        exact ⟨ckLenE_ok _ (by unfold wW wk; omega_using []) (by unfold wW wk; omega_arith), by unfold wW wk; omega_using [],
          by unfold wW wk; omega_using []⟩)
      (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
  exact ct_app (by simp [loadA]) (by simp) ldX (ct_app (a := [.block (decA aM)]) (by simp) (by simp [loadA])
    (ct_one (decA_ckct (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [ltA]) ldDX
    (ct_app (by simp [ltA]) (by simp [loadA]) (toGK (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide)
      (by decide) (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [mulE]) ldD
    (ct_app (by simp [mulE]) (by simp [wmodOne]) mE
    (ct_app (by simp [wmodOne]) (by simp [loadA]) rD
    (ct_app (by simp [loadA]) (by simp [mulE]) ldDX
    (ct_app (by simp [mulE]) (by simp [wmodOne]) mE rE))))))))

/-! ## `main` -/

/-- On entry to `main`. -/
def GKM (p : CkP) (s : State) : Prop := ∃ I : CkIn, I.pub = p ∧ CkPre I s ∧ I.cap = I.k

theorem pins_GKM : Pins GKM [.x0] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0]
  exact (congrArg CkP.B e₁).trans (congrArg CkP.B e₂).symm

theorem ckHead_ct : RelCT isa (Two GKM) (.block VG.Impl.Rsa.AArch64.CheckKey.head) (Two GK) :=
  two_piece [.x0] pins_GKM (by taint_decide) fun _ s ⟨I, e, h, hc⟩ =>
    WP.mono (ckHeadS_ok h hc) fun _ ⟨ht, hm⟩ => ⟨I, s.mem, true, e, ht, h.L, hm⟩

/-- `main` leaks the same in two runs with the same public data. -/
theorem ckMain_ct : RelCT isa (Two GKM) VG.Impl.Rsa.AArch64.CheckKey.main fun _ _ => True := by
  rw [ckMain_eq]
  refine (ct_app (by simp) (by simp [loadA]) (ct_one ckHead_ct)
    (ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ldWide_ct (by decide) (by decide) (by decide) CkP.pN CkP.k
      (by decide) (fun I m₀ s hs L => ⟨hs.args.n, hs.args.k, ⟨_, hs.n, L.nl⟩, show 1 ≤ I.k by have := L.k1; omega_arith, Nat.le_refl _⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp) (toGK (ofGK (ldWide_ct (by decide) (by decide) (by decide) CkP.pE CkP.el
      (by decide) (fun I m₀ s hs L => ⟨hs.args.e, hs.args.el, ⟨_, hs.e, L.ebl⟩, L.el1, L.el2⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp) (by simp [loadA]) (ct_cons (by simp) (zeroA_ckct (by decide) (by taint_decide))
      (ct_one (setOneA_ckct (by decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp [loadA]) ckDN_ct
    (ct_app (by simp [loadA]) (by simp [modChecks]) ckPQ_ct
    (ct_app (by simp [modChecks]) (by simp [modChecks]) (ckMod_ct (by decide) (by decide) (by decide) CkP.pP CkP.pDp
      CkP.pl (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, L.pcap⟩)
      (fun I m₀ s hs L => ⟨hs.args.dp, hs.args.pl, ⟨_, hs.dp, L.dpbl⟩, L.pl1, L.pcap⟩)
      (by taint_decide) (by taint_decide)
      (by decide) CkP.ql (fun I m₀ s hs L => ⟨hs.args.ql, L.qcap⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [modChecks]) (by simp [loadA]) (ckMod_ct (by decide) (by decide) (by decide) CkP.pQ CkP.pDq
      CkP.ql (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, L.qcap⟩)
      (fun I m₀ s hs L => ⟨hs.args.dq, hs.args.ql, ⟨_, hs.dq, L.dqbl⟩, L.ql1, L.qcap⟩)
      (by taint_decide) (by taint_decide)
      (by decide) CkP.pl (fun I m₀ s hs L => ⟨hs.args.pl, L.pcap⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp) ckQIC_ct (ct_one retMaskK_ct)))))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.CkCode`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_check_key` on AArch64: correctness

`CheckKey.code`, from a state its contract allows, returns 1 exactly when
`checkKey` accepts its inputs (`ckCode_correct`), against `ckA`, which
states the shared contract's precondition on the registers and the stack.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `checkKey` of the inputs of a state. -/
def ckKeyOf (s : State) : Bool :=
  Spec.Rsa.checkKey (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat)

/-- `vg_rsa_check_key(n = x0, n_len = x1, e = x2, e_len = x3, d = x4,
d_len = x5, p = x6, p_len = x7, q = [sp], q_len = [sp + 8], dp = [sp + 16],
dp_len = [sp + 24], dq = [sp + 32], dq_len = [sp + 40], qinv = [sp + 48],
qinv_len = [sp + 56], scratch = [sp + 64], scratch_len = [sp + 72])`. -/
def ckA : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let e : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let d : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let p : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dp : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dq : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let qi : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    s.sp.toNat + 80 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, p, q, dp, dq, qi, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧ (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x1).toNat ∧ 1 ≤ (s.gpr .x3).toNat ∧ (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat ∧
      1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat ≤ (s.gpr .x1).toNat ∧
      1 ≤ (s.gpr .x7).toNat ∧ (s.gpr .x7).toNat < (s.gpr .x1).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .x1).toNat ∧ (stackArg s 3).toNat = (s.gpr .x7).toNat ∧
      (stackArg s 7).toNat = (s.gpr .x7).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x1).toNat ≤ (stackArg s 9).toNat
  post s s' := (s'.gpr .x0).setWidth 32 = if ckKeyOf s then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 10).map (stackArg s₁) = (List.range 10).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat

/-! ## The entry -/

theorem ckEntry_eq : entry = ([.ldrSp .x8 64, .str .x .x0 .x8 (8 * Public.sN), .str .x .x1 .x8 (8 * Public.sK),
    .str .x .x2 .x8 (8 * sE), .str .x .x3 .x8 (8 * sElen), .str .x .x4 .x8 (8 * sD), .str .x .x5 .x8 (8 * sDlen),
    .str .x .x6 .x8 (8 * sP), .str .x .x7 .x8 (8 * sPlen)] : List Instr) ++
    (hdrPairs [(0, sQ), (1, sQlen), (2, sDP), (4, sDQ), (6, sQI)] ++
      ([mov .x0 .x8, mov .x4 .x2, mov .x5 .x3] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def ckEntryMemA (m : Mem) (B : Addr) (vn vk ve vel vd vdl vp vpl : BitVec 64) : Mem :=
  (((((((m.writeW (off B (8 * Public.sN)) vn).writeW (off B (8 * Public.sK)) vk).writeW (off B (8 * sE)) ve).writeW
    (off B (8 * sElen)) vel).writeW (off B (8 * sD)) vd).writeW (off B (8 * sDlen)) vdl).writeW
    (off B (8 * sP)) vp).writeW (off B (8 * sPlen)) vpl

/-- The header after the entry's stores. -/
def ckEntryMem (m : Mem) (B : Addr) (vn vk ve vel vd vdl vp vpl vq vql vdp vdq vqi : BitVec 64) : Mem :=
  (((((ckEntryMemA m B vn vk ve vel vd vdl vp vpl).writeW (off B (8 * sQ)) vq).writeW
    (off B (8 * sQlen)) vql).writeW (off B (8 * sDP)) vdp).writeW (off B (8 * sDQ)) vdq).writeW (off B (8 * sQI)) vqi

theorem ckEntryMemA_outside (m : Mem) (B : Addr) (vn vk ve vel vd vdl vp vpl : BitVec 64) :
    Outside B 0 (8 * 32) m (ckEntryMemA m B vn vk ve vel vd vdl vp vpl) := by
  unfold ckEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem ckEntryMem_facts (m : Mem) (B : Addr) (vn vk ve vel vd vdl vp vpl vq vql vdp vdq vqi : BitVec 64) :
    let m' := ckEntryMem m B vn vk ve vel vd vdl vp vpl vq vql vdp vdq vqi
    word m' B (8 * Public.sN) = vn ∧ word m' B (8 * Public.sK) = vk ∧ word m' B (8 * sE) = ve ∧
    word m' B (8 * sElen) = vel ∧ word m' B (8 * sD) = vd ∧ word m' B (8 * sDlen) = vdl ∧
    word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧ word m' B (8 * sQ) = vq ∧
    word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDP) = vdp ∧ word m' B (8 * sDQ) = vdq ∧
    word m' B (8 * sQI) = vqi ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' ckEntryMem ckEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, the working space's base
(stack argument 8) in `x0`, and `e` and `e_len` in `x4` and `x5`. -/
theorem ckEntry_ok {s : State} {B : Addr} (hB : stackArg s 8 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 10, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .x0 = B ∧ t.gpr .x4 = s.gpr .x2 ∧ t.gpr .x5 = s.gpr .x3 ∧
      t.mem = ckEntryMem s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
        (s.gpr .x6) (s.gpr .x7) (stackArg s 0) (stackArg s 1) (stackArg s 2) (stackArg s 4) (stackArg s 6) ∧
      Keep [.x0, .x4, .x5, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = B := hB
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  rw [ckEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = ckEntryMemA s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
        (s.gpr .x6) (s.gpr .x7)) ?_ (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [exec_ldrSp ho ha8, hB', hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (show sE < 32 by decide), hdr_enc (show sElen < 32 by decide), hdr_enc (show sD < 32 by decide),
      hdr_enc (show sDlen < 32 by decide), hdr_enc (show sP < 32 by decide), hdr_enc (show sPlen < 32 by decide),
      hw Public.sN (by decide), hw Public.sK (by decide), hw sE (by decide), hw sElen (by decide), hw sD (by decide),
      hw sDlen (by decide), hw sP (by decide), hw sPlen (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact ckEntryMemA_outside _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x0, .x4, .x5] (Q := fun t => t.gpr .x0 = B ∧ t.gpr .x4 = s.gpr .x2 ∧
      t.gpr .x5 = s.gpr .x3 ∧ t.mem = t₂.mem)
    (by brun [h8₂, k12.gpr .x2 (by decide), k12.gpr .x3 (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h0, h4, h5, hm⟩, k₃⟩ => ⟨h0, h4, h5, by rw [hm, hm₂, hm₁]; rfl, (k12.trans k₃).mono (by decide)⟩

/-! ## The precondition, as the code uses it -/

/-- The inputs of `main`, from the entry state. -/
def ckIn (s : State) : CkIn where
  B := stackArg s 8
  Z := (stackArg s 9).toNat * 8
  k := (s.gpr .x1).toNat
  el := (s.gpr .x3).toNat
  dl := (s.gpr .x5).toNat
  pl := (s.gpr .x7).toNat
  ql := (stackArg s 1).toNat
  pN := s.gpr .x0
  pE := s.gpr .x2
  pD := s.gpr .x4
  pP := s.gpr .x6
  pQ := stackArg s 0
  pDp := stackArg s 2
  pDq := stackArg s 4
  pQi := stackArg s 6
  nb := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  eb := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  db := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  pb := Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  qb := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  dpb := Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat
  dqb := Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat
  qib := Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat
  W := s.wr

/-- What `CheckKey.code` uses of its contract's precondition. -/
structure CkCtx (s : State) : Prop where
  L : CkLens (ckIn s)
  hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8)
  ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 10, ∀ m', Outside (stackArg s 8) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x0) (ckIn s).nb
  e : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x2) (ckIn s).eb
  d : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x4) (ckIn s).db
  p : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x6) (ckIn s).pb
  q : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 0) (ckIn s).qb
  dp : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 2) (ckIn s).dpb
  dq : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 4) (ckIn s).dqb
  qi : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 6) (ckIn s).qib

theorem ckCtx_of {s : State} (h : ckA.pre s) : CkCtx s := by
  simp only [ckA] at h
  sig_split h
  rename_i hsp hrd hwr dns des dds dps dqs ddps ddqs dqis dsa wN wE wD wP wQ wDp wDq wQi wS hk hel1
    hel2 hdl1 hdl2 hpl1 hpl2 hql1 hql2 hdpl hqil hdql
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 80⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hdpl] at ddps wDp hrd
  rw [hqil] at dqis wQi hrd
  rw [hdql] at ddqs wDq hrd
  refine ⟨⟨hk1, hk2, hel1, hel2, hdl1, hdl2, hpl1, hpl2, hql1, hql2, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, by simp only [ckIn]; omega_arith, by simp only [ckIn]; omega_arith, by rfl,
      by simp only [ckIn]; omega_arith, by simp only [ckIn]; omega_arith, by simp only [ckIn]; omega_arith,
      by simp only [ckIn, wW, wk]; omega_arith, rfl⟩, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 80) (by omega_arith) (by omega_arith))
      rw [← stkAddr_add s j b] at this; omega_arith)),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd]; simp) (by omega_arith) des,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dds,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dps,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dqs,
    src_of_region (by rw [hrd]; simp) (by omega_arith) ddps,
    src_of_region (by rw [hrd]; simp) (by omega_arith) ddqs,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dqis⟩

/-- After `entry`, from `s`. -/
structure CkHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 8) ((stackArg s 9).toNat * 8)
  x0 : t.gpr .x0 = stackArg s 8
  x4 : t.gpr .x4 = s.gpr .x2
  x5 : t.gpr .x5 = BitVec.ofNat 64 (s.gpr .x3).toNat
  args : CkArgs t.mem (ckIn s).B (ckIn s).k (ckIn s).el (ckIn s).dl (ckIn s).pl (ckIn s).ql (ckIn s).pN
    (ckIn s).pE (ckIn s).pD (ckIn s).pP (ckIn s).pQ (ckIn s).pDp (ckIn s).pDq (ckIn s).pQi
  inScr : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem
  keep : Keep [.x0, .x4, .x5, .x8, .x9] s t

/-- `entry`. -/
theorem ckHead_ok' {s : State} (c : CkCtx s) : WP isa (.block entry) s (CkHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 8) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.mono (ckEntry_ok rfl hw c.ha c.hsep) fun t ⟨h0, h4, h5, hm, k⟩ => ?_
  obtain ⟨hN, hK, hE, hEl, hD, hDl, hP, hPl, hQ, hQl, hDP, hDQ, hQI, ho⟩ :=
    ckEntryMem_facts s.mem (stackArg s 8) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
      (s.gpr .x6) (s.gpr .x7) (stackArg s 0) (stackArg s 1) (stackArg s 2) (stackArg s 4) (stackArg s 6)
  rw [← hm] at hN hK hE hEl hD hDl hP hPl hQ hQl hDP hDQ hQI ho
  refine ⟨c.hs.congr k.wr, h0, h4, by rw [h5, ofNat_toNat64],
    ⟨hN, show word _ (stackArg s 8) _ = BitVec.ofNat 64 (s.gpr .x1).toNat by rw [hK, ofNat_toNat64], hE,
      show word _ (stackArg s 8) _ = BitVec.ofNat 64 (s.gpr .x3).toNat by rw [hEl, ofNat_toNat64], hD,
      show word _ (stackArg s 8) _ = BitVec.ofNat 64 (s.gpr .x5).toNat by rw [hDl, ofNat_toNat64], hP,
      show word _ (stackArg s 8) _ = BitVec.ofNat 64 (s.gpr .x7).toNat by rw [hPl, ofNat_toNat64], hQ,
      show word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hQl, ofNat_toNat64], hDP, hDQ,
      hQI⟩,
    InScr.of_outside ho (by omega_arith), k⟩

/-- `main`'s hypotheses after the head and the checks of `e` and `n`. -/
theorem ckPre_of {s t₁ t : State} (c : CkCtx s) (h : CkHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t) :
    CkPre (ckIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.wr, x0 := (k.gpr .x0 (by decide)).trans h.x0, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, e := c.e.congrK hi kk, d := c.d.congrK hi kk, p := c.p.congrK hi kk,
      q := c.q.congrK hi kk, dp := c.dp.congrK hi kk, dq := c.dq.congrK hi kk, qi := c.qi.congrK hi kk,
      L := c.L, wr := kk.wr }

theorem ckKeyOf_eq (s : State) : ckKeyOf s = Spec.Rsa.keyValid (ckIn s).k (ckIn s).N (ckIn s).E (ckIn s).D
    (ckIn s).P (ckIn s).Q (ckIn s).DP (ckIn s).DQ (ckIn s).QI := by
  simp only [ckKeyOf, Spec.Rsa.checkKey, bytesAt_length]
  rfl

theorem keyValid_false {k N E D P Q DP DQ QI : Nat}
    (h : Spec.Rsa.modulusValid N k = false ∨ Spec.Rsa.exponentValid E = false) :
    Spec.Rsa.keyValid k N E D P Q DP DQ QI = false := by
  unfold Spec.Rsa.keyValid
  rcases h with h | h <;> simp [h]

/-- `vg_rsa_check_key`. -/
theorem ckCode_correct (s : State) (h : ckA.pre s) :
    ∃ t s', Exec isa CheckKey.code s t s' ∧ abiPreserved s s' ∧ ckA.post s s' := by
  have c := ckCtx_of h
  clear h
  have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
  have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
  have hel1 : 1 ≤ (s.gpr .x3).toNat := c.L.el1
  have hel2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat := c.L.el2
  suffices hwp : WP isa CheckKey.code s fun s' => abiPreserved s s' ∧ ckA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold CheckKey.code
  refine WP.seq (WP.mono (ckHead_ok' c) fun t₁ h₁ => ?_)
  have heb₁ := c.e.congrK h₁.inScr h₁.keep
  have hel : (ckIn s).eb.length = (s.gpr .x3).toNat := bytesAt_length _ _ _
  refine WP.seq (WP.mono (expCheck_ok (eb := (ckIn s).eb) h₁.x4 h₁.x5 hel1 (by omega_arith)
    (fun i hi => heb₁.rd i (by rw [hel]; exact hi)) ?_) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_)
  · rw [← hel]
    refine List.ext_getElem (by simp [Spec.Rsa.bytesAt]) fun i h1 h2 => ?_
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact (heb₁.val i h1).symm
  have kk₂ := h₁.keep.trans k₂
  refine WP.ite (!Spec.Rsa.exponentValid (ckIn s).E) (by rw [eval_zero, hz₂]; cases Spec.Rsa.exponentValid _ <;> rfl)
    (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.exponentValid (ckIn s).E = false := by simpa using hb
    refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0) (by brun [fail]) (by decide) (by decide)
      (by decide +kernel)) fun t ⟨h0, kt⟩ => ⟨abiPreserved_of_keep ((kk₂.trans kt).mono (by decide)), ?_⟩
    show (t.gpr .x0).setWidth 32 = if ckKeyOf s then 1 else 0
    rw [ckKeyOf_eq, keyValid_false (.inr hv), h0]
    rfl
  · have hv : Spec.Rsa.exponentValid (ckIn s).E = true := by simpa using hb
    have hs₂ := h₁.scr.congr k₂.wr
    have hn := hs₂.nowrap
    have hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
    have h0₂ : t₂.gpr .x0 = stackArg s 8 := (k₂.gpr .x0 (by decide)).trans h₁.x0
    have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (stackArg s 8) (8 * i)) 8 := fun i hi => hs₂.ld (by omega_arith)
    have aN : word t₂.mem (stackArg s 8) (8 * Public.sN) = s.gpr .x0 := by rw [hm₂]; exact h₁.args.n
    have aK : word t₂.mem (stackArg s 8) (8 * Public.sK) = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [hm₂]; exact h₁.args.k
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x2, .x3] (Q := fun t => t.gpr .x2 = s.gpr .x0 ∧
        t.gpr .x3 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ t.mem = t₂.mem) (by
      brun [h0₂, hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sN (by decide), hl Public.sK (by decide), aN, aK])
      (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h2, h3, hm₃⟩, k₃⟩ => ?_
    have kk₃ := kk₂.trans k₃
    have hnb₃ := c.n.congrK (by rw [hm₃, hm₂]; exact h₁.inScr) kk₃
    have hnl : (ckIn s).nb.length = (s.gpr .x1).toNat := bytesAt_length _ _ _
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h2 h3 hk1 hk2 hnl
      (fun i hi => hnb₃.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb₃.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t₄ ⟨⟨hz₄, hm₄, _⟩, k₄⟩ => ?_
    have kk₄ := kk₃.trans k₄
    refine WP.ite (!Spec.Rsa.modulusValid (ckIn s).N (s.gpr .x1).toNat)
      (by rw [eval_zero, hz₄]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb' => ?_) (fun hb' => ?_)
    · have hv' : Spec.Rsa.modulusValid (ckIn s).N (s.gpr .x1).toNat = false := by simpa using hb'
      refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0) (by brun [fail]) (by decide) (by decide)
        (by decide +kernel)) fun t ⟨h0, kt⟩ => ⟨abiPreserved_of_keep ((kk₄.trans kt).mono (by decide)), ?_⟩
      show (t.gpr .x0).setWidth 32 = if ckKeyOf s then 1 else 0
      rw [ckKeyOf_eq, keyValid_false (k := (ckIn s).k) (.inl hv'), h0]
      rfl
    · have hv' : Spec.Rsa.modulusValid (ckIn s).N (s.gpr .x1).toNat = true := by simpa using hb'
      have hpre := ckPre_of c h₁ (by rw [hm₄, hm₃, hm₂]) ((k₂.trans (k₃.trans k₄)).mono (by decide))
      refine WP.mono (WP.keep (.x0 :: mmRegs) (ckMain_ok hpre hv' hv rfl) (by decide +kernel)
        (by decide) (by decide +kernel)) fun t ⟨hx, kt⟩ =>
        ⟨abiPreserved_of_keep ((kk₄.trans kt).mono (by decide)), ?_⟩
      show (t.gpr .x0).setWidth 32 = if ckKeyOf s then 1 else 0
      rw [ckKeyOf_eq, hx, setWidth_flag]

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_check_key` on AArch64: constant time but for `n` and `e`

`entry`, the checks of `e` and `n`, `fail` and `main` (`ckMain_ct`) leak
the same in runs that agree on the public data (`ckCode_ct`): the
contract's `ConstantTime` (`ckCode_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A state the contract allows, with the public data `p`. -/
def CKRel (p : CkP) (s : State) : Prop := ckA.pre s ∧ (ckIn s).pub = p

theorem ckEntry_split : entry = ([.ldrSp .x8 64] : List Instr) ++ entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def CK1 (p : CkP) (t : State) : Prop :=
  ∃ s, CKRel p s ∧ t.gpr .x8 = p.B ∧ t.gpr .x2 = p.pE ∧ t.gpr .x3 = BitVec.ofNat 64 p.el ∧
    WP isa (.block (entry.drop 1)) t (CkHeadPost s)

/-- After `entry`. -/
def CK2 (p : CkP) (t : State) : Prop := ∃ s, CKRel p s ∧ CkHeadPost s t

/-- After the check of `e`. -/
def CK3 (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CKRel p s ∧ CkHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)).toNat

/-- After the loads of `n`'s pointer and length. -/
def CK3b (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CKRel p s ∧ CkHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x2 = p.pN ∧ t.gpr .x3 = BitVec.ofNat 64 p.k ∧ Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true

/-- After the check of `n`. -/
def CK4 (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CKRel p s ∧ CkHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k).toNat ∧
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true

theorem ckRel_x {p : CkP} {s : State} (h : CKRel p s) :
    s.gpr .x0 = p.pN ∧ s.gpr .x1 = BitVec.ofNat 64 p.k ∧ s.gpr .x2 = p.pE ∧ s.gpr .x3 = BitVec.ofNat 64 p.el := by
  obtain ⟨-, rfl⟩ := h
  exact ⟨rfl, (ofNat_toNat64 _).symm, rfl, (ofNat_toNat64 _).symm⟩

/-- `fail` leaks nothing. -/
theorem ckFail_ct {α : Type} {Φ : α → State → Prop} : RelCT isa (Two Φ) (.block fail) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ _ hr => absurd hr (List.not_mem_nil)) (by taint_decide)

/-- `entry` leaks the same in runs with the same public data. -/
theorem ckEntry_ct : RelCT isa (Two CKRel) (.block entry) (Two CK2) := by
  rw [ckEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CK1) [.x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(ckRel_x h₁).2.2.1, (ckRel_x h₂).2.2.1]
    · rw [(ckRel_x h₁).2.2.2, (ckRel_x h₂).2.2.2]) (by taint_decide) ?_)
    (two_piece [.x8, .x2, .x3] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro p s hs
  have c := ckCtx_of hs.1
  have hh : WP isa (.block (([.ldrSp .x8 64] : List Instr) ++ entry.drop 1)) s (CkHeadPost s) := by
    rw [← ckEntry_split]; exact ckHead_ok' c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = stackArg s 8 := rfl
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := c.ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  obtain ⟨-, -, h2, h3⟩ := ckRel_x hs
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 8)
    (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
      ⟨s, hs, h8.trans (congrArg CkP.B hs.2), (k.gpr .x2 (by decide)).trans h2, (k.gpr .x3 (by decide)).trans h3, hw⟩

/-- `vg_rsa_check_key` leaks the same in runs that agree on the public
data. -/
theorem ckCode_ct : RelCT isa (Two CKRel) CheckKey.code fun _ _ => True := by
  unfold CheckKey.code
  refine RelCT.seq ckEntry_ct (RelCT.seq (R := Two CK3) ?_ ?_)
  -- The check of `e`.
  · refine two_piece [.x4, .x5] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.x4, h₂.x4, (ckRel_x c₁).2.2.1, (ckRel_x c₂).2.2.1]
      · rw [h₁.x5, h₂.x5, ofNat_toNat64, ofNat_toNat64, (ckRel_x c₁).2.2.2, (ckRel_x c₂).2.2.2])
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := ckCtx_of hs.1
    have heb := c.e.congrK h.inScr h.keep
    have hel : (ckIn s).eb.length = (s.gpr .x3).toNat := bytesAt_length _ _ _
    have hel1 : 1 ≤ (s.gpr .x3).toNat := c.L.el1
    have hel2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat := c.L.el2
    have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
    refine WP.mono (expCheck_ok (eb := (ckIn s).eb) h.x4 h.x5 hel1 (by omega_using [hel2, hk2])
      (fun i hi => heb.rd i (by rw [hel]; exact hi)) ?_) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    · rw [← hel]
      refine List.ext_getElem (by simp [Spec.Rsa.bytesAt]) fun i h1 h2 => ?_
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      exact (heb.val i h1).symm
    · rw [hz, ← hs.2]; rfl
  -- `fail` or the check of `n`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) (ckFail_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  refine RelCT.seq (R := Two CK4) (RelCT.block_append (RelCT.seq (R := Two CK3b) ?_ ?_)) ?_
  · refine two_piece [.x0] (fun p s₁ s₂ ⟨⟨σ₁, t₁, c₁, h₁, _, k₁, _⟩, _⟩ ⟨⟨σ₂, t₂, c₂, h₂, _, k₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [k₁.gpr .x0 (by decide), k₂.gpr .x0 (by decide), h₁.x0, h₂.x0]
      exact (congrArg CkP.B c₁.2).trans (congrArg CkP.B c₂.2).symm) (by taint_decide) ?_
    rintro p t ⟨⟨s, t₁, hs, h, hm, k, hz⟩, he⟩
    have hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true := by
      rw [eval_zero, hz] at he
      cases hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)
      · rw [hv] at he; exact absurd he (by decide)
      · rfl
    have c := ckCtx_of hs.1
    have hs₂ := h.scr.congr k.wr
    have hn := hs₂.nowrap
    have hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
    have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
    have h0 : t.gpr .x0 = stackArg s 8 := (k.gpr .x0 (by decide)).trans h.x0
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 8) (8 * i)) 8 := fun i hi => hs₂.ld (by omega_using [hZ, hk1, hi])
    have aN : word t.mem (stackArg s 8) (8 * Public.sN) = s.gpr .x0 := by rw [hm]; exact h.args.n
    have aK : word t.mem (stackArg s 8) (8 * Public.sK) = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [hm]; exact h.args.k
    refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = s.gpr .x0 ∧
        t'.gpr .x3 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ t'.mem = t.mem) (by
      brun [h0, hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sN (by decide), hl Public.sK (by decide), aN, aK])
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h2, h3, hm'⟩, k'⟩ =>
        ⟨s, t₁, hs, h, by rw [hm', hm], (k.trans k').mono (by decide), by rw [h2, ← hs.2]; rfl,
          by rw [h3, ← hs.2]; rfl, hev⟩
  · refine two_piece [.x2, .x3] (fun p s₁ s₂ ⟨_, _, _, _, _, _, a₁, b₁, _⟩ ⟨_, _, _, _, _, _, a₂, b₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide) ?_
    rintro p t ⟨s, t₁, hs, h, hm, k, h2, h3, hev⟩
    have c := ckCtx_of hs.1
    have hnb := c.n.congrK (by rw [hm]; exact h.inScr) (h.keep.trans k)
    have hnl : (ckIn s).nb.length = (s.gpr .x1).toNat := bytesAt_length _ _ _
    have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
    have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
    rw [← hs.2] at h2 h3
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h2 h3 hk1 hk2 hnl
      (fun i hi => hnb.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hz, hm', _⟩, k'⟩ =>
        ⟨s, t₁, hs, h, by rw [hm', hm], (k.trans k').mono (by decide), by rw [hz, ← hs.2]; rfl, hev⟩
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, z₂, _⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) (ckFail_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  exact ckMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
    ⟨ckIn s, hs.2, ckPre_of (ckCtx_of hs.1) h hm k, rfl⟩) h) fun _ _ h => h

/-- `vg_rsa_check_key` is constant time but for `n` and `e`. -/
theorem ckCode_constantTime : ConstantTime isa ckA.pre ckA.pub CheckKey.code := by
  refine RelCT.constantTime (ckCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(ckIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩,
    hp.2.1⟩) fun _ _ h => h)
  obtain ⟨hr, hsp, ha, hn, he⟩ := hp
  have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have a : ∀ j < 10, stackArg s₂ j = stackArg s₁ j := fun j hj => by
    have := congrArg (fun l => l[j]?) ha
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [CkIn.pub, ckIn, CkP.mk.injEq]
  refine ⟨a 8 (by decide), by rw [a 9 (by decide)], by rw [r .x1 (by decide)], by rw [r .x1 (by decide)], by rw [r .x3 (by decide)],
    by rw [r .x5 (by decide)], by rw [r .x7 (by decide)], by rw [a 1 (by decide)], r .x0 (by decide),
    r .x2 (by decide), r .x4 (by decide), r .x6 (by decide), a 0 (by decide), a 2 (by decide), a 4 (by decide),
    a 6 (by decide), hn.symm, he.symm, ?_⟩
  rw [w₁, w₂, a 8 (by decide), a 9 (by decide)]

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_check_key` on AArch64: verified against the shared contract

`ckA` states the shared contract on the registers and the stack
(`ck_implies`); with correctness (`ckCode_correct`) and constant time
(`ckCode_constantTime`), `CheckKey.code` is verified (`ck_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.CheckKey

/-- A state meeting `ckA.pre`: a 512-bit modulus, one-byte values, and the
stack arguments at `0x6000`. -/
def ckSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 64 | .x2 => 0x2100 | .x3 => 1 | .x4 => 0x2200 | .x5 => 1 | .x6 => 0x2300
    | .x7 => 1 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6048 then 0x20
    else if a = 0x6001 then 0x24 else if a = 0x6008 then 1 else if a = 0x6011 then 0x25
    else if a = 0x6018 then 1 else if a = 0x6021 then 0x26 else if a = 0x6028 then 1
    else if a = 0x6031 then 0x27 else if a = 0x6038 then 1 else if a = 0x6041 then 0x80
    else if a = 0x6049 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x2300, 1⟩, ⟨0x2400, 1⟩, ⟨0x2500, 1⟩, ⟨0x2600, 1⟩,
    ⟨0x2700, 1⟩, ⟨0x6000, 80⟩]
  wr := [⟨0x8000, 8448⟩]

theorem stackArgs_ten' (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

theorem ck_implies : ckA.Implies (Spec.Rsa.checkKeyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq] at h
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, ckKeyOf, stackArgs_ten',
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    rw [List.map_append, List.map_append] at hl
    obtain ⟨hn, he⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, r1])
    refine ⟨?_, hsp, by rw [stackArgs_ten', stackArgs_ten', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten',
      List.append_eq] [ckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ckSatState

/-- `vg_rsa_check_key`. -/
theorem ck_verified : Verified target VG.Impl.Rsa.AArch64.CheckKey.code (Spec.Rsa.checkKeyContract abi) :=
  Verified.of_correct ckCode_correct ckCode_constantTime ck_implies

end VG.Proof.Rsa.AArch64
