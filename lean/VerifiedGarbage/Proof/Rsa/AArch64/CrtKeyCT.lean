import VerifiedGarbage.Proof.Rsa.AArch64.CkCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCode

/-!
# `vg_rsa_check_crt_key` on AArch64: constant time, `main`

`vg_rsa_check_key`'s pieces (`CkCT.lean`, `CkCTMain.lean`), with the
shortened remainder (`reduceTop_ckct`): each block of `reduceTop` reads `w`
and its count `c` from the header, and pins the registers the code after it
uses (`blkHi_ok`, `blkLo_ok`, `blkCnt_ok`) to the public data, for a count
that is a function of it (`1` or `⌈q_len / 8⌉`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sP sPlen sQ sQlen sQI aX aR aM aA aRem aT aOne aE ltA mulE mulXR)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ hiTail loTail cntTail reduceTop topE topQ modOne modChecks)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The registers `blkHi`'s copy uses, from the public data. -/
def hiVal (C : CkP → Nat) (p : CkP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wW p.k) aA + 8 * C p)
  | .x17 => off p.B (slot (wW p.k) aRem)
  | .x12 => BitVec.ofNat 64 (wW p.k - C p)
  | _ => 0

/-- The registers `blkLo`'s copy uses. -/
def loVal (C : CkP → Nat) (p : CkP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wW p.k) aA)
  | .x17 => off p.B (slot (wW p.k) aQ + 8 * (wW p.k - C p))
  | .x12 => BitVec.ofNat 64 (C p)
  | _ => 0

/-- The registers the loop uses. -/
def cntVal (C : CkP → Nat) (p : CkP) : Reg → BitVec 64
  | .x0 => p.B
  | .x12 => BitVec.ofNat 64 (wW p.k)
  | .x11 => BitVec.ofNat 64 (8 * (wW p.k + 2))
  | .x6 => BitVec.ofNat 64 (64 * C p)
  | _ => 0

/-- `reduceTop top` leaks the same in two runs with the same public data,
for a count `C p` of words that `top` sets. -/
theorem reduceTop_ckct {top : List Instr} (C : CkP → Nat)
    (hT : ∀ p s, GK p s → TopOk top p.B p.Z s.mem (C p)) (hC : ∀ p s, GK p s → 1 ≤ C p ∧ C p < wW p.k)
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
  have lay : ∀ {p : CkP} {s : State}, GK p s → slot (wW p.k) 16 ≤ p.Z ∧ 1 ≤ wW p.k ∧ wW p.k < 2 ^ 24 ∧
      p.B.toNat + p.Z ≤ 2 ^ 64 := fun h => ⟨h.ws.hZ, by have := h.ws.w1; omega, h.ws.w2, h.ws.scr.nowrap⟩
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
        have sA := Nat.le_trans (slot_lt (w := wW p.k) (show aA < 16 by decide)) hZ
        have sR := Nat.le_trans (slot_lt (w := wW p.k) (show aRem < 16 by decide)) hZ
        have pAR := slot_sep (w := wW p.k) (show aA ≠ aRem by decide)
        refine WP.seq (WP.mono (blkHi_ok h.ws (hT p s h) hc) fun t ⟨⟨e16, e17, e12, m⟩, k⟩ => ?_)
        have hs := h.ws.scr.congr k.wr
        refine WP.mono (copyWords_ok e16 e17 e12 (by omega) (by omega) (by omega)
          (fun i hi => hs.ld (by omega)) (fun i hi => hs.st (by omega))
          (fun i hi b hb => by rw [ofs_off p.B (by omega)]; omega)) fun u ⟨_, _, o, _, _, k'⟩ => ?_
        rw [m] at o
        exact h.arr (show aRem < 16 by decide) (Nat.le_refl _) (o.mono (by omega) (by omega)) (k.trans k')
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
        have sA := Nat.le_trans (slot_lt (w := wW p.k) (show aA < 16 by decide)) hZ
        have sQ := Nat.le_trans (slot_lt (w := wW p.k) (show aQ < 16 by decide)) hZ
        have pAQ := slot_sep (w := wW p.k) (show aA ≠ aQ by decide)
        refine WP.seq (WP.mono (blkLo_ok h.ws (hT p s h) hc) fun t ⟨⟨e16, e17, e12, m⟩, k⟩ => ?_)
        have hs := h.ws.scr.congr k.wr
        refine WP.mono (copyWords_ok e16 e17 e12 hc1 (by omega) (by omega)
          (fun i hi => hs.ld (by omega)) (fun i hi => hs.st (by omega))
          (fun i hi b hb => by rw [ofs_off p.B (by omega)]; omega)) fun u ⟨_, _, o, _, _, k'⟩ => ?_
        rw [m] at o
        exact h.arr (show aQ < 16 by decide) (Nat.le_refl _) (o.mono (by omega) (by omega)) (k.trans k')
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
    (hT : ∀ p s, GK p s → TopOk top p.B p.Z s.mem (C p)) (hC : ∀ p s, GK p s → 1 ≤ C p ∧ C p < wW p.k)
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

/-- The checks modulo `X - 1`. -/
theorem ckModC_ct {sX sXlen sDX : Nat} (hsX : sX < 32) (hsL : sXlen < 32) (hsD : sDX < 32) (pX pDX : CkP → Addr)
    (xl : CkP → Nat)
    (hX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sX) = pX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.k)
    (hDX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sDX) = pDX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pDX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aM .x8 ++ [ldh .x1 sX, ldh .x2 sXlen]))
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htDX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aX .x8 ++ [ldh .x1 sDX, ldh .x2 sXlen]))
      hc₂).isSome = true) :
    RelCT isa (Two GK) (seqs (modChecks sX sXlen sDX)) (Two GK) := by
  rw [ckcModChecks_eq]
  have ldX := toGK (ofGK (ld_ct (j := aM) (by decide) hsX hsL pX xl (by decide) hX (by taint_decide) htX (by taint_decide)))
  have ldDX := ofGK (ld_ct (j := aX) (by decide) hsD hsL pDX xl (by decide) hDX (by taint_decide) htDX (by taint_decide))
  have mE := mulE_ckct (by taint_decide) (by taint_decide)
  exact ct_app (by simp [loadA]) (by simp) ldX (ct_app (a := [.block (decA aM)]) (by simp) (by simp [loadA])
    (ct_one (decA_ckct (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [ltA]) ldDX
    (ct_app (by simp [ltA]) (by simp [mulE]) (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide)
      (by decide) (by decide) (by taint_decide))
    (ct_app (by simp [mulE]) (by simp [modOne]) mE
      (modOneTop_ckct (fun _ => 1) (fun p _ _ => topE_ok _ _ _)
        (fun p _ _ => ⟨Nat.le_refl _, by simp only [wW, wk]; omega⟩) (by taint_decide) (by taint_decide) (by taint_decide))))))

/-- `qInv < p` and `q qInv ≡ 1 (mod p)`. -/
theorem ckQIC_ct : RelCT isa (Two GK) (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++
    (loadA aR sQ sQlen ++ (mulXR ++ modOne topQ)))))) (Two GK) :=
  ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pP CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))))
  (ofGK (ct_app (by simp [loadA]) (by simp [ltA]) (ld_ct (by decide) (by decide) (by decide) CkP.pQi CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.qi, hs.args.pl, ⟨_, hs.qi, L.qibl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
  (ct_app (by simp [ltA]) (by simp [loadA]) (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide) (by decide)
    (by decide) (by taint_decide))
  (ct_app (by simp [loadA]) (by simp [mulXR]) (toGKb (ld_ct (by decide) (by decide) (by decide) CkP.pQ CkP.ql
    (js := [aX]) (by decide) (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, Nat.le_of_lt L.ql2⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) (js' := [aX, aR]) (by decide))
  (ct_app (by simp [mulXR]) (by simp [modOne]) (mulXR_ckct (by taint_decide) (by taint_decide))
    (modOneTop_ckct (fun p => (p.ql + 7) / 8) (fun p s h => by
        obtain ⟨I, m₀, c, rfl, hs, L, -⟩ := h
        exact topQ_ok hs.args.ql (by simp only [CkIn.pub]; have := L.ql2; have := L.k2; omega)
          (by simp only [CkIn.pub]; have := hs.ws.h256; omega))
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, -, L, -⟩ := h
        have := L.ql1; have := L.ql2
        exact ⟨by simp only [CkIn.pub]; omega, by simp only [CkIn.pub, wW, wk]; omega⟩) (by taint_decide) (by taint_decide) (by taint_decide)))))))

/-! ## `main` -/

/-- `main` leaks the same in two runs with the same public data. -/
theorem ckcMain_ct : RelCT isa (Two GKM) VG.Impl.Rsa.AArch64.CheckCrtKey.main fun _ _ => True := by
  rw [ckcMain_eq]
  refine (ct_app (by simp) (by simp [loadA]) (ct_one ckHead_ct)
    (ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pN CkP.k
      (by decide) (fun I m₀ s hs L => ⟨hs.args.n, hs.args.k, ⟨_, hs.n, L.nl⟩, show 1 ≤ I.k by have := L.k1; omega, Nat.le_refl _⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pE CkP.el
      (by decide) (fun I m₀ s hs L => ⟨hs.args.e, hs.args.el, ⟨_, hs.e, L.ebl⟩, L.el1, L.el2⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp) (by simp [loadA]) (ct_cons (by simp) (zeroA_ckct (by decide) (by taint_decide))
      (ct_one (setOneA_ckct (by decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp [modChecks]) ckPQ_ct
    (ct_app (by simp [modChecks]) (by simp [modChecks]) (ckModC_ct (by decide) (by decide) (by decide) CkP.pP CkP.pDp
      CkP.pl (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
      (fun I m₀ s hs L => ⟨hs.args.dp, hs.args.pl, ⟨_, hs.dp, L.dpbl⟩, L.pl1, Nat.le_of_lt L.pl2⟩)
      (by taint_decide) (by taint_decide))
    (ct_app (by simp [modChecks]) (by simp [loadA]) (ckModC_ct (by decide) (by decide) (by decide) CkP.pQ CkP.pDq
      CkP.ql (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, Nat.le_of_lt L.ql2⟩)
      (fun I m₀ s hs L => ⟨hs.args.dq, hs.args.ql, ⟨_, hs.dq, L.dqbl⟩, L.ql1, Nat.le_of_lt L.ql2⟩)
      (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp) ckQIC_ct (ct_one retMaskK_ct))))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.AArch64
