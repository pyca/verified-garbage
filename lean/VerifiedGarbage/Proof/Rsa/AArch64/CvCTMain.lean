module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rsa.AArch64.WDivCT
public import VerifiedGarbage.Proof.Rsa.AArch64.WDiv
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
meta import VerifiedGarbage.Proof.Rsa.AArch64.WDivCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.WDiv
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_crt_values` on AArch64: constant time, `main`

The pieces of `CvCT.lean` in sequence (`loads_ct`, `pqCheck_ct`,
`invPart_ct`, `divisor_ct`), the stores (`stores_ct`, from `GS`), and
`main` (`cvMain_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN)

/-! ## Sequences -/

theorem ct_cons {α : Type} {Φ Ψ Ξ : α → State → Prop} {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (he : RelCT isa (Two Φ) e (Two Ψ)) (hr : RelCT isa (Two Ψ) (seqs l) (Two Ξ)) :
    RelCT isa (Two Φ) (seqs (e :: l)) (Two Ξ) := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact RelCT.seq he hr

theorem ct_one {α : Type} {Φ Ψ : α → State → Prop} {e : Prog isa} (he : RelCT isa (Two Φ) e (Two Ψ)) :
    RelCT isa (Two Φ) (seqs [e]) (Two Ψ) := he

theorem ct_app {α : Type} {Φ Ψ Ξ : α → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (hA : RelCT isa (Two Φ) (seqs a) (Two Ψ)) (hB : RelCT isa (Two Ψ) (seqs b) (Two Ξ)) :
    RelCT isa (Two Φ) (seqs (a ++ b)) (Two Ξ) :=
  RelCT.seqs_append ha hb (RelCT.seq hA hB)

/-! ## The loads -/

/-- The four loads. -/
theorem loads_ct0 : RelCT isa (Two GA) (seqs (loadA aN Public.sN Public.sK ++
    (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl)))) (Two GA) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * wk k := fun {k} => by unfold wk; omega
  refine ct_app (by simp [loadA]) (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) CvP.pN CvP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA])
    (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) CvP.pP CvP.pl (fun p s h => ?_)
      (by taint_decide) (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp [loadA])
    (loadA_ct (by decide) (by decide) (by decide) CvP.pQ CvP.ql (fun p s h => ?_) (by taint_decide)
      (by taint_decide) (by taint_decide))
    (loadA_ct (by decide) (by decide) (by decide) CvP.pD CvP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide) (by taint_decide))))
  all_goals
    obtain ⟨I, m₀, c, rfl, h, L, -⟩ := h
    dsimp only [CvIn.pub]
    have := L.k1
  · exact ⟨h.args.n, h.args.k, ⟨_, h.n, L.nl⟩, by omega, k8⟩
  · exact ⟨h.args.p, h.args.pl, ⟨_, h.p, L.pbl⟩, L.pl1, by have := L.pl2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.q, h.args.ql, ⟨_, h.q, L.qbl⟩, L.ql1, by have := L.ql2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.d, h.args.dl, ⟨_, h.d, L.dbl⟩, L.dl1, by have := L.dl2; have := @k8 I.k; omega⟩

/-- The four loads, which leave `p` and `q` within their lengths. -/
theorem loads_ct : RelCT isa (Two GA) (seqs (loadA aN Public.sN Public.sK ++
    (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl)))) (Two GB) :=
  two_post (loads_ct0.mono (fun _ _ h => h) fun _ _ _ => trivial) fun _ _ h => by
    obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
    exact WP.mono (cvLoads_ok h' L) fun t ⟨ht, mt, _, vP, vQ, _⟩ => ⟨⟨I, m₀, c, rfl, ht, L, O, mt.trans hm⟩,
      by have := os2ip_lt I.pb; rw [L.pbl] at this; dsimp only [CvIn.pub]; rw [vP]; exact this,
      by have := os2ip_lt I.qb; rw [L.qbl] at this; dsimp only [CvIn.pub]; rw [vQ]; exact this⟩

/-! ## The arithmetic -/

/-- `GB` with the product's arrays zero. -/
def GZ (p : CvP) (s : State) : Prop :=
  GB p s ∧ ∀ i < 2 * (wk p.k + 2), word s.mem p.B (slot (wk p.k) aU + 8 * i) = 0

theorem pqZero_ct : RelCT isa (Two GB) (seqs [zeroA aU, zeroA aV]) (Two GZ) :=
  two_post ((ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide)) (ct_one (zeroA_ct (by decide)
    (by taint_decide)))).mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) fun _ _ _ => trivial)
    fun p s ⟨h, bP, bQ⟩ => by
      obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
      have hn := h'.ws.scr.nowrap
      have sV := h'.ws.sl (j := aV) (by decide)
      have h8U : 8 * 32 ≤ slot (wk I.k) aU := by
        have := hdr_lt_slot (wk I.k) aU (show 31 < 32 by decide); omega
      have eV : slot (wk I.k) aV = slot (wk I.k) aU + 8 * ((wk I.k) + 2) := by simp only [slot, aU, aV]; omega
      have pP := slot_sep (w := wk I.k) (show aU ≠ aP by decide)
      have pP' := slot_sep (w := wk I.k) (show aV ≠ aP by decide)
      have pQ := slot_sep (w := wk I.k) (show aU ≠ aQ by decide)
      have pQ' := slot_sep (w := wk I.k) (show aV ≠ aQ by decide)
      have sP := h'.ws.sl (j := aP) (by decide)
      have sQ := h'.ws.sl (j := aQ) (by decide)
      exact WP.mono (pqZero_ok h') fun t ⟨ht, hz, o⟩ => ⟨⟨⟨I, m₀, c, rfl, ht, L, O, by
          show word t.mem I.B (8 * Public.sMask) = _
          rw [o.word (Or.inl (by unfold Public.sMask sFn; omega)) (by unfold Public.sMask sFn; omega)]; exact hm⟩,
        by dsimp only [CvIn.pub] at bP ⊢; rw [o.wv (by omega) (by omega)]; exact bP,
        by dsimp only [CvIn.pub] at bQ ⊢; rw [o.wv (by omega) (by omega)]; exact bQ⟩, hz⟩

/-- The registers `mulRows` needs pinned. -/
def pqVal (p : CvP) : Reg → BitVec 64
  | .x0 => p.B
  | .x11 => off p.B (slot (wk p.k) aP)
  | .x9 => off p.B (slot (wk p.k) aQ)
  | .x8 => off p.B (slot (wk p.k) aU)
  | .x12 => BitVec.ofNat 64 ((p.ql + 7) / 8)
  | .x13 => BitVec.ofNat 64 ((p.pl + 7) / 8)
  | _ => 0

theorem pqProd_ct : RelCT isa (Two GZ) (seqs [.block (ws ++ base aP .x5 ++ base aQ .x9 ++ base aU .x8 ++
      [mov .x11 .x5, ldh .x12 sQl, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, ldh .x13 sPl, .addImm .x .x13 .x13 7,
        .lsr .x .x13 .x13 3, movi .x7 0]), VG.Impl.Rsa.AArch64.Crt.mulRows]) (Two GA) := by
  refine pin_ct [.x0] [.x0, .x11, .x9, .x8, .x12, .x13, .x7] pqVal
    (fun a s₁ s₂ h₁ h₂ => pins_GA a s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) (fun p s h => ?_) (by taint_decide)
    fun p s h => ?_
  all_goals
    obtain ⟨⟨⟨I, m₀, c, rfl, h', L, O, hm⟩, bP, bQ⟩, hz⟩ := id h
  · refine WP.mono (pqSetup_ok h' L) fun t ⟨⟨h11, h9, h8, h12, h13, h7, _⟩, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans h'.ws.x0
    all_goals assumption
  · have hn := h'.ws.scr.nowrap
    have h8U : 8 * 32 ≤ slot (wk I.k) aU := by
      have := hdr_lt_slot (wk I.k) aU (show 31 < 32 by decide); omega
    exact WP.mono (pqProd_ok h' L hz bP bQ) fun t ⟨ht, _, o⟩ => ⟨I, m₀, c, rfl, ht, L, O, by
      show word t.mem I.B (8 * Public.sMask) = _
      rw [o.word (Or.inl (by unfold Public.sMask sFn; omega)) (by unfold Public.sMask sFn; omega)]; exact hm⟩

theorem pqCmp_ct : RelCT isa (Two GA) (seqs (eqA aU aN ++ ([.block [.addImm .x .x14 .x12 4],
    countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16], .block andZero] : List (Prog isa)))) (Two GA) := by
  show RelCT isa (Two GA) (.seq (.block (ws ++ [movi .x9 0, mov .x14 .x12])) (seqs ([.block (base aU .x16 ++ base aN .x17),
    countLoop .x14 xorBody] ++ [.block [.addImm .x .x14 .x12 4],
    countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16], .block andZero]))) (Two GA)
  refine ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
  exact WP.mono (pqCmp_ok h' hm) fun t ⟨ht, mt, _⟩ => ⟨I, m₀, _, rfl, ht, L, O, mt⟩

theorem pqCheck_ct0 : RelCT isa (Two GB) (seqs pqCheck) (Two GA) := by
  rw [pqCheck_eq]
  exact ct_app (by simp) (by simp) pqZero_ct (ct_app (by simp) (by simp [eqA]) pqProd_ct pqCmp_ct)

/-- `p q = n`, which leaves `p` and `q`. -/
theorem pqCheck_ct : RelCT isa (Two GB) (seqs pqCheck) (Two GB) :=
  two_post (pqCheck_ct0.mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun _ _ ⟨h, bP, bQ⟩ => by
      obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
      exact WP.mono (cvCheck_ok h' L hm bP bQ) fun t ⟨ht, ⟨c', mt, _⟩, pt⟩ => ⟨⟨I, m₀, c', rfl, ht, L, O, mt⟩,
        by dsimp only [CvIn.pub] at bP ⊢; rw [pt aP (.inl rfl)]; exact bP,
        by dsimp only [CvIn.pub] at bQ ⊢; rw [pt aQ (.inr (.inl rfl))]; exact bQ⟩

theorem invSetup_ct : RelCT isa (Two GB) (seqs invSetup) (Two GI) := by
  refine two_post ((?_ : RelCT isa (Two GA) (seqs invSetup) (Two GA)).mono (fun _ _ h => two_mono
    (fun _ _ h => h.1) h) fun _ _ _ => trivial) fun p s ⟨h, bP, bQ⟩ => ?_
  · unfold invSetup
    exact ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
      (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
      (ct_cons (by simp) (setOneA_ct (by decide) (by taint_decide))
      (ct_one (zeroA_ct (by decide) (by taint_decide))))))))
  · obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
    exact WP.mono (invSetup_ok h' L) fun t ⟨ht, mt, _, vU, vm, _, _, pt⟩ =>
      ⟨⟨I, m₀, c, rfl, ht, L, O, mt.trans hm⟩, vm, by dsimp only [CvIn.pub] at bQ ⊢; rw [vU]; exact bQ,
        by dsimp only [CvIn.pub] at bP ⊢; rw [pt aP (.inl rfl)]; exact bP⟩

theorem invPart_ct [InvLaw] : RelCT isa (Two GB) (seqs invPart) (Two GA) := by
  unfold invPart
  exact ct_app (by simp [invSetup]) (by simp) invSetup_ct
    (ct_app (by simp) (by simp [eqA])
      (ct_cons (by simp) (inverseAt_ct (by taint_decide))
        (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
          (ct_one (setOneA_ct (by decide) (by taint_decide)))))
      (ct_app (by simp [eqA]) (by simp) (eqA_ct (by decide) (by decide) (by taint_decide)) (ct_one andZero_ct)))

theorem divisor_ct {j : Nat} (hj : j < 16) (hjC : aC ≠ j) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base aC .x17)) copyWords)
      hc₁).isSome = true) :
    RelCT isa (Two GA) (seqs (divisor j)) (Two GA) := by
  unfold divisor
  exact ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (copyA_ct (by decide) hj hjC ht)
    (ct_cons (by simp) (decA_ct (by decide) (by taint_decide))
    (ct_cons (by simp) (zeroA_ct (by decide) (by taint_decide))
    (ct_one (copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))))

/-! ## `d mod (j - 1)` -/

/-- `n`'s first byte, as `wordGuard` reads it. -/
def gbyte (p : CvP) : BitVec (8 * 1) := Mem.read (fun _ => p.nb[0]?.getD 0) 0 1

/-- The guard passes for `p`. -/
def GPass (p : CvP) : Prop := guardVal p.k p.pl p.ql (gbyte p) = 0

/-- After `wordGuard`: its value, pinned. -/
def GW (p : CvP) (s : State) : Prop := GA p s ∧ s.gpr .x9 = guardVal p.k p.pl p.ql (gbyte p)

/-- The registers `wordGuard` reads `n` through. -/
def gwVal (p : CvP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => p.pN
  | _ => 0

theorem guard_ct : RelCT isa (Two GA) (.block (wordGuard sPl sQl)) (Two GW) := by
  rw [wordGuard_eq]
  refine RelCT.block_append (pin_ct [.x0] [.x0, .x16] gwVal pins_GA (by taint_decide) (fun p s h => ?_)
    (by taint_decide) fun p s h => ?_)
  all_goals obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := id h
  · have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi =>
      h'.ws.scr.ld (by have := h'.ws.h256; omega)
    refine WP.mono (WP.keep [.x13, .x14, .x15, .x16] (Q := fun t => t.gpr .x16 = I.pN) (by
      brun [h'.ws.x0, hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hdr_enc (show sPl < 32 by decide), hdr_enc (show sQl < 32 by decide), hl Public.sN (by decide),
        hl Public.sK (by decide), hl sPl (by decide), hl sQl (by decide), h'.args.n]) (by decide) (by decide)
      (by decide +kernel)) fun t ⟨h16, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans h'.ws.x0
    · exact h16
  · have hn0 : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega
    have hb : s.mem.read I.pN 1 = gbyte I.pub := by
      refine read1_eq ?_
      have := h'.n.val 0 hn0
      rw [show I.pN + BitVec.ofNat 64 0 = I.pN by simp] at this
      rw [this]
      dsimp only [CvIn.pub]
      rw [List.getElem?_eq_getElem hn0]; rfl
    refine WP.seq_iff.mpr (WP.block_append_iff.mp ?_)
    rw [← wordGuard_eq sPl sQl]
    exact WP.mono (wordGuard_ok h'.ws.scr h'.ws.x0 h'.ws.h256 (by decide) (by decide) h'.args.k h'.args.pl h'.args.ql
      h'.args.n hb (by simpa using h'.n.rd 0 hn0)) fun t ⟨⟨h9, mt⟩, kt⟩ =>
        ⟨h.same mt kt (by decide), h9⟩

theorem wordChoice_ct {j : Nat} (hj : j = aP ∨ j = aQ) : RelCT isa (Two GA) (wordChoice j) (Two GA) := by
  have hj16 : j < 16 := by rcases hj with rfl | rfl <;> decide
  have hjC : aC ≠ j := by rcases hj with rfl | rfl <;> decide
  have hdiv : RelCT isa (Two GA) (seqs (divisor j)) (Two GA) := by
    rcases hj with rfl | rfl
    · exact divisor_ct (by decide) (by decide) (by taint_decide)
    · exact divisor_ct (by decide) (by decide) (by taint_decide)
  unfold wordChoice
  refine RelCT.seq guard_ct (two_ite (fun p s₁ s₂ h₁ h₂ => by
    obtain ⟨-, e₁⟩ := h₁
    obtain ⟨-, e₂⟩ := h₂
    rw [eval_zero, eval_zero, e₁, e₂]) ?_ ?_)
  · -- The guard passes: `wdiv`.
    have hd' : RelCT isa (Two fun p s => GW p s ∧ isa.eval (.zero .x .x9) s = some true) (seqs (divisor j))
        (Two fun p s => GA p s ∧ GPass p) :=
      two_post (hdiv.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ _ => trivial) fun p s ⟨⟨h, h9⟩, he⟩ => by
        obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := id h
        have hg : GPass I.pub := by
          rw [eval_zero, h9] at he; simpa [GPass] using he
        exact WP.mono (cvDivisor_ok h' L hj) fun t ⟨ht, mt, _, _, _⟩ => ⟨⟨I, m₀, c, rfl, ht, L, O, mt.trans hm⟩, hg⟩
    refine ct_app (by simp [divisor]) (by simp) hd' (ct_one (wdiv_ct CvP.B CvP.Z (fun p => wk p.k)
      (fun _ _ h => h.1.ws) (by taint_decide) fun p s ⟨h, hg⟩ => ?_))
    obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := id h
    have hk1 := L.k1
    have hk2 := L.k2
    have pl2 := L.pl2
    have ql2 := L.ql2
    obtain ⟨g16, -, -, -⟩ := guard_zero (k := I.k) (pl := I.pl) (ql := I.ql) (by omega) (by omega) (by omega) hg
    exact WP.mono (wdiv_ok h'.ws (iX := aD) (iM := aC) (iR := aV) (iT := aT) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cvWm_ok (wk I.k) (by unfold wk; omega)) (cvLen_ok (wk I.k))
      (cvXb_ok I.B (wk I.k) (by unfold wk; omega) (by unfold wk; omega)) (by unfold wk; omega) (by omega) (by omega)
      (by omega)) fun t ⟨_, ft, kt, _⟩ => h.frm ft (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨aV, by decide, .inl rfl⟩
        · exact ⟨aT, by decide, .inl rfl⟩) kt (by decide)
  · -- `divmod`.
    exact (ct_app (by simp [divisor]) (by simp) hdiv (ct_one (divmod_ct (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)
      (by taint_decide)))).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h

/-! ## The stores -/

/-- Between the stores: the working space, the header, the mask, and the
outputs, but not memory outside the working space. -/
def GS (p : CvP) (s : State) : Prop :=
  ∃ (I : CvIn) (c : Bool), I.pub = p ∧ Ws s I.B I.Z (wk I.k) ∧
    CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD ∧ s.wr = I.W ∧ CvLens I ∧
    CvOuts I ∧ mword s.mem I.B = mask c

theorem GS.ws {p : CvP} {s : State} (h : GS p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, c, rfl, h, -⟩ := h
  exact h

theorem GA.gs {p : CvP} {s : State} (h : GA p s) : GS p s := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  exact ⟨I, c, rfl, h.ws, h.args, h.wr, L, O, hm⟩

theorem pins_GS : Pins GS [.x0] := pins_ws CvP.B CvP.Z (fun p => wk p.k) fun _ _ h => h.ws

/-- The registers `storeBE` needs pinned: the base, the end of the output
and its length. -/
def soVal (B base ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => base
  | .x1 => ptr + BitVec.ofNat 64 len
  | .x9 => BitVec.ofNat 64 len
  | _ => 0

/-- The block before `storeBE`: the base of `[j]`, the pointer, the length
and the mask. -/
theorem storeBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 Public.sMask]))
      s fun t => ∀ r ∈ [Reg.x0, .x8, .x1, .x9], t.gpr r = soVal B (off B (slot w j)) ptr len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x9, .x15] (Q := fun t => t.gpr .x1 = ptr + BitVec.ofNat 64 len ∧
          t.gpr .x9 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, hdr_enc (show Public.sMask < 32 by decide), m₃, m₂, hl₃ sPtr hP,
            hl₃ sLen hL, hl₃ Public.sMask (by decide), hp, hl])
        rfl rfl rfl)
      fun t ⟨⟨h1, h9⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h9))

theorem storeA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr)
    (len : CvP → Nat)
    (hA : ∀ p s, GS p s → word s.mem p.B (8 * sPtr) = ptr p ∧ word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∀ i < len p, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < len p, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 sLen,
      .add .x .x1 .x1 .x9, ldh .x15 Public.sMask])) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x9]) storeBE hc₂).isSome = true) :
    RelCT isa (Two GS) (seqs (storeA j sPtr sLen Public.sMask)) (Two GS) :=
  pin_ct [.x0] [.x0, .x8, .x1, .x9] (fun p => soVal p.B (off p.B (slot (wk p.k) j)) (ptr p) (len p)) pins_GS ht₁
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact storeBlk_ok h.ws hP hL hp hl) ht₂ fun p s h => by
      obtain ⟨hp, hl, hwr, hsep, hl1, hlw⟩ := hA p s h
      obtain ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩ := h
      dsimp only [CvIn.pub] at hp hl hwr hsep hl1 hlw ⊢
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      refine WP.mono (storeA_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact hwr i hi) hsep)
        fun t ⟨_, _, ht, hf, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
      exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold argSlot at hi; omega), k.wr.trans hW, L, O,
        (fw _ (by decide)).trans hm⟩

theorem retMask_ct : RelCT isa (Two GS) (.block retMask) fun _ _ => True :=
  two_taint [.x0] pins_GS (by taint_decide)

/-- The stores and the exit. -/
theorem stores_ct : RelCT isa (Two GS) (seqs (storeA aX₂ sQi sPl Public.sMask ++
    (storeA aX₁ sDp sPl Public.sMask ++ (storeA aV sDq sQl Public.sMask ++
      ([.block retMask] : List (Prog isa)))))) (Two fun (_ : CvP) (_ : State) => True) := by
  have k8 : ∀ {k l : Nat}, l < k → l ≤ 8 * wk k := fun {k l} h => by unfold wk; omega
  refine (ct_app (by simp [storeA]) (by simp [storeA])
    (storeA_ct (by decide) (by decide) (by decide) CvP.pQi CvP.pl (fun p s h => ?_) (by taint_decide)
      (by taint_decide))
    (ct_app (by simp [storeA]) (by simp [storeA])
      (storeA_ct (by decide) (by decide) (by decide) CvP.pDp CvP.pl (fun p s h => ?_) (by taint_decide)
        (by taint_decide))
      (ct_app (by simp [storeA]) (by simp)
        (storeA_ct (by decide) (by decide) (by decide) CvP.pDq CvP.ql (fun p s h => ?_) (by taint_decide)
          (by taint_decide))
        (ct_one (Ψ := fun (_ : CvP) (_ : State) => True) (two_post retMask_ct fun _ _ h => by
          obtain ⟨I, c, rfl, hw, -, -, -, -, hm⟩ := h
          exact WP.mono (cvExit_ok hw hm) fun _ _ => trivial)))))
  all_goals
    obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    dsimp only [CvIn.pub]
  · exact ⟨ha.qi, ha.pl, O.qi, O.sqi, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dp, ha.pl, O.dp, O.sdp, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dq, ha.ql, O.dq, O.sdq, L.ql1, k8 L.ql2⟩

end VG.Proof.Rsa.AArch64
