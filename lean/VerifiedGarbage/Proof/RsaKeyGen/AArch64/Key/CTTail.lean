import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTLcm
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTOut

/-!
# An RSA key from its primes on AArch64: constant time, `keyPart`

`qInv`, `dP`, `dQ`, `n` and the final mask, from the front's facts and a
mask in `kOk` (`TF`), which each keeps (`qinvPart_ct`, `crtPart_ct`,
`nPart_ct`, `finalMask_ct`); then the stores and the exit (`keyPart_ct`).
Each is a chain checked by the taint analysis, with the facts between its
parts from their correctness, and the facts after it from the correctness
of the whole (`qinvPart_k`, `crtPart_k`, `nPart_k`, `finalMask_k`).

`finalMask` reloads `w` and the stride twice in its middle: its three
parts are checked one after the other, with `KS` between them from the
correctness of the first (`finTopT_k`) and of the second (`finOddT_k`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- Before and after each piece of `keyPart`: the front's facts and a mask
in `kOk`. -/
abbrev TF : KIn → State → Prop := fun I t => PF I t ∧ KokM I t

/-! ## Shared pieces -/

theorem gcdIsOneT_eq : gcdIsOne = constA 1 ++ (eqMask aV aC ++
    ([.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]] : List (Prog isa))) := by
  simp only [gcdIsOne, List.append_assoc]

/-- `gcdIsOne`, with no postcondition. -/
theorem gcdIsOneT_ct0 {F : KIn → State → Prop} : RelCT isa (Two (KG F)) (seqs gcdIsOne) fun _ _ => True := by
  rw [gcdIsOneT_eq]
  refine rs_app (R := Two (KG NF)) (by simp [constA]) (by simp [eqMask, eqA])
    ((constA_ct 1 (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide)).mono
      (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) ?_
  exact (two_taint [.x0] (pins_kg NF) (by taint_decide) :
    RelCT isa _ (.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]) fun _ _ => True)

theorem divisorOfT_eq (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    ([.block (ws ++ (base aM .x16 ++ ([ld .x3 .x16, movi .x4 1, .logic .and .x .x4 .x15 .x4,
      .logic .orr .x .x3 .x3 .x4, st .x3 .x16] : List Instr)))] : List (Prog isa)))) := by
  simp only [divisorOf, List.append_assoc]

/-- `divisorOf j` (the taint checks of the code that depends on `j` as
parameters). -/
theorem divisorOfT_ct {j : Nat} (hj : j < 16) (hjM : j ≠ aM) (hjC : j ≠ aC)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base aM .x17)) copyWords)
      hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x9 0, mov .x14 .x12] : List Instr))
      (.seq (.block (base j .x16 ++ base aC .x17)) (.seq (countLoop .x14 xorBody) (.block zeroMask)))) hc₂).isSome =
      true) :
    RelCT isa (Two (KG NF)) (seqs (divisorOf j)) (Two (KG NF)) := by
  refine kg_ct ?_ fun I _ s h _ _ => WP.mono (divisorOf_k h hj hjM hjC) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩
  rw [divisorOfT_eq]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aM, copyA aM j]) _ from
    RelCT.seq (zeroA_ct (by decide) (stab_nf _ _) (by taint_decide)) (copyA_ct (by decide) hj hjM.symm
      (stab_nf _ _) ht₁)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (by decide) (stab_nf _ _) (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := NF) hj (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) ht₂) ?_
  exact (kg_wsb0 (by taint_decide) : RelCT isa _ (.block (ws ++ (base aM .x16 ++ ([ld .x3 .x16, movi .x4 1,
    .logic .and .x .x4 .x15 .x4, .logic .orr .x .x3 .x3 .x4, st .x3 .x16] : List Instr)))) fun _ _ => True)

/-! ## `qInv` -/

/-- `KokM` and word `W` of `u` zero, across a piece that keeps memory. -/
theorem kt_mem {I : KIn} {s t : State} (hm : t.mem = s.mem) (h : KokM I s ∧ TopZ aU I s) :
    KokM I t ∧ TopZ aU I t := by
  obtain ⟨⟨c, hc⟩, ht⟩ := h
  refine ⟨⟨c, ?_⟩, ?_⟩
  · dsimp only [word] at hc ⊢; rw [hm]; exact hc
  · dsimp only [TopZ, atop, word] at ht ⊢; rw [hm]; exact ht

/-- `qinvPart`'s mask block. -/
abbrev qBlkT : List Instr :=
  ([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++ ([.logic .orr .x .x15 .x15 .x10] : List Instr))

theorem qinvBlk_eq : ([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++ ([.logic .orr .x .x15 .x15 .x10] :
    List Instr)) = ([mov .x10 .x15] : List Instr) ++ (ws ++ (base aPa .x16 ++ (([ld .x3 .x16, movi .x4 1,
      .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr) ++
      ([.logic .orr .x .x15 .x15 .x10] : List Instr)))) := by
  simp only [evenMaskOf, List.append_assoc]

/-- The mask block: memory kept, a mask in `x15`. -/
theorem qinvBlkT_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {c : Bool} (h15 : s.gpr .x15 = mask c) :
    WP isa (.block qBlkT) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧ X15M I t := by
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x10]
    (Q := fun t => t.gpr .x10 = mask c ∧ t.mem = s.mem) (by brun [h15]) (by decide) (by decide)
      (by decide +kernel)) fun s₄ ⟨⟨h10₄, m₄⟩, k₄⟩ => WP.block_append_iff.mpr ?_)
  have h₄ := h.regs m₄ k₄
  refine WP.mono (evenMaskOf_k h₄ (j := aPa) (by decide)) fun s₅ ⟨h₅, m₅, h15₅, _, _, k₅⟩ => ?_
  have h10₅ : s₅.gpr .x10 = mask c := by rw [k₅.gpr .x10 (by decide), h10₄]
  refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = mask (decide (av I s₄.mem aPa % 2 = 0) || c) ∧
    t.mem = s₅.mem) (by brun [h15₅, h10₅, qinv_mask_or]) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨h15₆, m₆⟩, k₆⟩ => ⟨h₅.regs m₆ k₆, by rw [m₆, m₅, m₄], _, h15₆⟩

/-- The mask block, keeping `KokM` and word `W` of `u` zero. -/
theorem qinvBlkT_ct : RelCT isa (Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) (.block qBlkT)
    (Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) := by
  refine kg_ct ?_ fun I _ s h _ ⟨hf, _, h15⟩ => WP.mono (qinvBlkT_k h h15) fun t ⟨ht, hm, hx⟩ =>
    ⟨ht, kt_mem hm hf, hx⟩
  show RelCT isa _ (.block (([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++
    ([.logic .orr .x .x15 .x15 .x10] : List Instr)))) _
  rw [qinvBlk_eq]
  exact kg_blk_ws0 (G := NF) (by taint_decide) (fun I _ s h _ _ => WP.mono (WP.keep [.x10] (Q := fun t => t.mem = s.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun _ ⟨hm, k⟩ => ⟨h.regs hm k, trivial⟩)
    (by taint_decide)

/-- `qinvPart`, with no postcondition, from a mask in `kOk`. -/
theorem qinvPartT_ct0 : RelCT isa (Two (KG KokM)) (seqs qinvPart) fun _ _ => True := by
  have sK : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .hdr kOk ∉ cs → Stab KokM cs rs :=
    fun _ rs hok hn => stab_kok rs hok hn
  have sT : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .arr aU ∉ cs → Stab (TopZ aU) cs rs :=
    fun _ rs hok hn => stab_top rs (by decide) hok hn
  rw [qinvPart_eq]
  -- `[aU] := q`, word `W` zero.
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aU, copyA aU aQa]) _ from
    zc_ct (by decide) (by decide) (by decide) (sK _ _ (by decide) (by decide)) (by taint_decide)
      (by taint_decide)) ?_
  -- `x15 := ` the mask of `p < 3`.
  refine rs_app (by simp [constA]) (by simp [ltA, cmpA]) (constA_ct 3 (by decide)
    (stab_and (sK _ _ (by decide) (by decide)) (sT _ _ (by decide) (by decide))) (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) (by simp [ltA, cmpA]) (by simp)
    (ltA_ct (by decide) (by decide) (fun _ _ _ _ hf hm _ h15 => ⟨kt_mem hm hf, _, h15⟩) (by taint_decide)) ?_
  -- The mask of `p` even or below 3; `[aM] := p`.
  refine rs_app (R := Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t)) (by simp) (by simp [selC]) ?_ ?_
  · have sX : ∀ (rs : List Reg), .x15 ∉ rs →
        Stab (fun I t => (KokM I t ∧ TopZ aU I t) ∧ X15M I t) [.arr aM] rs := fun _ h =>
      stab_and (stab_and (sK _ _ (by decide) (by decide)) (sT _ _ (by decide) (by decide))) (stab_x15 h)
    exact RelCT.seq qinvBlkT_ct (RelCT.seq (zeroA_ct (by decide) (sX _ (by decide)) (by taint_decide))
      (copyA_ct (by decide) (by decide) (by decide) (sX _ (by decide)) (by taint_decide)))
  -- `[aM] := M`.
  refine rs_app (by simp [selC]) (by simp [invFrom]) (selC_ct (F := fun I t => KokM I t ∧ TopZ aU I t)
    (by decide) (by decide) (stab_and (sK _ _ (by decide) (by decide)) (sT _ _ (by decide) (by decide)))
    (by taint_decide)) ?_
  -- The inverse, and its mask.
  refine rs_app (R := Two (KG fun I t => (KokM I t ∧ TopZ aU I t) ∧ AvEq aV aM I t ∧ AvIs aX₁ 1 I t ∧
    AvIs aX₂ 0 I t)) (by simp [invFrom]) (by simp [gcdIsOne, constA])
    (show RelCT isa _ (seqs (([zeroA aV] : List (Prog isa)) ++ ([copyA aV aM, zeroA aX₁, .block (setOneA aX₁),
      zeroA aX₂] : List (Prog isa)))) _ from
    rs_app (by simp) (by simp) (zeroA_ct (by decide)
      (stab_and (sK [.arr aV] _ (by decide) (by decide)) (sT [.arr aV] _ (by decide) (by decide)))
      (by taint_decide))
      (invStart_ct (o := aV) (a := aM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (stab_and (sK [.arr aV, .arr aX₁, .arr aX₂] _ (by decide) (by decide))
          (sT [.arr aV, .arr aX₁, .arr aX₂] _ (by decide) (by decide))) (by taint_decide))) ?_
  refine rs_app (R := Two (KG KokM)) (by simp) (by simp [gcdIsOne, constA])
    (show RelCT isa _ (seqs [inverse aU aV aX₁ aX₂ aM aT]) _ from
    (inverse_ct (F := KokM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sK _ _ (by decide) (by decide))
    (by taint_decide)).mono (fun _ _ h => two_kg (fun _ _ ⟨⟨hk, tU⟩, he, h1, h2⟩ => ⟨hk, tU, he, h1, h2⟩) h)
    fun _ _ h => h) gcdIsOneT_ct0

/-- `qinvPart` keeps `TF`. -/
theorem qinvPart_ct : RelCT isa (Two (KG TF)) (seqs qinvPart) (Two (KG TF)) :=
  kg_ct (qinvPartT_ct0.mono (fun _ _ h => two_kg (fun _ _ h => h.2) h) fun _ _ h => h)
    fun I _ s h _ ⟨hf, _, hok⟩ => WP.mono (qinvPart_k h hf.1 hf.2.1 hok) fun _ ⟨ht, f, ok, _⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, _, ok⟩

/-! ## `dP`, `dQ` and `n` -/

theorem crtPartT_eq : crtPart = divisorOf aPm ++ (([zeroA aU, copyA aU aDd, divmod aU aV aM aT, zeroA aX₁,
    copyA aX₁ aV] : List (Prog isa)) ++ (divisorOf aQm ++ ([zeroA aU, copyA aU aDd, divmod aU aV aM aT] :
      List (Prog isa)))) := by
  simp only [crtPart, List.append_assoc]

/-- `crtPart`, with no postcondition. -/
theorem crtPartT_ct0 : RelCT isa (Two (KG NF)) (seqs crtPart) fun _ _ => True := by
  have tail : RelCT isa (Two (KG NF)) (seqs [zeroA aU, copyA aU aDd, divmod aU aV aM aT]) (Two (KG NF)) :=
    RelCT.seq (zeroA_ct (by decide) (stab_nf _ _) (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (stab_nf _ _) (by taint_decide))
        (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide)))
  rw [crtPartT_eq]
  refine rs_app (by simp [divisorOf]) (by simp) (divisorOfT_ct (j := aPm) (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [divisorOf]) (show RelCT isa _ (seqs (([zeroA aU, copyA aU aDd,
    divmod aU aV aM aT] : List (Prog isa)) ++ ([zeroA aX₁, copyA aX₁ aV] : List (Prog isa)))) _ from
      rs_app (by simp) (by simp) tail (RelCT.seq (zeroA_ct (by decide) (stab_nf _ _) (by taint_decide))
        (copyA_ct (by decide) (by decide) (by decide) (stab_nf _ _) (by taint_decide)))) ?_
  exact RelCT.drop (rs_app (by simp [divisorOf]) (by simp) (divisorOfT_ct (j := aQm) (by decide) (by decide)
    (by decide) (by taint_decide) (by taint_decide)) tail)

/-- `crtPart` keeps `TF`. -/
theorem crtPart_ct : RelCT isa (Two (KG TF)) (seqs crtPart) (Two (KG TF)) :=
  kg_ct (crtPartT_ct0.mono (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h)
    fun I _ s h _ ⟨hf, c, hok⟩ => WP.mono (crtPart_k h rfl rfl rfl) fun _ ⟨ht, f, _⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, c,
        (f.word (by decide) (by decide) (by decide)).trans hok⟩

/-- `nPart` keeps `TF`. -/
theorem nPart_ct : RelCT isa (Two (KG TF)) (seqs nPart) (Two (KG TF)) :=
  kg_ct (mulTo_ct0 (by decide) (by taint_decide) (by taint_decide)) fun I _ s h L ⟨hf, c, hok⟩ =>
    WP.mono (nPart_k h L.W hf.1 hf.2.1 L.P_lt L.Q_lt) fun _ ⟨ht, f, _⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, c,
        (f.word (by decide) (by decide) (by decide)).trans hok⟩

/-! ## The final mask -/

theorem finalMask_eq3 : finalMask = (ws ++ (base aQt .x16 ++ finTop)) ++ ((ws ++ (base aPa .x16 ++
    (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ finAnd)))) ++ (ws ++ (base aQa .x16 ++
    (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ (finAnd ++ (finE1 ++ (finE2 ++ ((carryMask ++ finAnd) ++
    (finE3 ++ (borrowMask ++ finSt))))))))))) := by
  rw [finalMask_eq]; simp only [oddMaskOf, List.append_assoc, List.cons_append, List.nil_append]

/-- `finalMask`'s first part: memory kept, registers of `mmRegs` changed. -/
theorem finTopT_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aQt .x16 ++ finTop))) s (KS I s₀) := by
  have hnw := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have sN := h.ws.sl (j := aQt) (by decide)
  have h256 := h.ws.h256
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aQt) fun s₁ ⟨⟨h16, h12, _, m₁⟩, k₁⟩ => ?_
  have hs₁ := h.ws.scr.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans h.ws.x0
  refine WP.mono (WP.keep [.x3, .x7, .x10, .x16] (Q := fun t => t.mem = s.mem) (by
    brun [finTop, h16, h12, h0₁, m₁, top_addr I.B (d := slot I.W aQt) (w := I.W) hw1 (by omega),
      hs₁.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega), hdr_enc (show kOk < 32 by decide),
      hs₁.ld (d := 8 * kOk) (by unfold kOk sFn; omega)])
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨hm, k⟩ => h.regs hm (k₁.trans k)

/-- `finalMask`'s second part: memory kept, registers of `mmRegs` changed. -/
theorem finOddT_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aPa .x16 ++ (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ finAnd)))))
      s (KS I s₀) := by
  have e : ws ++ (base aPa .x16 ++ (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ finAnd))) =
      oddMaskOf aPa ++ finAnd := by
    simp only [oddMaskOf, List.append_assoc]
  rw [e]
  refine WP.block_append_iff.mpr (WP.mono (oddMaskOf_k h (j := aPa) (by decide)) fun s₃ ⟨h₃, _⟩ => ?_)
  exact WP.mono (WP.keep [.x10] (Q := fun t => t.mem = s₃.mem) (by brun [finAnd]) (by decide) (by decide)
    (by decide +kernel)) fun _ ⟨hm, k⟩ => h₃.regs hm k

/-- `finalMask` keeps `TF`. -/
theorem finalMask_ct : RelCT isa (Two (KG TF)) (.block finalMask) (Two (KG TF)) := by
  refine kg_ct ?_ fun I _ s h L ⟨hf, _, hok⟩ =>
    WP.mono (finalMask_k h rfl hf.1 hf.2.1 L.E_lt hf.2.2.2.2.1 hok) fun _ ⟨ht, f, ok⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, _, ok⟩
  rw [finalMask_eq3]
  exact RelCT.block_append (RelCT.seq
    (kg_ct (G := NF) (kg_wsb0 (by taint_decide)) fun I _ s h _ _ => WP.mono (finTopT_k h) fun _ ht => ⟨ht, trivial⟩)
    (RelCT.block_append (RelCT.seq
      (kg_ct (G := NF) (kg_wsb0 (by taint_decide)) fun I _ s h _ _ => WP.mono (finOddT_k h) fun _ ht =>
        ⟨ht, trivial⟩)
      (kg_wsb0 (by taint_decide)))))

/-! ## `keyPart` -/

theorem keyPart_ct : RelCT isa (Two (KG TF)) keyPart fun _ _ => True := by
  rw [keyPart]
  simp only [List.append_assoc]
  refine rs_app (by simp [qinvPart]) (by simp [crtPart, divisorOf]) qinvPart_ct ?_
  refine rs_app (by simp [crtPart, divisorOf]) (by simp [nPart]) crtPart_ct ?_
  refine rs_app (by simp [nPart, mulTo]) (by simp) nPart_ct ?_
  refine rs_app (by simp) (by simp [outputs, storeA]) finalMask_ct ?_
  exact outputs_ct.mono (fun _ _ ⟨p, ⟨I₁, _, e₁, _, k₁, L₁, O₁, _, m₁⟩, ⟨I₂, _, e₂, _, k₂, L₂, O₂, _, m₂⟩, hsp⟩ =>
    ⟨p, ⟨I₁, e₁, k₁.ws, k₁.args, k₁.wr, L₁, O₁, m₁⟩, ⟨I₂, e₂, k₂.ws, k₂.args, k₂.wr, L₂, O₂, m₂⟩, hsp⟩)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.AArch64.Key
