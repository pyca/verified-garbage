import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTD
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain

/-!
# An RSA key from its primes on x86-64: constant time, the tail

`smallMask`; then `qInv`, `dP`, `dQ`, `n` and the final mask (keeping a mask
in `kOk`, which `storeA` needs), the stores and the exit; or the zeros and
the exit. The stores and the zeros write the outputs, among them `p` and
`q`, so from there on the runs are related by what the header and the
working space say (`EG`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-! ## `smallMask` -/

abbrev smallBlk : List Instr :=
  base aC .rbx ++ ([.mov .rax (.reg .r12), .shift .shr .rax 1, .mov32 .rdx (.imm 1), .store (ix .rbx .rax) .rdx] :
    List Instr)

theorem smallBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) :
    WP isa (.block (ws ++ smallBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem := by
  have hW := L.W
  have hn := h.ws.scr.nowrap
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h.ws.rdi) h9)
    fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  have h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aC + 8 * (I.pl / 8)))
      (1 : BitVec 64)) (by
    have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 (I.pl / 8) := by
      rw [ofNat_shr1 (by omega)]; congr 1; omega
    xrun [State.ea, ix, h12₂, ew, addr0 hbx rfl, hs₂.st (d := slot I.W aC + 8 * (I.pl / 8)) (by omega), mu₂, mu₁]
    rfl) rfl) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem I.B (1 : BitVec 64) (d := slot I.W aC + 8 * (I.pl / 8)) (by omega)
  rw [← hm] at o
  have f := KF.arr1 (I := I) (j := aC) o (by omega) (by omega)
  exact ⟨h.step f (all_mut_arr (by decide)) ((ku₁.trans ku₂).trans k) (by decide), f⟩

theorem smallMask_eq : smallMask = constA 1 ++ ([.block (ws ++ smallBlk)] ++ (ltA aDd aC ++
    [.block [.alu .and .rbp (.mem (hdr kOk)), .alu .test .rbp (.reg .rbp)]])) := by
  simp only [smallMask, smallBlk, List.append_assoc]

theorem smallMask_ct : RelCT isa (Two (KG NF)) (seqs smallMask) (Two (KG NF)) := by
  rw [smallMask_eq]
  refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (stab_nf _ _) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [ltA]) (show RelCT isa _ (seqs [.block (ws ++ smallBlk)]) _ from
    kg_wsb (by taint_decide) fun I _ s h L _ => WP.mono (smallBlk_k h L) fun t ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) ?_
  exact kg_rdi (by taint_decide) fun I _ s h _ _ => by
    have hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s.mem) (by xrun [State.ea, hdr, h.ws.rdi, hdrOff, hld])
      rfl) fun t ⟨hm, k⟩ => ⟨h.same hm k (by decide), trivial⟩

/-! ## The final mask -/

/-- `finalMask`'s first part, after `ws`: the masks of `n`'s top bit and `kOk`. -/
abbrev fm1 : List Instr :=
  base aQt .rbx ++ ([.mov .rax (.mem (ix .rbx .r12 (-8))), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .alu .and .rdx (.mem (hdr kOk)), .mov .rcx (.reg .rdx)] : List Instr)

/-- `finalMask`'s second part: and `p` odd. -/
abbrev fm2 : List Instr := oddMask aPa ++ ([.alu .and .rcx (.reg .rax)] : List Instr)

/-- `finalMask`'s last part: and `q` odd and `e` valid, into `kOk`. -/
abbrev fm3 : List Instr := oddMask aQa ++ ([.alu .and .rcx (.reg .rax),
    .mov .rax (.mem (hdr kEv)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .alu .and .rcx (.reg .rdx),
    .mov .rax (.mem (hdr kEv)), .alu .cmp .rax (.imm 3), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rdx),
    .mov .rax (.mem (hdr kEv)), .shift .shr .rax 33, .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .and .rcx (.reg .rdx), .store (hdr kOk) .rcx] : List Instr)

theorem finalMask_eq3 : finalMask = (ws ++ fm1) ++ (fm2 ++ fm3) := by
  simp only [finalMask, fm1, fm2, fm3, oddMask, List.append_assoc, List.cons_append, List.nil_append]

/-- A mask in `rcx`. -/
abbrev RcxM : KIn → State → Prop := fun _ t => ∃ c, t.gpr .rcx = mask c

theorem fm1_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hk : KokM I s) :
    WP isa (.block (ws ++ fm1)) s fun t => t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx] s t ∧
      RcxM I t := by
  obtain ⟨ok, hok⟩ := hk
  have hnw := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have sN := h.ws.sl (j := aQt) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aQt (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  have h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
  have hmu₂ : u₂.mem = s.mem := by rw [mu₂, mu₁]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t => t.gpr .rcx = mask
      (decide ((s.mem.readW (off I.B (slot I.W aQt + 8 * (I.W - 1))) 64).toNat / 2 ^ 63 = 1) && ok) ∧
    t.mem = s.mem) (by
      have hok₂ : word u₂.mem I.B (8 * kOk) = mask ok := by rw [hmu₂, hok]
      xrun [State.ea, ix, hdr, hdrOff, h12₂, addr_last hbx hw1, hs₂.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega),
        ((ku₁.trans ku₂).gpr (by decide)).trans h.ws.rdi, hs₂.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega),
        shr63_mask, hok₂, mask_and', hmu₂]
      have hok' : s.mem.readW (off I.B (8 * kOk)) 64 = mask ok := hok
      rw [hok', mask_and']) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by simp), _, hcx⟩

theorem fm2_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hc : RcxM I s) :
    WP isa (.block fm2) s fun t => t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx] s t ∧ RcxM I t := by
  obtain ⟨c, hcx⟩ := hc
  refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aPa) (by decide)) fun u₄ ⟨mu₄, hax₄, _, _, ku₄⟩ => ?_)
  have hcx₄ : u₄.gpr .rcx = mask c := by rw [ku₄.gpr (by decide), hcx]
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = mask (c && decide (av I s.mem aPa % 2 = 1)) ∧
    t.mem = u₄.mem) (by xrun [hax₄, hcx₄, mask_and']) rfl) fun t ⟨⟨hcx₅, mu₅⟩, ku₅⟩ =>
      ⟨by rw [mu₅, mu₄], (ku₄.trans ku₅).mono (by simp), _, hcx₅⟩

theorem fm3_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hc : RcxM I s) :
    WP isa (.block fm3) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧ KokM I t ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx] s t := by
  obtain ⟨c, hcx⟩ := hc
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aQa) (by decide)) fun u₆ ⟨mu₆, hax₆, _, _, ku₆⟩ => ?_)
  have hcx₆ : u₆.gpr .rcx = mask c := by rw [ku₆.gpr (by decide), hcx]
  have hs₆ := h.ws.scr.congr ku₆.2.2
  have hdi₆ : u₆.gpr .rdi = I.B := (ku₆.gpr (by decide)).trans h.ws.rdi
  generalize he : (word s.mem I.B (8 * kEv)).toNat = e
  have he64 : e < 2 ^ 64 := by rw [← he]; exact BitVec.isLt _
  have hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [← he, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hev₆ : u₆.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [mu₆]; exact hev
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk))
    (mask (c && decide (av I s.mem aQa % 2 = 1) && Spec.Rsa.exponentValid e))) (by
      xrun [State.ea, hdr, hdi₆, hdrOff, hs₆.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega),
        hs₆.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega), hev₆, hax₆, hcx₆, mask_and', mask_low,
        sxM1, maskNot, mu₆]
      have hev' : s.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := hev
      have hT : ((BitVec.ofNat 64 e) >>> 33).toNat = e / 2 ^ 33 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
      have hsub : ∀ c : Bool, 0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = mask c := fun _ => rfl
      rw [hev', BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, hT, hsub, hsub, maskNot, mask_and', mask_and',
        show BitVec.toNat (3 : BitVec 64) = 3 from rfl, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
      have e1 : (decide (e % 2 = 1) && !decide (e < 3) && decide (e / 2 ^ 33 < 1)) = Spec.Rsa.exponentValid e := by
        unfold Spec.Rsa.exponentValid
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
        omega
      refine congrArg (fun v => s.mem.writeW (off I.B (8 * kOk)) (mask v)) ?_
      rw [← e1]
      simp only [Bool.and_assoc]) rfl) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, ft, okt⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega) mt (ku₆.trans kt) (by decide)
  exact ⟨ht, ft, ⟨_, okt⟩, (ku₆.trans kt).mono (by simp)⟩

theorem finalMask_ct {F : KIn → State → Prop} (hF : Stab F [.hdr kOk] allR) :
    RelCT isa (Two (KG fun I t => F I t ∧ KokM I t)) (.block finalMask) (Two (KG fun I t => F I t ∧ KokM I t)) := by
  rw [finalMask_eq3]
  refine RelCT.block_append (RelCT.seq (kg_wsb (G := fun I t => F I t ∧ RcxM I t) (by taint_decide)
    fun I _ s h _ ⟨hf, hk⟩ => WP.mono (fm1_k h hk) fun t ⟨hm, k, hc⟩ =>
      ⟨h.same hm k (by decide), hF I s t h.hZ hf (kf_eq hm) (k.mono (by decide)), hc⟩) ?_)
  refine RelCT.block_append (RelCT.seq (R := Two (KG fun I t => F I t ∧ RcxM I t)) ?_ ?_)
  · have e : fm2 = ws ++ (base aPa .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1),
        .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .and .rcx (.reg .rax)] :
        List Instr)) := by
      simp only [fm2, oddMask, List.append_assoc, List.cons_append, List.nil_append]
    rw [e]
    exact kg_wsb (G := fun I t => F I t ∧ RcxM I t) (by taint_decide) fun I _ s h _ ⟨hf, hc⟩ => by
      rw [← e]
      exact WP.mono (fm2_k h hc) fun t ⟨hm, k, hc'⟩ =>
        ⟨h.same hm k (by decide), hF I s t h.hZ hf (kf_eq hm) (k.mono (by decide)), hc'⟩
  · have e : fm3 = ws ++ (base aQa .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1),
        .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .and .rcx (.reg .rax),
        .mov .rax (.mem (hdr kEv)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
        .alu .and .rcx (.reg .rdx),
        .mov .rax (.mem (hdr kEv)), .alu .cmp .rax (.imm 3), .alu .sbb .rdx (.reg .rdx),
        .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rdx),
        .mov .rax (.mem (hdr kEv)), .shift .shr .rax 33, .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx),
        .alu .and .rcx (.reg .rdx), .store (hdr kOk) .rcx] : List Instr)) := by
      simp only [fm3, oddMask, List.append_assoc, List.cons_append, List.nil_append]
    rw [e]
    exact kg_wsb (by taint_decide) fun I _ s h _ ⟨hf, hc⟩ => by
      rw [← e]
      exact WP.mono (fm3_k h hc) fun t ⟨ht, f, hk, k⟩ => ⟨ht, hF I s t h.hZ hf f (k.mono (by decide)), hk⟩

/-! ## `qInv` -/

/-- `qinvPart`'s mask of `p` odd and at least 3, after `ws`. -/
abbrev qBlk : List Instr :=
  base aPa .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)] : List Instr)

theorem qBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool} (hcx : s.gpr .rcx = mask c) :
    WP isa (.block (ws ++ qBlk)) s fun t => t.mem = s.mem ∧ RbpM I t ∧ Keep [.r12, .r9, .rbx, .rax, .rdx, .rbp] s t := by
  have e : ws ++ qBlk = oddMask aPa ++ [.alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)] := by
    simp only [qBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aPa) (by decide)) fun s₁ ⟨m₁, hax, _, _, k₁⟩ => ?_)
  have hcx₁ : s₁.gpr .rcx = mask c := (k₁.gpr (by decide)).trans hcx
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.mem = s₁.mem ∧ ∃ c', t.gpr .rbp = mask c') (by
      xrun [hax, hcx₁, mask_and']
      exact ⟨_, rfl⟩) rfl) fun t ⟨⟨hm, hbp⟩, k₂⟩ => ⟨by rw [hm, m₁], hbp, (k₁.trans k₂).mono (by simp)⟩

/-- `gcdIsOne`, keeping a mask in `kOk`. -/
theorem gcdIsOneK_ct {F : KIn → State → Prop} (hF : Stab F [.arr aC, .hdr kOk] allR) :
    RelCT isa (Two (KG fun I t => F I t ∧ KokM I t)) (seqs gcdIsOne) (Two (KG fun I t => F I t ∧ KokM I t)) := by
  unfold gcdIsOne
  simp only [List.append_assoc]
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 1 (stab_and (hF.mono (by simp) (by simp))
    (stab_kok _ (by decide) (by decide))).sub (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := fun I t => (F I t ∧ KokM I t) ∧ RbpM I t)
    (by decide) (by decide) (fun I s t hZ hf hm k hbp => ⟨(stab_and (hF.mono (cs' := []) (by simp) (by simp))
      (stab_kok (cs := []) _ (by decide) (by decide)) : Stab _ [] allR) I s t hZ hf (kf_eq hm) (k.mono (by decide)),
      _, hbp⟩) (by taint_decide)) ?_
  exact kg_rdi (by taint_decide) fun I _ s h _ ⟨⟨hf, c, hok⟩, c', hbp⟩ => by
    have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    have hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk)) (mask (c' && c))) (by
      xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst, hld, hbp, hok, mask_and']) rfl) fun t ⟨hm, k⟩ => ?_
    obtain ⟨ht, f, hw⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k (by decide)
    exact ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)), _, hw⟩

theorem qinvPart_eq2 : qinvPart = [zeroA aU, copyA aU aQa] ++ (constA 3 ++ (ltA aPa aC ++
    ([.block ([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] ++ (ws ++ qBlk))] ++
    ([zeroA aM, copyA aM aPa] ++ (selC aM ++ ((invFrom aM ++ [inverse aU aV aX₁ aX₂ aM aT]) ++ gcdIsOne)))))) := by
  simp only [qinvPart, qBlk, oddMask, gcdIsOne, List.append_assoc, List.cons_append, List.nil_append]

/-- `qinvPart`, keeping a mask in `kOk`. -/
theorem qinvPart_ct : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs qinvPart)
    (Two (KG fun I t => NF I t ∧ KokM I t)) := by
  have sK : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs →
      Stab (fun I t => NF I t ∧ KokM I t) cs allR := fun cs h1 h2 => stab_and (stab_nf _ _) (stab_kok _ h1 h2)
  have sKT : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs → .arr aU ∉ cs →
      Stab (fun I t => (NF I t ∧ KokM I t) ∧ TopZ aU I t) cs allR :=
    fun cs h1 h2 h3 => stab_and (sK cs h1 h2) (stab_top _ (by decide) h1 h3)
  rw [qinvPart_eq2]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aU, copyA aU aQa]) _ from
    zc_ct (by decide) (by decide) (by decide) (sK _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [constA]) (by simp [ltA]) (constA_ct 3 (sKT [.arr aC] (by decide) (by decide)
    (by decide)).sub (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := fun I t => ((NF I t ∧ KokM I t) ∧ TopZ aU I t) ∧ RbpM I t)
    (by decide) (by decide) (fun I s t hZ hf hm k hbp => ⟨sKT [] (by decide) (by decide) (by decide) I s t hZ hf
      (kf_eq hm) (k.mono (by simp)), _, hbp⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [.block ([.mov .rcx (.reg .rbp),
    .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] ++ (ws ++ qBlk))]) _ from RelCT.block_append (RelCT.seq
      (kg_regs (G := fun I t => ((NF I t ∧ KokM I t) ∧ TopZ aU I t) ∧ RcxM I t) (rs := [.rcx]) (by decide)
        (by taint_decide) fun I s hZ ⟨hf, c, hbp⟩ => WP.mono (WP.keep [.rcx] (Q := fun t =>
          t.gpr .rcx = mask (!c) ∧ t.mem = s.mem) (by xrun [hbp, sxM1, maskNot]) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ =>
            ⟨hm, k, sKT [] (by decide) (by decide) (by decide) I s t hZ hf (kf_eq hm) (k.mono (by simp)), _, hcx⟩)
      (kg_wsb (G := fun I t => ((NF I t ∧ KokM I t) ∧ TopZ aU I t) ∧ RbpM I t) (by taint_decide)
        fun I _ s h _ ⟨hf, c, hcx⟩ => WP.mono (qBlk_k h hcx) fun t ⟨hm, hbp, k⟩ =>
          ⟨h.same hm k (by decide), sKT [] (by decide) (by decide) (by decide) I s t h.hZ hf (kf_eq hm)
            (k.mono (by decide)), hbp⟩))) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [zeroA aM, copyA aM aPa]) _ from
    RelCT.seq (zeroA_ct (by decide) (stab_and (sKT [.arr aM] (by decide) (by decide) (by decide)).sub
      (stab_rbp (by decide))) (by taint_decide))
      (copyA_ct (by decide) (by decide) (by decide) (stab_and (sKT [.arr aM] (by decide) (by decide)
        (by decide)).sub (stab_rbp (by decide))) (by taint_decide))) ?_
  refine rs_app (by simp [selC]) (by simp [invFrom]) (selC_ct (by decide) (by decide)
    (sKT [.arr aM] (by decide) (by decide) (by decide)).sub (by taint_decide)) ?_
  refine rs_app (by simp [invFrom]) (by simp [gcdIsOne, constA]) (invFrom_ct (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (sK _ (by decide) (by decide)) (by taint_decide)
    (by taint_decide)) ?_
  exact gcdIsOneK_ct (stab_nf _ _)

/-! ## `dP`, `dQ` and `n` -/

/-- `divisorOf`'s `[aM] := [j]`, or 1 for `[j] = 0`, after `ws`. -/
abbrev dvBlk : List Instr :=
  base aM .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rbp (.imm 1), .alu .or .rax (.reg .rbp),
    .store (at0 .rbx) .rax] : List Instr)

theorem dvBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.block (ws ++ dvBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aM] s.mem t.mem ∧
      Keep [.r12, .r9, .rbx, .rax, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  have sM := h.ws.sl (j := aM) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aM (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
  have hmu : u₂.mem = s.mem := by rw [mu₂, mu₁]
  have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
    ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (slot I.W aM)) v) (by
      xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := slot I.W aM) (by omega), hs₂.st (d := slot I.W aM) (by omega), hmu]
      exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => ?_
  have kk := (ku₁.trans ku₂).trans k
  obtain ⟨ht, f⟩ := h.arrSome (by decide) hm kk (by decide)
  exact ⟨ht, f, kk.mono (by simp)⟩

theorem divisorOf_eq2 (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    [.block (ws ++ dvBlk)])) := by
  simp only [divisorOf, dvBlk, List.append_assoc]

/-- `divisorOf j`, for facts its changes keep. -/
theorem divisorOf_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjM : j ≠ aM)
    (hF : Stab F [.arr aM, .arr aC] allR) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aM .rbx))
      Impl.Rsa.X86_64.copyWords) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rbx ++ (base aC .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (divisorOf j)) (Two (KG F)) := by
  rw [divisorOf_eq2]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aM, copyA aM j]) _ from
    RelCT.seq (zeroA_ct (by decide) (hF.mono (by simp) (by simp)).sub (by taint_decide))
      (copyA_ct (by decide) hj hjM.symm (hF.mono (by simp) (by simp)).sub ht₁)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (hF.mono (by simp) (by simp)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := F) hj (by decide)
    (fun I s t hZ hf hm k _ => hF I s t hZ hf (kf_eq hm) (k.mono (by decide))) ht₂) ?_
  exact kg_wsb (by taint_decide) fun I _ s h _ hf => WP.mono (dvBlk_k h) fun t ⟨ht, f, k⟩ =>
    ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide))⟩

theorem crtPart_eq2 : crtPart = divisorOf aPm ++ ([zeroA aU, copyA aU aDd, divmod aU aV aM aT, zeroA aX₁,
    copyA aX₁ aV] ++ (divisorOf aQm ++ [zeroA aU, copyA aU aDd, divmod aU aV aM aT])) := by
  simp only [crtPart, List.append_assoc]

/-- `crtPart`, keeping a mask in `kOk`. -/
theorem crtPart_ct : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs crtPart)
    (Two (KG fun I t => NF I t ∧ KokM I t)) := by
  have sK : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs →
      Stab (fun I t => NF I t ∧ KokM I t) cs allR := fun cs h1 h2 => stab_and (stab_nf _ _) (stab_kok _ h1 h2)
  have tail : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs [zeroA aU, copyA aU aDd, divmod aU aV aM aT])
      (Two (KG fun I t => NF I t ∧ KokM I t)) :=
    RelCT.seq (zeroA_ct (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide))
        (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (sK [.arr aU, .arr aV, .arr aT] (by decide) (by decide)).sub (by taint_decide)))
  rw [crtPart_eq2]
  refine rs_app (by simp [divisorOf]) (by simp) (divisorOf_ct (by decide) (by decide) (sK _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [divisorOf]) (show RelCT isa _ (seqs ([zeroA aU, copyA aU aDd, divmod aU aV aM aT] ++
    [zeroA aX₁, copyA aX₁ aV])) _ from rs_app (by simp) (by simp) tail
      (RelCT.seq (zeroA_ct (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide))
        (copyA_ct (by decide) (by decide) (by decide) (sK _ (by decide) (by decide)).sub (by taint_decide)))) ?_
  exact rs_app (by simp [divisorOf]) (by simp) (divisorOf_ct (by decide) (by decide) (sK _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) tail

theorem nPart_eq : seqs nPart = .seq (zeroA aQt) (.seq (.block (ws ++ mulBlk aPa aQa aQt))
    Impl.Rsa.X86_64.Crt.mulRows) := by
  simp only [nPart, seqs, mulBlk, List.append_assoc]

theorem nPart_ct : RelCT isa (Two (KG fun I t => NF I t ∧ KokM I t)) (seqs nPart)
    (Two (KG fun I t => NF I t ∧ KokM I t)) := by
  rw [nPart_eq]
  exact mul_ct (by decide) (by decide) (by decide) (by decide) (by decide)
    (stab_and (stab_nf _ _) (stab_kok _ (by decide) (by decide))) (by taint_decide) (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64.Key
