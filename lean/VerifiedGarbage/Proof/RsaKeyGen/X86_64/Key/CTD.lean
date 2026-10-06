import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTLcm

/-!
# An RSA key from its primes on x86-64: constant time, `d`

`dPart` branches on `e`, which is public, and in each branch runs pieces of
the key routines: `loadEv`, `lGe2`, `gcdIsOne`, `inverse` from `invFrom`,
and `dOdd`'s blocks.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- A header store of some value into slot `i`. -/
theorem KS.hdrSome {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) {i : Nat} (hi : 29 ≤ i ∧ i < 32)
    (hm : ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (8 * i)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : KS I m₀ t ∧ KF I.B I.W [.hdr i] s.mem t.mem :=
  let ⟨_, hm⟩ := hm
  let ⟨ht, f, _⟩ := h.hdrW hi hm k hr
  ⟨ht, f⟩

/-- A store of some value into word 0 of array `j`. -/
theorem KS.arrSome {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16)
    (hm : ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (slot I.W j)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem := by
  obtain ⟨v, hm⟩ := hm
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have o := writeW_outside s.mem I.B v (d := slot I.W j) (by omega)
  rw [← hm] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  exact ⟨h.step f (all_mut_arr hj) k hr, f⟩

/-! ## `e` into `aE` -/

abbrev loadEvBlk : List Instr := base aE .rbx ++ ([.mov .rax (.mem (hdr kEv)), .store (at0 .rbx) .rax] : List Instr)

theorem loadEvBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.block (ws ++ loadEvBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aE] s.mem t.mem ∧
      Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sE := h.ws.sl (j := aE) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aE (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h.ws.scr.congr (k₂.trans k₃).2.2
  have hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans h.ws.rdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (slot I.W aE)) v) (by
    xrun [State.ea, at0, hdr, hbx, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega), hs₃.st (d := slot I.W aE) (by omega),
      m₃, m₂]
    exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k₄⟩ => ?_
  have kk := (k₂.trans k₃).trans k₄
  obtain ⟨ht, f⟩ := h.arrSome (by decide) hm kk (by decide)
  exact ⟨ht, f, kk.mono (by simp)⟩

theorem loadEv_ct {F : KIn → State → Prop} (hF : Stab F [.arr aE] allR) :
    RelCT isa (Two (KG F)) (seqs loadEv) (Two (KG F)) := by
  have e : seqs loadEv = .seq (zeroA aE) (.block (ws ++ loadEvBlk)) := by
    simp only [loadEv, seqs, loadEvBlk, List.append_assoc]
  rw [e]
  exact RelCT.seq (zeroA_ct (by decide) hF.sub (by taint_decide))
    (kg_wsb (by taint_decide) fun I _ s h _ hf => WP.mono (loadEvBlk_k h) fun t ⟨ht, f, k⟩ =>
      ⟨ht, hF I s t h.hZ hf f (k.mono (by decide))⟩)

/-! ## `kOk` -/

theorem lGe2_ct {F : KIn → State → Prop} (hF : Stab F [.arr aC, .hdr kOk] allR) :
    RelCT isa (Two (KG F)) (seqs lGe2) (Two (KG F)) := by
  unfold lGe2
  simp only [List.append_assoc]
  refine rs_app (by simp [constA]) (by simp [ltA]) (constA_ct 2 (hF.mono (by simp) (by simp)).sub (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := F) (by decide) (by decide)
    (fun I s t hZ hf hm k _ => hF I s t hZ hf (kf_eq hm) (k.mono (by decide))) (by taint_decide)) ?_
  exact kg_rdi (by taint_decide) fun I _ s h _ hf => by
    have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    refine WP.mono (WP.keep [.rbp] (Q := fun t => ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (8 * kOk)) v) (by
      xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst]
      exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => ?_
    obtain ⟨ht, f⟩ := h.hdrSome (by unfold kOk sFn; omega) hm k (by decide)
    exact ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide))⟩

theorem gcdIsOne_ct {F : KIn → State → Prop} (hF : Stab F [.arr aC, .hdr kOk] allR) :
    RelCT isa (Two (KG F)) (seqs gcdIsOne) (Two (KG F)) := by
  unfold gcdIsOne
  simp only [List.append_assoc]
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 1 (hF.mono (by simp) (by simp)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := F) (by decide) (by decide)
    (fun I s t hZ hf hm k _ => hF I s t hZ hf (kf_eq hm) (k.mono (by decide))) (by taint_decide)) ?_
  exact kg_rdi (by taint_decide) fun I _ s h _ hf => by
    have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    have hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    refine WP.mono (WP.keep [.rbp] (Q := fun t => ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (8 * kOk)) v) (by
      xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst, hld]
      exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => ?_
    obtain ⟨ht, f⟩ := h.hdrSome (by unfold kOk sFn; omega) hm k (by decide)
    exact ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide))⟩

/-! ## `inverse` from `invFrom` -/

/-- What `invFrom j` and `inverse … j aT` change. -/
abbrev csI : List Rc := [.arr aU, .arr aV, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo]

theorem invFrom_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjU : j ≠ aU) (hjV : j ≠ aV) (hj1 : j ≠ aX₁)
    (hj2 : j ≠ aX₂) (hjT : j ≠ aT) (hF : Stab F csI allR) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aV .rbx))
      Impl.Rsa.X86_64.copyWords) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep aU aV aX₁ aX₂ j aT) .ne)) hc₂).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ TopZ aU I t)) (seqs (invFrom j ++ [inverse aU aV aX₁ aX₂ j aT]))
      (Two (KG F)) := by
  have sFT : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csI) → cs.all Rc.ok = true → .arr aU ∉ cs →
      Stab (fun I t => F I t ∧ TopZ aU I t) cs allR :=
    fun cs h1 h2 h3 => stab_and (hF.mono h1 (by simp)) (stab_top _ (by decide) h2 h3)
  show RelCT isa _ (seqs ([zeroA aV] ++ ([copyA aV j, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂] ++
    [inverse aU aV aX₁ aX₂ j aT]))) _
  refine rs_app (by simp) (by simp) (zeroA_ct (by decide) (sFT [.arr aV] (by simp) (by decide) (by decide)).sub
    (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (invStart_ct (o := aV) (a := j) (by decide) hj hjV.symm (by decide) (by decide)
    hj1 hj2 (sFT [.arr aV, .arr aX₁, .arr aX₂] (by simp) (by decide) (by decide)) ht₁) ?_
  refine (inverse_ct (F := F) (by decide) (by decide) (by decide) (by decide) hj (by decide) (by decide)
    (by decide) (by decide) hjU.symm (by decide) (by decide) (by decide) hjV.symm (by decide) (by decide)
    hj1.symm (by decide) hj2.symm (by decide) hjT hF.sub ht₂).mono
    (fun s₁ s₂ h => two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p, h₁.imp fun I ⟨⟨hf, tU⟩, he, h1, h2⟩ =>
      ⟨hf, tU, he, h1, h2⟩, h₂.imp fun I ⟨⟨hf, tU⟩, he, h1, h2⟩ => ⟨hf, tU, he, h1, h2⟩⟩) h) fun _ _ h => h

/-! ## `e = 0` and `e = 1` -/

theorem dZero_ct : RelCT isa (Two (KG NF)) (.block dZero) (Two (KG NF)) :=
  kg_rdi (by taint_decide) fun I _ s h _ _ => by
    have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t => ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (8 * kOk)) v) (by
      unfold dZero
      xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst]
      exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => ⟨(h.hdrSome (by unfold kOk sFn; omega) hm k (by decide)).1, trivial⟩

theorem dOne_ct : RelCT isa (Two (KG NF)) (seqs dOne) (Two (KG NF)) := by
  unfold dOne
  simp only [List.append_assoc]
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 1 (stab_nf _ _) (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [.block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1))),
    .store (hdr kOk) .rbp]]) _ from kg_rdi (by taint_decide) fun I _ s h _ _ => by
      have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
      refine WP.mono (WP.keep [.rbp] (Q := fun t => ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (8 * kOk)) v) (by
        xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst]
        exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => ⟨(h.hdrSome (by unfold kOk sFn; omega) hm k (by decide)).1, trivial⟩) ?_
  exact one_ct (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide)

/-! ## `e` odd -/

/-- `e` odd. -/
abbrev OddE : KIn → State → Prop := fun I _ => I.E % 2 = 1

theorem stab_oddE (cs : List Rc) (rs : List Reg) : Stab OddE cs rs := fun _ _ _ _ h _ _ => h

theorem minvBlk_ok {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) (hev : EvOK I s)
    (ho : OddE I s) : WP isa (.block (([.mov .rbx (.mem (hdr kEv))] : List Instr) ++ minv)) s fun t =>
      t.mem = s.mem ∧ Keep [.rbx, .rax, .rcx, .rdx, .rsi, .r15] s t := by
  have he64 : I.E < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
  have hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 I.E ∧
    t.mem = s.mem) (by xrun [State.ea, hdr, h.ws.rdi, hdrOff, hld, hev]) rfl) fun s₁ ⟨⟨hbx, m₁⟩, k₁⟩ =>
      WP.mono (minvC_ok s₁ (by rw [hbx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]; exact ho))
        fun t ⟨_, _, k₂, m₂⟩ => ⟨by rw [m₂, m₁], (k₁.trans k₂).mono (by decide)⟩)

/-- `dOdd`'s computation of `c` into `r15` and `t` into `sMo`, after `ws`. -/
abbrev dBlk2 : List Instr :=
  base aX₂ .rbx ++ (base aR .r10 ++ ([.mov .rsi (.mem (hdr kEv)), .alu .sub .rsi (.mem (at0 .rbx)),
    .mov .rax (.mem (at0 .r10)), .mul .rsi, .alu .add .rax (.imm 1), .mul .rcx, .mov .r15 (.reg .rax),
    .store (hdr sMo) .rsi] : List Instr))

theorem dBlk2_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.block (ws ++ dBlk2)) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr sMo] s.mem t.mem ∧
      Keep [.r12, .r9, .rbx, .r10, .rsi, .rax, .rdx, .r15] s t := by
  have hn := h.ws.scr.nowrap
  have sX := h.ws.sl (j := aX₂) (by decide)
  have sR := h.ws.sl (j := aR) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aX₂ (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aR (r := .r10) (by decide) ((ku₂.gpr (by decide)).trans hdi₁)
    ((ku₂.gpr (by decide)).trans h9)) fun u₃ ⟨h10, mu₃, ku₃⟩ => ?_
  have hmu : u₃.mem = s.mem := by rw [mu₃, mu₂, mu₁]
  have hs₃ := h.ws.scr.congr ((ku₁.trans ku₂).trans ku₃).2.2
  have hdi₃ : u₃.gpr .rdi = I.B := ((ku₂.trans ku₃).gpr (by decide)).trans hdi₁
  have hbx₃ : u₃.gpr .rbx = off I.B (slot I.W aX₂) := (ku₃.gpr (by decide)).trans hbx
  refine WP.mono (WP.keep [.rsi, .rax, .rdx, .r15] (Q := fun t =>
    ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (8 * sMo)) v) (by
      xrun [State.ea, at0, hdr, hbx₃, h10, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₃.ld (d := slot I.W aX₂) (by omega), hs₃.ld (d := slot I.W aR) (by omega),
        hs₃.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega),
        hs₃.st (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega), hmu, execMul]
      exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => ?_
  have kk := ((ku₁.trans ku₂).trans ku₃).trans k
  obtain ⟨ht, f⟩ := h.hdrSome (by unfold sMo sFn; omega) hm kk (by decide)
  exact ⟨ht, f, kk.mono (by simp)⟩

/-- `dOdd`'s store of `c` into `[aDd]` and its base, `Q`'s, and `t`, after
`ws`. -/
abbrev dBlk3 : List Instr :=
  base aDd .r8 ++ (([.store (at0 .r8) .r15] : List Instr) ++ (base aQt .rax ++
    ([.mov .r9 (.reg .rax), .mov .rcx (.mem (hdr sMo))] : List Instr)))

theorem dBlk3_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hz : Zero aDd I s) :
    WP isa (.seq (.block (ws ++ dBlk3)) mulAddRow) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aDd] s.mem t.mem ∧
      Keep allR s t := by
  have hn := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have sD := h.ws.sl (j := aDd) (by decide)
  have sQ := h.ws.sl (j := aQt) (by decide)
  have spDQ := slot_far (w := I.W) (i := aDd) (j := aQt) (by decide)
  refine WP.seq (WP.mono (Q := fun (t : State) => t.mem = s.mem.writeW (off I.B (slot I.W aDd)) (s.gpr .r15) ∧
    t.gpr .r8 = off I.B (slot I.W aDd) ∧ t.gpr .r9 = off I.B (slot I.W aQt) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
    Keep [.r12, .r9, .r8, .rax, .rcx] s t) ?_ fun s₁ ⟨m₁, h8, h9, h12, k₁⟩ => ?_)
  · refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
    have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
    refine WP.mono (base_ok aDd (r := .r8) (by decide) hdi₁ h9) fun u₂ ⟨h8, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
    have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
    have h15 : u₂.gpr .r15 = s.gpr .r15 := (ku₁.trans ku₂).gpr (by decide)
    refine WP.mono (WP.keep [] (c := .block [.store (at0 .r8) .r15]) (Q := fun t => t.mem = s.mem.writeW
      (off I.B (slot I.W aDd)) (s.gpr .r15)) (by
        xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₂.st (d := slot I.W aDd) (by omega), h15, mu₂, mu₁]) rfl) fun u₃ ⟨mu₃, ku₃⟩ => WP.block_append_iff.mpr ?_
    have hdi₃ : u₃.gpr .rdi = I.B := ((ku₂.trans ku₃).gpr (by decide)).trans hdi₁
    have h9₃ : u₃.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) := ((ku₂.trans ku₃).gpr (by decide)).trans h9
    refine WP.mono (base_ok aQt (r := .rax) (by decide) hdi₃ h9₃) fun u₄ ⟨hax, mu₄, ku₄⟩ => ?_
    have hs₄ := h.ws.scr.congr (((ku₁.trans ku₂).trans ku₃).trans ku₄).2.2
    refine WP.mono (WP.keep [.r9, .rcx] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQt) ∧ t.mem = u₄.mem) (by
        xrun [State.ea, hdr, (ku₄.gpr (by decide)).trans hdi₃, hdrOff, hax,
          hs₄.ld (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega)]) rfl) fun t ⟨⟨h9t, mt⟩, kt⟩ =>
      ⟨by rw [mt, mu₄, mu₃], ((ku₄.trans kt).gpr (by decide)).trans ((ku₃.gpr (by decide)).trans h8), h9t,
        (((ku₂.trans ku₃).trans ku₄).trans kt).gpr (by decide) |>.trans h12,
        ((((ku₁.trans ku₂).trans ku₃).trans ku₄).trans kt).mono (by simp)⟩
  have o₁ := writeW_outside s.mem I.B (s.gpr .r15) (d := slot I.W aDd) (by omega)
  rw [← m₁] at o₁
  have f₁ := KF.arr1 (I := I) (j := aDd) o₁ (Nat.le_refl _) (by omega)
  have h₁ := h.step f₁ (all_mut_arr (by decide)) k₁ (by decide)
  have vD : wv s₁.mem I.B (slot I.W aDd) (I.W + 2) = (s.gpr .r15).toNat := by
    rw [m₁]
    have := wv_put (m := s.mem) (B := I.B) (d := slot I.W aDd) (N := I.W + 2) (k := 0) (s.gpr .r15)
      ((wv_eq_zero_iff _ _ _ _).mp hz) (by omega) (by omega) (I.W + 2) (Nat.le_refl _)
    rw [Nat.mul_zero, Nat.add_zero] at this
    rw [this, ite_eq_left (show 0 < I.W + 2 by omega), Nat.pow_zero, Nat.one_mul]
  have hbound : wv s₁.mem I.B (slot I.W aDd) (I.W + 2) + (s₁.gpr .rcx).toNat * wv s₁.mem I.B (slot I.W aQt) I.W <
      2 ^ (64 * (I.W + 2)) := by
    rw [vD]
    have hc := (s.gpr .r15).isLt
    have hx := (s₁.gpr .rcx).isLt
    have hQ := wv_lt s₁.mem I.B (slot I.W aQt) I.W
    have h1 : (s₁.gpr .rcx).toNat * wv s₁.mem I.B (slot I.W aQt) I.W < 2 ^ 64 * 2 ^ (64 * I.W) :=
      Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hQ) (by omega)
    have h2 : 2 ^ 64 + 2 ^ 64 * 2 ^ (64 * I.W) ≤ 2 ^ (64 * (I.W + 2)) := by
      rw [show 64 * (I.W + 2) = 64 + 64 + 64 * I.W by omega, Nat.pow_add, Nat.pow_add]
      have : 1 ≤ 2 ^ (64 * I.W) := Nat.one_le_two_pow
      have : 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * I.W) := Nat.le_mul_of_pos_right _ (by omega)
      have : 2 * (2 ^ 64 * 2 ^ (64 * I.W)) ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ (64 * I.W) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega
    omega
  refine WP.mono (mulAddRow_ok h₁.ws.scr h8 h9 h12 (by omega) (by omega) (by omega) (by omega) (by omega) hbound)
    fun t ⟨_, o, kt⟩ => ?_
  have ft := KF.arr1 (I := I) (j := aDd) o (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨h₁.step ft (all_mut_arr (by decide)) kt (by decide), (f₁.trans ft).mono (by simp),
    (k₁.trans kt).mono (by decide)⟩

theorem dOdd_eq2 : dOdd = loadEv ++ ([zeroA aQt, copyA aQt aL, divmod aQt aR aE aT] ++ ([zeroA aU, copyA aU aR] ++
    ((invFrom aE ++ [inverse aU aV aX₁ aX₂ aE aT]) ++ (lGe2 ++ (gcdIsOne ++
    ([.block (([.mov .rbx (.mem (hdr kEv))] : List Instr) ++ minv), .block (ws ++ dBlk2), zeroA aDd, .block (ws ++ dBlk3),
      mulAddRow] : List (Prog isa))))))) := by
  simp only [dOdd, dBlk2, dBlk3, List.append_assoc, List.cons_append, List.nil_append]

/-- `dOdd`, for an odd `e` in `kEv`. -/
theorem dOdd_ct : RelCT isa (Two (KG fun I t => EvOK I t ∧ OddE I t)) (seqs dOdd) (Two (KG NF)) := by
  have sF : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kEv ∉ cs →
      Stab (fun I t => EvOK I t ∧ OddE I t) cs allR := fun cs hok hn => stab_and (stab_ev _ hok hn) (stab_oddE _ _)
  rw [dOdd_eq2]
  refine rs_app (by simp [loadEv]) (by simp) (loadEv_ct (sF _ (by decide) (by decide))) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [zeroA aQt, copyA aQt aL, divmod aQt aR aE aT]) _ from
    RelCT.seq (zeroA_ct (by decide) (sF _ (by decide) (by decide)).sub (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (sF _ (by decide) (by decide)).sub (by taint_decide))
        (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (sF [.arr aQt, .arr aR, .arr aT] (by decide) (by decide)).sub
          (by taint_decide)))) ?_
  refine rs_app (by simp) (by simp [invFrom]) (show RelCT isa _ (seqs [zeroA aU, copyA aU aR]) _ from
    zc_ct (by decide) (by decide) (by decide) (sF _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [invFrom]) (by simp [lGe2]) (invFrom_ct (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (sF _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [lGe2, constA]) (by simp [gcdIsOne, constA]) (lGe2_ct (sF _ (by decide) (by decide))) ?_
  refine rs_app (by simp [gcdIsOne, constA]) (by simp) (gcdIsOne_ct (sF _ (by decide) (by decide))) ?_
  simp only [seqs]
  refine RelCT.seq (kg_rdi (G := NF) (by taint_decide) fun I _ s h L hf => WP.mono (minvBlk_ok h L hf.1 hf.2)
    fun t ⟨hm, k⟩ => ⟨h.same hm k (by decide), trivial⟩) ?_
  refine RelCT.seq (kg_wsb (G := NF) (by taint_decide) fun I _ s h _ _ => WP.mono (dBlk2_k h) fun t ⟨ht, _⟩ =>
    ⟨ht, trivial⟩) ?_
  refine RelCT.seq (kg_ws (G := Zero aDd) (by taint_decide) fun I _ s h _ _ => WP.mono (zeroA_k h (j := aDd)
    (by decide)) fun t ⟨ht, _, hz, _⟩ => ⟨ht, hz⟩) ?_
  exact kg_ws (by taint_decide) fun I _ s h _ hz => WP.mono (dBlk3_k h hz) fun t ⟨ht, _⟩ => ⟨ht, trivial⟩

/-! ## `e` even -/

/-- `dEven`'s `[aM] := L`, or 1 for `L = 0`, after `ws`. -/
abbrev mBlk : List Instr :=
  base aM .rbx ++ (base aC .r10 ++ ([.mov .rax (.mem (at0 .rbx)), .mov .rdx (.reg .r15), .alu .and .rdx (.imm 1),
    .alu .or .rax (.reg .rdx), .store (at0 .rbx) .rax] : List Instr))

theorem mBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.block (ws ++ mBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aM] s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have sM := h.ws.sl (j := aM) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aM (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .r10) (by decide) ((ku₂.gpr (by decide)).trans hdi₁)
    ((ku₂.gpr (by decide)).trans h9)) fun u₃ ⟨_, mu₃, ku₃⟩ => ?_
  have hmu : u₃.mem = s.mem := by rw [mu₃, mu₂, mu₁]
  have hs₃ := h.ws.scr.congr ((ku₁.trans ku₂).trans ku₃).2.2
  have hbx₃ : u₃.gpr .rbx = off I.B (slot I.W aM) := (ku₃.gpr (by decide)).trans hbx
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (slot I.W aM)) v) (by
      xrun [State.ea, at0, hbx₃, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₃.ld (d := slot I.W aM) (by omega), hs₃.st (d := slot I.W aM) (by omega), hmu]
      exact ⟨_, rfl⟩) rfl) fun t ⟨hm, k⟩ => h.arrSome (by decide) hm (((ku₁.trans ku₂).trans ku₃).trans k) (by decide)

/-- The second part of `dEven`'s mask of `L` odd and at least 3, after `ws`. -/
abbrev oBlk : List Instr :=
  base aL .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .and .rax (.reg .rcx), .store (hdr kOk) .rax,
    .mov .rbp (.reg .rax)] : List Instr)

theorem oBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool} (hcx : s.gpr .rcx = mask c) :
    WP isa (.block (ws ++ oBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧ RbpM I t ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .rbp] s t := by
  have e : ws ++ oBlk = oddMask aL ++ [.alu .and .rax (.reg .rcx), .store (hdr kOk) .rax, .mov .rbp (.reg .rax)] := by
    simp only [oBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aL) (by decide)) fun s₁ ⟨m₁, hax, _, _, k₁⟩ => ?_)
  have hst := (h.ws.scr.congr k₁.2.2).st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hcx₁ : s₁.gpr .rcx = mask c := (k₁.gpr (by decide)).trans hcx
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => (∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (8 * kOk)) v) ∧
    ∃ c', t.gpr .rbp = mask c') (by
      xrun [State.ea, hdr, (k₁.gpr (by decide)).trans h.ws.rdi, hdrOff, hst, hax, hcx₁, mask_and', m₁]
      exact ⟨⟨_, rfl⟩, _, rfl⟩) rfl) fun t ⟨⟨hm, hbp⟩, k₂⟩ => ?_
  have kk := k₁.trans k₂
  obtain ⟨ht, f⟩ := h.hdrSome (by unfold kOk sFn; omega) hm kk (by decide)
  exact ⟨ht, f, hbp, kk.mono (by simp)⟩

theorem dEven_eq2 : dEven = loadEv ++ ([zeroA aM, copyA aM aL] ++ (constA 0 ++ (eqMask aL aC ++
    (([.block [.mov .r15 (.reg .rbp)]] : List (Prog isa)) ++ (constA 1 ++ (([.block (ws ++ mBlk)] : List (Prog isa)) ++
    ([zeroA aQt, copyA aQt aE, divmod aQt aR aM aT] ++ ([zeroA aU, copyA aU aR] ++ (constA 3 ++ (ltA aL aC ++
    (([.block (([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ (ws ++ oBlk))] : List (Prog isa)) ++
    ([zeroA aM, copyA aM aL] ++ (selC aM ++ ((invFrom aM ++ [inverse aU aV aX₁ aX₂ aM aT]) ++ (gcdIsOne ++
    [zeroA aDd, copyA aDd aX₂]))))))))))))))) := by
  simp only [dEven, mBlk, oBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]

/-- `dEven`. -/
theorem dEven_ct : RelCT isa (Two (KG NF)) (seqs dEven) (Two (KG NF)) := by
  have sN : ∀ (cs : List Rc) (rs : List Reg), Stab NF cs rs := stab_nf
  have sT : ∀ (cs : List Rc), cs.all Rc.ok = true → .arr aU ∉ cs → Stab (fun I t => NF I t ∧ TopZ aU I t) cs allR :=
    fun cs h1 h2 => stab_and (sN _ _) (stab_top _ (by decide) h1 h2)
  rw [dEven_eq2]
  refine rs_app (by simp [loadEv]) (by simp) (loadEv_ct (sN _ _)) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aM, copyA aM aL]) _ from
    RelCT.seq (zeroA_ct (by decide) (sN _ _) (by taint_decide))
      (copyA_ct (by decide) (by decide) (by decide) (sN _ _) (by taint_decide))) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (sN _ _) (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [.mov .r15 (.reg .rbp)]]) _ from
    kg_regs (rs := [.r15]) (by decide) (by taint_decide) fun I s _ _ => WP.mono (WP.keep [.r15] (Q := fun t =>
      t.mem = s.mem) (by xrun) rfl) fun t ⟨hm, k⟩ => ⟨hm, k, trivial⟩) ?_
  refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (sN _ _) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [.block (ws ++ mBlk)]) _ from
    kg_wsb (by taint_decide) fun I _ s h _ _ => WP.mono (mBlk_k h) fun t ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [zeroA aQt, copyA aQt aE, divmod aQt aR aM aT]) _ from
    RelCT.seq (zeroA_ct (by decide) (sN _ _) (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (sN _ _) (by taint_decide))
        (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (sN _ _) (by taint_decide)))) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aU, copyA aU aR]) _ from
    zc_ct (by decide) (by decide) (by decide) (sN _ _) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [constA]) (by simp [ltA]) (constA_ct 3 (sT [.arr aC] (by decide) (by decide)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := fun I t => (NF I t ∧ TopZ aU I t) ∧ RbpM I t)
    (by decide) (by decide) (fun I s t hZ hf hm k hbp => ⟨sT [] (by decide) (by decide) I s t hZ hf (kf_eq hm)
      (k.mono (by simp)), _, hbp⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [.block ([.mov .rcx (.reg .rbp),
    .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] ++ (ws ++ oBlk))]) _ from RelCT.block_append (RelCT.seq
      (kg_regs (G := fun I t => (NF I t ∧ TopZ aU I t) ∧ ∃ c, t.gpr .rcx = mask c) (rs := [.rcx]) (by decide)
        (by taint_decide) fun I s hZ ⟨hf, c, hbp⟩ => WP.mono (WP.keep [.rcx] (Q := fun t =>
          t.gpr .rcx = mask (!c) ∧ t.mem = s.mem) (by xrun [hbp, sxM1, maskNot]) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ =>
            ⟨hm, k, sT [] (by decide) (by decide) I s t hZ hf (kf_eq hm) (k.mono (by simp)), _, hcx⟩)
      (kg_wsb (G := fun I t => (NF I t ∧ TopZ aU I t) ∧ RbpM I t) (by taint_decide) fun I _ s h _ ⟨hf, c, hcx⟩ =>
        WP.mono (oBlk_k h hcx) fun t ⟨ht, f, hbp, k⟩ =>
          ⟨ht, sT [.hdr kOk] (by decide) (by decide) I s t h.hZ hf f (k.mono (by decide)), hbp⟩))) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [zeroA aM, copyA aM aL]) _ from
    RelCT.seq (zeroA_ct (by decide) (stab_and (sT [.arr aM] (by decide) (by decide)).sub (stab_rbp (by decide)))
      (by taint_decide))
      (copyA_ct (by decide) (by decide) (by decide) (stab_and (sT [.arr aM] (by decide) (by decide)).sub
        (stab_rbp (by decide))) (by taint_decide))) ?_
  refine rs_app (by simp [selC]) (by simp [invFrom]) (selC_ct (by decide) (by decide)
    (sT [.arr aM] (by decide) (by decide)).sub (by taint_decide)) ?_
  refine rs_app (by simp [invFrom]) (by simp [gcdIsOne, constA]) (invFrom_ct (F := NF) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (sN _ _) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [gcdIsOne, constA]) (by simp) (gcdIsOne_ct (sN _ _)) ?_
  exact RelCT.seq (zeroA_ct (by decide) (sN _ _) (by taint_decide))
    (copyA_ct (by decide) (by decide) (by decide) (sN _ _) (by taint_decide))

/-! ## The branches on `e` -/

theorem KG.e {F : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s) :
    ∃ I, F I s ∧ I.E = Spec.Rsa.os2ip p.q.eb := by
  obtain ⟨I, m₀, he, -, -, -, -, hf⟩ := h
  exact ⟨I, hf, by rw [← he]; rfl⟩

/-- Two runs that took a branch, with the facts it gives. -/
theorem two_kg {F G : KIn → State → Prop} {P : State → Prop} (h : ∀ I s, F I s → P s → G I s) :
    ∀ s₁ s₂, Two (fun p s => KG F p s ∧ P s) s₁ s₂ → Two (KG G) s₁ s₂ :=
  fun _ _ ⟨p, ⟨h₁, q₁⟩, ⟨h₂, q₂⟩⟩ => ⟨p, h₁.imp fun I f => h I _ f q₁, h₂.imp fun I f => h I _ f q₂⟩

theorem dPart_ct : RelCT isa (Two (KG EvOK)) dPart (Two (KG NF)) := by
  unfold dPart
  refine RelCT.seq (kg_rdi (G := fun I t => EvOK I t ∧ t.cf = some (decide (I.E < 1)) ∧
      t.zf = some (decide (I.E = 1))) (by taint_decide) fun I _ s h L hev => ?_) ?_
  · have he64 : I.E < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
    have hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (I.E < 1)) ∧
      t.zf = some (decide (I.E = 1)) ∧ t.mem = s.mem) (by
        xrun [State.ea, hdr, h.ws.rdi, hdrOff, hld, hev, sx1]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
          ofNat_sub_beq he64 (by decide)]
        exact ⟨rfl, rfl⟩) rfl) fun t ⟨⟨hcf, hzf, hm⟩, k⟩ => ⟨h.same hm k (by decide), by
          dsimp only [EvOK]; rw [hm]; exact hev, hcf, hzf⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨I₁, ⟨-, c₁, -⟩, e₁⟩ := h₁.e
    obtain ⟨I₂, ⟨-, c₂, -⟩, e₂⟩ := h₂.e
    simp only [eval, c₁, c₂, e₁, e₂]
  · exact dZero_ct.mono (two_kg fun _ _ _ _ => trivial) fun _ _ h => h
  refine two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨I₁, ⟨-, -, z₁⟩, e₁⟩ := h₁.1.e
    obtain ⟨I₂, ⟨-, -, z₂⟩, e₂⟩ := h₂.1.e
    simp only [eval, z₁, z₂, e₁, e₂]
  · exact dOne_ct.mono (fun _ _ ⟨p, ⟨⟨a₁, _⟩, _⟩, ⟨⟨a₂, _⟩, _⟩⟩ =>
      ⟨p, a₁.imp fun _ _ => trivial, a₂.imp fun _ _ => trivial⟩) fun _ _ h => h
  refine RelCT.mono (P := Two (KG EvOK)) ?_ (fun _ _ ⟨p, ⟨⟨a₁, _⟩, _⟩, ⟨⟨a₂, _⟩, _⟩⟩ =>
    ⟨p, a₁.imp fun _ h => h.1, a₂.imp fun _ h => h.1⟩) fun _ _ h => h
  refine RelCT.seq (kg_rdi (G := fun I t => EvOK I t ∧ t.zf = some (decide (I.E % 2 = 0))) (by taint_decide)
    fun I _ s h L hev => ?_) ?_
  · have he64 : I.E < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
    have hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (I.E % 2 = 0)) ∧ t.mem = s.mem) (by
        xrun [State.ea, hdr, h.ws.rdi, hdrOff, hld, hev, sx1]
        rw [and1_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
        rcases Nat.mod_two_eq_zero_or_one I.E with h2 | h2 <;> rw [h2] <;> decide) rfl)
      fun t ⟨⟨hzf, hm⟩, k⟩ => ⟨h.same hm k (by decide), by dsimp only [EvOK]; rw [hm]; exact hev, hzf⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨I₁, ⟨-, z₁⟩, e₁⟩ := h₁.e
    obtain ⟨I₂, ⟨-, z₂⟩, e₂⟩ := h₂.e
    simp only [eval, z₁, z₂, e₁, e₂]
  · exact dOdd_ct.mono (two_kg fun I s ⟨hev, hz⟩ hc => ⟨hev, by
      simp only [eval, hz, Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      omega⟩) fun _ _ h => h
  · exact dEven_ct.mono (two_kg fun _ _ _ _ => trivial) fun _ _ h => h

end VG.Proof.RsaKeyGen.X86_64.Key
