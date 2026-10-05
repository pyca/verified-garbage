import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTFront
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm

/-!
# An RSA key from its primes on x86-64: constant time, `lcm(p − 1, q − 1)`

The product (`mul_ct`), the copies of `p − 1` and `q − 1` (`zc_ct`, which
leave their top words zero, as `inverse` needs of `u`), the halving's loop
(`twos_ct`, by `RelCT.loop` over the steps left), `gcdUV` (`gcdUV_ct`) and
the division.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- Word `W` of array `j` zero. -/
abbrev TopZ (j : Nat) : KIn → State → Prop := fun I t => atop I t.mem j = 0

theorem stab_top {j : Nat} {cs : List Rc} (rs : List Reg) (hj : j < 16) (hok : cs.all Rc.ok = true)
    (hn : .arr j ∉ cs) : Stab (TopZ j) cs rs := fun _ _ _ hZ h f _ => (f.top hok hj hn hZ).trans h

/-! ## The product -/

/-- The product's block: the bases of `a`, `b` and `o`, and `w = W / 2`. -/
abbrev mulBlk (a b o : Nat) : List Instr :=
  base a .r11 ++ (base b .rax ++ (base o .r8 ++ ([.mov .r9 (.reg .rax), .mov .r10 (.reg .r12), .shift .shr .r10 1,
    .alu .sub .r12 (.reg .r10)] : List Instr)))

/-- `[o] += [a] [b]` (`w` words each) from a zero `[o]`. -/
theorem mulTail_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) {a b o : Nat} (ha : a < 16)
    (hb : b < 16) (ho : o < 16) (hao : a ≠ o) (hbo : b ≠ o) (hz : Zero o I s) :
    WP isa (.seq (.block (ws ++ mulBlk a b o)) Impl.Rsa.X86_64.Crt.mulRows) s fun t =>
      KS I m₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧ Keep allR s t := by
  have hW := L.W
  have hn := h.ws.scr.nowrap
  have sP := h.ws.sl ha
  have sQ := h.ws.sl hb
  have sL := h.ws.sl ho
  have p1 := slot_far (w := I.W) hao
  have p2 := slot_far (w := I.W) hbo
  have hw2 := h.ws.w2
  have hw1 := h.ws.w1
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_))
  have hdi₂ : s₂.gpr .rdi = I.B := (k₂.gpr (by decide)).trans h.ws.rdi
  refine WP.block_append_iff.mpr (WP.mono (base_ok a (r := .r11) (by decide) hdi₂ h9) fun s₃ ⟨h11, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok b (r := .rax) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun s₄ ⟨hax, m₄, k₄⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok o (r := .r8) (by decide)
    (((k₃.trans k₄).gpr (by decide)).trans hdi₂) (((k₃.trans k₄).gpr (by decide)).trans h9))
    fun s₅ ⟨h8, m₅, k₅⟩ => ?_)
  have h12₅ : s₅.gpr .r12 = BitVec.ofNat 64 I.W := (((k₃.trans k₄).trans k₅).gpr (by decide)).trans h12
  have hax₅ : s₅.gpr .rax = off I.B (slot I.W b) := (k₅.gpr (by decide)).trans hax
  refine WP.mono (WP.keep [.r9, .r10, .r12] (Q := fun t => t.gpr .r9 = off I.B (slot I.W b) ∧
      t.gpr .r10 = BitVec.ofNat 64 (I.pl / 8) ∧ t.gpr .r12 = BitVec.ofNat 64 (I.pl / 8) ∧ t.mem = s₅.mem) (by
    xrun [h12₅, hax₅, ofNat_shr1 (show I.W < 2 ^ 64 by omega)]
    refine ⟨by rw [hW]; congr 1; omega, ?_⟩
    rw [ofNat_sub' (by omega) (by omega)]; congr 1; omega) rfl) fun s₆ ⟨⟨h9₆, h10₆, h12₆, m₆⟩, k₆⟩ => ?_
  have k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  have hm₆ : s₆.mem = s.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  have hz₆ : wv s₆.mem I.B (slot I.W o) (I.pl / 8 + I.pl / 8 + 2) = 0 := by
    rw [hm₆, ← hz]; congr 1; omega
  refine WP.mono (mulRows_ok (h.ws.scr.congr k26.2.2) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h11)
    h9₆ h10₆ h12₆ ((k₆.gpr (by decide)).trans h8) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [hz₆]; exact Nat.two_pow_pos _)) fun t ⟨_, o', k₇⟩ => ?_
  rw [hm₆] at o'
  have f := KF.arr1 (I := I) (j := o) o' (Nat.le_refl _) (by omega)
  exact ⟨h.step f (all_mut_arr ho) (k26.trans k₇) (by decide), f, (k26.trans k₇).mono (by decide)⟩

/-- `[o] := [a] [b]`, as `phi` and `nPart` compute it. -/
theorem mul_ct {F : KIn → State → Prop} {a b o : Nat} (ha : a < 16) (hb : b < 16) (ho : o < 16) (hao : a ≠ o)
    (hbo : b ≠ o) (hF : Stab F [.arr o] allR) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (mulBlk a b o)) Impl.Rsa.X86_64.Crt.mulRows) hc₂).isSome =
      true) :
    RelCT isa (Two (KG F)) (.seq (zeroA o) (.seq (.block (ws ++ mulBlk a b o)) Impl.Rsa.X86_64.Crt.mulRows)) (Two (KG F)) :=
  RelCT.seq (kg_ws (G := fun I t => F I t ∧ Zero o I t) ht₁ fun I _ s h _ hf =>
      WP.mono (zeroA_k h ho) fun _ ⟨ht, f, hz, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), hz⟩)
    (kg_ws ht₂ fun I _ s h L ⟨hf, hz⟩ => WP.mono (mulTail_k h L ha hb ho hao hbo hz) fun _ ⟨ht, f, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f k⟩)

theorem phi_eq : seqs phi = .seq (zeroA aL) (.seq (.block (ws ++ mulBlk aPm aQm aL)) Impl.Rsa.X86_64.Crt.mulRows) := by
  simp only [phi, seqs, mulBlk, List.append_assoc]

/-! ## The copies -/

/-- `[o] := [a]`, with word `W` of `[o]` zero. -/
theorem zc_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (hF : Stab F [.arr o] allR) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx))
      Impl.Rsa.X86_64.copyWords) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (zeroA o) (copyA o a)) (Two (KG fun I t => F I t ∧ TopZ o I t)) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx))) Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  refine RelCT.seq (kg_ws (G := fun I t => F I t ∧ TopZ o I t) ht₁ fun I _ s h _ hf =>
    WP.mono (zeroA_k h ho) fun _ ⟨ht, f, hz, k⟩ => ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), (wv_zero2 hz).2⟩) ?_
  rw [e]
  exact kg_ws ht₂ fun I _ s h _ ⟨hf, ht0⟩ => by
    rw [← e]
    exact WP.mono (copyA_k h ho ha hoa) fun _ ⟨ht, f, _, tt, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by decide)), tt.trans ht0⟩

/-! ## The halving -/

/-- `halfIf j` changes array `j` (but its word `W`) and `aT`. -/
theorem halfIfF_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {c : Bool} (hmo : word s.mem I.B (8 * sMo) = mask c) :
    WP isa (seqs (halfIf j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j, .arr aT] s.mem t.mem ∧
      atop I t.mem j = atop I s.mem j ∧ Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sT := h.ws.sl (j := aT) (by decide)
  have sp := slot_far (w := I.W) hjT
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have hZ := h.hZ
  simp only [halfIf, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.ws.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.seq (WP.mono (shr_ok (h.ws.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) hw1
    (by omega) (by omega) (by omega) (by omega)) fun s₃ ⟨_, o₃, k₃⟩ => ?_)
  rw [m₂, m₁] at o₃
  have f₃ := KF.arr1 (I := I) (j := aT) o₃ (Nat.le_refl _) (by omega)
  have h₃ := h.step f₃ (all_mut_arr (by decide)) ((k₁.trans k₂).trans k₃) (by decide)
  have hok : [Rc.arr aT].all Rc.ok = true := by decide
  have tj₃ : atop I s₃.mem j = atop I s.mem j := f₃.top hok hj (by simp [hjT]) hZ
  have hmo₃ : word s₃.mem I.B (8 * sMo) = mask c := by rw [f₃.word hok (by decide) (by decide), hmo]
  have k13 := (k₁.trans k₂).trans k₃
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!c) ∧
      t.mem = s₃.mem) (by
    have hl := h₃.ws.scr.ld (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega)
    xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hl, hmo₃, sxM1, maskNot]) rfl) fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ =>
    WP.mono (base2_ok j aT (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₄.gpr (by decide)).trans h₃.ws.rdi) ((k₄.gpr (by decide)).trans (((k₂.trans k₃).gpr (by decide)).trans h9))
      (by decide)) fun s₅ ⟨h8₅, hsi₅, m₅, k₅⟩ => ?_))
  refine WP.mono (sel_ok (h.ws.scr.congr ((k13.trans k₄).trans k₅).2.2) h8₅ hsi₅ ((k₅.gpr (by decide)).trans hbp)
    (((k₄.trans k₅).gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))) (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun t ⟨_, o, k₆⟩ => ?_
  rw [m₅, m₄] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  refine ⟨h₃.step f (all_mut_arr hj) ((k₄.trans k₅).trans k₆) (by decide), (f₃.trans f).mono (by simp), ?_,
    (((k13.trans k₄).trans k₅).trans k₆).mono (by simp)⟩
  dsimp only [atop]; rw [o.word (Or.inr (Nat.le_refl _)) (by omega)]; exact tj₃

/-- The mask of `u` and `v` both even, into `sMo`. -/
abbrev twoBlk : List Instr := base aU .rbx ++ (base aV .r10 ++ ([.mov .rax (.mem (at0 .rbx)),
  .alu .or .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .sub .rax (.imm 1), .store (hdr sMo) .rax] :
  List Instr))

/-- A mask in `sMo`. -/
abbrev SmoM : KIn → State → Prop := fun I t => ∃ c, word t.mem I.B (8 * sMo) = mask c

theorem twoBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.block (ws ++ twoBlk)) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr sMo] s.mem t.mem ∧ SmoM I t ∧
      Keep [.r12, .r9, .rbx, .r10, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sU := h.ws.sl (j := aU) (by decide)
  have sV := h.ws.sl (j := aV) (by decide)
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : s₁.gpr .rdi = I.B := (k₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₁ h9) fun s₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨h10, m₃, k₃⟩ => ?_
  have hs₃ := h.ws.scr.congr ((k₁.trans k₂).trans k₃).2.2
  have hbx₃ : s₃.gpr .rbx = off I.B (slot I.W aU) := (k₃.gpr (by decide)).trans hbx
  have hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans hdi₁
  have hm₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * sMo))
      (((s.mem.readW (off I.B (slot I.W aU)) 64 ||| s.mem.readW (off I.B (slot I.W aV)) 64) &&& 1) - 1)) (by
    xrun [State.ea, at0, hdr, hbx₃, h10, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.ld (d := slot I.W aU) (by omega), hs₃.ld (d := slot I.W aV) (by omega),
      hs₃.st (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega), hm₃]) rfl) fun t ⟨hm, k₄⟩ => ?_
  rw [twoMask] at hm
  have kk := ((k₁.trans k₂).trans k₃).trans k₄
  obtain ⟨ht, f, hw⟩ := h.hdrW (i := sMo) (by unfold sMo sFn; omega) hm kk (by decide)
  exact ⟨ht, f, ⟨_, hw⟩, kk.mono (by simp)⟩

/-- The facts the halving keeps: `F`, and words `W` of `u` and `v` zero. -/
abbrev TwB (F : KIn → State → Prop) : KIn → State → Prop := fun I t => F I t ∧ TopZ aU I t ∧ TopZ aV I t

/-- Before a step of the halving, with `n` steps left. -/
abbrev TwF (F : KIn → State → Prop) (n : Nat) : KIn → State → Prop := fun I t => TwB F I t ∧
  t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.gpr .r13 = BitVec.ofNat 64 (64 * I.W - n) ∧ 0 < n ∧ n ≤ 64 * I.W

/-- After a step of the halving, from `n` steps left. -/
abbrev TwP (F : KIn → State → Prop) (n : Nat) : KIn → State → Prop := fun I t => TwB F I t ∧
  t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧ t.gpr .r13 = BitVec.ofNat 64 (64 * I.W - n + 1) ∧
  t.zf = some (decide (64 * I.W - n + 1 = 64 * I.W)) ∧ 0 < n ∧ n ≤ 64 * I.W

theorem halfIf_eq (j : Nat) : seqs (halfIf j) = .seq (.block (ws ++ (base j .r8 ++ base aT .rsi)))
    (.seq (wordLoop 0 shrBody) (.seq (.block ([.mov .rbp (.mem (hdr sMo)),
      .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] ++ (base j .r8 ++ base aT .rsi))) (wordLoop 0 selBody))) := by
  simp only [halfIf, seqs, List.append_assoc]

theorem halfIf_ct {F : KIn → State → Prop} {n j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    (hF : Stab F [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] allR)
    (hjs : Rc.arr j ∈ [Rc.arr aU, Rc.arr aV, Rc.arr aL, Rc.arr aT, Rc.hdr sMo]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base aT .rsi))
      (.seq (wordLoop 0 shrBody) (.seq (.block ([.mov .rbp (.mem (hdr sMo)),
      .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] ++ (base j .r8 ++ base aT .rsi))) (wordLoop 0 selBody)))) hc).isSome =
      true) :
    RelCT isa (Two (KG fun I t => TwF F n I t ∧ SmoM I t)) (seqs (halfIf j))
      (Two (KG fun I t => TwF F n I t ∧ SmoM I t)) := by
  rw [halfIf_eq]
  refine kg_ws ht fun I _ s h _ ⟨⟨⟨hf, tU, tV⟩, h11, h13, hn⟩, c, hmo⟩ => ?_
  rw [← halfIf_eq]
  refine WP.mono (halfIfF_k h hj hjT hmo) fun t ⟨ht, f, tj, k⟩ => ?_
  have hZ := h.hZ
  have hok : [Rc.arr j, Rc.arr aT].all Rc.ok = true := by
    simp only [List.all_cons, List.all_nil, Rc.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hj, by decide⟩
  have top : ∀ i < 16, i ≠ aT → atop I t.mem i = atop I s.mem i := fun i hi hiT =>
    if e : i = j then e ▸ tj else f.top hok hi (by simp [e, hiT]) hZ
  refine ⟨ht, ⟨⟨hF I s t hZ hf (f.mono fun c hc => ?_) (k.mono (by decide)), (top aU (by decide) (by decide)).trans tU,
    (top aV (by decide) (by decide)).trans tV⟩, (k.gpr (by decide)).trans h11, (k.gpr (by decide)).trans h13, hn⟩,
    c, (f.word hok (by decide) (by simp)).trans hmo⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact hjs
  · simp

theorem twoStep_eq : twoStep = seqs ([.block (ws ++ twoBlk)] ++ (halfIf aU ++ (halfIf aV ++ (halfIf aL ++
    [.block countP])))) := by
  simp only [twoStep, twoBlk, List.append_assoc]

theorem twoStep_ct {F : KIn → State → Prop} (n : Nat) (hF : Stab F [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] allR) :
    RelCT isa (Two (KG (TwF F n))) twoStep (Two (KG (TwP F n))) := by
  rw [twoStep_eq]
  refine rs_app (by simp) (by simp [halfIf]) (show RelCT isa _ (seqs [.block (ws ++ twoBlk)]) _ from
    kg_wsb (G := fun I t => TwF F n I t ∧ SmoM I t) (by taint_decide)
      fun I _ s h _ ⟨⟨hf, tU, tV⟩, h11, h13, hn⟩ => WP.mono (twoBlk_k h) fun t ⟨ht, f, hmo, k⟩ => by
        have hok : [Rc.hdr sMo].all Rc.ok = true := by decide
        exact ⟨ht, ⟨⟨hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
          (f.top hok (by decide) (by decide) h.hZ).trans tU, (f.top hok (by decide) (by decide) h.hZ).trans tV⟩,
          (k.gpr (by decide)).trans h11, (k.gpr (by decide)).trans h13, hn⟩, hmo⟩) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide) hF (by simp)
    (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide) hF (by simp)
    (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp) (halfIf_ct (by decide) (by decide) hF (by simp) (by taint_decide)) ?_
  exact kg_regs (rs := [.r13]) (by decide) (by taint_decide) fun I s hZ ⟨⟨hb, h11, h13, hn⟩, _⟩ =>
    WP.mono (countP_ok s h13 h11 (by unfold slot hdrBytes at hZ; omega) (by unfold slot hdrBytes at hZ; omega))
      fun t ⟨hz, h13', hm, k⟩ => by
      have hb' : TwB F I t := by
        obtain ⟨hf, tU, tV⟩ := hb
        refine ⟨hF I s t hZ hf (by rw [hm]; exact (KF.refl _ _ _).mono (by simp)) (k.mono (by decide)), ?_, ?_⟩
        · dsimp only [TopZ, atop]; rw [hm]; exact tU
        · dsimp only [TopZ, atop]; rw [hm]; exact tV
      exact ⟨hm, k, hb', (k.gpr (by decide)).trans h11, h13', hz, hn⟩

theorem divInit_eq (iT : Nat) : divInit iT = ws ++ (base iT .r8 ++ (([.mov .r11 (.reg .r12)] : List Instr) ++
    (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)))) := by
  simp only [divInit, List.append_assoc]

theorem twos_ct {F : KIn → State → Prop} (hF : Stab F [.arr aU, .arr aV, .arr aL, .arr aT, .hdr sMo] allR) :
    RelCT isa (Two (KG (TwB F))) (seqs twos) (Two (KG (TwB F))) := by
  have e : seqs twos = .seq (.block (divInit aT)) (.loop twoStep .ne) := rfl
  rw [e, divInit_eq]
  refine RelCT.seq (kg_wsb (G := fun I t => TwB F I t ∧ t.gpr .r11 = BitVec.ofNat 64 (64 * I.W) ∧
      t.gpr .r13 = BitVec.ofNat 64 0) (by taint_decide) fun I _ s h _ ⟨hf, tU, tV⟩ => by
    rw [← divInit_eq]
    exact WP.mono (divInit_k h aT) fun t ⟨h11, h13, hm, k⟩ =>
      ⟨h.same hm k (by decide), ⟨hF I s t h.hZ hf (by rw [hm]; exact (KF.refl _ _ _).mono (by simp)) (k.mono (by decide)),
        by dsimp only [TopZ, atop]; rw [hm]; exact tU, by dsimp only [TopZ, atop]; rw [hm]; exact tV⟩, h11, h13⟩) ?_
  -- The loop, over the steps left.
  have hW : ∀ {G : KIn → State → Prop} {p : KP} {s : State}, KG G p s →
      ∃ I m₀, I.pub = p.q ∧ I.st = p.st ∧ KS I m₀ s ∧ KLens I ∧ KOuts I ∧ G I s ∧ I.W = 2 * p.q.pl / 8 :=
    fun ⟨I, m₀, he, hst, hk, L, O, hg⟩ => ⟨I, m₀, he, hst, hk, L, O, hg, by rw [← he]; rfl⟩
  refine RelCT.mono (RelCT.exists_ fun n => RelCT.loop (fun n => Two (KG (TwF F n))) (fun n => ?_) n)
    (fun s₁ s₂ ⟨p, h₁, h₂⟩ => ⟨64 * (2 * p.q.pl / 8), p, ?_, ?_⟩) (fun _ _ h => h)
  rotate_left
  · obtain ⟨I, m₀, he, hst, hk, L, O, ⟨hb, h11, h13⟩, hIW⟩ := hW h₁
    have := hk.ws.w1
    exact ⟨I, m₀, he, hst, hk, L, O, hb, h11, by rw [hIW, Nat.sub_self]; exact h13, by rw [← hIW]; omega,
      by rw [hIW]⟩
  · obtain ⟨I, m₀, he, hst, hk, L, O, ⟨hb, h11, h13⟩, hIW⟩ := hW h₂
    have := hk.ws.w1
    exact ⟨I, m₀, he, hst, hk, L, O, hb, h11, by rw [hIW, Nat.sub_self]; exact h13, by rw [← hIW]; omega,
      by rw [hIW]⟩
  refine (twoStep_ct n hF).mono (fun _ _ h => h) fun s₁ s₂ ⟨p, h₁, h₂⟩ => ?_
  obtain ⟨I₁, m₁, he₁, hst₁, hk₁, L₁, O₁, ⟨hb₁, h11₁, h13₁, hz₁, hn₁⟩, hW₁⟩ := hW h₁
  obtain ⟨I₂, m₂, he₂, hst₂, hk₂, L₂, O₂, ⟨hb₂, h11₂, h13₂, hz₂, hn₂⟩, hW₂⟩ := hW h₂
  rw [hW₁] at h11₁ h13₁ hz₁ hn₁
  rw [hW₂] at h11₂ h13₂ hz₂ hn₂
  refine ⟨by simp only [eval, hz₁, hz₂], fun hf => ⟨p, ⟨I₁, m₁, he₁, hst₁, hk₁, L₁, O₁, hb₁⟩,
    ⟨I₂, m₂, he₂, hst₂, hk₂, L₂, O₂, hb₂⟩⟩, fun ht => ⟨n - 1, by omega, p, ?_, ?_⟩⟩
  · simp only [eval, hz₁, Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at ht
    refine ⟨I₁, m₁, he₁, hst₁, hk₁, L₁, O₁, hb₁, by rw [hW₁]; exact h11₁, ?_, by omega, by rw [hW₁]; omega⟩
    rw [hW₁, h13₁]; congr 1; omega
  · simp only [eval, hz₁, Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at ht
    refine ⟨I₂, m₂, he₂, hst₂, hk₂, L₂, O₂, hb₂, by rw [hW₂]; exact h11₂, ?_, by omega, by rw [hW₂]; omega⟩
    rw [hW₂, h13₂]; congr 1; omega

/-! ## `gcd(u, v)` -/

/-- A mask in `kOk`. -/
abbrev KokM : KIn → State → Prop := fun I t => ∃ c, word t.mem I.B (8 * kOk) = mask c

theorem stab_kok {cs : List Rc} (rs : List Reg) (hok : cs.all Rc.ok = true) (hn : .hdr kOk ∉ cs) :
    Stab KokM cs rs := fun _ _ _ _ ⟨c, h⟩ f _ => ⟨c, (f.word hok (by decide) hn).trans h⟩

/-- Array `j`'s value. -/
abbrev AvIs (j v : Nat) : KIn → State → Prop := fun I t => av I t.mem j = v

theorem stab_av {j v : Nat} {cs : List Rc} (rs : List Reg) (hj : j < 16) (hok : cs.all Rc.ok = true)
    (hn : .arr j ∉ cs) : Stab (AvIs j v) cs rs := fun _ _ _ hZ h f _ => (f.av hok hj hn hZ).trans h

/-- Arrays `a` and `b` equal. -/
abbrev AvEq (a b : Nat) : KIn → State → Prop := fun I t => av I t.mem a = av I t.mem b

theorem stab_aveq {a b : Nat} {cs : List Rc} (rs : List Reg) (ha : a < 16) (hb : b < 16) (hok : cs.all Rc.ok = true)
    (hna : .arr a ∉ cs) (hnb : .arr b ∉ cs) : Stab (AvEq a b) cs rs := fun _ _ _ hZ h f _ => by
  dsimp only [AvEq] at h ⊢; rw [f.av hok ha hna hZ, f.av hok hb hnb hZ]; exact h

/-- `rbp`'s mask into `kOk`, and `rbp` negated. -/
theorem kokPut_ok {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool} (hbp : s.gpr .rbp = mask c) :
    WP isa (.block [.store (hdr kOk) .rbp, .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      KS I m₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧ word t.mem I.B (8 * kOk) = mask c ∧
      t.gpr .rbp = mask (!c) ∧ Keep [.rbp] s t := by
  have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk)) (mask c) ∧
    t.gpr .rbp = mask (!c)) (by xrun [State.ea, hdr, h.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun t ⟨⟨hm, hbp'⟩, k⟩ => ?_
  obtain ⟨ht, f, hw⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k (by decide)
  exact ⟨ht, f, hw, hbp', k⟩

/-- `kOk`'s mask, negated, into `rbp`. -/
theorem kokGetNot_ok {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool}
    (hk : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (.block [.mov .rbp (.mem (hdr kOk)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      t.mem = s.mem ∧ Keep [.rbp] s t ∧ t.gpr .rbp = mask (!c) := by
  have hl := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!c) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, h.ws.rdi, hdrOff, hl, hk, sxM1, maskNot]) rfl) fun t ⟨⟨hbp, hm⟩, k⟩ => ⟨hm, k, hbp⟩

/-- `gcdUV`'s first block, after `ws`. -/
abbrev gcdBlk : List Instr :=
  base aV .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .mov .r15 (.reg .rax),
    .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++ (base aU .rbx ++ base aV .r10))

/-- `gcdUV`'s swap of `u` and `v`, which keeps word `W` of `u`. -/
theorem gcdSwap_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (.seq (.block (ws ++ gcdBlk)) (wordLoop 0 cswapBody)) s fun t => KS I m₀ t ∧
      KF I.B I.W [.arr aU, .arr aV] s.mem t.mem ∧ atop I t.mem aU = atop I s.mem aU ∧ Keep allR s t := by
  have hn := h.ws.scr.nowrap
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  have sU := h.ws.sl (j := aU) (by decide)
  have sV := h.ws.sl (j := aV) (by decide)
  have spUV := slot_far (w := I.W) (i := aU) (j := aV) (by decide)
  have e : ws ++ gcdBlk = oddMask aV ++ [.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++
      (base aU .rbx ++ base aV .r10) := by
    simp only [gcdBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  have hb : WP isa (.block (oddMask aV ++ [.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++
      (base aU .rbx ++ base aV .r10))) s fun t => t.mem = s.mem ∧ (∃ c, t.gpr .r15 = mask c) ∧
      t.gpr .rbx = off I.B (slot I.W aU) ∧ t.gpr .r10 = off I.B (slot I.W aV) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .r15, .r10] s t := by
    simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono (oddMask_k h (j := aV) (by decide)) fun s₁ ⟨m₁, hax, h12, h9, k₁⟩ => ?_)
    refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask
      (!decide (av I s.mem aV % 2 = 1)) ∧ t.mem = s₁.mem) (by xrun [hax, sxM1, maskNot]) rfl)
      fun s₂ ⟨⟨h15, m₂⟩, k₂⟩ => WP.block_append_iff.mpr ?_)
    have hdi₂ : s₂.gpr .rdi = I.B := ((k₁.trans k₂).gpr (by decide)).trans h.ws.rdi
    have h9₂ : s₂.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) := (k₂.gpr (by decide)).trans h9
    refine WP.mono (base_ok aU (r := .rbx) (by decide) hdi₂ h9₂) fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
    refine WP.mono (base_ok aV (r := .r10) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
      ((k₃.gpr (by decide)).trans h9₂)) fun t ⟨h10, m₄, k₄⟩ => ⟨by rw [m₄, m₃, m₂, m₁],
        ⟨_, ((k₃.trans k₄).gpr (by decide)).trans h15⟩, (k₄.gpr (by decide)).trans hbx, h10,
        (((k₂.trans k₃).trans k₄).gpr (by decide)).trans h12, (((k₁.trans k₂).trans k₃).trans k₄).mono (by simp)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨m₁, ⟨c, h15⟩, hbx, h10, h12, k₁⟩ => ?_)
  refine WP.mono (cswap_ok (h.ws.scr.congr k₁.2.2) hbx h10 h15 h12 (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun t ⟨_, _, hf, k₂⟩ => ?_
  rw [m₁] at hf
  have f₂ : KF I.B I.W [.arr aU, .arr aV] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aU, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.arr aV, by simp, by simp [Rc.range], by simp [Rc.range]⟩
  refine ⟨h.step f₂ (all_mut_arrs (js := [aU, aV]) (by decide)) (k₁.trans k₂) (by decide), f₂, ?_,
    (k₁.trans k₂).mono (by decide)⟩
  dsimp only [atop]
  exact hf.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)

theorem gcdUV_eq2 : gcdUV = [.block (ws ++ gcdBlk), wordLoop 0 cswapBody] ++ (constA 2 ++ (ltA aV aC ++
    ([.block [.store (hdr kOk) .rbp, .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] ++ (constA 3 ++ (selC aV ++
    ([zeroA aM, copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂, inverse aU aV aX₁ aX₂ aM aT] ++
    (constA 1 ++ ([.block [.mov .rbp (.mem (hdr kOk)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] ++
      selC aV)))))))) := by
  simp only [gcdUV, gcdBlk, oddMask, List.append_assoc, List.cons_append, List.nil_append]

/-- What `gcdUV` changes. -/
abbrev csG : List Rc := [.arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo, .hdr kOk]

/-- `inverse`'s start from the copy into `[o]` of `[a]`: `x₁ := 1`,
`x₂ := 0`. -/
theorem invStart_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (ho1 : o ≠ aX₁) (ho2 : o ≠ aX₂) (ha1 : a ≠ aX₁) (ha2 : a ≠ aX₂) (hF : Stab F [.arr o, .arr aX₁, .arr aX₂] allR)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx))
      Impl.Rsa.X86_64.copyWords) hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs [copyA o a, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂])
      (Two (KG fun I t => F I t ∧ AvEq o a I t ∧ AvIs aX₁ 1 I t ∧ AvIs aX₂ 0 I t)) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx))) Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  have sE : ∀ (cs : List Rc), cs.all Rc.ok = true → .arr o ∉ cs → .arr a ∉ cs → Stab (AvEq o a) cs allR :=
    fun _ hok h1 h2 => stab_aveq _ ho ha hok h1 h2
  have ok1 : [Rc.arr aX₁].all Rc.ok = true := by decide
  have ok2 : [Rc.arr aX₂].all Rc.ok = true := by decide
  simp only [seqs]
  refine RelCT.seq (R := Two (KG fun I t => F I t ∧ AvEq o a I t)) ?_ ?_
  · rw [e]
    exact kg_ws ht fun I _ s h _ hf => by
      rw [← e]
      exact WP.mono (copyA_k h ho ha hoa) fun t ⟨ht, f, v, _, k⟩ =>
        ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
          by dsimp only [AvEq]; rw [v, f.av (by simp [Rc.ok, ho]) ha (by simp [hoa.symm]) h.hZ]⟩
  refine RelCT.seq (R := Two (KG fun I t => (F I t ∧ AvEq o a I t) ∧ Zero aX₁ I t)) ?_ ?_
  · exact kg_ws (by taint_decide) fun I _ s h _ ⟨hf, he⟩ => WP.mono (zeroA_k h (j := aX₁) (by decide))
      fun t ⟨ht, f, hz, k⟩ => ⟨ht, ⟨hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
        sE [.arr aX₁] ok1 (by simp [ho1]) (by simp [ha1]) I s t h.hZ he f (k.mono (by decide))⟩, hz⟩
  refine RelCT.seq (R := Two (KG fun I t => F I t ∧ AvEq o a I t ∧ AvIs aX₁ 1 I t)) ?_ ?_
  · rw [setOneA_eq]
    exact kg_wsb (by taint_decide) fun I _ s h _ ⟨⟨hf, he⟩, hz⟩ => by
      rw [← setOneA_eq]
      exact WP.mono (setOne_k h (j := aX₁) (by decide) hz) fun t ⟨ht, f, v, k⟩ =>
        ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
          sE [.arr aX₁] ok1 (by simp [ho1]) (by simp [ha1]) I s t h.hZ he f (k.mono (by decide)),
          av_of_full v (Nat.one_lt_two_pow (by have := h.ws.w1; omega))⟩
  · exact kg_ws (by taint_decide) fun I _ s h _ ⟨hf, he, h1⟩ => WP.mono (zeroA_k h (j := aX₂) (by decide))
      fun t ⟨ht, f, hz, k⟩ => ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
        sE [.arr aX₂] ok2 (by simp [ho2]) (by simp [ha2]) I s t h.hZ he f (k.mono (by decide)),
        stab_av _ (by decide) (by decide) (by decide) I s t h.hZ h1 f k, av_of_full hz (Nat.two_pow_pos _)⟩

theorem gcdUV_ct {F : KIn → State → Prop} (hF : Stab F csG allR) :
    RelCT isa (Two (KG fun I t => F I t ∧ TopZ aU I t)) (seqs gcdUV) (Two (KG F)) := by
  have sF : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → Stab F cs allR := fun _ hc => hF.mono hc (by simp)
  have sT : ∀ (cs : List Rc), cs.all Rc.ok = true → .arr aU ∉ cs → Stab (TopZ aU) cs allR :=
    fun _ hok hn => stab_top _ (by decide) hok hn
  have sK : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kOk ∉ cs → Stab KokM cs allR :=
    fun _ hok hn => stab_kok _ hok hn
  have sFT : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → cs.all Rc.ok = true → .arr aU ∉ cs →
      Stab (fun I t => F I t ∧ TopZ aU I t) cs allR := fun cs h1 h2 h3 => stab_and (sF cs h1) (sT cs h2 h3)
  have sFTK : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → cs.all Rc.ok = true → .arr aU ∉ cs → .hdr kOk ∉ cs →
      Stab (fun I t => (F I t ∧ TopZ aU I t) ∧ KokM I t) cs allR :=
    fun cs h1 h2 h3 h4 => stab_and (sFT cs h1 h2 h3) (sK cs h2 h4)
  have sFK : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csG) → cs.all Rc.ok = true → .hdr kOk ∉ cs →
      Stab (fun I t => F I t ∧ KokM I t) cs allR := fun cs h1 h2 h4 => stab_and (sF cs h1) (sK cs h2 h4)
  rw [gcdUV_eq2]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block (ws ++ gcdBlk), wordLoop 0 cswapBody]) _
    from kg_ws (G := fun I t => F I t ∧ TopZ aU I t) (by taint_decide) fun I _ s h _ ⟨hf, tU⟩ =>
      WP.mono (gcdSwap_k h) fun t ⟨ht, f, tt, k⟩ => ⟨ht, sF _ (by simp) I s t h.hZ hf f k, tt.trans tU⟩) ?_
  refine rs_app (by simp [constA]) (by simp [ltA]) (constA_ct 2 (sFT [.arr aC] (by simp) (by decide) (by decide)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [ltA]) (by simp) (ltA_ct (G := fun I t => (F I t ∧ TopZ aU I t) ∧ RbpM I t)
    (by decide) (by decide) (fun I s t hZ hf hm k hbp => ⟨sFT [] (by simp) (by decide) (by decide) I s t hZ hf
      (kf_eq hm) (k.mono (by simp)), _, hbp⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [.store (hdr kOk) .rbp,
    .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]]) _ from kg_rdi
    (G := fun I t => ((F I t ∧ TopZ aU I t) ∧ KokM I t) ∧ RbpM I t) (by taint_decide)
    fun I _ s h _ ⟨hf, c, hbp⟩ => WP.mono (kokPut_ok h hbp) fun t ⟨ht, f, hk, hbp', k⟩ =>
      ⟨ht, ⟨sFT [.hdr kOk] (by simp) (by decide) (by decide) I s t h.hZ hf f (k.mono (by simp)), _, hk⟩,
        _, hbp'⟩) ?_
  refine rs_app (by simp [constA]) (by simp [selC]) (constA_ct 3 (stab_and (sFTK [.arr aC] (by simp) (by decide)
    (by decide) (by decide)).sub (stab_rbp (by decide))) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [selC]) (by simp) (selC_ct (by decide) (by decide)
    (sFTK [.arr aV] (by simp) (by decide) (by decide) (by decide)).sub (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => F I t ∧ KokM I t)) (by simp) (by simp [constA]) ?_ ?_
  · -- `inverse` modulo `[aM] = v`.
    show RelCT isa _ (seqs ([zeroA aM] ++ ([copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂] ++
      [inverse aU aV aX₁ aX₂ aM aT]))) _
    refine rs_app (by simp) (by simp) (zeroA_ct (by decide) (sFTK [.arr aM] (by simp) (by decide) (by decide)
      (by decide)).sub (by taint_decide)) ?_
    refine rs_app (by simp) (by simp) (invStart_ct (o := aM) (a := aV) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (sFTK [.arr aM, .arr aX₁, .arr aX₂] (by simp) (by decide)
      (by decide) (by decide)) (by taint_decide)) ?_
    refine (inverse_ct (F := fun I t => F I t ∧ KokM I t) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (sFK _ (by simp) (by decide) (by decide)).sub (by taint_decide)).mono
      (fun s₁ s₂ h => two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p, h₁.imp fun I ⟨⟨⟨hf, tU⟩, hk⟩, he, h1, h2⟩ =>
        ⟨⟨hf, hk⟩, tU, he.symm, h1, h2⟩, h₂.imp fun I ⟨⟨⟨hf, tU⟩, hk⟩, he, h1, h2⟩ =>
          ⟨⟨hf, hk⟩, tU, he.symm, h1, h2⟩⟩) h)
      fun _ _ h => h
  refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (sFK [.arr aC] (by simp) (by decide) (by decide)).sub
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [.block [.mov .rbp (.mem (hdr kOk)),
    .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]]) _ from kg_rdi (G := fun I t => F I t ∧ RbpM I t)
    (by taint_decide) fun I _ s h _ ⟨hf, c, hk⟩ => WP.mono (kokGetNot_ok h hk) fun t ⟨hm, k, hbp⟩ =>
      ⟨h.same hm k (by decide), sF [] (by simp) I s t h.hZ hf (kf_eq hm) (k.mono (by simp)), _, hbp⟩) ?_
  exact selC_ct (by decide) (by decide) (sF [.arr aV] (by simp)).sub (by taint_decide)

theorem phi_ct : RelCT isa (Two (KG EvOK)) (seqs phi) (Two (KG EvOK)) := by
  rw [phi_eq]
  exact mul_ct (by decide) (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)

/-- `lcmPart`, keeping `e` in `kEv`. -/
theorem lcmPart_ct : RelCT isa (Two (KG EvOK)) (seqs lcmPart) (Two (KG EvOK)) := by
  have sE : ∀ (cs : List Rc), cs.all Rc.ok = true → .hdr kEv ∉ cs → Stab EvOK cs allR :=
    fun _ hok hn => stab_ev _ hok hn
  rw [lcmPart_eq]
  refine rs_app (by simp [phi]) (by simp) phi_ct ?_
  refine rs_app (by simp) (by simp [twos]) (show RelCT isa _ (seqs ([zeroA aU, copyA aU aPm] ++
    [zeroA aV, copyA aV aQm])) (Two (KG (TwB EvOK))) from rs_app (by simp) (by simp)
      (zc_ct (by decide) (by decide) (by decide) (sE _ (by decide) (by decide)) (by taint_decide) (by taint_decide))
      ((zc_ct (by decide) (by decide) (by decide) (stab_and (sE [.arr aV] (by decide) (by decide))
        (stab_top _ (by decide) (by decide) (by decide))) (by taint_decide) (by taint_decide)).mono
        (fun _ _ h => h) fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
          ⟨p, h₁.imp fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, h₂.imp fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩) h)) ?_
  refine rs_app (by simp [twos]) (by simp [gcdUV]) (twos_ct (sE _ (by decide) (by decide))) ?_
  refine rs_app (by simp [gcdUV]) (by simp) ((gcdUV_ct (sE _ (by decide) (by decide))).mono
    (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p, h₁.imp fun _ ⟨a, b, _⟩ => ⟨a, b⟩, h₂.imp fun _ ⟨a, b, _⟩ => ⟨a, b⟩⟩) h) fun _ _ h => h) ?_
  exact divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (sE [.arr aL, .arr aR, .arr aT] (by decide) (by decide)).sub (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64.Key
