module
public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Enc

import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Dec
import VerifiedGarbage.Proof.AesXts.AArch64.CT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Enc
meta import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Dec
meta import VerifiedGarbage.Proof.AesXts.AArch64.CT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# XTS-AES of data units on AArch64: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), from the correctness proof's states between the pieces: the
taint analysis covers the code between the calls (the swap's loop with
them), from the registers the states pin to public values (`Inv.agree`),
each call is constant time by its callee's proof (`xcall_rel`), and the one
branch, on whether there is a partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.AesXts.AArch64 (taint_rel)

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c)
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre (modeAArch64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The registers the states pin to public values. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x22, .x23, .x24]

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_x2 : s₀.gpr .x2 = s₀'.gpr .x2 := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_x2 hq]
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.1
theorem pub_x5 : s₀.gpr .x5 = s₀'.gpr .x5 := hq.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_x5 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_x5 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.x19, h₂.x19, pub_W hq]
  · rw [h₁.x20, h₂.x20, pub_x2 hq]
  · rw [h₁.x22, h₂.x22, pub_x5 hq]
  · rw [h₁.x23, h₂.x23, pub_D hq]
  · rw [h₁.x24, h₂.x24, pub_S hq]

theorem Inv.sp_eq {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : s₁.sp = s₂.sp := by
  rw [h₁.sp, h₂.sp, pub_sp hq]

omit hq in
/-- Agreement on the public registers and more. -/
theorem agree_cons {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r)
    (h' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : ∀ r ∈ rs ++ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h' r hr
  · exact h r hr

end

/-! ## Taint checks -/

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6])
    (.block pro) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.x9, .x10] : List Reg) ++ pubRegs))
    (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.block (nextT ++ split ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.x24]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub f.code) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (tweak f) fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have p := taint_rel [.x0, .x1, .x2, .x3, .x4, .x5, .x6] pro_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact pub_sp hq)
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      have hq' := hq
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, _⟩ := hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals with_reducible assumption)
    (F₁ := ProPost s₀) (F₂ := ProPost s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨pro_wp hp, pro_wp hp'⟩
  have c := xcall_rel true ok ct (n := f.name) (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_S hq, pub_R hq]; exact h.2.pre, Inv.sp_eq hq h.1.inv h.2.inv⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp ok nf h.1, tcall_wp hp' ok nf h.2⟩)
  exact p.seq c

theorem blocks_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c)
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre (modeAArch64 (AesXts.xtsMode enc)).pub c)
    (nf : c.noFrames = true) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀')
    (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (.call n c)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xcall_rel enc ok ct
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_W hq, pub_Tp hq, pub_D hq, pub_S hq, hNN, pub_R hq]; exact h.2.pre,
      Inv.sp_eq hq h.1.tw.inv h.2.tw.inv⟩)
    fun a b h => ⟨blocks_call hp enc ok nf hN h.1.tw h.1.pre, blocks_call hp' enc ok nf hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (taint_rel [.x24] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.x24, h.2.inv.x24, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial, WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

omit hp hp' in
theorem eval_eq {s₁ s₂ : State} (h₁ : s₁.gpr .x10 = BitVec.ofNat 64 (B s₀))
    (h₂ : s₂.gpr .x10 = BitVec.ofNat 64 (B s₀')) : isa.eval (.zero .x .x10) s₁ = isa.eval (.zero .x .x10) s₂ := by
  rw [eval_b h₁, eval_b h₂, pub_B hq]

theorem encrypt_rel {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub f.code) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (Impl.AesXts.AArch64Unit.encrypt f) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq ok nf ct
  have a := taint_rel pubRegs argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocks_rel hp hp' hq true ok ct nf (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) hM
    (n := f.name)
  have sp := taint_rel pubRegs split_taint (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitAll_wp hp h.1, splitAll_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite (.zero .x .x10) (.block []) (encSteal f)) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq hq h.1.x10 h.2.x10) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; rw [eval_b h.1.1.x10] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.x10] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.x9, .x10] ++ pubRegs) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => Inv.sp_eq hq h.1.all.inv h.2.all.inv)
        (fun a b h => agree_cons (Inv.agree hq h.1.all.inv h.2.all.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.x9, h.2.x9, hM]
          · rw [h.1.x10, h.2.x10, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true ok ct (n := f.name) (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp ok nf h.1.choose_spec.2 h.1.choose_spec.1 hB,
          encLastCall_wp hp' ok nf h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel {e d : Impl.Aes.AArch64.Blocks} (okE : XtsOk true e.code) (nfE : e.code.noFrames = true)
    (ctE : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub e.code)
    (okD : XtsOk false d.code) (nfD : d.code.noFrames = true)
    (ctD : ConstantTime isa (modeAArch64 (AesXts.xtsMode false)).pre (modeAArch64 (AesXts.xtsMode false)).pub
      d.code) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (Impl.AesXts.AArch64Unit.decrypt e d) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq okE nfE ctE
  have sp := taint_rel pubRegs split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.gpr .x10 = BitVec.ofNat 64 (B s₀))
    (F₂ := fun s => TwPost s₀' s ∧ s.gpr .x10 = BitVec.ofNat 64 (B s₀'))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.gpr .x10 = BitVec.ofNat 64 (B s₀)) ∧
      (TwPost s₀' b ∧ b.gpr .x10 = BitVec.ofNat 64 (B s₀')))
      (.ite (.zero .x .x10) (.seq (.block argsAll) (.call d.name d.code)) (decSteal d))
      fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq hq h.1.2 h.2.2) ?_ ?_
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := taint_rel pubRegs argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀))
        (F₂ := BlocksReady s₀' (M s₀')) fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
      have c := blocks_rel hp hp' hq false okD ctD nfD (by rw [len_eq s₀]; omega)
        (by rw [len_eq s₀']; omega) hM (n := d.name)
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨whole_fin h.1 hb, whole_fin h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := taint_rel pubRegs argsHead_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀ - 1))
        (F₂ := BlocksReady s₀' (M s₀' - 1)) fun a b h => ⟨argsHead_wp hp h.1, argsHead_wp hp' h.2⟩
      have c₁ := blocks_rel hp hp' hq false okD ctD nfD (N := M s₀ - 1)
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) (by rw [hM]) (n := d.name)
      have l₁ := taint_rel pubRegs decL1_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false okD ctD (n := d.name) (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          Inv.sp_eq hq h.1.inv h.2.inv⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp okD nfD h.1, decL2_wp hp' okD nfD h.2⟩
      have l₃ := taint_rel pubRegs decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false okD ctD (n := d.name) (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp okD nfD h.1.choose_spec.2 h.1.choose_spec.1 hB,
          decLast_wp hp' okD nfD h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub f.code) :
    ConstantTime isa (unitAArch64 true).pre (unitAArch64 true).pub (Impl.AesXts.AArch64Unit.encrypt f) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq ok nf ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct {e d : Impl.Aes.AArch64.Blocks} (okE : XtsOk true e.code) (nfE : e.code.noFrames = true)
    (ctE : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub e.code)
    (okD : XtsOk false d.code) (nfD : d.code.noFrames = true)
    (ctD : ConstantTime isa (modeAArch64 (AesXts.xtsMode false)).pre (modeAArch64 (AesXts.xtsMode false)).pub
      d.code) :
    ConstantTime isa (unitAArch64 false).pre (unitAArch64 false).pub (Impl.AesXts.AArch64Unit.decrypt e d) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq okE nfE ctE okD nfD ctD _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.AArch64.Unit
