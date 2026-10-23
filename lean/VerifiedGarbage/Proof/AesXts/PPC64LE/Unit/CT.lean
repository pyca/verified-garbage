module

import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Dec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Dec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Enc

/-!
# XTS-AES of data units on PPC64LE: constant time

As on AArch64 (`Proof/AesXts/AArch64/Unit/CT.lean`): two runs from states
that agree on the public arguments are related piece by piece (`RelCT`),
from the correctness proof's states between the pieces: the taint analysis
covers the code between the calls (the swap's loop with them), from the
registers the states pin to public values (`Inv.agree`), each call is
constant time by its callee's proof (`xcall_rel`), and the one branch, on
whether there is a partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Proof.AesCbc.PPC64LE (modePPC64LE)

/-- A piece of code the taint analysis checks from the registers `rs`, which
agree in two runs (as do the stack pointers), with what each run reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp) (ha : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨hsp x y hp, fun r h' => ha x y hp r (Taint.mem_ofRegs.mp h')⟩) ht).wp hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- A whole-block function, constant time. -/
abbrev XtsCt (enc : Bool) (c : Prog isa) : Prop :=
  ConstantTime isa (modePPC64LE (AesXts.xtsMode enc)).pre (modePPC64LE (AesXts.xtsMode enc)).pub c

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c) (ct : XtsCt enc c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The registers the states pin to public values. -/
abbrev pubRegs : List Reg := [.r14, .r15, .r17, .r18, .r19]

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_r5 : s₀.gpr .r5 = s₀'.gpr .r5 := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r5 hq]
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.1
theorem pub_r8 : s₀.gpr .r8 = s₀'.gpr .r8 := hq.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_r8 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_r8 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r14, h₂.r14, pub_W hq]
  · rw [h₁.r15, h₂.r15, pub_r5 hq]
  · rw [h₁.r17, h₂.r17, pub_D hq]
  · rw [h₁.r18, h₂.r18, pub_r8 hq]
  · rw [h₁.r19, h₂.r19, pub_S hq]

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

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (.block pro) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.r10, .r11] : List Reg) ++ pubRegs))
    (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.block (nextT ++ split ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r19]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.PPC64LE.encrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') tweak fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have p := taint_rel [.r3, .r4, .r5, .r6, .r7, .r8, .r9] pro_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact pub_sp hq)
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      have hq' := hq
      obtain ⟨h3, h4, h5, h6, h7, h8, h9, _⟩ := hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      · exact h8
      · exact h9)
    (F₁ := ProPost s₀) (F₂ := ProPost s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨pro_wp hp, pro_wp hp'⟩
  have c := xcall_rel true ok ct (n := "vg_aes_xts_encrypt") (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_S hq, pub_R hq]; exact h.2.pre, Inv.sp_eq hq h.1.inv h.2.inv⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp ok nf h.1, tcall_wp hp' ok nf h.2⟩)
  exact p.seq c

theorem blocks_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c) (ct : XtsCt enc c)
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
  (taint_rel [.r19] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.r19, h.2.inv.r19, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial, WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

omit hp hp' in
theorem eval_eq {s₁ s₂ : State} (h₁ : s₁.gpr .r11 = BitVec.ofNat 64 (B s₀))
    (h₂ : s₂.gpr .r11 = BitVec.ofNat 64 (B s₀')) : isa.eval (.zero .d .r11) s₁ = isa.eval (.zero .d .r11) s₂ := by
  rw [eval_b h₁, eval_b h₂, pub_B hq]

theorem encrypt_rel (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.PPC64LE.encrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.PPC64LEUnit.encrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq ok nf ct
  have a := taint_rel pubRegs argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocks_rel hp hp' hq true ok ct nf (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) hM
    (n := "vg_aes_xts_encrypt")
  have sp := taint_rel pubRegs split_taint (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitAll_wp hp h.1, splitAll_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite (.zero .d .r11) (.block []) encSteal) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq hq h.1.r11 h.2.r11) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; rw [eval_b h.1.1.r11] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.r11] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.r10, .r11] ++ pubRegs) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => Inv.sp_eq hq h.1.all.inv h.2.all.inv)
        (fun a b h => agree_cons (Inv.agree hq h.1.all.inv h.2.all.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.r10, h.2.r10, hM]
          · rw [h.1.r11, h.2.r11, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true ok ct (n := "vg_aes_xts_encrypt") (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp ok nf h.1.choose_spec.2 h.1.choose_spec.1 hB,
          encLastCall_wp hp' ok nf h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel (okE : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nfE : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ctE : XtsCt true Impl.AesXts.PPC64LE.encrypt)
    (okD : XtsOk false Impl.AesXts.PPC64LE.decrypt) (nfD : Impl.AesXts.PPC64LE.decrypt.noFrames = true)
    (ctD : XtsCt false Impl.AesXts.PPC64LE.decrypt) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.PPC64LEUnit.decrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq okE nfE ctE
  have sp := taint_rel pubRegs split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.gpr .r11 = BitVec.ofNat 64 (B s₀))
    (F₂ := fun s => TwPost s₀' s ∧ s.gpr .r11 = BitVec.ofNat 64 (B s₀'))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.gpr .r11 = BitVec.ofNat 64 (B s₀)) ∧
      (TwPost s₀' b ∧ b.gpr .r11 = BitVec.ofNat 64 (B s₀')))
      (.ite (.zero .d .r11) (.seq (.block argsAll) decCall) decSteal)
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
        (by rw [len_eq s₀']; omega) hM (n := "vg_aes_xts_decrypt")
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
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) (by rw [hM])
        (n := "vg_aes_xts_decrypt")
      have l₁ := taint_rel pubRegs decL1_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false okD ctD (n := "vg_aes_xts_decrypt") (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          Inv.sp_eq hq h.1.inv h.2.inv⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp okD nfD h.1, decL2_wp hp' okD nfD h.2⟩
      have l₃ := taint_rel pubRegs decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.sp_eq hq h.1.inv h.2.inv)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false okD ctD (n := "vg_aes_xts_decrypt") (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre, by
          rw [pub_W hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.choose_spec.2.pre,
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp okD nfD h.1.choose_spec.2 h.1.choose_spec.1 hB,
          decLast_wp hp' okD nfD h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ct : XtsCt true Impl.AesXts.PPC64LE.encrypt) :
    ConstantTime isa (unitPPC64LE true).pre (unitPPC64LE true).pub Impl.AesXts.PPC64LEUnit.encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq ok nf ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct (okE : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nfE : Impl.AesXts.PPC64LE.encrypt.noFrames = true) (ctE : XtsCt true Impl.AesXts.PPC64LE.encrypt)
    (okD : XtsOk false Impl.AesXts.PPC64LE.decrypt) (nfD : Impl.AesXts.PPC64LE.decrypt.noFrames = true)
    (ctD : XtsCt false Impl.AesXts.PPC64LE.decrypt) :
    ConstantTime isa (unitPPC64LE false).pre (unitPPC64LE false).pub Impl.AesXts.PPC64LEUnit.decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq okE nfE ctE okD nfD ctD _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.PPC64LE.Unit
