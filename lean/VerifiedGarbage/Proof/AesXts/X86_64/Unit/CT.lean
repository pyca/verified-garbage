module
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Enc

import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Dec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Enc
meta import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Dec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# XTS-AES of data units on x86-64: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), from the correctness proof's states between the pieces: the
taint analysis covers the code between the calls (the swap's loop with
them), from the registers the states pin to public values (`Inv.agree`),
each call is constant time by its callee's proof (`xcall_rel`), and the one
branch, on whether there is a partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc.X86_64 (modeX86_64)

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.gpr .rsp = s₂.gpr .rsp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_rdx : s₀.gpr .rdx = s₀'.gpr .rdx := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rdx hq]
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.1
theorem pub_r9 : s₀.gpr .r9 = s₀'.gpr .r9 := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_r9 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_r9 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pinned, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rdx hq]
  · rw [h₁.r12, h₂.r12, pub_D hq]
  · rw [h₁.r13, h₂.r13, pub_r9 hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]
  · rw [h₁.rsp, h₂.rsp, pub_rsp hq]

omit hq in
/-- Agreement on the pinned registers and more. -/
theorem agree_cons {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ pinned, s₁.gpr r = s₂.gpr r)
    (h' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : ∀ r ∈ rs ++ pinned, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h' r hr
  · exact h r hr

end

/-! ## Taint checks -/

theorem ldS_taint : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block ldS) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (.block pro) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.rax, .r8] : List Reg) ++ pinned))
    (.seq (.seq (.block stealPre) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pinned)
    (.block (nextT ++ split ++ lastAddr ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pinned)
    (.seq (.seq (.block (split ++ stealPre)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel (v : XtsImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (tweak v.enc) fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have l := taint_rel [.rsp] ldS_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_singleton] at hr; subst hr; exact pub_rsp hq)
    (F₁ := fun s => s = s₀.setReg .rax (S s₀)) (F₂ := fun s => s = s₀'.setReg .rax (S s₀'))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨ldS_wp hp, ldS_wp hp'⟩
  have p := taint_rel [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] pro_taint
    (P := fun a b => a = s₀.setReg .rax (S s₀) ∧ b = s₀'.setReg .rax (S s₀'))
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      have hq' := hq
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, pub_S hq]
      all_goals rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide)]
      all_goals with_reducible assumption)
    (F₁ := ProPost s₀) (F₂ := ProPost s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨pro_wp hp, pro_wp hp'⟩
  have c := xcall_rel true v.encOk v.encCt (n := v.enc.name) (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_S hq, pub_R hq]; exact h.2.pre,
      by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp v.encOk v.encNosp v.encDepth h.1, tcall_wp hp' v.encOk v.encNosp v.encDepth h.2⟩)
  exact (l.mono (fun _ _ h => h) fun _ _ h => h).seq (p.seq c)

theorem blocks_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub c)
    (nosp : NoSp c) (depth : c.depth ≤ 1) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀')
    (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (.call n c)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xcall_rel enc ok ct
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_W hq, pub_Tp hq, pub_D hq, pub_S hq, hNN, pub_R hq]; exact h.2.pre,
      by rw [h.1.tw.inv.rsp, h.2.tw.inv.rsp, pub_rsp hq]⟩)
    fun a b h => ⟨blocks_call hp enc ok nosp depth hN h.1.tw h.1.pre, blocks_call hp' enc ok nosp depth hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (taint_rel [.r15] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.r15, h.2.inv.r15, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial, WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

theorem encrypt_rel (v : XtsImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (Impl.AesXts.X86_64Unit.encrypt v.xts) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have a := taint_rel pinned argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocks_rel hp hp' hq true v.encOk v.encCt v.encNosp v.encDepth (by rw [len_eq s₀]; omega)
    (by rw [len_eq s₀']; omega) hM (n := v.enc.name)
  have sp := taint_rel pinned split_taint (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitAll_wp hp h.1, splitAll_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite .e (.block []) (encSteal v.enc)) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.zf, h.2.zf, pub_B hq]
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.rax, .r8] ++ pinned) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => agree_cons (Inv.agree hq h.1.all.inv h.2.all.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.rax, h.2.rax, hM]
          · rw [h.1.r8, h.2.r8, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true v.encOk v.encCt (n := v.enc.name) (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp v h.1 hB, encLastCall_wp hp' v h.2 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel (v : XtsImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (Impl.AesXts.X86_64Unit.decrypt v.xts) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have sp := taint_rel pinned split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.zf = some (decide (B s₀ = 0)))
    (F₂ := fun s => TwPost s₀' s ∧ s.zf = some (decide (B s₀' = 0)))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.zf = some (decide (B s₀ = 0))) ∧
      (TwPost s₀' b ∧ b.zf = some (decide (B s₀' = 0))))
      (.ite .e (.seq (.block argsAll) (.call v.dec.name v.dec.code)) (decSteal v.dec))
      fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, pub_B hq]
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := taint_rel pinned argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀))
        (F₂ := BlocksReady s₀' (M s₀')) fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
      have c := blocks_rel hp hp' hq false v.decOk v.decCt v.decNosp v.decDepth (by rw [len_eq s₀]; omega)
        (by rw [len_eq s₀']; omega) hM (n := v.dec.name)
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨whole_fin h.1 hb, whole_fin h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := taint_rel pinned argsHead_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀ - 1))
        (F₂ := BlocksReady s₀' (M s₀' - 1)) fun a b h => ⟨argsHead_wp hp h.1, argsHead_wp hp' h.2⟩
      have c₁ := blocks_rel hp hp' hq false v.decOk v.decCt v.decNosp v.decDepth (N := M s₀ - 1)
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) (by rw [hM]) (n := v.dec.name)
      have l₁ := taint_rel pinned decL1_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false v.decOk v.decCt (n := v.dec.name) (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp v h.1, decL2_wp hp' v h.2⟩
      have l₃ := taint_rel pinned decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false v.decOk v.decCt (n := v.dec.name) (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀') fun a b h => ⟨decLast_wp hp v h.1 hB, decLast_wp hp' v h.2 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct (v : XtsImpl) :
    ConstantTime isa (unitX86_64 true).pre (unitX86_64 true).pub (Impl.AesXts.X86_64Unit.encrypt v.xts) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct (v : XtsImpl) :
    ConstantTime isa (unitX86_64 false).pre (unitX86_64 false).pub (Impl.AesXts.X86_64Unit.decrypt v.xts) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.X86_64.Unit
