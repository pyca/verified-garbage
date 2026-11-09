module

public import VerifiedGarbage.Proof.AesXts.X86_64.UnitTo.Crypt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.To.Copy
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.CT
import VerifiedGarbage.Proof.AesXts.X86_64.CT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesXts.X86_64.UnitTo.Crypt
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesXts.X86_64.Unit.CT
meta import VerifiedGarbage.Proof.AesXts.X86_64.CT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# XTS-AES of data units out of place on x86-64: constant time and `Verified`

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), from the correctness proof's states between the pieces, as
in place (`Unit/CT.lean`): the taint analysis covers the code between the
calls (the copy and the swap's loop with them), from the registers the
states pin to public values (`Inv.agree`), each call is constant time by its
callee's proof, and the one branch, on whether there is a partial block,
agrees in both runs. Correctness and constant time give `Verified` for the
shared contracts of `Spec/Xts/OutOfPlace.lean`, with 24 bytes of stack (the
return addresses of the out-of-place whole-block function, of its call of
an in-place one, and of that one's call of a block function).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.UnitTo

open VG VG.X86_64 VG.Impl.AesXts.X86_64Unit
open VG.Impl.AesXts.X86_64UnitTo renaming ldS → ldSTo, setup → setupTo, pro → proTo, tweak → tweakTo,
  argsAll → argsAllTo, argsHead → argsHeadTo, encrypt → encryptTo, decrypt → decryptTo
open VG.Impl.AesXts.X86_64UnitTo (copyRest wholeBytes headBytes decStealTail)
open VG.Proof.AesCbc.X86_64 (modeX86_64)
open VG.Proof.AesXts.X86_64 (taint_rel)
open VG.Proof.AesXts.X86_64.To (xtsToX86_64 XtPre xtsTo_rel)
open VG.Proof.AesXts.X86_64.Unit (xcall_rel)

/-- An out-of-place call, with the same arguments in both runs, and what each
run leaves. -/
theorem xtcall_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (xtsToX86_64 enc).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s')
    (ct : ConstantTime isa (xtsToX86_64 enc).pre (xtsToX86_64 enc).pub c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T Sr D S : Addr, ∃ N R : Nat,
      XtPre s₁ W T Sr D S N R ∧ XtPre s₂ W T Sr D S N R ∧ s₁.gpr .rsp = s₂.gpr .rsp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xtsTo_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_rdx : s₀.gpr .rdx = s₀'.gpr .rdx := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rdx hq]
theorem pub_Sr : Sr s₀ = Sr s₀' := hq.2.2.2.2.1
theorem pub_r9 : s₀.gpr .r9 = s₀'.gpr .r9 := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2.1
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_r9 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_r9 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pinned, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rdx hq]
  · rw [h₁.r12, h₂.r12, pub_D hq]
  · rw [h₁.r13, h₂.r13, pub_r9 hq]
  · rw [h₁.r14, h₂.r14, pub_Sr hq]
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

theorem ldS_taint : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block ldSTo) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (.block proTo) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsAllTo) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsHeadTo) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem copyAll_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.seq (.block wholeBytes) copyRest) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem copyHead_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.seq (.block headBytes) copyRest) h).isSome =
    true := ⟨_, by taint_decide⟩

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

theorem tweak_rel (v : UnitImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (tweakTo v.x.enc) fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
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
  have c := xcall_rel true v.x.encOk v.x.encCt (n := v.x.enc.name)
    (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_S hq, pub_R hq]; exact h.2.pre,
      by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp v.x.encOk v.x.encNosp v.x.encDepth h.1,
      tcall_wp hp' v.x.encOk v.x.encNosp v.x.encDepth h.2⟩)
  exact (l.mono (fun _ _ h => h) fun _ _ h => h).seq (p.seq c)

theorem blocksTo_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (xtsToX86_64 enc).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s')
    (ct : ConstantTime isa (xtsToX86_64 enc).pre (xtsToX86_64 enc).pub c)
    (nosp : NoSp c) (depth : c.depth ≤ 2) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀')
    (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (.call n c)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xtcall_rel enc ok ct
    (fun a b h => ⟨_, _, _, _, _, _, _, h.1.pre, by
      rw [pub_W hq, pub_Tp hq, pub_Sr hq, pub_D hq, pub_S hq, hNN, pub_R hq]; exact h.2.pre,
      by rw [h.1.tw.inv.rsp, h.2.tw.inv.rsp, pub_rsp hq]⟩)
    fun a b h => ⟨blocks_call hp enc ok nosp depth hN h.1.tw h.1.pre,
      blocks_call hp' enc ok nosp depth hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (taint_rel [.r15] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.r15, h.2.inv.r15, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial,
      WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

theorem encrypt_rel (v : UnitImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encryptTo v.x.xts v.xt) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have a := taint_rel pinned argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocksTo_rel hp hp' hq true v.encToOk v.encToCt v.encToNosp v.encToDepth (by rw [len_eq s₀]; omega)
    (by rw [len_eq s₀']; omega) hM (n := v.encTo.name)
  have cp := taint_rel pinned copyAll_taint
    (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := Copied true s₀ (M s₀)) (F₂ := Copied true s₀' (M s₀'))
    fun a b h => ⟨copiedAll_wp hp h.1, copiedAll_wp hp' h.2⟩
  have sp := taint_rel pinned split_taint
    (P := fun a b => Copied true s₀ (M s₀) a ∧ Copied true s₀' (M s₀') b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitCopied_wp hp h.1, splitCopied_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite .e (.block []) (encSteal v.x.enc)) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.zf, h.2.zf, pub_B hq]
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this
      exact ⟨whole_fin h.1.1.cp hb, whole_fin h.1.2.cp (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.rax, .r8] ++ pinned) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => agree_cons (Inv.agree hq h.1.cp.inv h.2.cp.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.rax, h.2.rax, hM]
          · rw [h.1.r8, h.2.r8, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true v.x.encOk v.x.encCt (n := v.x.enc.name)
        (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp v h.1 hB, encLastCall_wp hp' v h.2 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (cp.seq (sp.seq (br.seq (restore_rel hp hp' hq))))))

theorem decrypt_rel (v : UnitImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decryptTo v.x.xts v.xt) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have sp := taint_rel pinned split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.zf = some (decide (B s₀ = 0)))
    (F₂ := fun s => TwPost s₀' s ∧ s.zf = some (decide (B s₀' = 0)))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.zf = some (decide (B s₀ = 0))) ∧
      (TwPost s₀' b ∧ b.zf = some (decide (B s₀' = 0))))
      (.ite .e (.seq (.block argsAllTo) (.call v.decTo.name v.decTo.code))
        (.seq (.block argsHeadTo) (.seq (.call v.decTo.name v.decTo.code)
          (.seq (.seq (.block headBytes) copyRest) (decStealTail v.x.dec)))))
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
      have c := blocksTo_rel hp hp' hq false v.decToOk v.decToCt v.decToNosp v.decToDepth
        (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) hM (n := v.decTo.name)
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨allPost_fin hp h.1 hb, allPost_fin hp' h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := taint_rel pinned argsHead_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀ - 1))
        (F₂ := BlocksReady s₀' (M s₀' - 1)) fun a b h => ⟨argsHead_wp hp h.1, argsHead_wp hp' h.2⟩
      have c₁ := blocksTo_rel hp hp' hq false v.decToOk v.decToCt v.decToNosp v.decToDepth (N := M s₀ - 1)
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) (by rw [hM])
        (n := v.decTo.name)
      have cp := taint_rel pinned copyHead_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := Copied false s₀ (M s₀ - 1))
        (F₂ := Copied false s₀' (M s₀' - 1)) fun a b h => ⟨copiedHead_wp hp h.1, copiedHead_wp hp' h.2⟩
      have l₁ := taint_rel pinned decL1_taint
        (P := fun a b => Copied false s₀ (M s₀ - 1) a ∧ Copied false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false v.x.decOk v.x.decCt (n := v.x.dec.name)
        (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp v h.1, decL2_wp hp' v h.2⟩
      have l₃ := taint_rel pinned decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false v.x.decOk v.x.decCt (n := v.x.dec.name)
        (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp v h.1 hB, decLast_wp hp' v h.2 hB'⟩
      exact a.seq (c₁.seq (cp.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃)))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct (v : UnitImpl) :
    ConstantTime isa (unitToX86_64 true).pre (unitToX86_64 true).pub (encryptTo v.x.xts v.xt) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct (v : UnitImpl) :
    ConstantTime isa (unitToX86_64 false).pre (unitToX86_64 false).pub (decryptTo v.x.xts v.xt) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem encrypt_mx (v : UnitImpl) : (encryptTo v.x.xts v.xt).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encryptTo, tweakTo, encSteal, swap, copyRest, Code.allInstrs, v.x.encMxcsr, v.encToMxcsr]
  decide +kernel

theorem decrypt_mx (v : UnitImpl) : (decryptTo v.x.xts v.xt).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decryptTo, tweakTo, decStealTail, swap, copyRest, Code.allInstrs, v.x.encMxcsr, v.x.decMxcsr,
    v.decToMxcsr]
  decide +kernel

theorem encrypt_spSafe (v : UnitImpl) : (encryptTo v.x.xts v.xt).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encryptTo, tweakTo, encSteal, swap, copyRest, Code.all, v.x.encSpSafe, v.encToSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : UnitImpl) : (decryptTo v.x.xts v.xt).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decryptTo, tweakTo, decStealTail, swap, copyRest, Code.all, v.x.encSpSafe, v.x.decSpSafe,
    v.decToSpSafe]
  decide +kernel

theorem encrypt_correct (v : UnitImpl) (s : State) (hs : (unitToX86_64 true).pre s) :
    ∃ t s', Exec isa (encryptTo v.x.xts v.xt) s t s' ∧ abiPreserved s s' ∧ (unitToX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : UnitImpl) (s : State) (hs : (unitToX86_64 false).pre s) :
    ∃ t s', Exec isa (decryptTo v.x.xts v.xt) s t s' ∧ abiPreserved s s' ∧ (unitToX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
from `0x4000` to `0x5000` (the first stack argument), and the scratch buffer
at 0 (the third, zero). -/
def unitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 10 | .rcx => 0x3000 | .r8 => 0x4000 | .r9 => 16
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8009 then 0x50 else if a = 0x8010 then 16 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩, ⟨0x4000, 16⟩, ⟨0x8008, 24⟩]
  wr := [⟨0x5000, 16⟩, ⟨0, 2432⟩]

theorem encrypt_verified (v : UnitImpl) :
    Verified X86_64.target (encryptTo v.x.xts v.xt) (Spec.Xts.aesEncryptUnitToContract X86_64.abi 24) :=
  Verified.of_correct (encrypt_correct v) (encrypt_ct v) (by
    sig_implies [Spec.Xts.aesEncryptUnitToContract, Spec.Xts.aesUnitToSig, Spec.Xts.aesUnitToPre,
      Spec.Xts.aesEncryptUnitToPost, unitToX86_64, unitPre, unitPub, Unit.xtsOf, W, K, R, I, Sr, Len, D, DLen, S,
      schR, tschR, iR, srcR, dstR, scrR, argR, retR, To.stk3, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : UnitImpl) :
    Verified X86_64.target (decryptTo v.x.xts v.xt) (Spec.Xts.aesDecryptUnitToContract X86_64.abi 24) :=
  Verified.of_correct (decrypt_correct v) (decrypt_ct v) (by
    sig_implies [Spec.Xts.aesDecryptUnitToContract, Spec.Xts.aesUnitToSig, Spec.Xts.aesUnitToPre,
      Spec.Xts.aesDecryptUnitToPost, unitToX86_64, unitPre, unitPub, Unit.xtsOf, W, K, R, I, Sr, Len, D, DLen, S,
      schR, tschR, iR, srcR, dstR, scrR, argR, retR, To.stk3, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

/-! ## Instances -/

/-- The whole-block functions of `x`, with its out-of-place ones
(`XtsImpl.to`). -/
def UnitImpl.of (x : Proof.AesXts.X86_64.XtsImpl) : UnitImpl where
  x := x
  encTo := x.to.enc
  encToDepth := x.to.encDepth
  encToOk := x.to.encOk
  encToCt := x.to.encCt
  encToNosp := x.to.encNosp
  encToMxcsr := x.to.encMxcsr
  encToSpSafe := x.to.encSpSafe
  decTo := x.to.dec
  decToDepth := x.to.decDepth
  decToOk := x.to.decOk
  decToCt := x.to.decCt
  decToNosp := x.to.decNosp
  decToMxcsr := x.to.decMxcsr
  decToSpSafe := x.to.decSpSafe

end VG.Proof.AesXts.X86_64.UnitTo
