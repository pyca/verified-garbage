module

public import VerifiedGarbage.Proof.AesXts.X86.Unit.Dec
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesXts.X86.Unit.Dec
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# XTS-AES of data units on x86: constant time

Two runs from states that agree on `esp` and the stack arguments are related
piece by piece (`RelCT`), from the correctness proof's states between the
pieces: the taint analysis covers the code between the calls (the swap's
loop with them), from the stack arguments, which every piece reloads, and
`esi`, which holds `b` after `split`; each call is constant time by its
callee's proof (`xcall_rel`), and the one branch, on whether there is a
partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit

/-- A piece the taint analysis covers, with what each run leaves. -/
theorem rel_agree {F F' G G' : State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hag : ∀ s s', F s → F' s' → VG.X86.Taint.Agree τ s s')
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) τ (fun s s' h => hag s s' h.1 h.2) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel {enc : Bool} {f : Impl.Aes.X86.Blocks} (hf : XFn enc f) {P : State → State → Prop}
    {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : BitVec 32, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.gpr .esp = s₂.gpr .esp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (xcall f) s₁ F₁ ∧ WP isa (xcall f) s₂ F₂) :
    RelCT isa P (xcall f) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc hf.ok hf.ct (n := f.name) hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem XPre.of_eq {s : State} {W T D S W' T' D' S' : BitVec 32} {N R R' : Nat} (h : XPre s W' T' D' S' N R')
    (e₁ : W = W') (e₂ : T = T') (e₃ : D = D') (e₄ : S = S') (e₅ : R = R') : XPre s W T D S N R := by
  subst e₁ e₂ e₃ e₄ e₅; exact h

theorem arg_cur {s₀ s : State} (hesp : s.gpr .esp = s₀.gpr .esp) {i : Nat}
    (hm : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) : arg s i = arg s₀ i := by
  show s.mem.readW (argAddr s i) 32 = _
  rw [show argAddr s i = argAddr s₀ i by simp only [argAddr, hesp]]; exact hm

theorem UPre.argsOut {s₀ : State} (hp : UPre s₀) {s : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hwr : s.wr = s₀.wr) : ArgsOut 7 s := by
  have hs : (s₀.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_data hp.data_args.symm
  · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_scr hp.scr_args.symm

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.2 0 (by decide)
theorem pub_K : K s₀ = K s₀' := hq.2 1 (by decide)
theorem pub_R : R s₀ = R s₀' := by rw [R, R, hq.2 2 (by decide)]
theorem pub_D : D s₀ = D s₀' := hq.2 4 (by decide)
theorem pub_S : S s₀ = S s₀' := hq.2 6 (by decide)
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, hq.2 5 (by decide)]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, hq.2 5 (by decide)]
theorem pub_Lv : Lv s₀ = Lv s₀' := by rw [Lv, Lv, pub_D hq, pub_M hq]
theorem pub_Tv : Tv s₀ = Tv s₀' := by rw [Tv, Tv, pub_S hq]
theorem pub_Zv : Zv s₀ = Zv s₀' := by rw [Zv, Zv, pub_S hq]
theorem pub_So {o : Nat} : S s₀ + BitVec.ofNat 32 o = S s₀' + BitVec.ofNat 32 o := by rw [pub_S hq]

variable (hp : UPre s₀) (hp' : UPre s₀')
include hp hp'

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem tagree {rs : List Reg} {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp]; exact hq.1) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by
      rw [arg_cur h₁.esp ((Inv.args hp h₁).val i hi), arg_cur h₂.esp ((Inv.args hp' h₂).val i hi), hq.2 i hi]

theorem tagree₀ : VG.X86.Taint.Agree (argTaint [] (4 + 4 * 7)) s₀ s₀' :=
  agree_argTaint (fun _ h => absurd h List.not_mem_nil) hq.1 (hp.argsOut rfl rfl) (hp'.argsOut rfl rfl) hq.2

theorem tagreeB {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) (e₁ : s₁.gpr .esi = BitVec.ofNat 32 (B s₀))
    (e₂ : s₂.gpr .esi = BitVec.ofNat 32 (B s₀')) : VG.X86.Taint.Agree (argTaint [.esi] (4 + 4 * 7)) s₁ s₂ :=
  tagree hq hp hp' h₁ h₂ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂, pub_B hq]

omit hp hp' in
theorem esp_eq {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : s₁.gpr .esp = s₂.gpr .esp := by
  rw [h₁.esp, h₂.esp]; exact hq.1

end

/-! ## Taint checks -/

theorem pro_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block pro) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem stealPre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 7))
    (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 7)) (.block (nextT ++ argsL zO)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

/-- Before the call on the last whole block of decryption: `Pₘ` and `CC`
swapped into place. -/
def DecL3 (s₀ s : State) : Prop := ∃ m₅, DecMem s₀ m₅ ∧ LastReady tO s₀ s m₅

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel {e : Impl.Aes.X86.Blocks} (he : XFn true e) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (tweak e) fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have p := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := ProPost s₀) (G' := ProPost s₀')
    (argTaint [] (4 + 4 * 7)) (fun s s' e e' => by subst e e'; exact tagree₀ hq hp hp') pro_taint
    (fun s e => by rw [e]; exact pro_wp hp) (fun s e => by rw [e]; exact pro_wp hp')
  have c := xcall_rel he (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre,
      h.2.pre.of_eq (pub_K hq) (pub_Zv hq) (pub_Tv hq) (pub_S hq) (pub_R hq), esp_eq hq h.1.inv h.2.inv⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp he h.1, tcall_wp hp' he h.2⟩)
  exact p.seq c

theorem ready_rel : RelCT isa (fun a b => TwPost s₀ a ∧ TwPost s₀' b) (.block argsAll)
    fun a b => BlocksReady s₀ (M s₀) a ∧ BlocksReady s₀' (M s₀') b :=
  rel_agree (argTaint [] (4 + 4 * 7)) (fun _ _ h₁ h₂ => tagree hq hp hp' h₁.inv h₂.inv fun _ h => absurd h List.not_mem_nil)
    argsAll_taint (fun _ h => ready_wp hp h) (fun _ h => ready_wp hp' h)

theorem blocks_rel {enc : Bool} {f : Impl.Aes.X86.Blocks} (hf : XFn enc f) {N N' : Nat} (hN : 16 * N ≤ Len s₀)
    (hN' : 16 * N' ≤ Len s₀') (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (xcall f)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  (xcall_rel hf
    (fun _ _ h => ⟨_, _, _, _, _, _, h.1.pre,
      (hNN ▸ h.2.pre).of_eq (pub_W hq) (pub_Tv hq) (pub_D hq) (pub_S hq) (pub_R hq),
      esp_eq hq h.1.tw.inv h.2.tw.inv⟩)
    (F₁ := AllPost enc s₀ N) (F₂ := AllPost enc s₀' N')
    fun _ _ h => ⟨WP.mono (blocks_call hp hf hN h.1.tw h.1.pre) fun _ h' => h'.1,
      WP.mono (blocks_call hp' hf hN' h.2.tw h.2.pre) fun _ h' => h'.1⟩)

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (rel_agree (F := Fin enc s₀) (F' := Fin enc s₀') (G := fun _ => True) (G' := fun _ => True)
    (argTaint [] (4 + 4 * 7)) (fun _ _ h₁ h₂ => tagree hq hp hp' h₁.inv h₂.inv fun _ h => absurd h List.not_mem_nil)
    restore_taint (fun _ h => WP.mono (fin_wp hp h.inv) fun _ _ => trivial)
    (fun _ h => WP.mono (fin_wp hp' h.inv) fun _ _ => trivial)).mono
    (fun _ _ h => h) fun _ _ _ => trivial

omit hp hp' in
theorem eval_eq' {s₁ s₂ : State} (h₁ : s₁.zf = some (decide (B s₀ = 0))) (h₂ : s₂.zf = some (decide (B s₀' = 0))) :
    isa.eval .e s₁ = isa.eval .e s₂ := by
  rw [eval_b h₁, eval_b h₂, pub_B hq]

theorem encrypt_rel {f : Impl.Aes.X86.Blocks} (hf : XFn true f) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encrypt f) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq hf
  have a := ready_rel hp hp' hq
  have c := blocks_rel hp hp' hq hf (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) hM
  have sp := rel_agree (F := AllPost true s₀ (M s₀)) (F' := AllPost true s₀' (M s₀'))
    (G := SplitPost true s₀ (M s₀)) (G' := SplitPost true s₀' (M s₀')) (argTaint [] (4 + 4 * 7))
    (fun _ _ h₁ h₂ => tagree hq hp hp' h₁.inv h₂.inv fun _ h => absurd h List.not_mem_nil) split_taint
    (fun _ h => splitAll_wp hp h) (fun _ h => splitAll_wp hp' h)
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite .e (.block []) (encSteal f)) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq' hq h.1.zf h.2.zf) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; rw [eval_b h.1.1.zf] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) (a b : State) =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.zf] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := rel_agree (F := SplitPost true s₀ (M s₀)) (F' := SplitPost true s₀' (M s₀'))
        (G := EncLast s₀) (G' := EncLast s₀') (argTaint [.esi] (4 + 4 * 7))
        (fun _ _ h₁ h₂ => tagreeB hq hp hp' h₁.all.inv h₂.all.inv h₁.esi h₂.esi) stealPre_taint
        (fun _ h => WP.mono (stealPre_wp hp h.all.inv h.esi hB) fun _ h' => ⟨_, h.all.mem, h'⟩)
        (fun _ h => WP.mono (stealPre_wp hp' h.all.inv h.esi hB') fun _ h' => ⟨_, h.all.mem, h'⟩)
      have c := xcall_rel hf (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre,
          h.2.choose_spec.2.pre.of_eq (pub_W hq) (pub_So hq) (pub_Lv hq) (pub_S hq) (pub_R hq),
          esp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp hf h.1.choose_spec.2 h.1.choose_spec.1 hB,
          encLastCall_wp hp' hf h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel {e d : Impl.Aes.X86.Blocks} (he : XFn true e) (hd : XFn false d) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decrypt e d) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq he
  have sp := rel_agree (F := TwPost s₀) (F' := TwPost s₀')
    (G := fun s => TwPost s₀ s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀) ∧ s.zf = some (decide (B s₀ = 0)))
    (G' := fun s => TwPost s₀' s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀') ∧ s.zf = some (decide (B s₀' = 0)))
    (argTaint [] (4 + 4 * 7)) (fun _ _ h₁ h₂ => tagree hq hp hp' h₁.inv h₂.inv fun _ h => absurd h List.not_mem_nil)
    split_taint (fun _ h => split_tw_wp hp h) (fun _ h => split_tw_wp hp' h)
  have br : RelCT isa (fun a b =>
      (TwPost s₀ a ∧ a.gpr .esi = BitVec.ofNat 32 (B s₀) ∧ a.zf = some (decide (B s₀ = 0))) ∧
      (TwPost s₀' b ∧ b.gpr .esi = BitVec.ofNat 32 (B s₀') ∧ b.zf = some (decide (B s₀' = 0))))
      (.ite .e (.seq (.block argsAll) (xcall d)) (decSteal d)) fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq' hq h.1.2.2 h.2.2.2) ?_ ?_
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) (a b : State) => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := ready_rel hp hp' hq
      have c := blocks_rel hp hp' hq hd (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) hM
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨whole_fin h.1 hb, whole_fin h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) (a b : State) =>
          (TwPost s₀ a ∧ a.gpr .esi = BitVec.ofNat 32 (B s₀)) ∧
          (TwPost s₀' b ∧ b.gpr .esi = BitVec.ofNat 32 (B s₀'))) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2.2] at this; simpa using this,
          ⟨h.1.1.1, h.1.1.2.1⟩, ⟨h.1.2.1, h.1.2.2.1⟩⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := rel_agree (F := fun s => TwPost s₀ s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀))
        (F' := fun s => TwPost s₀' s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀'))
        (G := fun s => BlocksReady s₀ (M s₀ - 1) s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀))
        (G' := fun s => BlocksReady s₀' (M s₀' - 1) s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀'))
        (argTaint [] (4 + 4 * 7))
        (fun _ _ h₁ h₂ => tagree hq hp hp' h₁.1.inv h₂.1.inv fun _ h => absurd h List.not_mem_nil) argsHead_taint
        (fun _ h => WP.mono (head_wp hp h.1) fun _ h' => ⟨h'.1, h'.2.trans h.2⟩)
        (fun _ h => WP.mono (head_wp hp' h.1) fun _ h' => ⟨h'.1, h'.2.trans h.2⟩)
      have c₁ : RelCT isa (fun a b => (BlocksReady s₀ (M s₀ - 1) a ∧ a.gpr .esi = BitVec.ofNat 32 (B s₀)) ∧
          (BlocksReady s₀' (M s₀' - 1) b ∧ b.gpr .esi = BitVec.ofNat 32 (B s₀'))) (xcall d)
          fun a b => (AllPost false s₀ (M s₀ - 1) a ∧ a.gpr .esi = BitVec.ofNat 32 (B s₀)) ∧
            (AllPost false s₀' (M s₀' - 1) b ∧ b.gpr .esi = BitVec.ofNat 32 (B s₀')) :=
        xcall_rel hd
          (fun _ _ h => ⟨_, _, _, _, _, _, h.1.1.pre,
            (show M s₀ - 1 = M s₀' - 1 by rw [hM]) ▸ h.2.1.pre |>.of_eq (pub_W hq) (pub_Tv hq) (pub_D hq) (pub_S hq)
              (pub_R hq), esp_eq hq h.1.1.tw.inv h.2.1.tw.inv⟩)
          fun _ _ h => ⟨WP.mono (blocks_call hp hd (by rw [len_eq s₀]; omega) h.1.1.tw h.1.1.pre)
              fun _ h' => ⟨h'.1, h'.2.trans h.1.2⟩,
            WP.mono (blocks_call hp' hd (by rw [len_eq s₀']; omega) h.2.1.tw h.2.1.pre)
              fun _ h' => ⟨h'.1, h'.2.trans h.2.2⟩⟩
      have l₁ := rel_agree (F := fun s => AllPost false s₀ (M s₀ - 1) s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀))
        (F' := fun s => AllPost false s₀' (M s₀' - 1) s ∧ s.gpr .esi = BitVec.ofNat 32 (B s₀'))
        (G := DecL1 s₀) (G' := DecL1 s₀') (argTaint [.esi] (4 + 4 * 7))
        (fun _ _ h₁ h₂ => tagreeB hq hp hp' h₁.1.inv h₂.1.inv h₁.2 h₂.2)
        decL1_taint (fun _ h => decL1_wp hp h.1 h.2) (fun _ h => decL1_wp hp' h.1 h.2)
      have c₂ := xcall_rel hd (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre,
          h.2.pre.of_eq (pub_W hq) (pub_Zv hq) (pub_Lv hq) (pub_S hq) (pub_R hq),
          esp_eq hq h.1.inv h.2.inv⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp hd h.1, decL2_wp hp' hd h.2⟩
      have l₃ := rel_agree (F := DecL2 s₀) (F' := DecL2 s₀') (G := DecL3 s₀) (G' := DecL3 s₀')
        (argTaint [.esi] (4 + 4 * 7)) (fun _ _ h₁ h₂ => tagreeB hq hp hp' h₁.inv h₂.inv h₁.esi h₂.esi)
        stealPre_taint
        (fun _ h => WP.mono (stealPre_wp hp h.inv h.esi hB) fun _ h' => ⟨_, h.mem, h'⟩)
        (fun _ h => WP.mono (stealPre_wp hp' h.inv h.esi hB') fun _ h' => ⟨_, h.mem, h'⟩)
      have c₃ := xcall_rel hd (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre,
          h.2.choose_spec.2.pre.of_eq (pub_W hq) (pub_So hq) (pub_Lv hq) (pub_S hq) (pub_R hq),
          esp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp hd h.1.choose_spec.2 h.1.choose_spec.1 hB,
          decLast_wp hp' hd h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct {f : Impl.Aes.X86.Blocks} (hf : XFn true f) :
    ConstantTime isa (unitX86 true).pre (unitX86 true).pub (encrypt f) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq hf _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct {e d : Impl.Aes.X86.Blocks} (he : XFn true e) (hd : XFn false d) :
    ConstantTime isa (unitX86 false).pre (unitX86 false).pub (decrypt e d) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq he hd _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.X86.Unit
