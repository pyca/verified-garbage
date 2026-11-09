module
-- separate module: the P-521 fast window's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Dbl
public import VerifiedGarbage.Proof.Weierstrass.JacMadd

/-!
# P-521 on x86-64: field programs by the fast steps, and the mixed addition

`fprogF_ok`: a list of field operations by `stepProg` (all into slots below
`p`), as `fprogB_ok`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass
  VG.Proof.Weierstrass.X86_64 Spec.Weierstrass

variable {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

theorem _root_.VG.Proof.Weierstrass.X86_64.Inv.toW {V : List Nat} {E : Nat → Fin m} {s : State} (h : Inv M base size m Sl V E s) :
    InvW M base size m Sl V [] E s :=
  ⟨h, fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (List.not_mem_nil),
    fun _ h => absurd h (List.not_mem_nil)⟩

/-- One operation into a slot below `p`. -/
theorem opF_ok (H : StepCtx M size m Sl) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x ∧ x + 72 ≤ 3520)
    (h1 : op.out ≠ 1) (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (stepProg maddS (.op op)).inline s fun s' => OpKeepF base op.out s s' ∧
      Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      at hS hR h1
    exact WP.mono (mulStepS_ok H hI.toW (by simp [weakOp, maddS, h1]) hS.1.1 hS.1.2 hS.2.1.2 hS.2.2.2 hR.1 hR.2)
      fun s' ⟨k, I⟩ => ⟨k, I.inv⟩
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      at hS hR
    exact WP.mono (addStep_ok H hI.toW hS.1.1 hS.1.2 hS.2.1.2 hS.2.2.2 hR.1 hR.2) fun s' ⟨k, I⟩ => ⟨k, I.inv⟩
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      at hS hR
    exact WP.mono (subStep_ok H hI.toW hS.1.1 hS.1.2 hS.2.1.2 hS.2.2.2 hR.1 hR.2) fun s' ⟨k, I⟩ => ⟨k, I.inv⟩

/-- Operations by the fast steps, as `fprogB_ok`. -/
theorem fprogF_ok (H : StepCtx M size m Sl) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x ∧ x + 72 ≤ 3520) →
      (∀ op ∈ ops, op.out ≠ 1) → readsOk ops V = true →
      WP isa (progs (ops.map fun f => stepProg maddS (.op f))).inline s fun t =>
        KeepW base (ops.map FOp.out) s t ∧ Inv M base size m Sl (validAfter ops V) (runOps ops E) t
  | [], _, _, s, hI, _, _, _ => WP.block_nil ⟨KeepW.refl _ _ s, hI⟩
  | [op], V, E, s, hI, hS, h1, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    exact WP.mono (opF_ok H hI (hS op (List.mem_cons_self ..)) (h1 op (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ⟨KeepW.cons (List.mem_cons_self ..) k₁ (KeepW.refl _ _ _), I₁⟩
  | op :: op' :: ops, V, E, s, hI, hS, h1, hR => by
    rw [readsOk, Bool.and_eq_true, List.all_eq_true] at hR
    simp only [decide_eq_true_eq] at hR
    rw [List.map_cons, List.map_cons, progs_inline_cons]
    refine WP.seq (WP.mono (opF_ok H hI (hS op (List.mem_cons_self ..)) (h1 op (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprogF_ok H (op' :: ops) I₁ (fun o h => hS o (List.mem_cons_of_mem _ h))
      (fun o h => h1 o (List.mem_cons_of_mem _ h)) hR.2) fun s₂ ⟨k₂, I₂⟩ => ⟨?_, I₂⟩
    have k₂' : KeepW base ((op :: op' :: ops).map FOp.out) s₁ s₂ :=
      ⟨k₂.gpr, k₂.rd, k₂.wr, fun x hx ht => k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht⟩
    exact KeepW.cons (List.mem_cons_self ..) k₁ k₂'

/-- `KeepW` with `clob 9` kept as `ProgKeep`. -/
theorem progKeep_of (H : StepCtx M size m Sl) {Ws : List Nat} {s t : State} (k : KeepRegs (clob 9) s t)
    (h : KeepW base Ws s t) : ProgKeep M base Ws s t :=
  ⟨by rw [H.n9]; exact k.gpr, k.rd, k.wr, fun x hx ht => h.mem x (by rw [H.n9] at hx; exact hx)
    (by rw [H.tmp, H.n9] at ht; exact ht)⟩

/-- A field program by the fast steps with `rbx` and `rsi` kept in `xmm15`, `xmm14`. -/
theorem savedF_ok (H : StepCtx M size m Sl) {ops : List FOp} {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hS : ∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x ∧ x + 72 ≤ 3520)
    (h1 : ∀ op ∈ ops, op.out ≠ 1) (hR : readsOk ops V = true)
    (hkb : KeepReg.keeps .rbx (Code.seq (.block save) (.seq (progs (ops.map fun f => stepProg maddS (.op f)))
      (.block restore))).inline = true)
    (hks : KeepReg.keeps .rsi (Code.seq (.block save) (.seq (progs (ops.map fun f => stepProg maddS (.op f)))
      (.block restore))).inline = true) :
    WP isa (Code.seq (.block save) (.seq (progs (ops.map fun f => stepProg maddS (.op f))) (.block restore))).inline s
      fun t => ProgKeep M base (ops.map FOp.out) s t ∧ Inv M base size m Sl (validAfter ops V) (runOps ops E) t := by
  have hw : WP isa (Code.seq (.block save) (.seq (progs (ops.map fun f => stepProg maddS (.op f)))
      (.block restore))).inline s fun t => (∀ r, r ≠ .rbx → r ≠ .rsi → r ∉ fclob → t.gpr r = s.gpr r) ∧
      KeepW base (ops.map FOp.out) s t ∧ Inv M base size m Sl (validAfter ops V) (runOps ops E) t := by
    show WP isa (.seq (.block save) (.seq (progs (ops.map fun f => stepProg maddS (.op f))).inline
      (.block restore))) s _
    refine WP.seq (WP.mono (save_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
    have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hI.scr.rdi, by rw [wr₁]; exact hI.scr.wr, hI.scr.nowrap⟩
    have hI₁ : Inv M base size m Sl V E s₁ :=
      ⟨hs₁, m₁ ▸ hI.mod, hI.sl, fun x hx => m₁ ▸ hI.lt x hx, fun x hx => m₁ ▸ hI.val x hx⟩
    refine WP.seq (WP.mono (fprogF_ok H ops hI₁ hS h1 hR) fun s₂ ⟨k₂, I₂⟩ => ?_)
    refine WP.mono (restore_ok s₂) fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ => ⟨fun r hb hs hr => ?_, ?_, ?_⟩
    · rw [g₃ r hb hs, k₂.gpr r hr, g₁]
    · exact ⟨fun r hr => by
          rw [g₃ r (fun h => hr (h ▸ by decide)) (fun h => hr (h ▸ by decide)), k₂.gpr r hr, g₁],
        by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁],
        fun x hx ht => by rw [m₃, k₂.mem x hx ht, m₁]⟩
    · exact ⟨⟨by rw [g₃ _ (by decide) (by decide)]; exact I₂.scr.rdi, by rw [wr₃]; exact I₂.scr.wr,
        I₂.scr.nowrap⟩, m₃ ▸ I₂.mod, I₂.sl, fun x hx => m₃ ▸ I₂.lt x hx, fun x hx => m₃ ▸ I₂.val x hx⟩
  obtain ⟨tr, t, he, hq⟩ := hw
  refine ⟨tr, t, he, progKeep_of H ⟨fun r hr => ?_, hq.2.1.rd, hq.2.1.wr⟩ hq.2.1, hq.2.2⟩
  by_cases hb : r = .rbx
  · subst hb; exact Exec.gpr_keeps hkb he
  by_cases hs : r = .rsi
  · subst hs; exact Exec.gpr_keeps hks he
  exact hq.1 r hb hs (fclob_sub hr hb hs)

/-- `o = p + q` for an affine `q` by `madd`, as `ofN_ok` for `maddJ`. -/
theorem maddF_ok (H : StepCtx M size m Sl) {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x ∧ x + 72 ≤ 3520 ∧ x ≠ 1) {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V)
    (hkb : KeepReg.keeps .rbx (madd S p q o).inline = true)
    (hks : KeepReg.keeps .rsi (madd S p q o).inline = true) :
    WP isa (madd S p q o).inline s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (maddJ S p q o) E) s' ∧
      (runOps (maddJ S p q o) E o.x, runOps (maddJ S p q o) E o.y, runOps (maddJ S p q o) E o.z) =
        (runOps maddJN (fun y => E (rcbσ S p q o y)) 6, runOps maddJN (fun y => E (rcbσ S p q o y)) 7,
          runOps maddJN (fun y => E (rcbσ S p q o y)) 8) := by
  have hR : readsOk (maddJ S p q o) V = true := by
    rw [maddJ_eq]; exact readsOk_mono (ofN_readsOk maddJN_ok S p q o) hV
  have hS : ∀ op ∈ maddJ S p q o, ∀ x ∈ op.out :: op.ins, Sl x ∧ x + 72 ≤ 3520 := by
    rw [maddJ_eq]; exact fun op hop x hx => ⟨(hSl x (ofN_slots op hop x hx)).1, (hSl x (ofN_slots op hop x hx)).2.1⟩
  have h1 : ∀ op ∈ maddJ S p q o, op.out ≠ 1 := by
    rw [maddJ_eq]; exact fun op hop => (hSl _ (ofN_slots op hop _ (List.mem_cons_self ..))).2.2
  refine WP.mono (savedF_ok H hI hS h1 hR hkb hks) fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    rw [maddJ_eq] at hop
    exact ofN_out maddJN_ok op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · rw [maddJ_eq]; exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx
  · rw [maddJ_eq]
    exact congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 6) (congrArg₂ Prod.mk (ofN_run maddJN_ok hA E 7)
      (ofN_run maddJN_ok hA E 8))

end VG.Proof.Weierstrass.X86_64.P521F
