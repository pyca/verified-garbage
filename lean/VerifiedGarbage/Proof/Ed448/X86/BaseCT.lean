import VerifiedGarbage.Proof.Ed448.X86.BaseMain
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified

/-!
# Ed448 base-point multiplication on x86 (32-bit): constant time

The calls of the field functions are related run by run (`RelCT`,
`Proof/X448/X86/Runs.lean`), and so is the whole function: the entry block
from the arguments (`scalarTaint`), the field programs by the field
functions' constant time, the swaps, the counter and the encoding's last
block by the taint analysis from what each run's correctness says of its own
state (`BaseMain.lean`'s stages), and the loop and the inversion's runs of
squarings by `RelCT.loop`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (scalarBase baseLoop baseStep baseSwap baseEncode toOp field initSlots baseBits)
open VG.Impl.Ed448 (doubleOps addOps)

/-- Two entry states the constant-time statement relates. -/
def BP₀ (σ₁ σ₂ : State) : Prop :=
  scalarBaseLocal.pre σ₁ ∧ scalarBaseLocal.pre σ₂ ∧ scalarBaseLocal.pub σ₁ σ₂

theorem BP₀.hp {σ₁ σ₂ : State} (h : BP₀ σ₁ σ₂) : bsB σ₁ = bsB σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp :=
  ⟨by simp only [bsB, h.2.2.2.2.2], h.2.2.1⟩

/-! ## The entry -/

theorem scalarBase_wf {s : State} (h : scalarBaseLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  have hp := BasePre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarBase_agree {s t : State} (hs : scalarBaseLocal.pre s) (ht : scalarBaseLocal.pre t)
    (hp : scalarBaseLocal.pub s t) : VG.X86.Taint.Agree (scalarTaint 2 3) s t := by
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := BasePre.of hs
  have pt := BasePre.of ht
  refine scalarTaint_agree (scalarBase_wf hs) (scalarBase_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

/-! ## The loop -/

/-- `n + 1` iterations left. -/
def LadB (n : Nat) (σ s : State) : Prop := n < 456 ∧ ∃ s₄, BL σ s₄ s (n + 1)

/-- After an iteration's counter. -/
def StepB (n : Nat) (σ t : State) : Prop := FE bsB σ t ∧ t.gpr .esi = BitVec.ofNat 32 n

theorem fieldB_rel (n : Nat) (l : List Impl.Ed448.FOp) (xs : List FieldOp)
    (hl : l.map toOp = xs.map FieldOp.impl) :
    RelCT isa (Runs BP₀ (StepB n)) (field l) (Runs BP₀ (StepB n)) := by
  rw [field, hl]
  exact Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.1.fs) xs) fun σ s h =>
    WP.mono (ops_FE h.1 xs) fun t ⟨fe, k, _⟩ => ⟨fe, (k.regs.1 _ (by decide)).trans h.2⟩

theorem baseStep_tr (n : Nat) : RelCT isa (Runs BP₀ (LadB n)) baseStep fun _ _ => True := by
  unfold baseStep
  refine RelCT.seq (Runs.step (G := StepB n) (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    (RelCT.seq (fieldB_rel n _ _ doubleFields_impl) (RelCT.seq (fieldB_rel n _ _ addFields_impl) ?_))
  · rintro σ s ⟨hn, s₄, h⟩
    refine WP.mono (h.2.2.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
      (Q := fun t => t.gpr .esi = BitVec.ofNat 32 n)
      (WP.mono (decCounter_ok (by omega) h.2.1.esi) fun t ⟨c, g, m, r, w, _⟩ =>
        ⟨FInv.of_counter h.2.2.fin g m r w, g _ (by decide), w, c⟩)) fun t ⟨fe, c⟩ => ⟨fe, c⟩
  · refine RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) ?_ (by taint_decide)
    rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨f₁, c₁⟩, ⟨f₂, c₂⟩⟩
    refine agree_regs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact f₁.sp.trans (hP.hp.2.trans f₂.sp.symm)
    · exact c₁.trans c₂.symm
    · exact edi_eq f₁.fin.scr (hP.hp.1 ▸ f₂.fin.scr)

theorem baseLoop_rel : ∀ n, RelCT isa (Runs BP₀ (LadB n)) (.loop baseStep .ne)
    (Runs BP₀ fun σ s => ∃ s₄, BL σ s₄ s 0) := by
  refine RelCT.loop (M := isa) (fun n => Runs BP₀ (LadB n)) fun n => ?_
  refine Runs.then (G := fun σ t => (n < 456 ∧ ∃ s₄, BL σ s₄ t n) ∧ t.zf = some (decide (n = 0)))
    (fun _ _ h => h) (baseStep_tr n) ?_ ?_
  · rintro σ s ⟨hn, s₄, h⟩
    exact WP.mono (step_stage hn h) fun t ⟨l, z⟩ => ⟨⟨hn, s₄, l⟩, z⟩
  · rintro σ₁ σ₂ t₁ t₂ hP - ⟨l₁, z₁⟩ ⟨l₂, z₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun hz => ⟨σ₁, σ₂, hP, ?_, ?_⟩, fun hz => ?_⟩
    · have : n = 0 := by simpa using hz
      subst this; exact l₁.2
    · have : n = 0 := by simpa using hz
      subst this; exact l₂.2
    · have hn0 : n ≠ 0 := fun h0 => by simp [h0] at hz
      obtain ⟨hn, a₁, L₁⟩ := l₁
      obtain ⟨-, a₂, L₂⟩ := l₂
      have e : n - 1 + 1 = n := by omega
      exact ⟨n - 1, by omega, σ₁, σ₂, hP, ⟨by omega, a₁, e ▸ L₁⟩, ⟨by omega, a₂, e ▸ L₂⟩⟩

/-! ## The whole function -/

theorem baseEntry_rel :
    RelCT isa (Runs BP₀ fun σ s => s = σ ∧ BasePre σ)
      (.block (Impl.Ed448.X86.save 12 ++ initSlots ++ baseBits)) (Runs BP₀ BMid) := by
  refine Runs.step (RelCT.taint (A := taint) (scalarTaint 2 3) ?_ (by taint_decide))
    fun σ s ⟨e, h⟩ => by subst e; exact entry_stage h
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨rfl, -⟩, ⟨rfl, -⟩⟩
  exact scalarBase_agree hP.1 hP.2.1 hP.2.2

theorem baseLoopAll_rel : RelCT isa (Runs BP₀ BMid) baseLoop (Runs BP₀ fun σ s => ∃ s₄, BL σ s₄ s 0) := by
  unfold baseLoop
  refine RelCT.seq (Runs.step (G := LadB 455) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_) (baseLoop_rel 455)
  intro σ s m
  refine WP.mono (setCounter_ok s 456 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨by decide, s, m, m.start t h1 h2 h3 h4 h5, ?_⟩
  exact ⟨FInv.of_counter m.fe.fin h2 h3 h4 h5, (h2 _ (by decide)).trans m.fe.sp, h5.trans m.fe.wr,
    by rw [h3]; exact m.fe.frame⟩

theorem baseEncode_tr : RelCT isa (Runs BP₀ fun σ s => ∃ s₄, BL σ s₄ s 0) baseEncode fun _ _ => True := by
  unfold baseEncode
  refine RelCT.seq (Runs.step (G := FE bsB)
    (rf_tr (fun _ _ h => h.hp) (fun _ _ ⟨_, h⟩ => h.2.2.fs) invert_rel) ?_)
    (RelCT.seq (R := Runs BP₀ (FE bsB)) ?_ ?_)
  · rintro σ s ⟨_, h⟩
    exact WP.mono (h.2.2.wp (NoSp.of_all (by lit_decide)) (by lit_decide) (Q := fun _ => True)
      (WP.mono (invert_ok h.2.2.fin.scr h.2.2.fin.ctx h.2.2.fin.bounded) fun t ⟨k, b, _⟩ =>
        ⟨⟨k.scr h.2.2.fin.scr, k.ctx h.2.2.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, trivial⟩))
      fun t ⟨fe, _⟩ => fe
  · rw [encodeFields_impl]
    exact Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.fs) encodeFields) fun σ s h =>
      WP.mono (ops_FE h encodeFields) fun t ⟨fe, _⟩ => fe
  · refine RelCT.taint (A := taint) (τa 16) ?_ (by taint_decide)
    rintro s₁ s₂ ⟨σ₁, σ₂, hP, f₁, f₂⟩
    have p₁ := BasePre.of hP.1
    have p₂ := BasePre.of hP.2.1
    have a := scalarBase_agree hP.1 hP.2.1 hP.2.2
    have wr : ∀ {σ : State}, BasePre σ → ∀ r ∈ σ.wr, Region.Disjoint ⟨(σ.gpr .esp).setWidth 64, 16⟩ r := by
      intro σ p r hr
      have := p.sp_fit
      rw [p.wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) p.ret_out p.args_out
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) p.ret_sc p.args_sc
    have ad : ∀ {σ : State}, BasePre σ → ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20],
        (⟨argAddr σ 0, 16 - 4⟩ : Region).Disjoint r := by
      intro σ p r hr
      rw [p.wr, ← stkR_below p.sp_room] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.args_out
      · exact p.args_sc
      · exact p.stk_args.symm
    exact f₁.agreeA f₂ hP.hp.1 hP.hp.2 (by have := p₁.sp_fit; omega) (by have := p₂.sp_fit; omega)
      (wr p₁) (wr p₂) (ad p₁) (ad p₂) fun k h4 hk => by
        have := a.argMem k h4 hk
        simpa only [scalarTaint, VG.X86.Taint.depth, Nat.zero_add] using this

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    ((?_ : RelCT isa (Runs BP₀ fun σ s => s = σ ∧ BasePre σ) scalarBase fun _ _ => True).mono
      (fun s₁ s₂ h => ⟨s₁, s₂, h, ⟨rfl, BasePre.of h.1⟩, ⟨rfl, BasePre.of h.2.1⟩⟩) fun _ _ h => h)
  unfold scalarBase
  exact baseEntry_rel.seq (baseLoopAll_rel.seq baseEncode_tr)

end VG.Proof.Ed448.X86
