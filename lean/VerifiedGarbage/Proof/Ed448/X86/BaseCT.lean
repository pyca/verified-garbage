module

public import VerifiedGarbage.Proof.Ed448.X86.BaseMain
meta import VerifiedGarbage.Proof.Ed448.X86.BaseMain
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
meta import VerifiedGarbage.Proof.Ed448.X86.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
meta import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
import VerifiedGarbage.Proof.X448.X86.Counters
meta import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Iter
meta import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.Carry
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Step
meta import VerifiedGarbage.Proof.Ed448.ScalarWords
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X25519.X86.Basic
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.X86.Carry
meta import VerifiedGarbage.Proof.X448.X86.Columns
meta import VerifiedGarbage.Proof.X448.X86.Copy
meta import VerifiedGarbage.Proof.X448.X86.FnVerified
meta import VerifiedGarbage.Proof.X448.X86.Frame
meta import VerifiedGarbage.Proof.X448.X86.Freeze
meta import VerifiedGarbage.Proof.X448.X86.Restore
meta import VerifiedGarbage.Proof.X448.X86.Select
meta import VerifiedGarbage.Proof.X448.X86.Small
meta import VerifiedGarbage.Proof.X448.X86.Step

/-!
# Ed448 base-point multiplication on x86 (32-bit): constant time

The calls of the field functions are related run by run (`RelCT`,
`Proof/X448/X86/Runs.lean`), and so is the whole function: the entry block
from the arguments (`scalarTaint`), the field programs by the field
functions' constant time, the selection of the comb's entry (a scan of every
entry under masks), the counter and the encoding's last block by the taint
analysis from what each run's correctness says of its own state
(`BaseMain.lean`'s stages), and the loop and the inversion's runs of
squarings by `RelCT.loop`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (scalarBase combLoop combStep combSelect baseEncode toOp field initSlots baseEntry)
open VG.Impl.Ed448 (doubleOps addOps)
open VG.Impl.X448.X86 (BITS ACC ops)

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

/-- `n + 1` rows left. -/
def LadB (n : Nat) (σ s : State) : Prop := n < 114 ∧ ∃ s₄, BL σ s₄ s (n + 1)

/-- The scalar's bits, a byte each at `BITS`. -/
def BitsB (σ t : State) : Prop :=
  ∀ i < 456, t.mem (off (bsB σ) (BITS + i)) = BitVec.ofNat 8 ((kB σ >>> i) &&& 1)

/-- The field operations keep the bytes at `BITS`. -/
theorem BitsB.keep {σ s t : State} (h : BitsB σ s) (k : Keep (bsB σ) s t) : BitsB σ t := fun i hi => by
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  rw [k.mem _ (by rw [ofs_off' _ (by omega_using [hi, hB])]; omega_using [hi, hB])
    (by rw [ofs_off' _ (by omega_using [hi, hB])]; omega_using [hB])
    (by rw [ofs_off' _ (by omega_using [hi, hB])]; omega_using [hi, hB, hA])]
  exact h i hi

/-- In row `n`, after its counter. -/
def StepB (n : Nat) (σ t : State) : Prop :=
  FE bsB σ t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧ n < 114 ∧ BitsB σ t

theorem fieldB_rel (n : Nat) (l : List Impl.X448.X86.Op) (xs : List FieldOp)
    (hl : l = xs.map FieldOp.impl) :
    RelCT isa (Runs BP₀ (StepB n)) (ops l) (Runs BP₀ (StepB n)) := by
  rw [hl]
  exact Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.1.fs) xs) fun σ s h =>
    WP.mono (ops_FE h.1 xs) fun t ⟨fe, k, _⟩ => ⟨fe, (k.regs.1 _ (by decide)).trans h.2.1, h.2.2.1, h.2.2.2.keep k⟩

theorem agreeB {n : Nat} {s₁ s₂ : State} (h : Runs BP₀ (StepB n) s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .esi, .edi]) s₁ s₂ := by
  obtain ⟨σ₁, σ₂, hP, ⟨f₁, c₁, -⟩, ⟨f₂, c₂, -⟩⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact f₁.sp.trans (hP.hp.2.trans f₂.sp.symm)
  · exact c₁.trans c₂.symm
  · exact edi_eq f₁.fin.scr (hP.hp.1 ▸ f₂.fin.scr)

/-- The selection of the row's entry keeps what the field operations need. -/
theorem selectB_ok {n : Nat} {σ s : State} (h : StepB n σ s) :
    WP isa (.block (Impl.Ed448.X86.combDigit BITS ++ combSelect)) s (StepB n σ) := by
  obtain ⟨fe, c, hn, bits⟩ := h
  have hB : BITS = 3072 := rfl
  refine WP.mono (fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => Keep (bsB σ) s t) ?_) fun t ⟨fe', k⟩ =>
      ⟨fe', (k.regs.1 _ (by decide)).trans c, hn, bits.keep k⟩
  rw [WP.block_append_iff]
  refine WP.mono (combDigit_ok fe.fin.scr (by omega_using [hB]) hn c bits) fun u ⟨d, ku, mu⟩ => ?_
  obtain hsu := fe.fin.scr.of_keeps ku (by decide)
  obtain K : Keep (bsB σ) s u := ⟨ku.mono (by decide), by rw [mu]; exact WsOut2.refl _ _ _ _ _ _⟩
  refine WP.mono (combSelect_ok hsu (mu ▸ fe.fin.bounded) (Proof.Ed448.combDigit_lt (kB σ) n) d)
    fun t ⟨kt, bt, _⟩ => ?_
  obtain K' := K.trans kt
  exact ⟨⟨K'.scr fe.fin.scr, K'.ctx fe.fin.ctx, bt⟩, K'.regs.1 _ (by decide), K'.regs.2.2, K'⟩

theorem combStep_tr (n : Nat) : RelCT isa (Runs BP₀ (LadB n)) combStep fun _ _ => True := by
  unfold combStep
  refine RelCT.seq (Runs.step (G := StepB n) (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    (RelCT.seq (fieldB_rel n _ _ doubleFields_impl)
      (RelCT.seq (Runs.step (G := StepB n)
          (RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => agreeB h) (by taint_decide))
          fun _ _ h => selectB_ok h)
        (RelCT.seq (fieldB_rel n _ _ addTake_impl)
          (RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => agreeB h) (by taint_decide)))))
  rintro σ s ⟨hn, s₄, h⟩
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  obtain bits : BitsB σ s := fun i hi => by
    rw [h.2.1.mem _ (by rw [ofs_off' _ (by omega_using [hi, hB])]; omega_using [hi, hB])
      (by rw [ofs_off' _ (by omega_using [hi, hB])]; omega_using [hB])
      (by rw [ofs_off' _ (by omega_using [hi, hB])]; omega_using [hi, hB, hA])]
    exact h.1.bits i hi
  refine WP.mono (h.2.2.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => t.gpr .esi = BitVec.ofNat 32 n ∧ t.mem = s.mem)
    (WP.mono (decCounter_ok (by omega_using [hn]) h.2.1.esi) fun t ⟨c, g, m, r, w, _⟩ =>
      ⟨FInv.of_counter h.2.2.fin g m r w, g _ (by decide), w, c, m⟩)) fun t ⟨fe, c, m⟩ =>
        ⟨fe, c, hn, fun i hi => by rw [m]; exact bits i hi⟩

theorem combLoop_rel : ∀ n, RelCT isa (Runs BP₀ (LadB n)) (.loop combStep .ne)
    (Runs BP₀ fun σ s => ∃ s₄, BL σ s₄ s 0) := by
  refine RelCT.loop (M := isa) (fun n => Runs BP₀ (LadB n)) fun n => ?_
  refine Runs.then (G := fun σ t => (n < 114 ∧ ∃ s₄, BL σ s₄ t n) ∧ t.zf = some (decide (n = 0)))
    (fun _ _ h => h) (combStep_tr n) ?_ ?_
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
      have e : n - 1 + 1 = n := by omega_using [hn0]
      exact ⟨n - 1, by omega_using [hn0], σ₁, σ₂, hP, ⟨by omega_using [hn], a₁, e ▸ L₁⟩, ⟨by omega_using [hn], a₂, e ▸ L₂⟩⟩

/-! ## The whole function -/

theorem baseEntry_rel :
    RelCT isa (Runs BP₀ fun σ s => s = σ ∧ BasePre σ)
      baseEntry (Runs BP₀ BMid) := by
  refine Runs.step (RelCT.taint (A := taint) (scalarTaint 2 3) ?_ (by taint_decide))
    fun σ s ⟨e, h⟩ => by subst e; exact entry_stage h
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨rfl, -⟩, ⟨rfl, -⟩⟩
  exact scalarBase_agree hP.1 hP.2.1 hP.2.2

theorem combLoopAll_rel : RelCT isa (Runs BP₀ BMid) combLoop (Runs BP₀ fun σ s => ∃ s₄, BL σ s₄ s 0) := by
  unfold combLoop
  refine RelCT.seq (Runs.step (G := LadB 113) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_) (combLoop_rel 113)
  intro σ s m
  refine WP.mono (setCounter_ok s 114 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
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
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [this]) p.ret_out p.args_out
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [this]) p.ret_sc p.args_sc
    have ad : ∀ {σ : State}, BasePre σ → ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20],
        (⟨argAddr σ 0, 16 - 4⟩ : Region).Disjoint r := by
      intro σ p r hr
      rw [p.wr, ← stkR_below p.sp_room] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.args_out
      · exact p.args_sc
      · exact p.stk_args.symm
    exact f₁.agreeA f₂ hP.hp.1 hP.hp.2 (by have := p₁.sp_fit; omega_using [this]) (by have := p₂.sp_fit; omega_using [this])
      (wr p₁) (wr p₂) (ad p₁) (ad p₂) fun k h4 hk => by
        have := a.argMem k h4 hk
        simpa only [scalarTaint, VG.X86.Taint.depth, Nat.zero_add] using this

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    ((?_ : RelCT isa (Runs BP₀ fun σ s => s = σ ∧ BasePre σ) scalarBase fun _ _ => True).mono
      (fun s₁ s₂ h => ⟨s₁, s₂, h, ⟨rfl, BasePre.of h.1⟩, ⟨rfl, BasePre.of h.2.1⟩⟩) fun _ _ h => h)
  unfold scalarBase
  exact baseEntry_rel.seq (combLoopAll_rel.seq baseEncode_tr)

end VG.Proof.Ed448.X86
