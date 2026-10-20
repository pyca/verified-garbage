module

public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal4
public import VerifiedGarbage.Impl.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Option.Basic
public import VerifiedGarbage.TCB.Code

/-! Direct relational timing for four-word UMAAL rows. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

private def regs : List Reg := [.r0, .r12, .lr]
private def Pub (s t : State) : Prop := ∀ r ∈ regs, s.gpr r = t.gpr r
private def PubZ (s t : State) : Prop := Pub s t ∧ s.z = t.z
private def inputT : VG.Arm.Taint.T := Taint.ofRegs regs
private def outputT : VG.Arm.Taint.T := { inputT with flags := true }

private theorem checked {code : Prog isa} {out : VG.Arm.Taint.T} {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (check : (taint.check inputT code hint).map (fun next => taint.le out next) = some true) :
    RelCT isa Pub code (VG.Arm.Taint.Agree out) := by
  intro s t tr1 tr2 u v h e1 e2
  cases hc : taint.check inputT code hint with
  | none => simp [hc] at check
  | some next =>
    have le : taint.le out next = true := by simpa [hc] using check
    obtain ⟨trace, agree⟩ := VG.Taint.check_sound hc (Taint.agree_ofRegs h) e1 e2
    exact ⟨trace, taint.le_sound le agree⟩

private theorem checkedPub {code : Prog isa} {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (check : (taint.check inputT code hint).map (fun next => taint.le inputT next) = some true) :
    RelCT isa Pub code Pub :=
  (checked check).mono (fun _ _ h => h) (fun _ _ h r hr => h.rf.1 r (by simpa [inputT, Taint.ofRegs] using hr))

private theorem checkedZ {code : Prog isa} {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (check : (taint.check inputT code hint).map (fun next => taint.le outputT next) = some true) :
    RelCT isa Pub code PubZ :=
  (checked check).mono (fun _ _ h => h) (fun _ _ h => ⟨fun r hr => h.rf.1 r (by simpa [outputT, inputT, Taint.ofRegs] using hr), (h.rf.2 rfl).2.1⟩)

private theorem keep {code : Prog isa}
    (untouched : ∀ r ∈ regs, (instrs code).all (fun i => !(VG.Arm.clobbers i r)) = true)
    (noCalls : code.noCalls = true)
    (ct : RelCT isa Pub code (fun _ _ => True)) : RelCT isa Pub code Pub := by
  intro s t tr1 tr2 u v h e1 e2
  refine ⟨(ct _ _ _ _ _ _ h e1 e2).1, ?_⟩
  intro r hr
  have unchanged {a b : State} {tr} (run : Exec isa code a tr b) : b.gpr r = a.gpr r := by
    apply Exec.gpr (h := run) (hn := Or.inl noCalls)
    intro i hi
    have item := List.all_eq_true.mp (untouched r hr) i hi
    cases hc : VG.Arm.clobbers i r <;> simp_all
  rw [unchanged e1, unchanged e2]
  exact h r hr

private theorem umaal_public (lo hi a b : Reg)
    (safe : ∀ r ∈ regs, r ≠ lo ∧ r ≠ hi) :
    RelCT isa Pub (.block [.umaal lo hi a b]) Pub := by
  apply keep
  · intro r hr
    obtain ⟨hl, hh⟩ := safe r hr
    simp [instrs, VG.Arm.clobbers, hl, hh, ]
  · rfl
  · intro s t tr1 tr2 u v _ e1 e2
    rw [Exec.block_iff] at e1 e2
    by_cases same : lo = hi
    · simp [execBlock, isa, VG.Arm.exec, same] at e1
    · simp [execBlock, isa, VG.Arm.exec, same, VG.Arm.addrs] at e1 e2
      exact ⟨e1.2.trans e2.2.symm, trivial⟩

private theorem append {a b : List Instr} {P R Q : State → State → Prop}
    (ha : RelCT isa P (.block a) R) (hb : RelCT isa R (.block b) Q) :
    RelCT isa P (.block (a ++ b)) Q := by
  intro s t tr1 tr2 u v h e1 e2
  have split1 := (execBlock_append (M := isa) a b s)
  have split2 := (execBlock_append (M := isa) a b t)
  rw [Exec.block_iff, split1] at e1
  rw [Exec.block_iff, split2] at e2
  simp only [Option.bind_eq_some_iff, Prod.exists, Option.map_eq_some_iff] at e1 e2
  obtain ⟨mid1, trA1, first1, end1, trB1, last1, pair1⟩ := e1
  obtain ⟨mid2, trA2, first2, end2, trB2, last2, pair2⟩ := e2
  obtain ⟨rfl, next⟩ := ha _ _ _ _ _ _ h (.block first1) (.block first2)
  obtain ⟨rfl, post⟩ := hb _ _ _ _ _ _ next (.block last1) (.block last2)
  simp only [Prod.mk.injEq] at pair1 pair2
  obtain ⟨rfl, rfl⟩ := pair1
  obtain ⟨rfl, rfl⟩ := pair2
  exact ⟨rfl, post⟩

private theorem first_public (k : Nat) (hk : k = 0 ∨ k = 4 ∨ k = 8) : RelCT isa Pub (.block (rowFirstAtU k)) Pub := by
  unfold rowFirstAtU
  change RelCT isa Pub (.block ([.ldr .r2 .r12 k, .ldr .r3 .r0 k] ++
    ([.umaal .r3 .r11 .r2 .r9] ++ [.str .r3 .r0 k]))) Pub
  apply append
  · apply checkedPub (hint := .block [])
    rcases hk with rfl | rfl | rfl <;> decide +kernel
  apply append
  · apply umaal_public
    simp [regs]
  · apply checkedPub (hint := .block [])
    rcases hk with rfl | rfl | rfl <;> decide +kernel

private theorem step12_public : RelCT isa Pub (.block (rowStepU 12)) Pub := by
  unfold rowStepU
  change RelCT isa Pub (.block ([.ldr .r2 .r12 12, .ldr .r3 .r0 12, .mov .r5 (.reg .r3)] ++
    ([.umaal .r3 .r11 .r2 .r9] ++ [.str .r3 .r0 12]))) Pub
  apply append
  · exact checkedPub (hint := .block []) (by decide +kernel)
  apply append
  · apply umaal_public
    simp [regs]
  · exact checkedPub (hint := .block []) (by decide +kernel)

private theorem four_public : RelCT isa Pub (.block rowBodyU4) PubZ := by
  unfold rowBodyU4
  repeat' apply append
  · exact first_public 0 (by simp)
  · exact first_public 4 (by simp)
  · exact first_public 8 (by simp)
  · exact step12_public
  · exact checkedZ (hint := .block []) (by decide +kernel)

private theorem pair_public : RelCT isa Pub (.block rowBodyU) PubZ := by
  unfold rowBodyU rowFirstU
  change RelCT isa Pub (.block (rowFirstAtU 0 ++ (rowStepU 4 ++ rowAdvance2))) PubZ
  apply append
  · exact first_public 0 (by simp)
  apply append
  · unfold rowStepU
    change RelCT isa Pub (.block ([.ldr .r2 .r12 4, .ldr .r3 .r0 4, .mov .r5 (.reg .r3)] ++
      ([.umaal .r3 .r11 .r2 .r9] ++ [.str .r3 .r0 4]))) Pub
    apply append
    · exact checkedPub (hint := .block []) (by decide +kernel)
    apply append
    · apply umaal_public
      simp [regs]
    · exact checkedPub (hint := .block []) (by decide +kernel)
  · exact checkedZ (hint := .block []) (by decide +kernel)

private theorem emptyZ : RelCT isa PubZ (.block []) PubZ := by
  intro s t tr1 tr2 u v h e1 e2
  rw [Exec.block_iff] at e1 e2
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ⟨rfl, h⟩

private theorem condition (s t : State) (h : PubZ s t) : isa.eval .ne s = isa.eval .ne t := by
  change some (!s.z) = some (!t.z)
  rw [h.2]

private theorem loop_public {body : Prog isa} (step : RelCT isa Pub body PubZ) :
    RelCT isa Pub (.loop body .ne) Pub := by
  intro s t tr1 tr2 u v h e1 e2
  generalize eq : Code.loop body Cond.ne = code at e1
  induction e1 generalizing t tr2 v with
  | loopExit first done =>
    cases eq
    cases e2 with
    | loopExit other _ =>
      obtain ⟨rfl, post⟩ := step _ _ _ _ _ _ h first other
      exact ⟨rfl, post.1⟩
    | loopNext other again _ =>
      have equal := condition _ _ (step _ _ _ _ _ _ h first other).2
      rw [done, again] at equal
      cases equal
  | loopNext first again rest _ ih =>
    cases eq
    cases e2 with
    | loopExit other done =>
      have equal := condition _ _ (step _ _ _ _ _ _ h first other).2
      rw [again, done] at equal
      cases equal
    | loopNext other _ rest2 =>
      obtain ⟨rfl, next⟩ := step _ _ _ _ _ _ h first other
      obtain ⟨rfl, post⟩ := ih _ _ _ next.1 rest2 rfl
      exact ⟨rfl, post⟩
  | _ => cases eq

private theorem end_public : RelCT isa Pub (.block rowUEnd) Pub := by
  unfold rowUEnd
  change RelCT isa Pub (.block ([.mov .r6 (.reg .r5), .mov .r4 (.imm 0)] ++
    ([.umaal .r6 .r4 .r2 .r9] ++ [.mov .r6 (.shifted .r2 .lsr 16), .movw .r9 0xffff,
      .dp .and .r2 .r2 (.reg .r9), .mul .r7 .r1 .r6]))) Pub
  apply append
  · exact checkedPub (hint := .block []) (by decide +kernel)
  apply append
  · apply umaal_public
    simp [regs]
  · exact checkedPub (hint := .block []) (by decide +kernel)

private theorem loopU4_public : RelCT isa Pub rowLoopU4 Pub := by
  unfold rowLoopU4
  apply RelCT.seq (checkedPub (hint := .block []) (by decide +kernel))
  apply RelCT.seq (checkedZ (hint := .block []) (by decide +kernel))
  apply RelCT.seq
  · apply RelCT.ite condition
    · exact pair_public.mono (fun _ _ h => h.1.1) (fun _ _ h => h)
    · exact emptyZ.mono (fun _ _ h => h.1) (fun _ _ h => h)
  apply RelCT.seq
  · exact (checkedZ (hint := .block []) (by decide +kernel)).mono (fun _ _ h => h.1) (fun _ _ h => h)
  apply RelCT.seq
  · apply RelCT.ite condition
    · exact (loop_public four_public).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
    · exact emptyZ.mono (fun _ _ h => h.1) (fun _ _ h => h.1)
  exact end_public

private theorem rowU4_public : RelCT isa Pub rowU4 Pub := by
  unfold rowU4
  apply RelCT.seq (checkedZ (hint := .block []) (by decide +kernel))
  apply RelCT.seq
  · apply RelCT.ite condition
    · exact (checkedZ (hint := .seq inputT (.seq inputT (.block []) (.seq inputT (.block []) (.seq inputT (.block []) (.seq inputT (.block []) (.block []))))) (.block []))
        (by decide +kernel)).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
    · exact emptyZ.mono (fun _ _ h => h.1) (fun _ _ h => h)
  apply RelCT.seq
  · exact (checkedZ (hint := .block []) (by decide +kernel)).mono (fun _ _ h => h.1) (fun _ _ h => h)
  apply RelCT.seq
  · apply RelCT.ite condition
    · exact loopU4_public.mono (fun _ _ h => h.1.1) (fun _ _ h => h)
    · exact emptyZ.mono (fun _ _ h => h.1) (fun _ _ h => h.1)
  exact checkedPub (hint := .block []) (by decide +kernel)

theorem row4_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr) rowU4 := by
  intro s t tr1 tr2 u v _ _ h e1 e2
  apply (rowU4_public s t tr1 tr2 u v ?_ e1 e2).1
  intro r hr
  simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem row4Full_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr)
    (.seq rowU4 rowCarry) := by
  have ct : RelCT isa Pub (.seq rowU4 rowCarry) Pub := by
    apply RelCT.seq rowU4_public
    exact checkedPub (hint := .seq inputT (.block []) (.seq inputT (.block []) (.block []))) (by decide +kernel)
  intro s t tr1 tr2 u v _ _ h e1 e2
  apply (ct s t tr1 tr2 u v ?_ e1 e2).1
  intro r hr
  simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

end VG.Proof.Bignum.Arm
