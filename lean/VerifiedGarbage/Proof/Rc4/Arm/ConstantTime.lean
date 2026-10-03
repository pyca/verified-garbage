import VerifiedGarbage.Proof.Rc4.Arm.Contract
import VerifiedGarbage.Proof.Rc4.Arm.Lit
import VerifiedGarbage.Proof.Rc4.Arm.Apply
import VerifiedGarbage.Proof.Framework.RelCT

/-! # RC4 on ARMv7: constant time

Initialization is checked by the taint analysis alone. The stream function
first loads the PRGA index `i` from the context, which the analysis takes
for secret: the contract lets it leak, so the proof makes it public by hand
(`entry_ct`) and the analysis checks the rest.
-/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem init_ct : ConstantTime isa initC.pre initC.pub VG.Impl.Rc4.Arm.init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ ⟨_, h0, h1, h2, h3⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption)
    (by taint_decide)

/-- The taint after `entry`, with `i` in `r12`. -/
def loopTaint : VG.Arm.Taint.T := Taint.ofRegs [.r0, .r1, .r2, .r3, .r12]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem entry_ct : RelCT isa (fun a b => applyC.pre a ∧ applyC.pre b ∧ applyC.pub a b)
    (.block entry) fun a b => VG.Arm.Taint.Agree loopTaint a b ∧ a.z = b.z := by
  intro a b tr tr' a' b' ⟨hpa, hpb, ⟨_, hi⟩, h0, h1, h2, h3⟩ ea eb
  obtain ⟨htrace, -⟩ := RelCT.taint (A := taint) (P := fun a b => VG.Arm.Taint.Agree
    (Taint.ofRegs [.r0, .r1, .r2, .r3]) a b) (Taint.ofRegs [.r0, .r1, .r2, .r3]) (fun _ _ h => h)
    (by taint_decide) a b tr tr' a' b' (Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ea eb
  obtain ⟨_, u, eu, -, hak, ha12, haz⟩ := apply_entry a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, -, hbk, hb12, hbz⟩ := apply_entry b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  have hi' : (contextAt a.mem (State.addr (a.gpr .r0))).i =
      (contextAt b.mem (State.addr (b.gpr .r0))).i :=
    BitVec.eq_of_toNat_eq (List.cons.inj hi).1
  refine ⟨htrace, Taint.agree_ofRegs fun r hr => ?_, by rw [haz, hbz, h2]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h0]
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h1]
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h2]
  · rw [hak.gpr (by decide), hbk.gpr (by decide), h3]
  · rw [ha12, hb12, hi']

theorem nil_ct {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True := by
  intro _ _ _ _ _ _ _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

theorem apply_ct : ConstantTime isa applyC.pre applyC.pub VG.Impl.Rc4.Arm.apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold VG.Impl.Rc4.Arm.apply
  refine RelCT.seq entry_ct (RelCT.ite ?_ nil_ct ?_)
  · intro a b ⟨_, hz⟩
    rw [eval_eq, eval_eq, hz]
  · exact RelCT.taint (A := taint) loopTaint (fun _ _ h => h.1.1) (by taint_decide)

end VG.Proof.Rc4.Arm
