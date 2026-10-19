module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCoreTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtArithmeticTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrimePowerTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Mont.X86.WindowTiming

/-! # The factors' exponentiations branch only on their public lengths

Each factor's exponentiation runs at `half n` words or at the modulus's width,
by its length, an argument that two calls share; either way the taint analysis
checks the code with only the workspace pointer public.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Dsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

/-- The runs' workspace pointers agree. -/
abbrev Public (s t : State) : Prop := VG.X86.Taint.Agree (workspaceTaint false) s t

theorem zeroCopy_relCT (n h src dst : Nat) :
    RelCT isa Public (.seq (zerosW dst (4 * n)) (copyArray h src dst)) Public := by
  apply erased_relCT (.seq (zerosW dst (4 * n)) (copyArray h src dst)) (.seq (zerosW 0 4) (copyArray 1 0 0))
    (VG.Taint.hintOf taint (workspaceTaint false) (.seq (zerosW 0 4) (copyArray 1 0 0))) rfl rfl rfl
  rfl

theorem checkedWindowPower_relCT (n tab : Nat) :
    RelCT isa Public (checkedWindowPower n tab) Public :=
  VG.RelCT.seq (R := Public) (primeMask_relCT n) (VG.RelCT.seq (R := Public) (preparePrime_relCT n)
    (checkedProgramChange (windowExponentiate_check n (2 * n) tab) (by rfl)))

theorem narrowPower_relCT (n prime exponent output : Nat) :
    RelCT isa Public (narrowPower n prime exponent output) Public := by
  unfold narrowPower reduceInput loadNarrow checkedPreparePrime
  refine VG.RelCT.seq (R := Public) ?_ (VG.RelCT.seq (R := Public) ?_
    (VG.RelCT.seq (R := Public) (checkedWindowPower_relCT _ _) (zeroCopy_relCT _ _ _ _)))
  · exact VG.RelCT.seq (copyArray_relCT _ _ _) (VG.RelCT.seq (copyArray_relCT _ _ _)
      (VG.RelCT.seq (VG.RelCT.seq (primeMask_relCT n) (preparePrime_relCT n))
        (VG.RelCT.seq (reduceOperand_relCT n 5) (copyArray_relCT _ _ _))))
  · exact VG.RelCT.seq (copyArray_relCT _ _ _) (VG.RelCT.seq (copyArray_relCT _ _ _) (copyArray_relCT _ _ _))

theorem factorPowerFit_relCT {base : Addr} {bytes : Nat} (n prime exponent output lenArg : Nat)
    (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) :
    RelCT isa (fun s t => Public s t ∧ s.gpr .esp = t.gpr .esp ∧
        ∃ v, CallArgument s base bytes lenArg v ∧ CallArgument t base bytes lenArg v)
      (factorPowerFit n prime exponent output lenArg) Public := by
  have Compare : RelCT isa (fun s t => Public s t ∧ s.gpr .esp = t.gpr .esp)
      (.block (lengthFits n lenArg)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) stackTaint
      (fun _ _ H => agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.2))
      (hc := .block [])
    change (taint.checkBlock stackTaint
      ([.mov .eax (.mem (PublicFn.argument lenArg))] ++
        [.alu .cmp .eax (.imm (BitVec.ofNat 32 (8 * half n + 1)))])).isSome = true
    rw [VG.Proof.Mont.X86.Dynamic.check_append taint stackTaint, argumentLoad_check .eax lenArg (by decide)]
    rfl
  intro s t tr ur sf tf ⟨A, SP, v, As, At⟩ E F
  unfold factorPowerFit at E F
  cases E with | @seq _ _ _ u _ _ _ E₁ E₂ => cases F with | @seq _ _ _ w _ _ _ F₁ F₂ =>
  have T₁ := Compare _ _ _ _ _ _ ⟨A, SP⟩ E₁ F₁
  obtain ⟨_, Ks, Cs⟩ := wp_result (lengthFits_ok hn32 As) E₁
  obtain ⟨_, Kt, Ct⟩ := wp_result (lengthFits_ok hn32 At) F₁
  have A' : Public u w := agree_regs (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]
    exact A.rf.1 _ (by decide))
  have Branch : RelCT isa (fun s t => Public s t ∧ s.cf = t.cf)
      (.ite .b (narrowPower n prime exponent output) (factorPower n prime exponent output)) Public :=
    RelCT.ite (fun _ _ H => H.2)
      ((narrowPower_relCT n prime exponent output).mono (fun _ _ H => H.1.1) (fun _ _ h => h))
      ((factorPower_relCT n prime exponent output hn).mono (fun _ _ H => H.1.1) (fun _ _ h => h))
  have T₂ := Branch _ _ _ _ _ _ ⟨A', Cs.trans Ct.symm⟩ E₂ F₂
  rw [T₁.1, T₂.1]
  exact ⟨rfl, T₂.2⟩

theorem compute_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => Public s t ∧ Pair base bytes len args s t)
      (compute (Spec.Rsa.modulusWords len)) Public := by
  intro s t tr ur sf tf ⟨A, H⟩ E F
  have dims := H.left.dimensions
  unfold compute powers at E F
  cases E with | seq Ep Er => cases F with | seq Fp Fr =>
  cases Ep with | seq E₁ E₂ => cases Fp with | seq F₁ F₂ =>
  have T₁ := factorPowerFit_relCT (base := base) (bytes := bytes) _ _ _ _ _ dims.1 dims.2.1 _ _ _ _ _ _
    ⟨A, H.sp, args 7, H.left.stack 7 (by decide), H.right.stack 7 (by decide)⟩ E₁ F₁
  have power (σ : State) {τ : State} {tr : List Leak} (I : Inputs base bytes len args σ)
      (X : Exec isa (factorPowerFit (Spec.Rsa.modulusWords len) pSlot dpSlot mpSlot 7) σ tr τ) :=
    wp_result (factorPowerFit_ok I.scratch dims.1 dims.2.1 I.space (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (I.stack 7 (by decide))) X
  obtain ⟨_, Os, Ks⟩ := power s H.left E₁
  obtain ⟨_, Ot, Kt⟩ := power t H.right F₁
  have H' := H.keep Ks Kt (by decide) (by decide) (factor_outside Os (by decide) H.left.space)
    (factor_outside Ot (by decide) H.left.space)
  have T₂ := factorPowerFit_relCT (base := base) (bytes := bytes) _ _ _ _ _ dims.1 dims.2.1 _ _ _ _ _ _
    ⟨T₁.2, H'.sp, args 9, H'.left.stack 9 (by decide), H'.right.stack 9 (by decide)⟩ E₂ F₂
  have T₃ := VG.RelCT.seq (coefficient_relCT _) (crtRecombine_relCT _ _ _ _ _ _ _) _ _ _ _ _ _ T₂.2 Er Fr
  rw [T₁.1, T₂.1, T₃.1]
  exact ⟨rfl, T₃.2⟩

end VG.Proof.Bignum.X86.Crt
