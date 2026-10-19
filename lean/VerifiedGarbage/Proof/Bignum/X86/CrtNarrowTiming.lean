module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCoefficientStageTiming
public import VerifiedGarbage.Proof.Bignum.X86.SafePrime
public import VerifiedGarbage.Proof.Bignum.X86.CrtArithmeticTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrimePowerTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.X86.CrtBothPowers
public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Mont.X86.WindowTiming

/-! # The factors' exponentiations branch only on their public lengths

Each factor's exponentiation runs at `half n` words or at the modulus's width,
by its length, an argument that two calls share; either way the taint analysis
checks the code with only the workspace pointer public. The loop over the two
factors branches on its counter, which both runs advance alike.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Dsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86

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

/-- A factor's length compared with `8 half n`; only the argument's address is read. -/
theorem lengthFits_relCT (n lenArg : Nat) :
    RelCT isa (fun s t => Public s t ∧ s.gpr .esp = t.gpr .esp) (.block (lengthFits n lenArg))
      (fun _ _ => True) := by
  apply RelCT.taint (A := taint) stackTaint
    (fun _ _ H => agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.2))
    (hc := .block [])
  change (taint.checkBlock stackTaint
    ([.mov .eax (.mem (PublicFn.argument lenArg))] ++
      [.alu .cmp .eax (.imm (BitVec.ofNat 32 (8 * half n + 1)))])).isSome = true
  rw [VG.Proof.Mont.X86.Dynamic.check_append taint stackTaint, argumentLoad_check .eax lenArg (by decide)]
  rfl

/-- The two runs' workspace pointers, from a workspace pointer that a block kept. -/
theorem public_keep {s t u w : State} (A : Public s t) (Ku : Keeps [.eax] s u) (Kw : Keeps [.eax] t w) :
    Public u w :=
  agree_regs (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [Ku.1 _ (by decide), Kw.1 _ (by decide)]
    exact A.rf.1 _ (by decide))

theorem select_branch {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} (n lenArg : Nat)
    (hn32 : 128 * n < 2 ^ 32) (hl : lenArg < 18) :
    RelCT isa (fun u w => Public u w ∧ Pair base bytes len args u w)
      (.block (lengthFits n lenArg)) (fun u w => Public u w ∧ u.cf = w.cf) := by
  refine ((lengthFits_relCT n lenArg).mono (fun _ _ H => ⟨H.1, H.2.sp⟩) (fun _ _ h => h)).wpDep
    (F := fun (σ u : State) => u.mem = σ.mem ∧ Keeps [.eax] σ u ∧
      u.cf = some (decide ((args lenArg).toNat < 8 * half n + 1)))
    (fun s t ⟨_, H⟩ => ⟨lengthFits_ok hn32 (H.left.stack lenArg hl),
      lengthFits_ok hn32 (H.right.stack lenArg hl)⟩) |>.mono (fun _ _ h => h) ?_
  rintro u w ⟨-, σ₁, σ₂, ⟨A, _⟩, ⟨_, K₁, C₁⟩, ⟨_, K₂, C₂⟩⟩
  exact ⟨public_keep A K₁ K₂, C₁.trans C₂.symm⟩

/-- Runs whose counters agree take the same factor's length. -/
theorem selectLength_relCT {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} (n : Nat)
    (hn32 : 128 * n < 2 ^ 32) :
    RelCT isa (fun s t => Public s t ∧ Pair base bytes len args s t ∧
        w32 s.mem base counterOffset = w32 t.mem base counterOffset)
      (selectLength n) (fun u w => Public u w ∧ u.cf = w.cf) := by
  have Test : RelCT isa Public (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc counterOffset)),
      .alu .cmp .eax (.imm 0)]) Public := by
    apply erased_relCT (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc counterOffset)), .alu .cmp .eax (.imm 0)])
      (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc counterOffset)), .alu .cmp .eax (.imm 0)])
      (.block []) rfl rfl rfl
    rfl
  unfold selectLength
  refine RelCT.seq (R := fun (u w : State) => Public u w ∧ Pair base bytes len args u w ∧ u.zf = w.zf) ?_
    (RelCT.ite (fun _ _ h => h.2.2) ((select_branch n 7 hn32 (by decide)).mono (fun _ _ h => ⟨h.1.1, h.1.2.1⟩)
      (fun _ _ h => h)) ((select_branch n 9 hn32 (by decide)).mono (fun _ _ h => ⟨h.1.1, h.1.2.1⟩)
      (fun _ _ h => h)))
  refine (Test.mono (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
    (F := fun (σ u : State) => u.mem = σ.mem ∧ Keeps [.eax] σ u ∧
      u.zf = some (decide (w32 σ.mem base counterOffset = 0)))
    (fun s t ⟨_, H, _⟩ => ⟨counterTest_ok H.left.scratch (by have := H.left.space; unfold size VG.Impl.Mont.X86.Dynamic.slot at this; omega),
      counterTest_ok H.right.scratch (by have := H.left.space; unfold size VG.Impl.Mont.X86.Dynamic.slot at this; omega)⟩)
    |>.mono (fun _ _ h => h) ?_
  rintro u w ⟨A, σ₁, σ₂, ⟨_, H, C⟩, ⟨M₁, K₁, Z₁⟩, ⟨M₂, K₂, Z₂⟩⟩
  refine ⟨A, H.keep K₁ K₂ (by decide) (by decide) (by rw [M₁]; exact VG.Proof.Mont.Outside.refl _ _ _ _)
    (by rw [M₂]; exact VG.Proof.Mont.Outside.refl _ _ _ _), ?_⟩
  rw [Z₁, Z₂, C]

theorem fitPower_relCT (n prime exponent output : Nat) :
    RelCT isa (fun s t => Public s t ∧ s.cf = t.cf) (fitPower n prime exponent output) Public :=
  RelCT.ite (fun _ _ H => H.2)
    ((narrowPower_relCT n prime exponent output).mono (fun _ _ H => H.1.1) (fun _ _ h => h))
    ((factorPower_relCT n prime exponent output).mono (fun _ _ H => H.1.1) (fun _ _ h => h))

theorem swapSlots_relCT (n k a b : Nat) : RelCT isa Public (swapSlots n k a b) Public :=
  RelCT.seq (copyArray_relCT _ _ _) (RelCT.seq (copyArray_relCT _ _ _) (copyArray_relCT _ _ _))

theorem swapFactors_relCT (n : Nat) : RelCT isa Public (swapFactors n) Public :=
  RelCT.seq (swapSlots_relCT _ _ _ _) (RelCT.seq (swapSlots_relCT _ _ _ _) (swapSlots_relCT _ _ _ _))

theorem counterNext_relCT :
    RelCT isa Public (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc counterOffset)), .alu .add .eax (.imm 1),
      .store (VG.Impl.Mont.X86.sc counterOffset) .eax, .alu .cmp .eax (.imm 2)]) Public := by
  apply erased_relCT (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc counterOffset)), .alu .add .eax (.imm 1),
      .store (VG.Impl.Mont.X86.sc counterOffset) .eax, .alu .cmp .eax (.imm 2)])
    (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc counterOffset)), .alu .add .eax (.imm 1),
      .store (VG.Impl.Mont.X86.sc counterOffset) .eax, .alu .cmp .eax (.imm 2)]) (.block []) rfl rfl rfl
  rfl

theorem factorStep_relCT {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} (n : Nat)
    (hn32 : 128 * n < 2 ^ 32) :
    RelCT isa (fun s t => Public s t ∧ Pair base bytes len args s t ∧
        w32 s.mem base counterOffset = w32 t.mem base counterOffset)
      (factorStep n) Public := by
  unfold factorStep
  exact RelCT.seq (selectLength_relCT n hn32) (RelCT.seq (fitPower_relCT _ _ _ _)
    (RelCT.seq (swapFactors_relCT n) counterNext_relCT))

theorem powers_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => Public s t ∧ Pair base bytes len args s t)
      (powers (Spec.Rsa.modulusWords len)) Public := by
  have Init : RelCT isa Public (.block [.mov .eax (.imm 0),
      .store (VG.Impl.Mont.X86.sc counterOffset) .eax]) Public := by
    apply erased_relCT (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc counterOffset) .eax])
      (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc counterOffset) .eax]) (.block []) rfl rfl rfl
    rfl
  let I : Nat → State → State → Prop := fun m u w => ∃ k, m = 2 - k ∧ k < 2 ∧ Public u w ∧
    Pair base bytes len args u w ∧ w32 u.mem base counterOffset = k ∧ w32 w.mem base counterOffset = k
  unfold powers
  refine RelCT.seq (R := I 2) ?_ (VG.RelCT.loop (M := isa) (body := factorStep _) (c := .ne) (Q := Public) I ?_ 2)
  · refine (Init.mono (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
      (F := fun (σ u : State) => Outside base counterOffset 4 σ.mem u.mem ∧ Keeps [.eax] σ u ∧
        w32 u.mem base counterOffset = 0)
      (fun s t ⟨_, H⟩ => ⟨powersInit_ok H.left.scratch (by have := H.left.space; unfold size VG.Impl.Mont.X86.Dynamic.slot at this; omega),
        powersInit_ok H.right.scratch (by have := H.left.space; unfold size VG.Impl.Mont.X86.Dynamic.slot at this; omega)⟩)
      |>.mono (fun _ _ h => h) ?_
    rintro u w ⟨A, σ₁, σ₂, ⟨_, H⟩, ⟨O₁, K₁, C₁⟩, ⟨O₂, K₂, C₂⟩⟩
    have b₁ := H.left.space
    have b₂ := H.right.space
    unfold size VG.Impl.Mont.X86.Dynamic.slot at b₁ b₂
    unfold counterOffset multiplierOffset at O₁ O₂
    exact ⟨0, rfl, by decide, A, H.keep K₁ K₂ (by decide) (by decide) (O₁.mono (by omega) (by omega))
      (O₂.mono (by omega) (by omega)), C₁, C₂⟩
  · intro m s t tr ur sf tf ⟨k, hm, hk, A, H, Cs, Ct⟩ E F
    have dims := H.left.dimensions
    have T := factorStep_relCT (base := base) (bytes := bytes) (len := len) (args := args) _ dims.2.1
      _ _ _ _ _ _ ⟨A, H, Cs.trans Ct.symm⟩ E F
    have step (σ : State) {τ : State} {tr : List Leak} (In : Inputs base bytes len args σ)
        (C : w32 σ.mem base counterOffset = k)
        (X : Exec isa (factorStep (Spec.Rsa.modulusWords len)) σ tr τ) :=
      wp_result (factorStep_ok In.scratch dims.1 dims.2.1 In.space hk C rfl
        (In.stack (if k = 0 then 7 else 9) (by split <;> decide))) X
    obtain ⟨_, _, _, _, _, _, _, Cs', Zs, Os, Ks⟩ := step s H.left Cs E
    obtain ⟨_, _, _, _, _, _, _, Ct', Zt, Ot, Kt⟩ := step t H.right Ct F
    refine ⟨T.1, by simp only [eval, Zs, Zt], fun _ => T.2, fun more => ?_⟩
    have last : k + 1 < 2 := by
      by_contra h
      simp only [eval, Zs, show k + 1 = 2 by omega, decide_true, Option.map_some, Bool.not_true,
        Option.some.injEq] at more
      cases more
    refine ⟨2 - (k + 1), by omega, k + 1, rfl, last, T.2, H.keep Ks Kt (by decide) (by decide)
      (powers_outside Os H.left.space) (powers_outside Ot H.left.space), Cs', Ct'⟩

/-- What the coefficient stage needs, from correctness of the powers. -/
theorem powers_stage {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State} {sp : BitVec 32}
    (I : Inputs base bytes len args s) (A : PowerArgs base bytes (Spec.Rsa.modulusWords len) s)
    (hsp : s.gpr .esp = sp) :
    WP isa (powers (Spec.Rsa.modulusWords len)) s (StageReady (Spec.Rsa.modulusWords len) sp base) := by
  have dims := I.dimensions
  refine WP.mono (powers_ok I.scratch dims.1 dims.2.1 I.space A) fun u ⟨P, _, _, _, Pu, _, _, K⟩ => ?_
  exact ⟨(K.1 _ (by decide)).trans hsp, bytes, I.scratch.of_keeps K (by decide) (by decide), I.space,
    hsp ▸ I.room, by
      rw [P, Pu]
      exact Nat.mod_lt _ (by have := safePrime_gt_one (wordsVal s.mem base (slot (Spec.Rsa.modulusWords len) pSlot) (Spec.Rsa.modulusWords len)); omega)⟩

theorem compute_relCT_at (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32)
    (hn : 2 ≤ Spec.Rsa.modulusWords len) (hn32 : 128 * Spec.Rsa.modulusWords len < 2 ^ 32) :
    RelCT isa (fun s t => (Public s t ∧ Pair base bytes len args s t ∧
        PowerArgs base bytes (Spec.Rsa.modulusWords len) s ∧
        PowerArgs base bytes (Spec.Rsa.modulusWords len) t) ∧ s.gpr .esp = sp)
      (compute (Spec.Rsa.modulusWords len)) Public := by
  unfold compute
  refine VG.RelCT.seq ?_ (VG.RelCT.seq (coefficient_relCT hn hn32 sp base) (crtRecombine_relCT _ _ _ _ _ _ _))
  exact ((powers_relCT base bytes len args).mono (P' := fun (s t : State) => (Public s t ∧ Pair base bytes len args s t ∧
      PowerArgs base bytes (Spec.Rsa.modulusWords len) s ∧
      PowerArgs base bytes (Spec.Rsa.modulusWords len) t) ∧ s.gpr .esp = sp)
    (fun _ _ h => ⟨h.1.1, h.1.2.1⟩) fun _ _ h => h).wp
    (F₁ := StageReady (Spec.Rsa.modulusWords len) sp base) (F₂ := StageReady (Spec.Rsa.modulusWords len) sp base)
    fun _ _ ⟨⟨_, H, A, B⟩, e⟩ => ⟨powers_stage H.left A e, powers_stage H.right B (H.sp.symm.trans e)⟩

theorem compute_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => Public s t ∧ Pair base bytes len args s t ∧
        PowerArgs base bytes (Spec.Rsa.modulusWords len) s ∧ PowerArgs base bytes (Spec.Rsa.modulusWords len) t)
      (compute (Spec.Rsa.modulusWords len)) Public := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have dims := hp.2.1.left.dimensions
  have hn : 2 ≤ Spec.Rsa.modulusWords len := by
    have := hp.2.1.left.lower; unfold Spec.Rsa.modulusWords; omega
  exact compute_relCT_at base bytes len args _ hn dims.2.1 _ _ _ _ _ _ ⟨hp, rfl⟩ e₁ e₂

end VG.Proof.Bignum.X86.Crt
