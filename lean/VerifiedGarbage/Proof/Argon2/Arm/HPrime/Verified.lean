import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.Arm.HPrime.OutputCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract

/-!
# Argon2 H′ on ARMv7: verified

Constant time, by relating two runs with the same public data piece by piece
(`code_ct`): the setup is checked by the taint analysis from the stack
argument, `first` and `finishOutput` by their pieces; then `hPrime_verified`
against `hPrimeArm`, and `hPrimeShared_verified` against
`Spec.Argon2.hPrimeContract`.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (setup restore first finishOutput chooseLength absorbInput finishInput
  absorbFixed)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_sub wp_cmp op2_reg op2_imm op2_lsr eval_eq)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

theorem Same.inp_eq {s₀ s₀' : State} (q : Same s₀ s₀') : inp s₀' = inp s₀ := q.r0

/-! ## The setup -/

theorem agreeS {s₁ s₂ : State} (hp₁ : Pre s₁) (hp₂ : Pre s₂) (q : Same s₁ s₂) :
    VG.Arm.Taint.Agree (argTaint [] 4) s₁ s₂ := by
  have e : ∀ s : State, (argR s) = ⟨State.addr s.sp, 4⟩ := fun s => by simp [argR, stackArgAddr]
  refine agree_argTaint (fun _ h => nomatch h) q.sp.symm ⟨hp₁.sp_hi, fun r hr => ?_⟩
    ⟨hp₂.sp_hi, fun r hr => ?_⟩ (argMem_of (j := 1) q.sp.symm (by have := hp₁.sp_hi; omega) fun i hi => ?_)
  · rw [← e]; rw [hp₁.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp₁.arg_out
    · exact hp₁.arg_scr
  · rw [← e]; rw [hp₂.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp₂.arg_out
    · exact hp₂.arg_scr
  · have : i = 0 := by omega
    subst this; exact q.scr.symm

theorem setup_F0 {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (F0 s₀) := by
  have hif := hp.in_fits
  refine (setup_ok hp).mono fun t ⟨b, o, f⟩ => ⟨b, o, ?_⟩
  exact Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := inR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi

theorem setup_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') :
    RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') (.block setup) fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂ :=
  ((RelCT.taint (A := taint) (argTaint [] 4) (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact agreeS hp hp' q)
    (by taint_decide)).wp fun _ _ ⟨e₁, e₂⟩ =>
      ⟨by subst e₁; exact setup_F0 hp, by subst e₂; exact setup_F0 hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## `first` -/

/-- The count `finishInput` passes to `finalize`, low and high words. -/
def cntLo (s₀ : State) : BitVec 32 := s₀.gpr .r1 + 4
def cntHi (s₀ : State) : BitVec 32 :=
  0 + 0 + (if decide (2 ^ 32 ≤ (s₀.gpr .r1).toNat + (4 : BitVec 32).toNat) then 1 else 0)

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

include hp in
theorem choose_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.dp .sub .r1 .r8 (.imm 1), .mov .r1 (.shifted .r1 .lsr 6), .cmp .r1 (.imm 0)]) s
      fun t => F0 s₀ t ∧ isa.eval .eq t = some (decide (ol s₀ ≤ 64)) := by
  have hol := (s₀.gpr .r3).isLt
  have hpos := hp.ol_pos
  have l₀ : s.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [h.out.left]; rfl
  refine wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ⟨h.keeps hp ?_, ?_⟩
  · exact Keeps.same (fun r hr => by rw [f₃.gpr, u₂.other _ (kept_ne r hr).2.1, u₁.other _ (kept_ne r hr).2.1])
      (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd])
      (by rw [f₃.wr, u₂.wr, u₁.wr])
  · show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, u₂.gpr, u₁.gpr, l₀]; exact congrArg some (le64_beq hpos hol)

include hp hp' q in
theorem choose_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) chooseLength fun _ _ => True := by
  unfold chooseLength
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => choose_blk hp h) (fun _ h => choose_blk hp' h)) ?_
  exact RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, q.ol_eq])
    (rel_none ⟨_, by taint_decide⟩) (rel_none ⟨_, by taint_decide⟩)

include hp in
theorem absorbInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .r2 (.imm 4), .mov .r3 (.imm 0), .mov .r9 (.reg .r5), .mov .r10 (.reg .r6)]) s
      (UpdateIn (scr s₀) (sp₀ s₀) (inp s₀) (inl s₀) 4 0) := by
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have o₄ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have k₄ : Keeps (scr s₀) (sp₀ s₀) s s₄ := Keeps.same (fun r hr => o₄ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1 (kept_ne r hr).2.2.2.2.1 (kept_ne r hr).2.2.2.2.2.1)
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have F₄ := h.keeps hp k₄
  refine ⟨F₄.body.ctx hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.body.r5]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.body.r6]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [F₄.body.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩

include hp in
theorem finishInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .r3 (.imm 0), .adds .r2 .r6 (.imm 4), .adc .r3 .r3 (.imm 0)]) s
      (FinalizeIn (scr s₀) (sp₀ s₀) (cntLo s₀) (cntHi s₀)) := by
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_adds (op2_imm (by decide)) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => WP.block_nil ?_
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => o₃ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1)
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  have r6 : s₁.gpr .r6 = s₀.gpr .r1 := by rw [u₁.other _ (by decide), h.body.r6]
  refine ⟨(h.keeps hp k₃).body.ctx hp, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, r6]; rfl
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, c₂, r6]; rfl

include q in
theorem cnt_eq : cntLo s₀' = cntLo s₀ ∧ cntHi s₀' = cntHi s₀ := by
  simp only [cntLo, cntHi, q.r1, and_self]

include hp hp' q in
theorem first_ct : RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) first fun _ _ => True := by
  have hs := hp.scr_fits
  have nE : nF s₀' = nF s₀ := by simp only [nF, q.ol_eq]
  unfold first
  refine RelCT.seq (rel_wp (choose_rel hp hp' q) (fun _ h => first_choose hp h)
    (fun _ h => first_choose hp' h)) ?_
  refine RelCT.seq (rel_wp ((init_rel (B := scr s₀) (SP := sp₀ s₀) (n := nF s₀) (nF_pos hp)
      (Nat.min_le_right _ _)).mono (fun _ _ ⟨⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, e₁⟩, by
          have c := f₂.body.ctx hp'
          rw [q.scr, q.sp] at c
          exact ⟨c, by rw [e₂, nE]⟩⟩) fun _ _ h => h)
    (fun _ h => first_init hp h) (fun _ h => first_init hp' h)) ?_
  refine RelCT.seq (rel_wp ((absorbFixed_rel (B := scr s₀) (SP := sp₀ s₀) (offset := 832) (size := 4)
      (by decide) (by decide) (by omega) (by decide) (by decide)
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))) fixed_check_832).mono
      (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, pfx_cov hp f₁.body⟩, by
          have c := f₂.body.ctx hp'
          have v := pfx_cov hp' f₂.body
          simp only [P] at v
          rw [q.scr, q.sp] at c; rw [q.scr] at v
          exact ⟨c, v⟩⟩) fun _ _ h => h)
    (fun _ h => first_fixed hp h) (fun _ h => first_fixed hp' h)) ?_
  refine RelCT.seq (rel_wp ?_ (fun _ h => first_input hp h) (fun _ h => first_input hp' h)) ?_
  · unfold absorbInput
    refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => absorbInput_blk hp h.1)
      (fun _ h => (absorbInput_blk hp' h.1).mono fun _ h => by
        rw [q.scr, q.sp, q.inp_eq, q.inl_eq] at h; exact h)) ?_
    exact update_rel hp.in_fits (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in
  · unfold finishInput
    refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => finishInput_blk hp h.1)
      (fun _ h => (finishInput_blk hp' h.1).mono fun _ h => by
        rw [q.scr, q.sp, (cnt_eq q).1, (cnt_eq q).2] at h; exact h)) ?_
    exact finalize_rel

include hp hp' q in
theorem first_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) first fun t₁ t₂ =>
      (F0 s₀ t₁ ∧ (digest s₀ t₁).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) ∧
      (F0 s₀' t₂ ∧ (digest s₀' t₂).take (nF s₀') =
        Spec.Argon2.H (nF s₀') (Spec.Argon2.le32 (ol s₀') ++ inB s₀')) :=
  rel_wp (first_ct hp hp' q) (fun _ h => first_ok hp h) (fun _ h => first_ok hp' h)

end

/-! ## Constant time -/

theorem code_ct : ConstantTime isa hPrimeArm.pre hPrimeArm.pub Impl.Argon2.Arm.HPrime.code := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    fun s₀ s₀' t₁ t₂ r₁ r₂ ⟨h₀, h₀', hq⟩ e₁ e₂ => ?_
  have hp := pre_of s₀ h₀
  have hp' := pre_of s₀' h₀'
  have q := Same.of_pub hq
  suffices h : RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') Impl.Argon2.Arm.HPrime.code fun _ _ => True from
    h s₀ s₀' t₁ t₂ r₁ r₂ ⟨rfl, rfl⟩ e₁ e₂
  unfold Impl.Argon2.Arm.HPrime.code
  refine RelCT.seq (setup_rel hp hp' q) (RelCT.seq (first_rel hp hp' q)
    (RelCT.seq (R := fun t₁ t₂ => Body s₀ t₁ ∧ Body s₀' t₂) ?_ ?_))
  · exact rel_wp ((finishOutput_rel hp hp' q).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
      ⟨⟨f₁.body, f₁.out⟩, ⟨f₂.body, f₂.out⟩⟩) fun _ _ h => h)
      (fun _ ⟨f, d⟩ => (finish_ok hp f.body f.out d).mono fun _ h => h.1)
      (fun _ ⟨f, d⟩ => (finish_ok hp' f.body f.out d).mono fun _ h => h.1)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.r4]) (fun _ _ ⟨b₁, b₂⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [b₁.r4, b₂.r4, q.scr]) (by taint_decide)

/-! ## A state satisfying the precondition -/

/-- `input` at `0x1000` (one byte), `out` at `0x2000` (one byte), `scratch`
at `0x10000`, its address the stack argument at `0x5000`. -/
def hSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5002 then 1 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩]

theorem hSat_pre : hPrimeArm.pre hSatState := by
  have e : stackArg hSatState 0 = 0x10000 := by decide
  have e2 : stackArgAddr hSatState 0 = 0x5000 := by decide
  simp only [hPrimeArm, e, e2]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem hPrime_verified : Verified Arm.target Impl.Argon2.Arm.HPrime.code hPrimeArm := by
  refine ⟨fun s hs => ?_, code_ct, ⟨hSatState, hSat_pre⟩⟩
  obtain ⟨t, s', he, h₁, h₂, h₃⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩

theorem hPrime_implies : hPrimeArm.Implies (Spec.Argon2.hPrimeContract Arm.abi 32) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, hPrimeArm, VG.Proof.Argon2.Arm.stkR,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [hSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using hSatState

/-- The emitted function, against the shared contract. -/
theorem hPrimeShared_verified :
    Verified Arm.target Impl.Argon2.Arm.HPrime.code (Spec.Argon2.hPrimeContract Arm.abi 32) :=
  hPrime_verified.of_implies hPrime_implies

end VG.Proof.Argon2.Arm.HPrime
