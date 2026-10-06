import VerifiedGarbage.Proof.AesOcb.Arm.CTPre

/-!
# AES-OCB on ARMv7: the data and the tag in two runs

Untrusted: everything here is checked by Lean. `body` and `tag d`, in two
runs with the same public arguments: the passes over the whole blocks and
the rest by the taint analysis, from the registers holding the data's
pointer, its blocks and the block index, the same in both runs; the calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` with the same arguments
in both runs (`body_rel`, `tag_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 and15 ofNat_sub32)

/-! ## The whole blocks -/

theorem passStart_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r7, .r8]))
    (.block passStart) h).isSome = true := ⟨_, by taint_decide⟩

theorem pass_check {b : List Instr} (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5, .r6, .r7, .r8])) (pass b) h).isSome =
      true := by
  rcases hb with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem wholeArgs_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (callArgs ++ ([.mov .r2 (.reg .r8), .mov .r3 (.reg .r7)] : List Instr))) h).isSome = true := ⟨_, by taint_decide⟩

theorem wholeTail_check {b : List Instr} (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r7, .r8]))
      (.seq (.block (copy16 o0O ofsO ++ passStart)) (pass b)) h).isSome = true := by
  rcases hb with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem pass_kept {p : Prm} (L : Lay p) {τ : State} (E : Env p τ) {b : List Instr}
    (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∀ t τ', Exec isa (pass b) τ t τ' → Kept p [.r7, .r8] τ τ' := by
  rcases hb with rfl | rfl | rfl <;>
    exact kept_of L E [.r7, .r8] (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The call between the passes, set up. -/
theorem wholeArgs_ok {p : Prm} (L : Lay p) {τ : State} (E : Env p τ) {m : Nat} (hmn : 16 * m ≤ p.n)
    (h8 : τ.gpr .r8 = p.D) (h7 : τ.gpr .r7 = BitVec.ofNat 32 m) :
    WP isa (.block (callArgs ++ ([.mov .r2 (.reg .r8), .mov .r3 (.reg .r7)] : List Instr))) τ fun t =>
      BlkCall t p.K p.D (p.W + BitVec.ofNat 32 scrO) p.R m ∧ Env p t ∧ t.gpr .r8 = p.D ∧
        t.gpr .r7 = BitVec.ofNat 32 m := by
  have fd := L.dw
  refine WP.of_runBlock ⟨_, by orun [callArgs, E.r9, E.r10, E.r11, h8, h7], ?_⟩
  have E' := E.of_others (s' := ((((τ.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 p.D).setReg .r3 (BitVec.ofNat 32 m))
    (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
    (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by omega)
    (Proof.AesGcm.Arm.covers_prefix E.perm.d hmn) (L.k_d.sub_right (Region.sub_prefix hmn))
    ((L.d_w' (d := scrO) (k := 2048) (by decide)).sub_left (Region.sub_prefix hmn))
    (L.bd.sub_right (Region.sub_prefix hmn)), E', by simp [gpr_setReg, h8], by simp [gpr_setReg, h7]⟩

/-- The whole blocks, in two runs with the same public arguments. -/
theorem whole_rel (F : BlkFn) {pre post : List Instr}
    (hpre : pre = addCk ++ xorOfs ∨ pre = xorOfs ∨ pre = xorOfs ++ addCk)
    (hpost : post = addCk ++ xorOfs ∨ post = xorOfs ∨ post = xorOfs ++ addCk)
    {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {m : Nat} (hmn : 16 * m ≤ p.n)
    (h8₁ : τ₁.gpr .r8 = p.D) (h8₂ : τ₂.gpr .r8 = p.D) (h7₁ : τ₁.gpr .r7 = BitVec.ofNat 32 m)
    (h7₂ : τ₂.gpr .r7 = BitVec.ofNat 32 m) : RelCT isa (Eq2 τ₁ τ₂) (whole (blkFrame F) pre post) TT := by
  unfold whole
  obtain ⟨s₁, run₁, r4₁, r5₁, r6₁, R₁⟩ := passStart_run h8₁ h7₁
  obtain ⟨s₂, run₂, r4₂, r5₂, r6₂, R₂⟩ := passStart_run h8₂ h7₂
  refine rel_seq (F₁ := (s₁ = ·)) (F₂ := (s₂ = ·)) (rel_env E₁ E₂ [.r7, .r8] (by simp [h7₁, h7₂, h8₁, h8₂])
    passStart_check) (WP.of_runBlock ⟨s₁, run₁, rfl⟩) (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun u₁ u₂ e₁ e₂ => ?_
  subst e₁ e₂
  have Es₁ : Env p s₁ := E₁.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have Es₂ : Env p s₂ := E₂.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have g₁ : ∀ r ∈ [Reg.r7, .r8], s₁.gpr r = τ₁.gpr r := fun r hr => R₁.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide)
  have g₂ : ∀ r ∈ [Reg.r7, .r8], s₂.gpr r = τ₂.gpr r := fun r hr => R₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide)
  refine rel_seqX (rel_env Es₁ Es₂ [.r4, .r5, .r6, .r7, .r8] (by
      simp [r4₁, r4₂, r5₁, r5₂, r6₁, r6₂, g₁ .r7 (by simp), g₂ .r7 (by simp), g₁ .r8 (by simp), g₂ .r8 (by simp),
        h7₁, h7₂, h8₁, h8₂]) (pass_check hpre))
    (pass_kept L Es₁ hpre) (pass_kept L Es₂ hpre) fun v₁ v₂ K₁ K₂ => ?_
  have h8v₁ : v₁.gpr .r8 = p.D := by rw [K₁.gpr _ (by simp), g₁ _ (by simp), h8₁]
  have h8v₂ : v₂.gpr .r8 = p.D := by rw [K₂.gpr _ (by simp), g₂ _ (by simp), h8₂]
  have h7v₁ : v₁.gpr .r7 = BitVec.ofNat 32 m := by rw [K₁.gpr _ (by simp), g₁ _ (by simp), h7₁]
  have h7v₂ : v₂.gpr .r7 = BitVec.ofNat 32 m := by rw [K₂.gpr _ (by simp), g₂ _ (by simp), h7₂]
  refine rel_seq (rel_env K₁.env K₂.env [] (by simp) wholeArgs_check) (wholeArgs_ok L K₁.env hmn h8v₁ h7v₁)
    (wholeArgs_ok L K₂.env hmn h8v₂ h7v₂) fun w₁ w₂ ⟨B₁, Ew₁, h8w₁, h7w₁⟩ ⟨B₂, Ew₂, h8w₂, h7w₂⟩ => ?_
  refine rel_seq (rel_blk F B₁ B₂ (Ew₁.sp_eq Ew₂)) (blk_call F B₁) (blk_call F B₂) fun x₁ x₂ C₁ C₂ => ?_
  exact rel_env (Ew₁.of_saved C₁.saved C₁.sp C₁.rd C₁.wr) (Ew₂.of_saved C₂.saved C₂.sp C₂.rd C₂.wr) [.r7, .r8]
    (by simp [C₁.saved .r7 (by decide) (by decide), C₂.saved .r7 (by decide) (by decide),
      C₁.saved .r8 (by decide) (by decide), C₂.saved .r8 (by decide) (by decide), h7w₁, h7w₂, h8w₁, h8w₂])
    (wholeTail_check hpost)

/-! ## The rest of the data -/

theorem restA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorB .r11 .r10 .r11 ofsO 240 ofsO ++ copy16 ofsO tmpO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem restTail_check (enc : Bool) : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (if enc then .seq padCk xorPad else .seq xorPad padCk) h).isSome = true := by
  cases enc <;> exact ⟨_, by taint_decide⟩

/-- The rest of the data, in two runs with the same pointer and length. -/
theorem rest_rel (enc : Bool) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) : RelCT isa (Eq2 τ₁ τ₂) (rest enc) TT :=
  rel_seqX (rel_env E₁ E₂ [] (by simp) restA_check)
    (kept_of L E₁ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (encOne_rel L K₁.env K₂.env (.inl rfl))
    (exec_of_wp (encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env K₁.env) (C₂.env K₂.env) [.r4, .r5] (by
    simp [C₁.saved .r4 (by decide), C₂.saved .r4 (by decide), C₁.saved .r5 (by decide), C₂.saved .r5 (by decide),
      K₁.gpr .r4 (by simp), K₂.gpr .r4 (by simp), K₁.gpr .r5 (by simp), K₂.gpr .r5 (by simp), h4, h5])
    (restTail_check enc)

/-! ## The data -/

/-- The start of `body`: the data in `r8`, its whole blocks in `r7`. -/
theorem bodyHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    WP isa (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)]) t fun t' =>
      Env p t' ∧ t'.gpr .r8 = p.D ∧ t'.gpr .r7 = BitVec.ofNat 32 (p.n / 16) ∧ t'.z = decide (p.n / 16 = 0) := by
  have n32 := L.n_lt
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.sp, a₈, a₁₂, A.a8, A.a12], ?_, ?_, ?_, ?_⟩
  · exact E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]
  · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ofNat_lsr32 n32]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, ofNat_lsr32 n32,
      Nat.reducePow, z_cmp0 (show p.n / 16 < 2 ^ 32 by omega)]

/-- Where the rest of the data is. -/
theorem restBlk_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) (h8 : t.gpr .r8 = p.D) :
    WP isa (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
        .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) t fun t' =>
      Env p t' ∧ t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.n % 16) ∧
        t'.z = decide (p.n % 16 = 0) := by
  have n32 := L.n_lt
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.sp, a₁₂, A.a12, h8], ?_, ?_, ?_, ?_⟩
  · exact E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
      toNat_ofNat32 n32, h8]
    rw [ofNat_sub32 (Nat.mod_le _ _) n32, BitVec.add_comm, show p.n - p.n % 16 = 16 * (p.n / 16) by omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
      toNat_ofNat32 n32]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15,
      toNat_ofNat32 n32, z_cmp0 (show p.n % 16 < 2 ^ 32 by omega)]

theorem bodyHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24)
    (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restBlk_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs [.r8]) 24)
    (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
      .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

/-- The whole blocks, if there are any, in two runs. -/
theorem wholeIte_rel (F : BlkFn) {pre post : List Instr}
    (hpre : pre = addCk ++ xorOfs ∨ pre = xorOfs ∨ pre = xorOfs ++ addCk)
    (hpost : post = addCk ++ xorOfs ∨ post = xorOfs ∨ post = xorOfs ++ addCk)
    {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (A₁ : Args p τ₁.mem)
    (A₂ : Args p τ₂.mem) :
    RelCT isa (Eq2 τ₁ τ₂) (.seq (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4),
      .cmp .r7 (imm 0)]) (.ite .eq (.block []) (whole (blkFrame F) pre post))) TT :=
  rel_seq (rel_envArg L E₁ E₂ A₁ A₂ [] (by simp) bodyHead_check) (bodyHead_ok L E₁ A₁) (bodyHead_ok L E₂ A₂)
    fun _ _ ⟨U₁, h8₁, h7₁, z₁⟩ ⟨U₂, h8₂, h7₂, z₂⟩ =>
  rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip)
    (fun _ => whole_rel F hpre hpost L U₁ U₂ (Nat.mul_div_le p.n 16) h8₁ h8₂ h7₁ h7₂)

/-- The rest of the data, if there is any, in two runs. -/
theorem restIte_rel (enc : Bool) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) (h8₁ : τ₁.gpr .r8 = p.D) (h8₂ : τ₂.gpr .r8 = p.D) :
    RelCT isa (Eq2 τ₁ τ₂) (.seq (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12,
      .dp .sub .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) (.ite .eq (.block []) (rest enc)))
      TT :=
  rel_seq (rel_envArg L E₁ E₂ A₁ A₂ [.r8] (by simp [h8₁, h8₂]) restBlk_check) (restBlk_ok L E₁ A₁ h8₁)
    (restBlk_ok L E₂ A₂ h8₂) fun _ _ ⟨U₁, h4₁, h5₁, z₁⟩ ⟨U₂, h4₂, h5₂, z₂⟩ =>
  rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip)
    (fun _ => rest_rel enc L U₁ U₂ (by rw [h4₁, h4₂]) (by rw [h5₁, h5₂]))

/-- `body` for `seal`, in two runs from the states `body` starts from. -/
theorem bodySeal_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₁)
    (ho0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₁.mem) 0)
    (hofs₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₂)
    (ho0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₂.mem) 0) :
    RelCT isa (Eq2 τ₁ τ₂) (body true) TT := by
  simp only [body, ↓reduceIte]
  refine RelCT.assoc (rel_seq (wholeIte_rel encF (.inl rfl) (.inr (.inl rfl)) L E₁ E₂ A₁ A₂)
    (wholeIte_ok encF (O0 := O₁) (l := lstarOf p τ₁.mem)
      (ckF1 := ckOf fun i => blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      L (sealPre_ok L) (xorOfs_ok L) E₁ A₁ hofs₁ ho0₁ hck₁ hl0₁ (fun _ => rfl) rfl (fun _ => rfl))
    (wholeIte_ok encF (O0 := O₂) (l := lstarOf p τ₂.mem)
      (ckF1 := ckOf fun i => blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      L (sealPre_ok L) (xorOfs_ok L) E₂ A₂ hofs₂ ho0₂ hck₂ hl0₂ (fun _ => rfl) rfl (fun _ => rfl))
    fun _ _ W₁ W₂ => ?_)
  exact restIte_rel true L W₁.env W₂.env (A₁.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₁.frame))
    (A₂.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₂.frame)) W₁.r8 W₂.r8

/-- `body` for `open`, in two runs from the states `body` starts from. -/
theorem bodyOpen_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₁)
    (ho0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₁.mem) 0)
    (hofs₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₂)
    (ho0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₂.mem) 0) :
    RelCT isa (Eq2 τ₁ τ₂) (body false) TT := by
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (rel_seq (wholeIte_rel decF (.inr (.inl rfl)) (.inr (.inr rfl)) L E₁ E₂ A₁ A₂)
    (wholeIte_ok decF (O0 := O₁) (l := lstarOf p τ₁.mem) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => invOf p τ₁.mem
        (blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₁ (lstarOf p τ₁.mem) (i + 1)) ^^^
          offAt O₁ (lstarOf p τ₁.mem) (i + 1))
      L (xorOfs_ok L) (openPost_ok L) E₁ A₁ hofs₁ ho0₁ hck₁ hl0₁ (fun _ => rfl) rfl (fun _ => rfl))
    (wholeIte_ok decF (O0 := O₂) (l := lstarOf p τ₂.mem) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => invOf p τ₂.mem
        (blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₂ (lstarOf p τ₂.mem) (i + 1)) ^^^
          offAt O₂ (lstarOf p τ₂.mem) (i + 1))
      L (xorOfs_ok L) (openPost_ok L) E₂ A₂ hofs₂ ho0₂ hck₂ hl0₂ (fun _ => rfl) rfl (fun _ => rfl))
    fun _ _ W₁ W₂ => ?_)
  exact restIte_rel false L W₁.env W₂.env (A₁.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₁.frame))
    (A₂.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₂.frame)) W₁.r8 W₂.r8

/-! ## The tag -/

theorem tagA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (copy16 ckO tmpO ++ xorW ofsO tmpO ++ xorW ldO tmpO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem tagB_check {d : Nat} (hd : d = tagO ∨ d = t2O) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (pubRegs [])) (.block (copy16 tmpO d ++ xorW sumO d)) h).isSome = true := by
  rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag d`, in two runs with the same public arguments. -/
theorem tag_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {d : Nat}
    (hd : d = tagO ∨ d = t2O) : RelCT isa (Eq2 τ₁ τ₂) (tag d) TT :=
  rel_seqX (rel_env E₁ E₂ [] (by simp) tagA_check)
    (kept_of L E₁ [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (encOne_rel L K₁.env K₂.env (.inl rfl))
    (exec_of_wp (encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env K₁.env) (C₂.env K₂.env) [] (by simp) (tagB_check hd)

end VG.Proof.AesOcb.Arm
