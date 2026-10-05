import VerifiedGarbage.Proof.AesOcb.Arm.CTBase

/-!
# AES-OCB on ARMv7: `Offset_0` and `HASH` in two runs

Untrusted: everything here is checked by Lean. `nonce` and `hash`, in two
runs with the same public arguments: the code between the calls by the taint
analysis, from the registers holding the public arguments and those pinned
to the same values in both runs (the nonce and its length, the associated
data's pointer and its blocks, the count of a chunk), and each call of
`vg_aes_encrypt_blocks` with the same arguments in both runs (`nonce_rel`,
`hash_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0)

/-! ## `Offset_0` -/

theorem nonceBlock_check :
    ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs [.r4, .r5]) 24) nonceBlock h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem offset0_check :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block offset0) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `nonce`, in two runs with the same public arguments, nonce pointer and
length. -/
theorem nonce_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (A₁ : Args p τ₁.mem)
    (A₂ : Args p τ₂.mem) (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) :
    RelCT isa (Eq2 τ₁ τ₂) nonce TT :=
  rel_seqX (rel_envArg L E₁ E₂ A₁ A₂ [.r4, .r5] (by simp [h4, h5]) nonceBlock_check)
    (kept_of L E₁ [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (encOne_rel L K₁.env K₂.env (.inl rfl)) (exec_of_wp (encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env K₁.env) (C₂.env K₂.env) [] (by simp) offset0_check

/-! ## A chunk of `HASH` -/

/-- The start of a chunk: `Z` set if fewer than 16 blocks are left. -/
theorem chunkB0_ok {p : Prm} (L : Lay p) {t₀ t : State} {j : Nat} (H : HInv p t₀ t j) :
    WP isa (.block [.mov .r12 (.shifted .r7 .lsr 4), .cmp .r12 (imm 0)]) t fun t' =>
      HInv p t₀ t' j ∧ t'.z = decide (p.al / 16 - j < 16) := by
  have al32 := L.al_lt
  have m32 : p.al / 16 - j < 2 ^ 32 := by omega
  have z₁ : (BitVec.ofNat 32 (p.al / 16 - j) >>> 4 == 0) = decide (p.al / 16 - j < 16) := by
    rw [ofNat_lsr32 m32, z_cmp0 (by omega)]; congr 1; apply propext; omega
  refine WP.of_runBlock ⟨_, by orun [H.r7], ?_, ?_⟩
  · exact ⟨H.env.of_others (rs := [.r12]) (by others_tac) (by rfl) (by rfl) (by rfl), H.frame, H.rd, H.wr, H.le,
      H.sum, H.oh, by simp [gpr_setReg, H.r4], by simp [gpr_setReg, H.r6], by simp [gpr_setReg, H.r7], H.l0⟩
  · simp only [z_subFlags, gpr_setReg, ite_true, H.r7, BitVec.sub_zero, z₁]

/-- The count of a chunk, `min(16, r7)`, in `r5`. -/
theorem chunkSel_ok {p : Prm} {t₀ t : State} {j : Nat} (H : HInv p t₀ t j)
    (hz : t.z = decide (p.al / 16 - j < 16)) :
    WP isa (.ite .eq (.block [.mov .r5 (.reg .r7)]) (.block [.mov .r5 (imm 16)])) t fun t' =>
      HInv p t₀ t' j ∧ t'.gpr .r5 = BitVec.ofNat 32 (min 16 (p.al / 16 - j)) := by
  have Hk : ∀ {t' : State}, t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      Others [.r5] t t' → HInv p t₀ t' j := fun hm hrd hwr hsp ho =>
    ⟨H.env.of_others ho hsp hrd hwr, by rw [hm]; exact H.frame, by rw [hrd, H.rd], by rw [hwr, H.wr], H.le,
      by rw [hm]; exact H.sum, by rw [hm]; exact H.oh, by rw [ho _ (by decide), H.r4], by rw [ho _ (by decide), H.r6],
      by rw [ho _ (by decide), H.r7], by rw [hm]; exact H.l0⟩
  refine WP.ite (decide (p.al / 16 - j < 16)) (eval_eq' hz) (fun hb => ?_) (fun hb => ?_)
  · have hlt : p.al / 16 - j < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by orun [H.r7], Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac), ?_⟩
    simp [gpr_setReg, H.r7, show min 16 (p.al / 16 - j) = p.al / 16 - j by omega]
  · have hlt : ¬ p.al / 16 - j < 16 := by simpa using hb
    refine WP.of_runBlock ⟨_, by orun [], Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac), ?_⟩
    simp [gpr_setReg, show min 16 (p.al / 16 - j) = 16 by omega]

/-- After a chunk's call: the count back in `r5`, the buffer in `r8`. -/
theorem chunkB4_ok {p : Prm} (L : Lay p) {t₀ t₂ t₃ : State} {j c : Nat} (F : FillInv p t₀ j c t₂ c)
    (hc : c ≤ 16) (C : BlkPost encF (chunkCallSt p c t₂) p.K (p.W + BitVec.ofNat 32 bufO)
      (p.W + BitVec.ofNat 32 scrO) p.R c t₃) :
    WP isa (.block [addI .r8 .r11 bufO, .ldr .r5 .r11 cnO]) t₃ fun t' =>
      Env p t' ∧ t'.gpr .r5 = BitVec.ofNat 32 c ∧ t'.gpr .r8 = p.W + BitVec.ofNat 32 bufO := by
  have fw := L.ww
  have E₂ : Env p (chunkCallSt p c t₂) := (chunkCall_blk L F hc).2
  have E₃ : Env p t₃ := E₂.of_saved C.saved C.sp C.rd C.wr
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have eS : State.addr (p.W + BitVec.ofNat 32 scrO) = State.addr p.W + BitVec.ofNat 64 scrO := L.wA (by decide)
  have fr := C.frame
  rw [eB, eS, E₂.sp] at fr
  have cnt₃ : t₃.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := by
    rw [fr.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 212, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by simp only [bufO]; omega)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)]
    exact F.cnt
  have rC₃ : InRegions (t₃.rd ++ t₃.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₃.perm.wR (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₃.r11, eC, rC₃, cnt₃], ?_, ?_, ?_⟩
  · exact E₃.of_others (rs := [.r5, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp [gpr_setReg]
  · simp [gpr_setReg, E₃.r11, bufO]

theorem chunkB0_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r7]))
    (.block [.mov .r12 (.shifted .r7 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSelT_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.mov .r5 (.reg .r7)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSelF_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.mov .r5 (imm 16)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB1_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), addI .r8 .r11 bufO]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkFill_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5, .r6, .r8]))
    (.loop hashFill .ne) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB3_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (callArgs ++ [addI .r2 .r11 bufO, .ldr .r3 .r11 cnO])) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB4_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [addI .r8 .r11 bufO, .ldr .r5 .r11 cnO]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSum_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r5, .r8]))
    (.seq hashSum (.block [.cmp .r7 (imm 0)])) h).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs at the same block of the associated data. -/
theorem chunk_rel {p : Prm} (L : Lay p) {a b τ₁ τ₂ : State} {j : Nat} (H₁ : HInv p a τ₁ j) (H₂ : HInv p b τ₂ j)
    (hj : j < p.al / 16) : RelCT isa (Eq2 τ₁ τ₂) hashChunk TT := by
  have hc0 : 0 < min 16 (p.al / 16 - j) := by omega
  have hc : min 16 (p.al / 16 - j) ≤ 16 := Nat.min_le_left _ _
  have hjc : j + min 16 (p.al / 16 - j) ≤ p.al / 16 := by omega
  unfold hashChunk
  refine rel_seq (rel_env H₁.env H₂.env [.r7] (by simp [H₁.r7, H₂.r7]) chunkB0_check) (chunkB0_ok L H₁)
    (chunkB0_ok L H₂) fun u₁ u₂ ⟨U₁, z₁⟩ ⟨U₂, z₂⟩ => ?_
  refine rel_seq (rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_env U₁.env U₂.env [] (by simp) chunkSelT_check)
    (fun _ => rel_env U₁.env U₂.env [] (by simp) chunkSelF_check)) (chunkSel_ok U₁ z₁) (chunkSel_ok U₂ z₂)
    fun v₁ v₂ ⟨V₁, h5₁⟩ ⟨V₂, h5₂⟩ => ?_
  refine rel_seq (rel_env V₁.env V₂.env [] (by simp) chunkB1_check) (chunkHead_ok L V₁ hc hjc h5₁)
    (chunkHead_ok L V₂ hc hjc h5₂) fun w₁ w₂ F₁ F₂ => ?_
  refine rel_seq (rel_env F₁.env F₂.env [.r4, .r5, .r6, .r8] (by simp [F₁.r4, F₂.r4, F₁.r5, F₂.r5, F₁.r6, F₂.r6,
    F₁.r8, F₂.r8]) chunkFill_check) (fill_ok L hc0 hc hjc F₁) (fill_ok L hc0 hc hjc F₂) fun x₁ x₂ G₁ G₂ => ?_
  refine rel_seq (F₁ := fun y => y = chunkCallSt p _ x₁) (F₂ := fun y => y = chunkCallSt p _ x₂)
    (rel_env G₁.env G₂.env [] (by simp) chunkB3_check) (WP.of_runBlock ⟨_, chunkArgs_run L G₁, rfl⟩)
    (WP.of_runBlock ⟨_, chunkArgs_run L G₂, rfl⟩) fun y₁ y₂ e₁ e₂ => ?_
  subst e₁ e₂
  have B₁ := chunkCall_blk L G₁ hc
  have B₂ := chunkCall_blk L G₂ hc
  refine rel_seq (rel_blk encF B₁.1 B₂.1 (B₁.2.sp_eq B₂.2)) (blk_call encF B₁.1) (blk_call encF B₂.1)
    fun z₁ z₂ C₁ C₂ => ?_
  have E₁ : Env p z₁ := B₁.2.of_saved C₁.saved C₁.sp C₁.rd C₁.wr
  have E₂ : Env p z₂ := B₂.2.of_saved C₂.saved C₂.sp C₂.rd C₂.wr
  exact rel_seq (rel_env E₁ E₂ [] (by simp) chunkB4_check) (chunkB4_ok L G₁ hc C₁) (chunkB4_ok L G₂ hc C₂)
    fun _ _ ⟨D₁, r5₁, r8₁⟩ ⟨D₂, r5₂, r8₂⟩ => rel_env D₁ D₂ [.r5, .r8] (by simp [r5₁, r5₂, r8₁, r8₂]) chunkSum_check

/-! ## `HASH` -/

theorem hashHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24)
    (.block (Impl.AesGcm.Arm.zero16 sumO ++ Impl.AesGcm.Arm.zero16 ohO ++
      ([.ldrSp .r4 0, .ldrSp .r7 4, .mov .r7 (.shifted .r7 .lsr 4), .mov .r6 (imm 1), .cmp .r7 (imm 0)] :
        List Instr))) h).isSome =
      true := ⟨_, by taint_decide⟩

theorem hashMid_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24)
    (.block [.ldrSp .r5 4, .dp .and .r5 .r5 (imm 15), .cmp .r5 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorB .r11 .r10 .r11 ohO 240 ohO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestPad_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (padTo bufO) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestB_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorW ohO bufO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestC_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorW bufO sumO)) h).isSome = true := ⟨_, by taint_decide⟩

/-- The rest of the associated data, in two runs with the same pointer and
length. -/
theorem hashRest_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) : RelCT isa (Eq2 τ₁ τ₂) hashRest TT :=
  rel_seqX (rel_env E₁ E₂ [] (by simp) hashRestA_check)
    (kept_of L E₁ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (rel_env K₁.env K₂.env [.r4, .r5] (by
      simp [K₁.gpr .r4 (by simp), K₂.gpr .r4 (by simp), K₁.gpr .r5 (by simp), K₂.gpr .r5 (by simp), h4, h5])
      hashRestPad_check)
    (kept_of L K₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L K₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ M₁ M₂ =>
  rel_seqX (rel_env M₁.env M₂.env [] (by simp) hashRestB_check)
    (kept_of L M₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L M₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ N₁ N₂ =>
  rel_seqX (encOne_rel L N₁.env N₂.env (.inr rfl))
    (exec_of_wp (encOne_ok L N₁.env (d := bufO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L N₂.env (d := bufO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env N₁.env) (C₂.env N₂.env) [] (by simp) hashRestC_check

/-- `HASH`, in two runs with the same public arguments. -/
theorem hash_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (A₁ : Args p τ₁.mem)
    (A₂ : Args p τ₂.mem)
    (hl₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (lstarOf p τ₁.mem) 0)
    (hl₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (lstarOf p τ₂.mem) 0) :
    RelCT isa (Eq2 τ₁ τ₂) Impl.AesOcb.Arm.hash TT := by
  unfold Impl.AesOcb.Arm.hash
  refine rel_seq (rel_envArg L E₁ E₂ A₁ A₂ [] (by simp) hashHead_check) (hashHead_ok L E₁ A₁ hl₁)
    (hashHead_ok L E₂ A₂ hl₂) fun u₁ u₂ ⟨U₁, z₁⟩ ⟨U₂, z₂⟩ => ?_
  refine rel_seq ?_ (hashWhole_ok L U₁ z₁) (hashWhole_ok L U₂ z₂) fun v₁ v₂ V₁ V₂ => ?_
  · refine rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip) fun hb => ?_
    have hm : p.al / 16 ≠ 0 := by simpa using hb
    refine rel_loop (fun k σ₁ σ₂ => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ HInv p τ₁ σ₁ j ∧ HInv p τ₂ σ₂ j)
      (fun k σ₁ σ₂ ⟨j, hk, hj, H₁, H₂⟩ => ?_) (p.al / 16 - 0) ⟨0, rfl, by omega, U₁, U₂⟩
    refine rel_wpQ (chunk_rel L H₁ H₂ hj) (hashChunk_ok L H₁ hj) (hashChunk_ok L H₂ hj)
      fun x y ⟨X, zx⟩ ⟨Y, zy⟩ => ⟨by rw [eval_ne' zx, eval_ne' zy], fun hc => ?_⟩
    rw [eval_ne' zx] at hc
    have hlt : j + min 16 (p.al / 16 - j) < p.al / 16 := by
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hc; omega
    exact ⟨p.al / 16 - (j + min 16 (p.al / 16 - j)), by omega, _, rfl, hlt, X, Y⟩
  · have Av₁ : Args p v₁.mem := A₁.mut L (hashR_mut L V₁.frame)
    have Av₂ : Args p v₂.mem := A₂.mut L (hashR_mut L V₂.frame)
    refine rel_seq (rel_envArg L V₁.env V₂.env Av₁ Av₂ [] (by simp) hashMid_check) (hashMid_ok L V₁ Av₁)
      (hashMid_ok L V₂ Av₂) fun w₁ w₂ ⟨W₁, h5₁, z₁'⟩ ⟨W₂, h5₂, z₂'⟩ => ?_
    exact rel_ite (eval_eq' z₁') (eval_eq' z₂') (fun _ => rel_skip)
      (fun _ => hashRest_rel L W₁.env W₂.env (by rw [W₁.r4, W₂.r4]) (by rw [h5₁, h5₂]))

end VG.Proof.AesOcb.Arm
