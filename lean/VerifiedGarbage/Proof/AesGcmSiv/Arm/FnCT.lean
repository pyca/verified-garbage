import VerifiedGarbage.Proof.AesGcmSiv.Arm.PolyvalCT

/-!
# AES-GCM-SIV on ARMv7: the functions are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments (`onePub`) have the same `prmOf`; each piece of `seal` and
`open` is related in the two runs by the lemmas of `KeysCT.lean` and
`PolyvalCT.lean`, the counter mode's blocks by `vg_aes_ctr32`'s proof with
the same arguments in both runs, and the comparison, the mask and the
restore by the taint analysis (`seal_ct`, `open_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall ctr_call eval_eq' eval_ne' arg args argAddr_zero)

/-! ## The tag -/

theorem tagA_check {o : Nat} (ho : o = 0 ∨ o = 176) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (pubRegs [])) (.block (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
      ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr))) h).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {o : Nat}
    (ho : o = 0 ∨ o = 176) : RelCT isa (Eq2 τ₁ τ₂) (tag o) TT := by
  have w : ∀ {τ : State}, Env p τ → WP isa (.block (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
      ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr))) τ fun t₁ => CtrCall t₁ (p.W + BitVec.ofNat 32 192)
        (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 o) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ Env p t₁ :=
    fun E => by
      obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := tagArgs_ok L E ho
      have E' : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
      exact WP.of_runBlock ⟨t₁, run₁, tagCall L E' ho r0 r1 r2 r3 r12 lr, E'⟩
  exact rel_seq (rel_env E₁ E₂ [] (by simp) (tagA_check ho)) (w E₁) (w E₂)
    fun a b A₁ A₂ => rel_ctr A₁.1 A₂.1 (A₁.2.sp_eq A₂.2)

/-! ## Counter mode -/

theorem blkA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkP_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block blockNext) h).isSome = true := ⟨_, by taint_decide⟩

/-- What the constant-time proof needs of a run of counter mode after `j`
blocks. -/
structure BL (p : Prm) (j : Nat) (t : State) : Prop where
  env : Env p t
  r4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)

/-- A block of counter mode, in two runs with the same public arguments,
pointer and count. -/
theorem cryptBlock_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (B₁ : BL p j τ₁) (B₂ : BL p j τ₂) : RelCT isa (Eq2 τ₁ τ₂) cryptBlock TT := by
  have w : ∀ {τ : State}, BL p j τ →
      WP isa (.block (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr))) τ fun t₁ =>
        CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.D + BitVec.ofNat 32 (16 * j))
          (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ BL p j t₁ := fun B => by
    obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok L B.env B.r4
    have E' : Env p t₁ := B.env.of_others ho₁ sp₁ rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, blkCall L E' hj r0 r1 r2 r3 r12 lr, E', by rw [ho₁ _ (by decide), B.r4],
      by rw [ho₁ _ (by decide), B.r5]⟩
  have wc : ∀ {t : State}, (CtrCall t (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112)
      (p.D + BitVec.ofNat 32 (16 * j)) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ BL p j t) →
      WP isa Impl.AesGcm.Arm.ctrFrame t (BL p j) := fun ⟨cc, B⟩ =>
    WP.mono (ctr_call cc) fun _ P => ⟨B.env.of_saved P.saved P.sp P.rd P.wr,
      by rw [P.saved _ (by decide) (by decide), B.r4], by rw [P.saved _ (by decide) (by decide), B.r5]⟩
  refine rel_seq (rel_env B₁.env B₂.env [.r4, .r5] (by simp [B₁.r4, B₂.r4, B₁.r5, B₂.r5]) blkA_check) (w B₁)
    (w B₂) fun u₁ u₂ A₁ A₂ => ?_
  exact rel_seq (rel_ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (wc A₁) (wc A₂)
    fun w₁ w₂ C₁ C₂ => rel_env C₁.env C₂.env [.r4, .r5] (by simp [C₁.r4, C₂.r4, C₁.r5, C₂.r5]) blkP_check

/-- A block of counter mode, for its registers. -/
theorem cryptBlockL_ok {p : Prm} (L : Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) {t : State} (B : BL p j t) :
    WP isa cryptBlock t fun t' => BL p (j + 1) t' ∧ t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0) := by
  obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok L B.env B.r4
  have E₁ : Env p t₁ := B.env.of_others ho₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call (blkCall L E₁ hj r0 r1 r2 r3 r12 lr)) fun t₂ P => ?_)
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.r4]
  have h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.r5]
  obtain ⟨t₃, run₃, -, r4₃, r5₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := blkPost_ok L E₂ hj h4₂ h5₂
  exact WP.of_runBlock ⟨t₃, run₃, ⟨E₂.of_others ho₃ sp₃ rd₃ wr₃, r4₃, r5₃⟩, z₃⟩

/-- The whole blocks of counter mode, for their registers. -/
theorem cryptMidL_ok {p : Prm} (L : Lay p) {t : State} (B : BL p 0 t) (hz : t.z = decide (p.n / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop cryptBlock .ne)) t (BL p (p.n / 16)) := by
  refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n / 16 = 0 := by simpa using ht
    rw [h0]; exact WP.block_nil B
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t') ?_
      (p.n / 16 - 0) t ⟨0, rfl, by omega, B⟩
    rintro k t' ⟨j, rfl, hj, B'⟩
    refine WP.mono (cryptBlockL_ok L (j := j) (by omega) B') fun t'' ⟨B'', z⟩ => ?_
    have ev := eval_ne' z
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega), he ▸ B''⟩
    · right; exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, B''⟩

theorem cryptHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12) (.block cryptHead) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem crypt5_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem cryptTailRest_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.seq (.block [Impl.AesGcm.Arm.addI .r1 .r11 bO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)])
      Impl.AesGcm.Arm.xorLoop) h).isSome = true := ⟨_, by taint_decide⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : PR p σ₁) (R₂ : PR p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) crypt TT := by
  have hn := L.n_lt
  have wh : ∀ {σ : State}, PR p σ → WP isa (.block cryptHead) σ fun t₁ => BL p 0 t₁ ∧
      t₁.z = decide (p.n / 16 = 0) := fun R => by
    obtain ⟨t₁, run₁, -, r4₁, r5₁, z₁, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L R.env R.args
    exact WP.of_runBlock ⟨t₁, run₁, ⟨R.env.of_others ho₁ sp₁ rd₁ wr₁,
      by rw [r4₁, Nat.mul_zero, Proof.AesGcm.Arm.add_ofNat_zero], by rw [r5₁, Nat.mul_zero, Nat.sub_zero]⟩, z₁⟩
  refine rel_seq (rel_envArg L R₁.env R₂.env R₁.args R₂.args [] (by simp) cryptHead_check) (wh R₁) (wh R₂)
    fun u₁ u₂ ⟨B₁, z₁⟩ ⟨B₂, z₂⟩ => ?_
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip) (fun hf => ?_))
    (cryptMidL_ok L B₁ z₁) (cryptMidL_ok L B₂ z₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t₁ ∧ BL p j t₂)
      (fun k t₁ t₂ ⟨j, hk, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 0) ⟨0, rfl, by omega, B₁, B₂⟩
    refine rel_wpQ (cryptBlock_rel L (j := j) (by omega) J₁ J₂)
      (cryptBlockL_ok L (by omega) J₁) (cryptBlockL_ok L (by omega) J₂) fun a b ⟨K₁, z₁⟩ ⟨K₂, z₂⟩ => ?_
    have ev₁ := eval_ne' z₁
    have ev₂ := eval_ne' z₂
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : (p.n - 16 * (j + 1)) / 16 ≠ 0 := by simpa using hc
    exact ⟨p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, K₁, K₂⟩
  -- The last bytes.
  have r5₁ : w₁.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [C₁.r5]; congr 1; omega
  have r5₂ : w₂.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [C₂.r5]; congr 1; omega
  have wC : ∀ {w : State}, BL p (p.n / 16) w → w.gpr .r5 = BitVec.ofNat 32 (p.n % 16) →
      WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) w fun u =>
        BL p (p.n / 16) u ∧ u.z = decide (p.n % 16 = 0) := fun B h5 =>
    WP.mono (cmp5_ok (by omega) h5) fun u ⟨z, g, _, sp, rd, wr⟩ =>
      ⟨⟨B.env.keep (fun r _ => by rw [g]) sp rd wr, by rw [g, B.r4], by rw [g, B.r5]⟩, z⟩
  refine rel_seq (rel_env C₁.env C₂.env [.r4, .r5] (by simp [C₁.r4, C₂.r4, C₁.r5, C₂.r5]) crypt5_check)
    (wC C₁ r5₁) (wC C₂ r5₂) fun c₁ c₂ ⟨D₁, cz₁⟩ ⟨D₂, cz₂⟩ => ?_
  refine rel_ite (eval_eq' cz₁) (eval_eq' cz₂) (fun _ => rel_skip) (fun _ => ?_)
  refine rel_seq (tag_rel L D₁.env D₂.env (o := 176) (by decide)) (tag_ok L D₁.env (o := 176) (by decide))
    (tag_ok L D₂.env (o := 176) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact rel_env T₁.env T₂.env [.r4, .r5] (by simp [T₁.r4, T₂.r4, T₁.r5, T₂.r5, D₁.r4, D₂.r4, D₁.r5, D₂.r5])
    cryptTailRest_check

/-! ## The functions -/

theorem entry_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint [.r0, .r1, .r2, .r3] 20) (.block entry) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem sealEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 16)
    (.block (tagOut ++ Impl.AesGcm.Arm.restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem recv_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 16) (.block recv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem openEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12)
    (.seq (.block cmp) (.seq mask (.block Impl.AesGcm.Arm.restore))) h).isSome = true := ⟨_, by taint_decide⟩

/-- The public arguments of two states with the same public data. -/
theorem prmOf_eq {σ₁ σ₂ : State} (h : onePub σ₁ σ₂) : prmOf σ₁ = prmOf σ₂ := by
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := h
  simp only [prmOf, h0, h1, h2, h3, hsp, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide),
    ha 4 (by decide)]

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {σ₁ σ₂ : State} (L₁ : Lay (prmOf σ₁)) (P₁ : Perm (prmOf σ₁) σ₁) (L₂ : Lay (prmOf σ₂))
    (P₂ : Perm (prmOf σ₂) σ₂) (h : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have hw : ∀ {σ : State}, Lay (prmOf σ) → Perm (prmOf σ) σ → σ.sp.toNat + 20 ≤ 2 ^ 32 ∧
      ∀ r ∈ σ.wr, Region.Disjoint ⟨State.addr σ.sp, 20⟩ r := fun L P => ⟨L.spf, P.argw⟩
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := h
  exact rel_arg _ 20 (by simp [h0, h1, h2, h3]) hsp (hw L₁ P₁) (hw L₂ P₂)
    (argMem_of (j := 5) hsp L₁.spf fun i hi => ha i hi) entry_check

/-- After the entry, what a run keeps. -/
theorem PR.entry {s s₁ : State} (L : Lay (prmOf s)) (En : Entered s s₁) : PR (prmOf s) s₁ :=
  ⟨En.env, (args_of s).frame L En.frame (by disj_tac L)⟩

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -⟩ := args_of_seal h₁
  obtain ⟨L₂, P₂, -⟩ := args_of_seal h₂
  have e := prmOf_eq hp
  refine rel_seq (entry_rel L P₁ L₂ P₂ hp) (entry_ok L P₁) (entry_ok L₂ P₂) fun τ₁ τ₂ En₁ En₂ => ?_
  have R₁ := PR.entry L En₁
  have R₂ := PR.entry L₂ En₂
  rw [← e] at R₂
  refine rel_seq (keys_rel L R₁.env R₂.env) (keys_ok L R₁.env) (keys_ok L R₂.env) fun a₁ a₂ K₁ K₂ => ?_
  have S₁ : PR (prmOf σ₁) a₁ := ⟨K₁.env, R₁.args.frame L K₁.frame (by disj_tac L)⟩
  have S₂ : PR (prmOf σ₁) a₂ := ⟨K₂.env, R₂.args.frame L K₂.frame (by disj_tac L)⟩
  refine rel_seq (polyval_rel L S₁ S₂) (polyval_ok L S₁.env S₁.args K₁.hkey K₁.acc)
    (polyval_ok L S₂.env S₂.args K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  have U₁ : PR (prmOf σ₁) b₁ := ⟨P₁.env, S₁.args.frame L P₁.frame (by disj_tac L)⟩
  have U₂ : PR (prmOf σ₁) b₂ := ⟨P₂.env, S₂.args.frame L P₂.frame (by disj_tac L)⟩
  refine rel_seq (tag_rel L U₁.env U₂.env (o := 0) (by decide)) (tag_ok L U₁.env (o := 0) (by decide))
    (tag_ok L U₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  have V₁ : PR (prmOf σ₁) c₁ := ⟨T₁.env, U₁.args.frame L T₁.frame (by disj_tac L)⟩
  have V₂ : PR (prmOf σ₁) c₂ := ⟨T₂.env, U₂.args.frame L T₂.frame (by disj_tac L)⟩
  exact rel_seq (crypt_rel L V₁ V₂) (crypt_ok L V₁.env V₁.args) (crypt_ok L V₂.env V₂.args)
    fun d₁ d₂ C₁ C₂ => rel_envArg16 L C₁.env C₂.env (V₁.args.frame L C₁.frame (by disj_tac L))
      (V₂.args.frame L C₂.frame (by disj_tac L)) [] (by simp) sealEnd_check

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁⟩ := args_of_open h₁
  obtain ⟨L₂, P₂⟩ := args_of_open h₂
  have e := prmOf_eq hp
  refine rel_seq (entry_rel L P₁ L₂ P₂ hp) (entry_ok L P₁) (entry_ok L₂ P₂) fun τ₁ τ₂ En₁ En₂ => ?_
  have R₀₁ := PR.entry L En₁
  have R₀₂ := PR.entry L₂ En₂
  rw [← e] at R₀₂
  have wr : ∀ {τ : State}, PR (prmOf σ₁) τ → WP isa (.block recv) τ (PR (prmOf σ₁)) := fun {τ} R => by
    obtain ⟨t, run, fR, -, ho, sp, rd, wr⟩ := recv_ok L R.env R.args
    have fR' : Frame [⟨State.addr (prmOf σ₁).W + BitVec.ofNat 64 0, 16⟩] τ.mem t.mem := by
      rw [BitVec.add_zero]; exact fR
    exact WP.of_runBlock ⟨t, run, R.env.of_others ho sp rd wr, R.args.frame L fR' (by disj_tac L)⟩
  refine rel_seq (rel_envArg16 L R₀₁.env R₀₂.env R₀₁.args R₀₂.args [] (by simp) recv_check) (wr R₀₁) (wr R₀₂)
    fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine rel_seq (keys_rel L R₁.env R₂.env) (keys_ok L R₁.env) (keys_ok L R₂.env) fun a₁ a₂ K₁ K₂ => ?_
  have S₁ : PR (prmOf σ₁) a₁ := ⟨K₁.env, R₁.args.frame L K₁.frame (by disj_tac L)⟩
  have S₂ : PR (prmOf σ₁) a₂ := ⟨K₂.env, R₂.args.frame L K₂.frame (by disj_tac L)⟩
  refine rel_seq (crypt_rel L S₁ S₂) (crypt_ok L S₁.env S₁.args) (crypt_ok L S₂.env S₂.args)
    fun b₁ b₂ C₁ C₂ => ?_
  have U₁ : PR (prmOf σ₁) b₁ := ⟨C₁.env, S₁.args.frame L C₁.frame (by disj_tac L)⟩
  have U₂ : PR (prmOf σ₁) b₂ := ⟨C₂.env, S₂.args.frame L C₂.frame (by disj_tac L)⟩
  have hG : ∀ {σ τ : State}, KeysPost (prmOf σ₁) σ τ → ∀ {u : State}, CryptPost (prmOf σ₁) τ u →
      Spec.Gcm.blockAt u.mem (State.addr (prmOf σ₁).W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt u.mem (State.addr (prmOf σ₁).W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt u.mem (State.addr (prmOf σ₁).W + BitVec.ofNat 64 80) = 0 := by
    intro _ _ K _ C
    rw [Proof.AesGcm.Arm.blockAt_frame C.frame (by disj_tac L), K.hkey,
      Proof.AesGcm.Arm.blockAt_frame C.frame (by disj_tac L), K.acc,
      bytesAt_keep C.frame (by disj_tac L) (by decide)]
    exact ⟨rfl, rfl⟩
  refine rel_seq (polyval_rel L U₁ U₂) (polyval_ok L U₁.env U₁.args (hG K₁ C₁).1 (hG K₁ C₁).2)
    (polyval_ok L U₂.env U₂.args (hG K₂ C₂).1 (hG K₂ C₂).2) fun c₁ c₂ P₁ P₂ => ?_
  have V₁ : PR (prmOf σ₁) c₁ := ⟨P₁.env, U₁.args.frame L P₁.frame (by disj_tac L)⟩
  have V₂ : PR (prmOf σ₁) c₂ := ⟨P₂.env, U₂.args.frame L P₂.frame (by disj_tac L)⟩
  refine rel_seq (tag_rel L V₁.env V₂.env (o := 176) (by decide)) (tag_ok L V₁.env (o := 176) (by decide))
    (tag_ok L V₂.env (o := 176) (by decide)) fun d₁ d₂ T₁ T₂ => ?_
  exact rel_envArg L T₁.env T₂.env (V₁.args.frame L T₁.frame (by disj_tac L))
    (V₂.args.frame L T₂.frame (by disj_tac L)) [] (by simp) openEnd_check

end VG.Proof.AesGcmSiv.Arm
