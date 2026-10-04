import VerifiedGarbage.Proof.AesGcmSiv.Arm.KeysCT

/-!
# AES-GCM-SIV on ARMv7: POLYVAL is constant time

Untrusted: everything here is checked by Lean. A chunk's blocks, their
number and the pointers come from the public lengths and addresses; the
calls of `vg_ghash` have the same arguments in both runs; the branches and
loops are on counts both runs agree on.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (GhCall gh_call eval_eq' eval_ne' z_cmp z_subFlags mem_subFlags gpr_subFlags sp_subFlags
  rd_subFlags wr_subFlags)

theorem chunkPre_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5])) chunkPre h).isSome
    = true := ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r5]))
    (.block wholeLeft) h).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs with the same public arguments, pointer and count. -/
theorem chunk_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ₁ : Src p τ₁ Q (16 * (m / 16)))
    (hQ₂ : Src p τ₂ Q (16 * (m / 16))) (a4 : τ₁.gpr .r4 = Q) (b4 : τ₂.gpr .r4 = Q)
    (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 m) (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 m) :
    RelCT isa (Eq2 τ₁ τ₂) chunk TT := by
  refine rel_seq (rel_env E₁ E₂ [.r4, .r5] (by simp [a4, b4, a5, b5]) chunkPre_check)
    (chunkPre_ok L E₁ hm h16 hQ₁ a4 a5) (chunkPre_ok L E₂ hm h16 hQ₂ b4 b5) fun u₁ u₂ P₁ P₂ => ?_
  have wG : ∀ {u : State}, ChunkPre p Q m (min (m / 16) 64) τ₁ u ∨ ChunkPre p Q m (min (m / 16) 64) τ₂ u →
      WP isa Impl.AesGcm.Arm.ghFrame u fun w => Env p w ∧ w.gpr .r5 = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) :=
    fun h => by
      rcases h with P | P <;>
      exact WP.mono (gh_call P.call) fun _ G =>
        ⟨P.env.of_saved G.saved G.sp G.rd G.wr, by rw [G.saved _ (by decide) (by decide), P.r5]⟩
  exact rel_seq (rel_gh P₁.call P₂.call (P₁.env.sp_eq P₂.env)) (wG (.inl P₁)) (wG (.inr P₂))
    fun w₁ w₂ G₁ G₂ => rel_env G₁.1 G₂.1 [.r5] (by simp [G₁.2, G₂.2]) chunkEnd_check

/-- The chunks, in two runs from `σ₁` and `σ₂` with the same public arguments. -/
theorem chunks_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (hQ₁ : Src p σ₁ Q (16 * (m / 16))) (hQ₂ : Src p σ₂ Q (16 * (m / 16))) {d : Nat}
    (hd : d < m / 16) {τ₁ τ₂ : State} (I₁ : CInv p σ₁ Q m d τ₁) (I₂ : CInv p σ₂ Q m d τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop chunk .ne) TT := by
  refine rel_loop (fun k t₁ t₂ => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p σ₁ Q m d t₁ ∧ CInv p σ₂ Q m d t₂)
    (fun k t₁ t₂ ⟨d, hk, hd, J₁, J₂⟩ => ?_) (m / 16 - d) ⟨d, rfl, hd, I₁, I₂⟩
  refine rel_wpQ (chunk_rel L J₁.abs.env J₂.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) (J₂.src hQ₂ hd)
      J₁.r4 J₂.r4 J₁.r5 J₂.r5)
    (chunk_ok L J₁.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) J₁.r4 J₁.r5)
    (chunk_ok L J₂.abs.env (by omega) (by omega) (J₂.src hQ₂ hd) J₂.r4 J₂.r5) fun a b C₁ C₂ => ?_
  obtain ⟨K₁, z₁⟩ := J₁.step L hQ₁ hd C₁
  obtain ⟨K₂, z₂⟩ := J₂.step L hQ₂ hd C₂
  have ev₁ := eval_ne' z₁
  have ev₂ := eval_ne' z₂
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : m / 16 - (d + min (m / 16 - d) 64) ≠ 0 := by simpa using hc
  exact ⟨m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl, by omega, K₁, K₂⟩

theorem absHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block wholeLeft) h).isSome = true := ⟨_, by taint_decide⟩

theorem absCmp_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem absTailPre_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5])) absTailPre
    h).isSome = true := ⟨_, by taint_decide⟩

/-- `chunk` on the block at `W + 224`. -/
theorem chunkB_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (a4 : τ₁.gpr .r4 = p.W + BitVec.ofNat 32 224) (b4 : τ₂.gpr .r4 = p.W + BitVec.ofNat 32 224)
    (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 16) (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 16) :
    RelCT isa (Eq2 τ₁ τ₂) chunk TT :=
  chunk_rel L E₁ E₂ (m := 16) (by decide) (by decide) (srcB L E₁.perm) (srcB L E₂.perm) a4 b4 a5 b5

/-- `cmp r5, #0`. -/
theorem cmp5_ok {t : State} {r : Nat} (hr : r < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) t fun t' => t'.z = decide (r = 0) ∧ t'.gpr = t.gpr ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  Proof.AesGcm.Arm.WP.run ⟨_, by srun [h5], rfl⟩ fun t' ht => by
    subst ht
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [z_subFlags]
    rw [z_cmp hr (by decide)]

/-- `absorb`, in two runs with the same public arguments, pointer and count. -/
theorem absorb_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (hd : (⟨State.addr Q, m⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩)
    (hQ₁ : Src p τ₁ Q m) (hQ₂ : Src p τ₂ Q m)
    (a4 : τ₁.gpr .r4 = Q) (b4 : τ₂.gpr .r4 = Q) (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 m)
    (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 m) :
    RelCT isa (Eq2 τ₁ τ₂) absorb TT := by
  have wH : ∀ {τ : State}, Env p τ → τ.gpr .r4 = Q → τ.gpr .r5 = BitVec.ofNat 32 m →
      WP isa (.block wholeLeft) τ fun u => Env p u ∧ u.gpr .r4 = Q ∧ u.gpr .r5 = BitVec.ofNat 32 m ∧
        u.z = decide (m / 16 = 0) ∧ u.mem = τ.mem ∧ u.rd = τ.rd ∧ u.wr = τ.wr := fun E h4 h5 => by
    obtain ⟨u, run, z, ho, hm', sp, rd, wr⟩ := wholeLeft_ok hm h5
    exact WP.of_runBlock ⟨u, run, E.of_others ho sp rd wr, by rw [ho _ (by decide), h4],
      by rw [ho _ (by decide), h5], z, hm', rd, wr⟩
  refine rel_seq (rel_env E₁ E₂ [.r4, .r5] (by simp [a4, b4, a5, b5]) absHead_check) (wH E₁ a4 a5)
    (wH E₂ b4 b5) fun u₁ u₂ ⟨F₁, u4₁, u5₁, z₁, m₁, rd₁, wr₁⟩ ⟨F₂, u4₂, u5₂, z₂, m₂, rd₂, wr₂⟩ => ?_
  have hQ₁' := hQ₁.of_eq rd₁ wr₁
  have hQ₂' := hQ₂.of_eq rd₂ wr₂
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_eq' z₁) (eval_eq' z₂)
      (fun _ => rel_skip) (fun hf => ?_))
    (absMid_ok L F₁ hm hQ₁' u4₁ u5₁ z₁) (absMid_ok L F₂ hm hQ₂' u4₂ u5₂ z₂)
    fun w₁ w₂ ⟨A₁, r4₁, r5₁⟩ ⟨A₂, r4₂, r5₂⟩ => ?_
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_rel L hm (hQ₁'.take (by omega)) (hQ₂'.take (by omega)) (d := 0) (by omega)
      (CInv.zero F₁ u4₁ u5₁) (CInv.zero F₂ u4₂ u5₂)
  -- The last bytes.
  have wC : ∀ {w : State}, Env p w → w.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) →
      w.gpr .r5 = BitVec.ofNat 32 (m % 16) → WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) w fun u =>
        Env p u ∧ u.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ u.gpr .r5 = BitVec.ofNat 32 (m % 16) ∧
          u.z = decide (m % 16 = 0) ∧ u.rd = w.rd ∧ u.wr = w.wr := fun E h4 h5 =>
    WP.mono (cmp5_ok (by omega) h5) fun u ⟨z, g, _, sp, rd, wr⟩ =>
      ⟨E.keep (fun r _ => by rw [g]) sp rd wr, by rw [g, h4], by rw [g, h5], z, rd, wr⟩
  refine rel_seq (rel_env A₁.env A₂.env [.r4, .r5] (by simp [r4₁, r4₂, r5₁, r5₂]) absCmp_check)
    (wC A₁.env r4₁ r5₁) (wC A₂.env r4₂ r5₂) fun c₁ c₂ ⟨G₁, c4₁, c5₁, cz₁, crd₁, cwr₁⟩ ⟨G₂, c4₂, c5₂, cz₂, crd₂, cwr₂⟩ => ?_
  refine rel_ite (eval_eq' cz₁) (eval_eq' cz₂) (fun _ => rel_skip) (fun hf => ?_)
  have h0 : m % 16 ≠ 0 := by simpa using hf
  have ea := hQ₁.addr (j := 16 * (m / 16)) (by omega)
  have dT : (⟨State.addr (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint
      ⟨State.addr p.W, 4096⟩ := by
    rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega))
  have hs₁ := ((hQ₁'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)).of_eq A₁.rd A₁.wr).of_eq crd₁ cwr₁
  have hs₂ := ((hQ₂'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)).of_eq A₂.rd A₂.wr).of_eq crd₂ cwr₂
  refine rel_seq (rel_env G₁ G₂ [.r4, .r5] (by simp [c4₁, c4₂, c5₁, c5₂]) absTailPre_check)
    (absTailPre_ok L G₁ (by omega) (by omega) hs₁.rd hs₁.wrap dT c4₁ c5₁)
    (absTailPre_ok L G₂ (by omega) (by omega) hs₂.rd hs₂.wrap dT c4₂ c5₂) fun z₁ z₂ T₁ T₂ => ?_
  exact chunkB_rel L T₁.env T₂.env T₁.r4 T₂.r4 T₁.r5 T₂.r5

theorem lensBlock_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12) (.block lensBlock) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem tagIn_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block tagIn) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem polyA_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12)
    (.block [.mov .r4 (.reg .r7), .ldrSp .r5 0]) h).isSome = true := ⟨_, by taint_decide⟩

theorem polyD_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12)
    (.block [.ldrSp .r4 4, .ldrSp .r5 8]) h).isSome = true := ⟨_, by taint_decide⟩

/-- What a run keeps before a piece: the environment and the stack
arguments. -/
structure PR (p : Prm) (t : State) : Prop where
  env : Env p t
  args : Args p t.mem

/-- After absorbing. -/
theorem PR.of_abs {p : Prm} (L : Lay p) {xs : List Spec.GcmSiv.Elem} {t t' : State} (h : PR p t)
    (P : AbsPost p xs t t') : PR p t' :=
  ⟨P.env, h.args.frame L P.frame (absorbR_args L)⟩

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : PR p σ₁) (R₂ : PR p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) polyval TT := by
  have wA : ∀ {σ : State}, PR p σ → WP isa (.block [.mov .r4 (.reg .r7), .ldrSp .r5 0]) σ fun t =>
      PR p t ∧ t.gpr .r4 = p.A ∧ t.gpr .r5 = BitVec.ofNat 32 p.al := fun R => by
    have a₀ := R.env.perm.argR' L (k := 0) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [R.env.sp, a₀, R.args.a0], rfl⟩ fun t ht => ?_
    subst ht
    exact ⟨⟨R.env.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, R.args⟩,
      by simp [gpr_setReg, R.env.r7], by simp [gpr_setReg]⟩
  have wD : ∀ {σ : State}, PR p σ → WP isa (.block [.ldrSp .r4 4, .ldrSp .r5 8]) σ fun t =>
      PR p t ∧ t.gpr .r4 = p.D ∧ t.gpr .r5 = BitVec.ofNat 32 p.n := fun R => by
    have a₄ := R.env.perm.argR' L (k := 4) (by decide)
    have a₈ := R.env.perm.argR' L (k := 8) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [R.env.sp, a₄, a₈, R.args.a4, R.args.a8], rfl⟩ fun t ht => ?_
    subst ht
    exact ⟨⟨R.env.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, R.args⟩,
      by simp [gpr_setReg], by simp [gpr_setReg]⟩
  refine rel_seq (rel_envArg L R₁.env R₂.env R₁.args R₂.args [] (by simp) polyA_check) (wA R₁) (wA R₂)
    fun a₁ a₂ ⟨G₁, a4₁, a5₁⟩ ⟨G₂, a4₂, a5₂⟩ => ?_
  refine rel_seq (absorb_rel L G₁.env G₂.env L.al_lt L.a_w (srcA L G₁.env.perm) (srcA L G₂.env.perm) a4₁ a4₂ a5₁ a5₂)
    (absorb_ok L G₁.env L.al_lt (srcA L G₁.env.perm) L.a_w a4₁ a5₁)
    (absorb_ok L G₂.env L.al_lt (srcA L G₂.env.perm) L.a_w a4₂ a5₂)
    fun b₁ b₂ B₁ B₂ => ?_
  have H₁ := G₁.of_abs L B₁
  have H₂ := G₂.of_abs L B₂
  refine rel_seq (rel_envArg L H₁.env H₂.env H₁.args H₂.args [] (by simp) polyD_check) (wD H₁) (wD H₂)
    fun c₁ c₂ ⟨K₁, c4₁, c5₁⟩ ⟨K₂, c4₂, c5₂⟩ => ?_
  refine rel_seq (absorb_rel L K₁.env K₂.env L.n_lt L.d_w (srcD L K₁.env.perm) (srcD L K₂.env.perm) c4₁ c4₂ c5₁ c5₂)
    (absorb_ok L K₁.env L.n_lt (srcD L K₁.env.perm) L.d_w c4₁ c5₁)
    (absorb_ok L K₂.env L.n_lt (srcD L K₂.env.perm) L.d_w c4₂ c5₂)
    fun d₁ d₂ D₁ D₂ => ?_
  have M₁ := K₁.of_abs L D₁
  have M₂ := K₂.of_abs L D₂
  refine rel_seq (c₁ := lens) ?_ (lens_ok L M₁.env M₁.args) (lens_ok L M₂.env M₂.args) fun e₁ e₂ F₁ F₂ =>
    rel_env F₁.env F₂.env [] (by simp) tagIn_check
  have wL : ∀ {d : State}, PR p d → WP isa (.block lensBlock) d fun t =>
      Env p t ∧ t.gpr .r4 = p.W + BitVec.ofNat 32 224 ∧ t.gpr .r5 = BitVec.ofNat 32 16 := fun R => by
    have w₀ := R.env.perm.wW (show 224 + 4 ≤ 4096 by decide)
    have w₁ := R.env.perm.wW (show 228 + 4 ≤ 4096 by decide)
    have w₂ := R.env.perm.wW (show 232 + 4 ≤ 4096 by decide)
    have w₃ := R.env.perm.wW (show 236 + 4 ≤ 4096 by decide)
    have a₀ := R.env.perm.argR' L (k := 0) (by decide)
    have a₈ := R.env.perm.argR' L (k := 8) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by simp only [lensBlock]; srun [R.env.r11, R.env.sp, L.wA, a₀, a₈,
      R.args.a0, R.args.a8, w₀, w₁, w₂, w₃], rfl⟩ fun t ht => ?_
    subst ht
    refine ⟨R.env.keep (fun q hq => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      by simp [gpr_setReg, R.env.r11], by simp [gpr_setReg]⟩
  exact rel_seq (rel_envArg L M₁.env M₂.env M₁.args M₂.args [] (by simp) lensBlock_check) (wL M₁)
    (wL M₂) fun f₁ f₂ ⟨K₁, x4₁, x5₁⟩ ⟨K₂, x4₂, x5₂⟩ => chunkB_rel L K₁ K₂ x4₁ x4₂ x5₁ x5₂

end VG.Proof.AesGcmSiv.Arm
