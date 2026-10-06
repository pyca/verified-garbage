import VerifiedGarbage.Proof.AesGcmSiv.AArch64.PolyvalCT

/-!
# AES-GCM-SIV on AArch64: the tag, counter mode and the functions are constant time

Untrusted: everything here is checked by Lean. Each call of `vg_aes_ctr32`
has the same arguments in both runs, which encrypt the same number of
blocks; the code around the calls, the comparison and the mask pass the
taint analysis (`open` never branches on whether the tag is right). The
loads of `W` from the stack and of `tag`'s address from `W` give the same
address in both runs (by correctness), and the taint analysis checks the
code after them (`entry_rel`, `rel_ldrT`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ctr rel_ite rel_taint ct_of GcmImpl CtrCall ctr_call eval_zero in_off
  RelCT.block_split
  eval_nonzero Others add_ofNat_assoc ofNat_sub lsr_ofNat)

/-! ## The tag -/

theorem tagA_check {o : Nat} (ho : o = 0 ∨ o = 224) : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ [Impl.AesGcm.AArch64.ptr .x3 .x19 o])) h).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {o : Nat}
    (ho : o = 0 ∨ o = 224) : RelCT isa (Eq2 τ₁ τ₂) (tag v.callees o) TT := by
  have w : ∀ {τ : State}, Env p τ → WP isa (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++
      [Impl.AesGcm.AArch64.ptr .x3 .x19 o])) τ fun t₁ => CtrCall t₁ (p.W + BitVec.ofNat 64 240)
        (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 o) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧ Env p t₁ :=
    fun E => by
      obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := tagArgs_ok E ho
      have E' : Env p t₁ := E.keep (fun r hr => ho₁ r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
      exact WP.of_runBlock ⟨t₁, run₁, tagCall L E' ho x0 x1 x2 x3 x4 x5, E'⟩
  exact rel_seq (rel_env E₁ E₂ [] (by simp) (tagA_check ho)) (w E₁) (w E₂)
    fun a b A₁ A₂ => rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.sp_eq A₂.2)

/-! ## Counter mode -/

theorem blkA_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28]))
    (.block (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27])) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkP_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28]))
    (.block [.ldr .w .x9 .x19 cbO, .addImm .w .x9 .x9 1, .str .w .x9 .x19 cbO, Impl.AesGcm.AArch64.ptr .x27 .x27 16,
      .subImm .x .x28 .x28 16, .lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A block of counter mode, in two runs with the same public arguments,
pointer and count. -/
theorem cryptBlock_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {j : Nat} (hj : 16 * (j + 1) ≤ p.n) (a27 : τ₁.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j))
    (b27 : τ₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)) (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j))
    (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) :
    RelCT isa (Eq2 τ₁ τ₂) (cryptBlock v.callees) TT := by
  have w : ∀ {τ : State}, Env p τ → τ.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) →
      τ.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) →
      WP isa (.block (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27])) τ fun t₁ =>
        CtrCall t₁ (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112) (p.D + BitVec.ofNat 64 (16 * j))
          (p.W + BitVec.ofNat 64 1760) p.R 1 ∧ Env p t₁ ∧ t₁.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧
          t₁.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := fun E h27 h28 => by
    obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok E h27
    have E' : Env p t₁ := E.keep (fun r hr => ho₁ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, blkCall L E' hj x0 x1 x2 x3 x4 x5, E', by rw [ho₁ _ (by decide), h27],
      by rw [ho₁ _ (by decide), h28]⟩
  have wc : ∀ {t : State}, (CtrCall t (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112)
      (p.D + BitVec.ofNat 64 (16 * j)) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧ Env p t ∧
      t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧ t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) →
      WP isa (callCtr v.callees) t fun u => Env p u ∧ u.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) ∧
        u.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := fun ⟨cc, E, h27, h28⟩ =>
    WP.mono (ctr_call v.ctr cc) fun _ P => ⟨E.of_saved P.saved P.sp P.rd P.wr,
      by rw [P.saved _ (by decide) (by decide), h27], by rw [P.saved _ (by decide) (by decide), h28]⟩
  refine rel_seq (rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) blkA_check) (w E₁ a27 a28)
    (w E₂ b27 b28) fun u₁ u₂ A₁ A₂ => ?_
  exact rel_seq (rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.1.sp_eq A₂.2.1)) (wc A₁) (wc A₂)
    fun w₁ w₂ ⟨F₁, c27₁, c28₁⟩ ⟨F₂, c27₂, c28₂⟩ => rel_env F₁ F₂ [.x27, .x28] (by simp [c27₁, c27₂, c28₁, c28₂])
      blkP_check

/-- What the constant-time proof needs of a run of counter mode after `j`
blocks. -/
structure BL (p : Prm) (j : Nat) (t : State) : Prop where
  env : Env p t
  x27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)
  x28 : t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)

/-- A block of counter mode, for its registers. -/
theorem cryptBlockL_ok (v : GcmImpl) {p : Prm} (L : Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) {t : State}
    (B : BL p j t) :
    WP isa (cryptBlock v.callees) t fun t' => BL p (j + 1) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * (j + 1)) / 16) := by
  have hn := L.n_lt
  obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok B.env B.x27
  have E₁ : Env p t₁ := B.env.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr (blkCall L E₁ hj x0 x1 x2 x3 x4 x5)) fun t₂ P => ?_)
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.x27]
  have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.x28]
  have c₀ := E₂.perm.wR (show 96 + 4 ≤ 3808 by decide)
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 3808 by decide)
  refine WP.run ⟨_, by grun [E₂.x19, c₀, c₁, h27₂, h28₂], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  refine ⟨⟨E₂.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, ?_, ?_⟩, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, add_ofNat_assoc]
    congr 2
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega)]; congr 1
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega), lsr_ofNat _ _ (by omega)]; congr 2

/-- The whole blocks of counter mode, for their registers. -/
theorem cryptMidL_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (B : BL p 0 t)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 (p.n / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (cryptBlock v.callees) (.nonzero .x .x9))) t
      (BL p (p.n / 16)) := by
  have hn := L.n_lt
  refine WP.ite (decide (p.n / 16 = 0)) (eval_zero h9 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n / 16 = 0 := by simpa using ht
    rw [h0]; exact WP.block_nil B
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t') ?_
      (p.n / 16 - 0) t ⟨0, rfl, by omega, B⟩
    rintro k t' ⟨j, rfl, hj, B'⟩
    refine WP.mono (cryptBlockL_ok v L (j := j) (by omega) B') fun t'' ⟨B'', x9⟩ => ?_
    have ev := eval_nonzero x9 (by omega)
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega), he ▸ B''⟩
    · right; exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, B''⟩

theorem cryptHead_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block cryptHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptTailRest_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28]))
    (.seq (.block [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27,
      Impl.AesGcm.AArch64.mov .x13 .x28]) Impl.AesGcm.AArch64.xorLoop) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt v.callees) TT := by
  have hn := L.n_lt
  have wh : ∀ {σ : State}, Env p σ → WP isa (.block cryptHead) σ fun t₁ => BL p 0 t₁ ∧
      t₁.gpr .x9 = BitVec.ofNat 64 (p.n / 16) := fun E => by
    obtain ⟨t₁, run₁, -, x27₁, x28₁, x9₁, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, ⟨E.keep (fun r hr => ho₁ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁,
      by rw [x27₁, Nat.mul_zero, BitVec.add_zero], by rw [x28₁, Nat.mul_zero, Nat.sub_zero]⟩, x9₁⟩
  refine rel_seq (rel_env E₁ E₂ [] (by simp) cryptHead_check) (wh E₁) (wh E₂)
    fun u₁ u₂ ⟨B₁, x9₁⟩ ⟨B₂, x9₂⟩ => ?_
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega)) (eval_zero x9₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (cryptMidL_ok v L B₁ x9₁) (cryptMidL_ok v L B₂ x9₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t₁ ∧ BL p j t₂)
      (fun k t₁ t₂ ⟨j, hk, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 0) ⟨0, rfl, by omega, B₁, B₂⟩
    refine rel_wpQ (cryptBlock_rel v L J₁.env J₂.env (j := j) (by omega) J₁.x27 J₂.x27 J₁.x28 J₂.x28)
      (cryptBlockL_ok v L (by omega) J₁) (cryptBlockL_ok v L (by omega) J₂) fun a b ⟨K₁, x9₁⟩ ⟨K₂, x9₂⟩ => ?_
    have ev₁ := eval_nonzero x9₁ (by omega)
    have ev₂ := eval_nonzero x9₂ (by omega)
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : j + 1 ≠ p.n / 16 := by simp at hc; omega
    exact ⟨p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, K₁, K₂⟩
  -- The last bytes.
  have x28₁ : w₁.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₁.x28]; congr 1; omega
  have x28₂ : w₂.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₂.x28]; congr 1; omega
  refine rel_ite (eval_zero x28₁ (by omega)) (eval_zero x28₂ (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun _ => ?_)
  refine rel_seq (tag_rel v L C₁.env C₂.env (o := 224) (by decide)) (tag_ok v L C₁.env (o := 224) (by decide))
    (tag_ok v L C₂.env (o := 224) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact rel_env T₁.env T₂.env [.x27, .x28] (by simp [T₁.x27, T₂.x27, T₁.x28, T₂.x28, C₁.x27, C₂.x27, C₁.x28, C₂.x28])
    cryptTailRest_check

/-! ## The functions -/

/-- `ldr x9, [sp]`: `W` in `x9`. -/
theorem ldr9_ok {s : State} (hA : Covers [args s] (s.rd ++ s.wr)) :
    WP isa (.block [.ldrSp .x9 0]) s fun s' => s'.gpr .x9 = stackArg s 0 ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa [args, stackArgAddr] using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  refine WP.run ⟨_, by grun [BitVec.add_zero, a₀], rfl⟩ fun s' hs => ?_
  subst hs
  exact ⟨by simp [gpr_write, stackArg, stackArgAddr, Mem.readW], fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl⟩

theorem ldr9_check : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 0]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem entryRest_check : ∃ h, (taint.check (Taint.ofRegs [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
    (.block (Impl.AesGcm.AArch64.save .x9 ++ [Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x2,
      Impl.AesGcm.AArch64.mov .x21 .x0, Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x23 .x3,
      Impl.AesGcm.AArch64.mov .x24 .x4, Impl.AesGcm.AArch64.mov .x25 .x5, Impl.AesGcm.AArch64.mov .x26 .x6,
      .str .x .x7 .x19 tagPO])) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block Impl.AesGcm.AArch64.restore) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem openEnd_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.seq (.block cmp) (.seq mask (.block ([Impl.AesGcm.AArch64.mov .x0 .x27] ++ Impl.AesGcm.AArch64.restore)))) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- The public arguments of two states with the same public data. -/
theorem prmOf_eq {σ₁ σ₂ : State} (h : onePub σ₁ σ₂) : prmOf σ₁ = prmOf σ₂ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw⟩ := h
  simp only [prmOf, h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw]

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {σ₁ σ₂ : State} (h : onePub σ₁ σ₂) (hA₁ : Covers [args σ₁] (σ₁.rd ++ σ₁.wr))
    (hA₂ : Covers [args σ₂] (σ₂.rd ++ σ₂.wr)) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hsp, hw⟩ := h
  show RelCT isa _ (.block ([.ldrSp .x9 0] ++ Impl.AesGcm.AArch64.save .x9 ++ _)) _
  rw [List.append_assoc]
  refine RelCT.block_split (rel_seq (rel_taint [] hsp (by simp) ldr9_check) (ldr9_ok hA₁) (ldr9_ok hA₂)
    fun τ₁ τ₂ ⟨x9₁, g₁, sp₁, _, _⟩ ⟨x9₂, g₂, sp₂, _, _⟩ => ?_)
  refine rel_taint _ (by rw [sp₁, sp₂, hsp]) ?_ entryRest_check
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂, hw]
  · rw [g₁ r h9, g₂ r h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The entry of the second run, with the first's public arguments. -/
theorem entry_pub {σ₁ σ₂ : State} (hp : onePub σ₁ σ₂) (P : Perm (prmOf σ₂) σ₂)
    (hA : Covers [args σ₂] (σ₂.rd ++ σ₂.wr)) :
    WP isa (.block entry) σ₂ fun s => Env (prmOf σ₁) s ∧ TagSlot (prmOf σ₁) s.mem := by
  rw [prmOf_eq hp]
  exact WP.mono (entry_ok P hA) fun _ h => ⟨h.1, h.2.2.2.1⟩

/-- `ldr x9, [x19, #216]`: `tag`'s address in `x9`. -/
theorem ldrT_ok {p : Prm} {s : State} (E : Env p s) (hT : TagSlot p s.mem) :
    WP isa (.block [.ldr .x .x9 .x19 tagPO]) s fun s' => s'.gpr .x9 = p.T ∧ Env p s' := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  refine WP.run ⟨_, by grun [E.x19, r₀, hT'], rfl⟩ fun s' hs => ?_
  subst hs
  exact ⟨by simp [gpr_write], E.write (by decide) _⟩

theorem ldrT_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block [.ldr .x .x9 .x19 tagPO]) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- `ldr x9, [x19, #216]` and then `l`, which the taint analysis checks with
`x9` public, in two runs with the same public arguments. -/
theorem rel_ldrT {p : Prm} {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) (T₁ : TagSlot p σ₁.mem)
    (T₂ : TagSlot p σ₂.mem) {l : List Instr}
    (hc : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x9])) (.block l) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (([.ldr .x .x9 .x19 tagPO] : List Instr) ++ l)) TT :=
  RelCT.block_split (rel_seq (rel_env E₁ E₂ [] (by simp) ldrT_check) (ldrT_ok E₁ T₁) (ldrT_ok E₂ T₂)
    fun _ _ ⟨x9₁, E₁'⟩ ⟨x9₂, E₂'⟩ => rel_env E₁' E₂' [.x9] (by simp [x9₁, x9₂]) hc)

theorem sealEnd_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x9]))
    (.block (tagOut.tail ++ Impl.AesGcm.AArch64.restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem recv_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x9])) (.block recv.tail) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -, hA₁⟩ := args_of_seal h₁
  obtain ⟨-, P₂, -, hA₂⟩ := args_of_seal h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  refine rel_seq (keys_rel v L E₁ E₂) (keys_ok v L E₁) (keys_ok v L E₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (polyval_rel v L K₁.env K₂.env) (polyval_ok v L K₁.env K₁.hkey K₁.acc)
    (polyval_ok v L K₂.env K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  refine rel_seq (tag_rel v L P₁.env P₂.env (o := 0) (by decide)) (tag_ok v L P₁.env (o := 0) (by decide))
    (tag_ok v L P₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  refine rel_seq (crypt_rel v L T₁.env T₂.env) (crypt_ok v L T₁.env) (crypt_ok v L T₂.env)
    fun d₁ d₂ C₁ C₂ => ?_
  have sl : ∀ {τ a b c d : State}, TagSlot (prmOf σ₁) τ.mem → KeysPost (prmOf σ₁) τ a → PolyPost (prmOf σ₁) a b →
      TagPost (prmOf σ₁) 0 b c → CryptPost (prmOf σ₁) c d → TagSlot (prmOf σ₁) d.mem := fun S K P T C =>
    (((S.frame K.frame (by disj_tac L)).frame P.frame (by disj_tac L)).frame T.frame (by disj_tac L)).frame C.frame
      (by disj_tac L)
  exact rel_ldrT (l := tagOut.tail ++ Impl.AesGcm.AArch64.restore) C₁.env C₂.env (sl S₁ K₁ P₁ T₁ C₁)
    (sl S₂ K₂ P₂ T₂ C₂) sealEnd_check

theorem open_ct (v : GcmImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, hA₁⟩ := args_of_open h₁
  obtain ⟨-, P₂, hA₂⟩ := args_of_open h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  have wr : ∀ {τ : State}, Env (prmOf σ₁) τ → TagSlot (prmOf σ₁) τ.mem → WP isa (.block recv) τ (Env (prmOf σ₁)) :=
    fun E S => by
      obtain ⟨t, run, -, -, -, ho, sp, rd, wr⟩ := recv_ok L E S
      exact WP.of_runBlock ⟨t, run, E.keep (fun r hr => ho r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr⟩
  refine rel_seq (rel_ldrT (l := recv.tail) E₁ E₂ S₁ S₂ recv_check) (wr E₁ S₁) (wr E₂ S₂) fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine rel_seq (keys_rel v L R₁ R₂) (keys_ok v L R₁) (keys_ok v L R₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (crypt_rel v L K₁.env K₂.env) (crypt_ok v L K₁.env) (crypt_ok v L K₂.env) fun b₁ b₂ C₁ C₂ => ?_
  have hG : ∀ {σ τ : State}, KeysPost (prmOf σ₁) σ τ → ∀ {u : State}, CryptPost (prmOf σ₁) τ u →
      Spec.Gcm.blockAt u.mem ((prmOf σ₁).W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt u.mem ((prmOf σ₁).W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt u.mem ((prmOf σ₁).W + BitVec.ofNat 64 80) = 0 := by
    intro _ _ K _ C
    rw [Proof.AesGcm.AArch64.blockAt_frame C.frame (by disj_tac L), K.hkey,
      Proof.AesGcm.AArch64.blockAt_frame C.frame (by disj_tac L), K.acc,
      bytesAt_keep C.frame (by disj_tac L) (by decide)]
    exact ⟨rfl, rfl⟩
  refine rel_seq (polyval_rel v L C₁.env C₂.env) (polyval_ok v L C₁.env (hG K₁ C₁).1 (hG K₁ C₁).2)
    (polyval_ok v L C₂.env (hG K₂ C₂).1 (hG K₂ C₂).2) fun c₁ c₂ P₁ P₂ => ?_
  exact rel_seq (tag_rel v L P₁.env P₂.env (o := 224) (by decide)) (tag_ok v L P₁.env (o := 224) (by decide))
    (tag_ok v L P₂.env (o := 224) (by decide)) fun d₁ d₂ T₁ T₂ => rel_env T₁.env T₂.env [] (by simp) openEnd_check

end VG.Proof.AesGcmSiv.AArch64
