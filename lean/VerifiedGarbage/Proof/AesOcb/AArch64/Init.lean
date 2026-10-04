import VerifiedGarbage.Proof.AesOcb.AArch64.Seal

/-!
# AES-OCB on AArch64: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
registers in the scratch buffer, expands the key into the key context
(`vg_aes_expand_key`), enciphers a zero block at byte 240 of it in place,
for `L_*` (`vg_aes_encrypt_blocks`), and restores the registers
(`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_cons covers_prefix covers_off covers_left in_off KeyCall key_call)

/-- The rounds, as `lsr 2; add 6` computes them from the key length. -/
theorem rounds_of_len {L : Nat} (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    BitVec.ofNat 64 L >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- What `vg_aes_ocb_init` is given: the key (`L` bytes at `K`), the key
context at `Ctx` and the scratch buffer at `W`. -/
structure IArgs (s : State) (K Ctx W : Addr) (L : Nat) : Prop where
  rd : s.rd = [⟨K, L⟩]
  wr : s.wr = [⟨Ctx, 256⟩, ⟨W, 2560⟩]
  kc : (⟨K, L⟩ : Region).Disjoint ⟨Ctx, 256⟩
  ks : (⟨K, L⟩ : Region).Disjoint ⟨W, 2560⟩
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  wc : Ctx.toNat + 256 ≤ 2 ^ 64
  ws : W.toNat + 2560 ≤ 2 ^ 64
  len : L = 16 ∨ L = 24 ∨ L = 32

theorem IArgs.of {s : State} (hp : initAArch64.pre s) :
    IArgs s (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := hp
  ⟨a, b, c, d, e, f, g, h⟩

namespace IArgs

variable {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L)
include Ar

theorem pW : Covers [⟨W, 2560⟩] s.wr := by rw [Ar.wr]; exact covers_of_mem (by simp)
theorem pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [Ar.wr]; exact covers_of_mem (by simp)
theorem pK : Covers [⟨K, L⟩] (s.rd ++ s.wr) := by rw [Ar.rd]; exact covers_of_mem (by simp)

end IArgs

/-- The registers saved and the arguments of `vg_aes_expand_key`. -/
theorem init1_ok {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L) (h0 : s.gpr .x0 = K)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (h2 : s.gpr .x2 = Ctx) (h3 : s.gpr .x3 = W) :
    WP isa (.block (save .x3 ++ [Impl.AesGcm.AArch64.mov .x19 .x3, Impl.AesGcm.AArch64.mov .x20 .x2,
        .lsr .x .x22 .x1 2, Impl.AesGcm.AArch64.ptr .x22 .x22 6, Impl.AesGcm.AArch64.ptr .x3 .x19 scrO])) s
      fun s₂ => s₂.gpr .x19 = W ∧ s₂.gpr .x20 = Ctx ∧
        s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
        KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧
        Spill.Saved W s.gpr saved s₂.mem ∧ Frame [⟨W + BitVec.ofNat 64 160, 88⟩] s.mem s₂.mem := by
  have pW := Ar.pW
  have pC := Ar.pC
  have hin : ∀ p ∈ saved, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    rw [h3]; exact in_off pW (by have := saved_in p hp; omega) (by decide)
  rw [save_eq]
  refine WP.block_append_iff.mpr (WP.mono (Spill.save_wp saved_fits.1 hin) fun s₁ St => ?_)
  rw [h3] at St
  obtain ⟨s₂, run₂, x19₂, x20₂, x22₂, x3₂, x0₂, x1₂, x2₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x19 .x3, Impl.AesGcm.AArch64.mov .x20 .x2, .lsr .x .x22 .x1 2,
        Impl.AesGcm.AArch64.ptr .x22 .x22 6, Impl.AesGcm.AArch64.ptr .x3 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .x3 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 L ∧
      s₂.gpr .x2 = Ctx ∧ s₂.sp = s.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, St.gpr, h3]
    · simp [gpr_write, St.gpr, h2]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, St.gpr, h1, BitVec.setWidth_eq]
      exact rounds_of_len Ar.len
    · simp [gpr_write, St.gpr, h3]
    · simp [gpr_write, St.gpr, h0]
    · simp [gpr_write, St.gpr, h1]
    · simp [gpr_write, St.gpr, h2]
    · simp only [sp_write]; exact St.sp
    · rfl
    · simp only [rd_write]; exact St.rd
    · simp only [wr_write]; exact St.wr
  refine WP.of_runBlock ⟨s₂, run₂, x19₂, x20₂, x22₂, ?_, sp₂, rd₂, wr₂, ?_, ?_⟩
  · refine ⟨x0₂, x1₂, x2₂, x3₂, Ar.len, Ar.kc.sub_right (Region.sub_prefix (by decide)),
      Ar.ks.sub_right (Lay.wSub (by decide)), (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂]
      exact covers_cons Ar.pK (covers_left (covers_cons (covers_prefix pC (by decide))
        (covers_off pW (by decide) (by decide))))
    · rw [wr₂]; exact covers_cons (covers_prefix pC (by decide)) (covers_off pW (by decide) (by decide))
  · rw [m₂, St.mem]; exact Spill.saveMem_saved saved_fits _ _ _
  · rw [m₂, St.mem]; exact Spill.saveMem_frame saved_in (by decide) _ _ _

/-- A zero block at byte 240 of the key context, and the arguments of its encipherment. -/
theorem init2_ok {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {t : State} (h19 : t.gpr .x19 = W) (h20 : t.gpr .x20 = Ctx)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 R) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    WP isa (.block [Impl.AesGcm.AArch64.imm .x9 0, st .x20 240 .x9, st .x20 248 .x9,
        Impl.AesGcm.AArch64.ptr .x2 .x20 240, Impl.AesGcm.AArch64.imm .x3 1, Impl.AesGcm.AArch64.mov .x0 .x20,
        Impl.AesGcm.AArch64.mov .x1 .x22, Impl.AesGcm.AArch64.ptr .x4 .x19 scrO]) t fun t₄ =>
      BCall t₄ Ctx (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 ∧
      (∀ r ∈ preserved, t₄.gpr r = t.gpr r) ∧ t₄.sp = t.sp ∧ t₄.rd = t.rd ∧ t₄.wr = t.wr ∧
      t₄.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
  have pW := Ar.pW
  have pC := Ar.pC
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  rw [← hwr] at w₁ w₂
  obtain ⟨s₄, run₄, m₄, x0₄, x1₄, x2₄, x3₄, x4₄, g₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa
      [Impl.AesGcm.AArch64.imm .x9 0, st .x20 240 .x9, st .x20 248 .x9, Impl.AesGcm.AArch64.ptr .x2 .x20 240,
        Impl.AesGcm.AArch64.imm .x3 1, Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO] t = some s₄ ∧
      s₄.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .x3 = BitVec.ofNat 64 1 ∧ s₄.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      (∀ r ∈ preserved, s₄.gpr r = t.gpr r) ∧ s₄.sp = t.sp ∧ s₄.rd = t.rd ∧ s₄.wr = t.wr := by
    refine ⟨_, by orun [h19, h20, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [mem_write, addr8]; rfl
    · simp [gpr_write, h20]
    · simp [gpr_write, h22]
    · simp [gpr_write, h20]
    · simp [gpr_write]
    · simp [gpr_write, h19]
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
    all_goals rfl
  have rd₄' : s₄.rd = s.rd := rd₄.trans hrd
  have wr₄' : s₄.wr = s.wr := wr₄.trans hwr
  refine WP.of_runBlock ⟨s₄, run₄,
    { x0 := x0₄, x1 := x1₄, x2 := x2₄, x3 := x3₄, x4 := x4₄, rounds := hR
      wrap := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); have := Ar.wc; omega
      kd := Offset.base_disjoint Ctx (by decide) (by have := Ar.wc; omega)
      ks := (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := (Ar.cs.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide))
      reads := by
        rw [rd₄', wr₄']
        exact covers_cons (covers_left (covers_prefix pC (by decide))) (covers_cons
          (covers_left (covers_off pC (by decide) (by decide))) (covers_left (covers_off pW (by decide) (by decide))))
      writes := by
        rw [wr₄']
        exact covers_cons (covers_off pC (by decide) (by decide)) (covers_off pW (by decide) (by decide)) },
    g₄, sp₄, rd₄, wr₄, m₄⟩

/-- `vg_aes_ocb_init`, for its arguments. -/
theorem init_wp' (v : BlocksImpl) {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (h2 : s.gpr .x2 = Ctx) (h3 : s.gpr .x3 = W) :
    WP isa (init (callees v)) s fun s' => GprAbi s s' ∧ Spec.Ocb.KeyRepr s'.mem Ctx (bytesAt s.mem K L) := by
  have pW := Ar.pW
  have hKL : L < 2 ^ 64 := by rcases Ar.len with h | h | h <;> omega
  unfold init
  refine WP.seq (WP.mono (init1_ok Ar h0 h1 h2 h3) fun s₂ ⟨x19₂, x20₂, x22₂, kc, sp₂, rd₂, wr₂, sv₂, f₂⟩ => ?_)
  generalize hRd : Spec.Aes.rounds (L / 4) = R at x22₂
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases Ar.len with rfl | rfl | rfl <;> decide
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR' with rfl | rfl | rfl <;> decide
  -- The key schedule.
  refine WP.seq (WP.mono (key_call (keyImpl v) kc) fun s₃ g => ?_)
  have g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  have g20 : s₃.gpr .x20 = Ctx := by rw [g.saved .x20 (by decide) (by decide), x20₂]
  have g22 : s₃.gpr .x22 = BitVec.ofNat 64 R := by rw [g.saved .x22 (by decide) (by decide), x22₂]
  refine WP.seq (WP.mono (init2_ok Ar hR' g19 g20 g22 (g.rd.trans rd₂) (g.wr.trans wr₂))
    fun s₄ ⟨bc, g₄, sp₄, rd₄, wr₄, m₄⟩ => ?_)
  have rd₄' : s₄.rd = s.rd := rd₄.trans (g.rd.trans rd₂)
  have wr₄' : s₄.wr = s.wr := wr₄.trans (g.wr.trans wr₂)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩ := bc.kd
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames bc) fun s₅ P₅ => ?_)
  -- The saved registers, and `restore`.
  have dSv : ∀ {d k : Nat}, d + k ≤ 256 → (⟨W + BitVec.ofNat 64 160, 88⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 d, k⟩ :=
    fun h => (Ar.cs.sub_left (Offset.sub_base _ h)).sub_right (Lay.wSub (by decide)) |>.symm
  have dSv' : ∀ {d k : Nat}, 512 ≤ d → d + k ≤ 2560 →
      (⟨W + BitVec.ofNat 64 160, 88⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Offset.disjoint W (.inl (by omega)) (by omega) (by have := Ar.ws; omega)
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact Proof.Cmac.frame_store2 _ _ _
  have sv₅ : Spill.Saved W s.gpr saved s₅.mem := by
    have a := Spill.Saved.frame_in sv₂ saved_in (rs := [⟨Ctx, 240⟩, ⟨W + BitVec.ofNat 64 512, 512⟩]) g.frame
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simpa using dSv (d := 0) (k := 240) (by decide)
        · exact dSv' (by decide) (by decide))
    have b := Spill.Saved.frame_in a saved_in f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dSv (by decide))
    exact Spill.Saved.frame_in b saved_in P₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSv (by decide)
      · exact dSv' (by decide) (by decide))
  have c19 : s₅.gpr .x19 = W := by rw [P₅.saved .x19 (by decide) (by decide), g₄ _ (by decide), g19]
  have sp₅ : s₅.sp = s.sp := by rw [P₅.sp, sp₄, g.sp, sp₂]
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp c19 saved_fits.1 (by decide) (fun p hp => by
    rw [P₅.rd, P₅.wr, rd₄', wr₄']; exact covers_left pW _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base W (by have := saved_in p hp; omega) (by have := saved_in p hp; have := Ar.ws; omega)⟩)
      sv₅) fun s₆ Rs => ⟨restore_abi Rs sp₅, ?_⟩
  -- The key context.
  have k₃ : bytesAt s₃.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [← hRd, g.out, Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.ks.sub_right (Lay.wSub (by decide)))
        (by omega)]
  have k₅ : bytesAt s₅.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [Proof.Cmac.bytesAt_frame P₅.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0.sub_left (Region.sub_prefix hRb)
        · exact (Ar.cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))) (by omega),
      Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dK0.sub_left (Region.sub_prefix hRb)) (by omega), k₃]
  refine ⟨?_, ?_⟩
  · rw [length_bytesAt, hRd, Rs.mem]; exact k₅
  · show blockAtMem s₆.mem (Ctx + BitVec.ofNat 64 240) = _
    have hz : blockAtMem s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
      rw [m₄, blockAtMem_store2, Proof.Cmac.le8_zero]; rfl
    rw [Rs.mem, P₅.enc0, hz, Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dK0.sub_left (Region.sub_prefix hRb)) (by omega), k₃,
      Spec.Ocb.aes, length_bytesAt, hRd]

/-- `vg_aes_ocb_init`. -/
theorem init_wp (v : BlocksImpl) {s : State} (hp : initAArch64.pre s) :
    WP isa (init (callees v)) s fun s' => GprAbi s s' ∧ initAArch64.post s s' :=
  init_wp' v (IArgs.of hp) rfl (ofNat_toNat64 _).symm rfl rfl

end VG.Proof.AesOcb.AArch64
