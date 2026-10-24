module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. As AES-GCM's `init`
(`Proof/AesGcm/PPC64LE/Init.lean`): `init` saves our caller's registers in
`scratch` (`W`), expands the key into the context with SM4's key expansion,
inlined, and computes the hash subkey `CIPH_K(0¹²⁸)` into its bytes 240–255
with SM4's counter mode on a zero block, from a zero counter block at
`W + 96` (`init_wp`). SM4's working space is the argument after `W` (`r6`), kept in `r28`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov tO)
open VG.Proof.AesGcm.PPC64LE (Keeps' SavedAt savedR save_ok restore_ok covers_mem covers_prefix covers_off
  in_off bytesAt_frame blockAt_frame blocksAt_one ctr32_single zero_block2 ctxH_eq write_8 saved_w
  length_bytesAt)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)

/-- After the entry, from `s₀`. -/
structure IS1 (s₀ s₁ : State) : Prop where
  r31 : s₁.gpr .r31 = s₀.gpr .r5
  r29 : s₁.gpr .r29 = s₀.gpr .r4
  r5 : s₁.gpr .r5 = s₀.gpr .r6
  r28 : s₁.gpr .r28 = s₀.gpr .r6
  r3 : s₁.gpr .r3 = s₀.gpr .r3
  r4 : s₁.gpr .r4 = s₀.gpr .r4
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₁.gpr r = s₀.gpr r
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem (s₀.gpr .r5) s₀
  frame : Frame [savedR (s₀.gpr .r5)] s₀.mem s₁.mem

theorem is1_wp {s₀ : State} (h : initPPC64LE.pre s₀) : WP isa (.block initPre) s₀ (IS1 s₀) := by
  obtain ⟨-, hwr, -, -, -, -, -, -⟩ := h
  have hW : Covers [⟨s₀.gpr .r5, 2560⟩] s₀.wr := by
    rw [hwr]; exact covers_prefix (covers_mem (r := ⟨s₀.gpr .r5, scrBytes⟩) (by simp)) (by decide)
  refine WP.block_append (WP.mono (save_ok (b := .r5) (by decide) hW) fun s ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e4 : s.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  have e6 : s.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e4, e6, h31]
  exact ⟨by simp [h31], by simp, by simp, by simp, by simp [hg], by simp [hg],
    fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩

theorem init_kc {s₀ s₁ : State} (h : initPPC64LE.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r6) := by
  obtain ⟨hrd, hwr, dkc, -, -, fk, fc, -, dkx, dcx, -, fx⟩ := h
  have hX : Covers [⟨s₀.gpr .r6, xBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hC : Covers [⟨s₀.gpr .r4, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  refine ⟨h1.r3, h1.r4, h1.r5, dkc.sub_right (Region.sub_prefix (by decide)),
    dkx.sub_right (Region.sub_prefix (by decide)),
    (dcx.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)), fk,
    by omega, by simp only [xBytes, kBytes] at fx ⊢; omega, ?_, ?_⟩
  · rw [h1.keeps.rd, h1.keeps.wr, hrd]
    exact Covers.cons (Covers.left (covers_mem (by simp))) (Covers.cons
      (Covers.right (covers_prefix hC (by decide))) (Covers.cons (Covers.right (covers_prefix hX
        (by decide))) Covers.nil))
  · rw [h1.keeps.wr]
    exact Covers.cons (covers_prefix hC (by decide)) (Covers.cons (covers_prefix hX (by decide))
      Covers.nil)

/-- `initArgs`: the hash subkey's block and `T` zeroed, and the arguments of
SM4's counter mode. -/
theorem initArgs_ok {C W X : Addr} {s : State} (h29 : s.gpr .r29 = C) (h31 : s.gpr .r31 = W)
    (h28 : s.gpr .r28 = X) (hc : Covers [⟨C, 256⟩] s.wr) (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block initArgs) s fun s' =>
      s'.mem = (((s.mem.writeW (C + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
          (C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
          (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .r3 = C ∧ s'.gpr .r4 = W + BitVec.ofNat 64 96 ∧ s'.gpr .r5 = C + BitVec.ofNat 64 240 ∧
      s'.gpr .r6 = BitVec.ofNat 64 1 ∧ s'.gpr .r7 = X ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have c₀ := in_off hc (show 240 + 8 ≤ 256 by decide) (by decide)
  have c₁ := in_off hc (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₀ := in_off hw (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₁ := in_off hw (show 104 + 8 ≤ 2560 by decide) (by decide)
  crun [initArgs, tO, h29, h31, h28, c₀, c₁, w₀, w₁, mov, BitVec.or_self, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e f => by simp [a, b, c, d, e, f], ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of `init`'s counter mode: the hash subkey's block
encrypted from the counter block `T`. -/
theorem init_cc {C W X : Addr} {s : State} (dcs : (⟨C, 256⟩ : Region).Disjoint ⟨W, scrBytes⟩)
    (dcx : (⟨C, 256⟩ : Region).Disjoint ⟨X, xBytes⟩) (dsx : (⟨W, scrBytes⟩ : Region).Disjoint ⟨X, xBytes⟩)
    (fc : C.toNat + 256 ≤ 2 ^ 64) (fs : W.toNat + scrBytes ≤ 2 ^ 64) (fx : X.toNat + xBytes ≤ 2 ^ 64)
    (hW : Covers [⟨W, scrBytes⟩] s.wr) (hX : Covers [⟨X, xBytes⟩] s.wr)
    (hC : Covers [⟨C, 256⟩] s.wr) (a3 : s.gpr .r3 = C) (a4 : s.gpr .r4 = W + BitVec.ofNat 64 96)
    (a5 : s.gpr .r5 = C + BitVec.ofNat 64 240) (a6 : s.gpr .r6 = BitVec.ofNat 64 1)
    (a7 : s.gpr .r7 = X) :
    CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240) X 1 := by
  have fs' : W.toNat + 2560 ≤ 2 ^ 64 := fs
  refine ⟨a3, a4, a5, a6, a7, by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, fx, ?_, ?_⟩
  · exact (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · simpa using Offset.disjoint C (d := 0) (n := 128) (e := 240) (k := 16) (.inl (by decide))
      (by decide) (by decide)
  · exact dcx.sub_left (Region.sub_prefix (by decide))
  · exact ((dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
  · exact dsx.sub_left (Offset.sub_base _ (by decide))
  · exact dcx.sub_left (Offset.sub_base _ (by decide))
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 96) (by decide),
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 240) (by decide),
      Nat.mod_eq_of_lt (by omega)]; omega
  · exact Covers.cons (Covers.right (covers_prefix hC (by decide))) (Covers.cons
      (Covers.right (covers_off hW (by decide) (by decide))) (Covers.cons
        (Covers.right (covers_off hC (by decide) (by decide))) (Covers.cons
          (Covers.right hX) Covers.nil)))
  · exact Covers.cons (covers_off hW (by decide) (by decide)) (Covers.cons
      (covers_off hC (by decide) (by decide)) (Covers.cons hX Covers.nil))

/-- `init`. -/
theorem init_wp {s₀ : State} (h : initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initPPC64LE.post s₀ s' := by
  have h' := h
  obtain ⟨hrd, hwr, dkc, dks, dcs, fk, fc, fs, dkx, dcx, dsx, fx⟩ := h'
  have fs' : (s₀.gpr .r5).toNat + 2560 ≤ 2 ^ 64 := fs
  have hW : Covers [⟨s₀.gpr .r5, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hX : Covers [⟨s₀.gpr .r6, xBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hW' : Covers [⟨s₀.gpr .r5, 2560⟩] s₀.wr := covers_prefix hW (by decide)
  have hC : Covers [⟨s₀.gpr .r4, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  -- Regions apart from the saved slots, and from the key schedule.
  have sW : ∀ {d k : Nat}, d + k ≤ scrBytes → (d + k ≤ 128 ∨ 248 ≤ d) →
      (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ =>
    Offset.disjoint _ (by omega) (by decide) (by simp only [scrBytes] at h₁; omega)
  have sC : ∀ {d k : Nat}, d + k ≤ 256 → (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r4 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => ((dcs.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ (by decide))).symm
  have sC0 : (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r4, 128⟩ :=
    (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
  have kW : ∀ {d k : Nat}, d + k ≤ scrBytes →
      (⟨s₀.gpr .r4, 128⟩ : Region).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ h₁)
  have kC : (⟨s₀.gpr .r4, 128⟩ : Region).Disjoint ⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩ := by
    simpa using Offset.disjoint (s₀.gpr .r4) (d := 0) (n := 128) (e := 240) (k := 16)
      (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (is1_wp h) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (key_wp (init_kc h h1)) fun s₂ kp => ?_)
  have g31 : s₂.gpr .r31 = s₀.gpr .r5 := (kp.saved _ (by decide)).trans h1.r31
  have g29 : s₂.gpr .r29 = s₀.gpr .r4 := (kp.saved _ (by decide)).trans h1.r29
  have g28 : s₂.gpr .r28 = s₀.gpr .r6 := (kp.saved _ (by decide)).trans h1.r28
  have wr₂ : s₂.wr = s₀.wr := kp.wr.trans h1.keeps.wr
  refine WP.seq (WP.mono (initArgs_ok g29 g31 g28 (by rw [wr₂]; exact hC) (by rw [wr₂]; exact hW'))
    fun s₃ ⟨hm₃, a3, a4, a5, a6, a7, hg₃, hk₃⟩ => ?_)
  have cc : CtrCall s₃ (s₀.gpr .r4) (s₀.gpr .r5 + BitVec.ofNat 64 96) (s₀.gpr .r4 + BitVec.ofNat 64 240)
      (s₀.gpr .r6) 1 :=
    init_cc dcs dcx dsx fc fs fx (by rw [hk₃.wr, wr₂]; exact hW) (by rw [hk₃.wr, wr₂]; exact hX)
      (by rw [hk₃.wr, wr₂]; exact hC) a3 a4 a5 a6 a7
  refine WP.seq (WP.mono (ctr_wp cc) fun s₄ cp => ?_)
  -- The memory along the way.
  obtain ⟨m₂', hm₂'⟩ : ∃ m, m = (s₂.mem.writeW (s₀.gpr .r4 + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
      (s₀.gpr .r4 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := ⟨_, rfl⟩
  rw [← hm₂'] at hm₃
  have fa : Frame [⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩] s₂.mem m₂' := by
    rw [hm₂']; exact Proof.Cmac.frame_store2 _ _ _
  have fb : Frame [⟨s₀.gpr .r5 + BitVec.ofNat 64 96, 16⟩] m₂' s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store2 _ _ _
  have f₃ : Frame [⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩, ⟨s₀.gpr .r5 + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem :=
    (fa.mono (by simp)).trans (fb.mono (by simp))
  have sv₄ : SavedAt s₄.mem (s₀.gpr .r5) s₀ := by
    refine ((h1.saved.frame kp.frame ?_).frame f₃ ?_).frame cp.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sC0
      · exact (dsx.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sC (by decide)
      · exact sW (by decide) (.inl (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sW (by decide) (.inl (by decide))
      · simpa using sC (d := 240) (k := 16) (by decide)
      · exact dsx.sub_left (Offset.sub_base _ (by decide))
  have hk₄ : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₄.gpr r = s₀.gpr r := fun r hr => by
    rw [cp.saved r (by revert hr; revert r; decide), hg₃ r (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide),
      kp.saved r (by revert hr; revert r; decide), h1.low r hr]
  refine WP.mono (restore_ok (s₀ := s₀) (by rw [cp.saved _ (by decide), hg₃ _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), g31])
    (by rw [cp.rd, cp.wr, hk₃.rd, hk₃.wr, wr₂]; exact Covers.right hW') sv₄
    (by rw [cp.sp, hk₃.sp, kp.sp, h1.keeps.sp])
    hk₄) fun s' ⟨hab, hm', _, _, _⟩ => ⟨hab, ?_⟩
  -- The key schedule and the hash subkey.
  have key₁ : Spec.Sm4.blockAt s₁.mem (s₀.gpr .r3) =
      Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .r3) 16).getD i.val 0 := by
    rw [← Proof.Sm4.ofFn_toList (Spec.Sm4.blockAt s₁.mem _), ← Proof.Sm4.bytesAt_eq_blockAt,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Offset.sub_base _ (by decide))) (by decide)]
  have ks₃ : Spec.Sm4.scheduleAt s₃.mem (s₀.gpr .r4) =
      Spec.Sm4.expandKey (Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .r3) 16).getD i.val 0) := by
    rw [Proof.Sm4.scheduleAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact kC
        · exact kW (by decide)), kp.out, key₁]
  simp only [initPPC64LE, KeyRepr, hm']
  refine ⟨?_, ?_⟩
  · rw [Proof.Sm4.scheduleAt_frame cp.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact kW (by decide)
        · simpa using kC
        · exact dcx.sub_left (Region.sub_prefix (by decide))), ks₃]
  · have cout := cp.out
    rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at cout
    have z₁ : blockAt s₃.mem (s₀.gpr .r5 + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block2]
    have z₂ : blockAt s₃.mem (s₀.gpr .r4 + BitVec.ofNat 64 240) = 0 := by
      rw [blockAt_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))),
        hm₂', zero_block2]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    simp only [Spec.Sm4.gcmCipherOfKey, ks₃]

end VG.Proof.Sm4Gcm.PPC64LE
