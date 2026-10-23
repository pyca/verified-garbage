module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Init.lean`): `init` saves our caller's registers in
`scratch` (`W`), expands the key into the context with
`vg_aes_expand_key_scratch`, and computes the hash subkey `CIPH_K(0¹²⁸)` into
its bytes 240–255 with `vg_aes_ctr32` on a zero block, from a zero counter
block at `W + 96` (`init_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr)

/-- The number of rounds for a key of `L` bytes, as `init` computes it. -/
theorem roundsOf {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) :
    (BitVec.ofNat 64 L >>> 2) + BitVec.ofNat 64 6 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_ok {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) :
    Spec.Aes.rounds (L / 4) = 10 ∨ Spec.Aes.rounds (L / 4) = 12 ∨ Spec.Aes.rounds (L / 4) = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ctr32_single (ciph : Block → Block) (icb x : Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem zero_block2 (m : Mem) (p : Addr) :
    blockAt ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) p = 0 := by
  rw [blockAt, zeroT_bytes]; decide

theorem add8 (p : Addr) (a : Nat) :
    p + BitVec.ofNat 64 (a + 8) = p + BitVec.ofNat 64 a + BitVec.ofNat 64 8 := by
  simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The number of rounds of `init`'s key. -/
abbrev initR (s₀ : State) : Nat := Spec.Aes.rounds ((s₀.gpr .r4).toNat / 4)

/-- After the entry, from `s₀`. -/
structure IS1 (s₀ s₁ : State) : Prop where
  r31 : s₁.gpr .r31 = s₀.gpr .r6
  r29 : s₁.gpr .r29 = s₀.gpr .r5
  r28 : s₁.gpr .r28 = BitVec.ofNat 64 (initR s₀)
  r6 : s₁.gpr .r6 = s₀.gpr .r6 + BitVec.ofNat 64 512
  r3 : s₁.gpr .r3 = s₀.gpr .r3
  r4 : s₁.gpr .r4 = s₀.gpr .r4
  r5 : s₁.gpr .r5 = s₀.gpr .r5
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₁.gpr r = s₀.gpr r
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem (s₀.gpr .r6) s₀
  frame : Frame [savedR (s₀.gpr .r6)] s₀.mem s₁.mem

theorem is1_wp {s₀ : State} (h : initPPC64LE.pre s₀) : WP isa (.block initPre) s₀ (IS1 s₀) := by
  obtain ⟨-, hwr, -, -, -, -, -, hlen⟩ := h
  have hW : Covers [⟨s₀.gpr .r6, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.block_append (WP.mono (save_ok (b := .r6) (by decide) hW) fun s ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e4 : s.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  have e5 : s.gpr .r5 = s₀.gpr .r5 := hg _ (by decide) (by decide)
  have hR : (s₀.gpr .r4 >>> 2) + BitVec.ofNat 64 6 = BitVec.ofNat 64 (initR s₀) := by
    have := roundsOf hlen; rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  crun [scrO, mov, BitVec.or_self, e4, e5, h31, hR]
  exact ⟨by simp [h31], by simp, by simp, by simp, by simp [hg], by simp [hg], by simp [hg],
    fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩

theorem init_kc {s₀ s₁ : State} (h : initPPC64LE.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .r3) (s₀.gpr .r4).toNat (s₀.gpr .r5) (s₀.gpr .r6 + BitVec.ofNat 64 512) := by
  obtain ⟨hrd, hwr, dkc, dks, dcs, fc, fs, hlen⟩ := h
  have hW : Covers [⟨s₀.gpr .r6, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hC : Covers [⟨s₀.gpr .r5, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  refine ⟨h1.r3, by rw [h1.r4]; simp, h1.r5, h1.r6, hlen, dkc.sub_right (Region.sub_prefix (by decide)),
    dks.sub_right (Offset.sub_base _ (by decide)),
    (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)), ?_, ?_⟩
  · rw [h1.keeps.rd, h1.keeps.wr, hrd]
    exact Covers.cons (Covers.left (covers_mem (by simp))) (Covers.cons
      (Covers.right (covers_prefix hC (by decide))) (Covers.cons (Covers.right (covers_off hW (by decide)
        (by decide))) Covers.nil))
  · rw [h1.keeps.wr]
    exact Covers.cons (covers_prefix hC (by decide)) (Covers.cons (covers_off hW (by decide) (by decide))
      Covers.nil)

/-- After the key expansion. -/
def IS2 (s₀ s₂ : State) : Prop :=
  ∃ s₁, IS1 s₀ s₁ ∧ KeyPost s₁ (s₀.gpr .r3) (s₀.gpr .r4).toNat (s₀.gpr .r5) (s₀.gpr .r6 + BitVec.ofNat 64 512) s₂

/-- `initArgs`: the hash subkey's block and `T` zeroed, and the arguments of
`vg_aes_ctr32`. -/
theorem initArgs_ok {C W : Addr} {R : Nat} {s : State} (h29 : s.gpr .r29 = C) (h31 : s.gpr .r31 = W)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 R) (hc : Covers [⟨C, 256⟩] s.wr) (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block initArgs) s fun s' =>
      s'.mem = (((s.mem.writeW (C + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
          (C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
          (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .r3 = C ∧ s'.gpr .r4 = BitVec.ofNat 64 R ∧ s'.gpr .r5 = W + BitVec.ofNat 64 96 ∧
      s'.gpr .r6 = C + BitVec.ofNat 64 240 ∧ s'.gpr .r7 = BitVec.ofNat 64 1 ∧
      s'.gpr .r8 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have c₀ := in_off hc (show 240 + 8 ≤ 256 by decide) (by decide)
  have c₁ := in_off hc (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₀ := in_off hw (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₁ := in_off hw (show 104 + 8 ≤ 2560 by decide) (by decide)
  crun [initArgs, tO, scrO, h29, h31, h28, c₀, c₁, w₀, w₁, mov, BitVec.or_self, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e f g => by simp [a, b, c, d, e, f, g], ⟨rfl, rfl, rfl, rfl⟩⟩

/-- `init`. -/
theorem init_wp {s₀ : State} (h : initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initPPC64LE.post s₀ s' := by
  have h' := h
  obtain ⟨hrd, hwr, dkc, dks, dcs, fc, fs, hlen⟩ := h'
  have hW : Covers [⟨s₀.gpr .r6, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hC : Covers [⟨s₀.gpr .r5, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hR := rounds_ok hlen
  have hRb : 16 * (initR s₀ + 1) ≤ 240 := by simp only [initR]; rcases hR with h' | h' | h' <;> omega
  -- Regions apart from the saved slots, and from the key schedule.
  have sW : ∀ {d k : Nat}, d + k ≤ 2560 → (d + k ≤ 128 ∨ 248 ≤ d) →
      (savedR (s₀.gpr .r6)).Disjoint ⟨s₀.gpr .r6 + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ => saved_w h₁ h₂
  have sC : ∀ {d k : Nat}, d + k ≤ 256 → (savedR (s₀.gpr .r6)).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => ((dcs.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ (by decide))).symm
  have sC0 : (savedR (s₀.gpr .r6)).Disjoint ⟨s₀.gpr .r5, 240⟩ :=
    (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
  have kW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨s₀.gpr .r5, 16 * (initR s₀ + 1)⟩ : Region).Disjoint ⟨s₀.gpr .r6 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (dcs.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₁)
  have kC : (⟨s₀.gpr .r5, 16 * (initR s₀ + 1)⟩ : Region).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 240, 16⟩ := by
    simpa using Offset.disjoint (s₀.gpr .r5) (d := 0) (n := 16 * (initR s₀ + 1)) (e := 240) (k := 16)
      (.inl (by omega)) (by omega) (by decide)
  refine WP.seq (WP.mono (is1_wp h) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (key_call (init_kc h h1)) fun s₂ kp => ?_)
  have g31 : s₂.gpr .r31 = s₀.gpr .r6 := (kp.saved _ (by decide)).trans h1.r31
  have g29 : s₂.gpr .r29 = s₀.gpr .r5 := (kp.saved _ (by decide)).trans h1.r29
  have g28 : s₂.gpr .r28 = BitVec.ofNat 64 (initR s₀) := (kp.saved _ (by decide)).trans h1.r28
  have wr₂ : s₂.wr = s₀.wr := kp.wr.trans h1.keeps.wr
  have rd₂ : s₂.rd = s₀.rd := kp.rd.trans h1.keeps.rd
  refine WP.seq (WP.mono (initArgs_ok g29 g31 g28 (by rw [wr₂]; exact hC) (by rw [wr₂]; exact hW))
    fun s₃ ⟨hm₃, a3, a4, a5, a6, a7, a8, hg₃, hk₃⟩ => ?_)
  have cc : CtrCall s₃ (s₀.gpr .r5) (s₀.gpr .r6 + BitVec.ofNat 64 96) (s₀.gpr .r5 + BitVec.ofNat 64 240)
      (s₀.gpr .r6 + BitVec.ofNat 64 512) (initR s₀) 1 := by
    refine ⟨a3, a4, a5, a6, a7, a8, hR, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · simpa using Offset.disjoint (s₀.gpr .r5) (d := 0) (n := 240) (e := 240) (k := 16) (.inl (by decide))
        (by decide) (by decide)
    · exact (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · exact ((dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact (dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 240) (by decide),
        Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hk₃.rd, hk₃.wr, wr₂]
      exact Covers.cons (Covers.right (covers_prefix hC (by decide))) (Covers.cons
        (Covers.right (covers_off hW (by decide) (by decide))) (Covers.cons
          (Covers.right (covers_off hC (by decide) (by decide))) (Covers.cons
            (Covers.right (covers_off hW (by decide) (by decide))) Covers.nil)))
    · rw [hk₃.wr, wr₂]
      exact Covers.cons (covers_off hW (by decide) (by decide)) (Covers.cons
        (covers_off hC (by decide) (by decide)) (Covers.cons (covers_off hW (by decide) (by decide)) Covers.nil))
  refine WP.seq (WP.mono (ctr_call cc) fun s₄ cp => ?_)
  -- The memory along the way.
  obtain ⟨m₂', hm₂'⟩ : ∃ m, m = (s₂.mem.writeW (s₀.gpr .r5 + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
      (s₀.gpr .r5 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := ⟨_, rfl⟩
  rw [← hm₂'] at hm₃
  have fa : Frame [⟨s₀.gpr .r5 + BitVec.ofNat 64 240, 16⟩] s₂.mem m₂' := by
    rw [hm₂']; exact Proof.Cmac.frame_store2 _ _ _
  have fb : Frame [⟨s₀.gpr .r6 + BitVec.ofNat 64 96, 16⟩] m₂' s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store2 _ _ _
  have f₃ : Frame [⟨s₀.gpr .r5 + BitVec.ofNat 64 240, 16⟩, ⟨s₀.gpr .r6 + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem :=
    (fa.mono (by simp)).trans (fb.mono (by simp))
  have sv₄ : SavedAt s₄.mem (s₀.gpr .r6) s₀ := by
    refine ((h1.saved.frame kp.frame ?_).frame f₃ ?_).frame cp.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sC0
      · exact sW (by decide) (.inr (by decide))
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
      · exact sW (by decide) (.inr (by decide))
  have hk₄ : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₄.gpr r = s₀.gpr r := fun r hr => by
    rw [cp.saved r (by revert hr; revert r; decide), hg₃ r (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide),
      kp.saved r (by revert hr; revert r; decide), h1.low r hr]
  refine WP.mono (restore_ok (s₀ := s₀) (by rw [cp.saved _ (by decide), hg₃ _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), g31])
    (by rw [cp.rd, cp.wr, hk₃.rd, hk₃.wr, wr₂]; exact Covers.right hW) sv₄
    (by rw [cp.sp, hk₃.sp, kp.sp, h1.keeps.sp])
    hk₄) fun s' ⟨hab, hm', _, _, _⟩ => ⟨hab, ?_⟩
  -- The key schedule and the hash subkey.
  have ks₃ : bytesAt s₃.mem (s₀.gpr .r5) (16 * (initR s₀ + 1)) =
      Spec.Aes.expandKey (bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) := by
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact kC
        · exact kW (by decide)) (by omega), kp.out,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Offset.sub_base _ (by decide))) (by omega)]
  simp only [initPPC64LE, KeyRepr, length_bytesAt, hm']
  refine ⟨?_, ?_⟩
  · rw [bytesAt_frame cp.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact kW (by decide)
        · simpa using kC
        · exact kW (by decide)) (by omega), ks₃]
  · have cout := cp.out
    rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at cout
    have z₁ : blockAt s₃.mem (s₀.gpr .r6 + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block2]
    have z₂ : blockAt s₃.mem (s₀.gpr .r5 + BitVec.ofNat 64 240) = 0 := by
      rw [blockAt_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))),
        hm₂', zero_block2]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    rw [ks₃, Spec.Gcm.aes, length_bytesAt]

end VG.Proof.AesGcm.PPC64LE
