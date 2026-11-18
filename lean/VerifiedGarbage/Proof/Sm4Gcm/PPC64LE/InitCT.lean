module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Callee
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Sm4Gcm.PPC64LE.Init`, which this module and modules that import it used -/

section

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
  obtain hW : Covers [⟨s₀.gpr .r5, 2560⟩] s₀.wr := by
    rw [hwr]; exact covers_prefix (covers_mem (r := ⟨s₀.gpr .r5, scrBytes⟩) (by simp)) (by decide)
  refine WP.block_append (WP.mono (save_ok (b := .r5) (by decide) hW) fun s ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  obtain e4 : s.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  obtain e6 : s.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e4, e6, h31]
  exact ⟨by simp [h31], by simp, by simp, by simp, by simp [hg], by simp [hg],
    fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩

theorem init_kc {s₀ s₁ : State} (h : initPPC64LE.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r6) := by
  obtain ⟨hrd, hwr, dkc, -, -, fk, fc, -, dkx, dcx, -, fx⟩ := h
  obtain hX : Covers [⟨s₀.gpr .r6, xBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hC : Covers [⟨s₀.gpr .r4, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  refine ⟨h1.r3, h1.r4, h1.r5, dkc.sub_right (Region.sub_prefix (by decide)),
    dkx.sub_right (Region.sub_prefix (by decide)),
    (dcx.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)), fk,
    by omega_using [fc], by simp only [xBytes, kBytes] at fx ⊢; omega_using [fx], ?_, ?_⟩
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
  obtain c₀ := in_off hc (show 240 + 8 ≤ 256 by decide) (by decide)
  obtain c₁ := in_off hc (show 248 + 8 ≤ 256 by decide) (by decide)
  obtain w₀ := in_off hw (show 96 + 8 ≤ 2560 by decide) (by decide)
  obtain w₁ := in_off hw (show 104 + 8 ≤ 2560 by decide) (by decide)
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
  refine ⟨a3, a4, a5, a6, a7, by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega_using [fc], ?_, ?_, fx, ?_, ?_⟩
  · exact (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · simpa using Offset.disjoint C (d := 0) (n := 128) (e := 240) (k := 16) (.inl (by decide))
      (by decide) (by decide)
  · exact dcx.sub_left (Region.sub_prefix (by decide))
  · exact ((dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
  · exact dsx.sub_left (Offset.sub_base _ (by decide))
  · exact dcx.sub_left (Offset.sub_base _ (by decide))
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 96) (by decide),
      Nat.mod_eq_of_lt (by omega_using [fs'])]; omega_using [fs']
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 240) (by decide),
      Nat.mod_eq_of_lt (by omega_using [fc])]; omega_using [fc]
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
  obtain hW : Covers [⟨s₀.gpr .r5, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hX : Covers [⟨s₀.gpr .r6, xBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hW' : Covers [⟨s₀.gpr .r5, 2560⟩] s₀.wr := covers_prefix hW (by decide)
  obtain hC : Covers [⟨s₀.gpr .r4, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  -- Regions apart from the saved slots, and from the key schedule.
  obtain sW : ∀ {d k : Nat}, d + k ≤ scrBytes → (d + k ≤ 128 ∨ 248 ≤ d) →
      (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ =>
    Offset.disjoint _ (by omega_using [h₂]) (by decide) (by simp only [scrBytes] at h₁; omega_using [h₁])
  obtain sC : ∀ {d k : Nat}, d + k ≤ 256 → (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r4 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => ((dcs.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ (by decide))).symm
  obtain sC0 : (savedR (s₀.gpr .r5)).Disjoint ⟨s₀.gpr .r4, 128⟩ :=
    (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
  obtain kW : ∀ {d k : Nat}, d + k ≤ scrBytes →
      (⟨s₀.gpr .r4, 128⟩ : Region).Disjoint ⟨s₀.gpr .r5 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ h₁)
  obtain kC : (⟨s₀.gpr .r4, 128⟩ : Region).Disjoint ⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩ := by
    simpa using Offset.disjoint (s₀.gpr .r4) (d := 0) (n := 128) (e := 240) (k := 16)
      (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (is1_wp h) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (key_wp (init_kc h h1)) fun s₂ kp => ?_)
  obtain g31 : s₂.gpr .r31 = s₀.gpr .r5 := (kp.saved _ (by decide)).trans h1.r31
  obtain g29 : s₂.gpr .r29 = s₀.gpr .r4 := (kp.saved _ (by decide)).trans h1.r29
  obtain g28 : s₂.gpr .r28 = s₀.gpr .r6 := (kp.saved _ (by decide)).trans h1.r28
  obtain wr₂ : s₂.wr = s₀.wr := kp.wr.trans h1.keeps.wr
  refine WP.seq (WP.mono (initArgs_ok g29 g31 g28 (by rw [wr₂]; exact hC) (by rw [wr₂]; exact hW'))
    fun s₃ ⟨hm₃, a3, a4, a5, a6, a7, hg₃, hk₃⟩ => ?_)
  obtain cc : CtrCall s₃ (s₀.gpr .r4) (s₀.gpr .r5 + BitVec.ofNat 64 96) (s₀.gpr .r4 + BitVec.ofNat 64 240)
      (s₀.gpr .r6) 1 :=
    init_cc dcs dcx dsx fc fs fx (by rw [hk₃.wr, wr₂]; exact hW) (by rw [hk₃.wr, wr₂]; exact hX)
      (by rw [hk₃.wr, wr₂]; exact hC) a3 a4 a5 a6 a7
  refine WP.seq (WP.mono (ctr_wp cc) fun s₄ cp => ?_)
  -- The memory along the way.
  obtain ⟨m₂', hm₂'⟩ : ∃ m, m = (s₂.mem.writeW (s₀.gpr .r4 + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
      (s₀.gpr .r4 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := ⟨_, rfl⟩
  rw [← hm₂'] at hm₃
  obtain fa : Frame [⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩] s₂.mem m₂' := by
    rw [hm₂']; exact Proof.Cmac.frame_store2 _ _ _
  obtain fb : Frame [⟨s₀.gpr .r5 + BitVec.ofNat 64 96, 16⟩] m₂' s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store2 _ _ _
  obtain f₃ : Frame [⟨s₀.gpr .r4 + BitVec.ofNat 64 240, 16⟩, ⟨s₀.gpr .r5 + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem :=
    (fa.mono (by simp)).trans (fb.mono (by simp))
  obtain sv₄ : SavedAt s₄.mem (s₀.gpr .r5) s₀ := by
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
  obtain hk₄ : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₄.gpr r = s₀.gpr r := fun r hr => by
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
  obtain key₁ : Spec.Sm4.blockAt s₁.mem (s₀.gpr .r3) =
      Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .r3) 16).getD i.val 0 := by
    rw [← Proof.Sm4.ofFn_toList (Spec.Sm4.blockAt s₁.mem _), ← Proof.Sm4.bytesAt_eq_blockAt,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Offset.sub_base _ (by decide))) (by decide)]
  obtain ks₃ : Spec.Sm4.scheduleAt s₃.mem (s₀.gpr .r4) =
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
    obtain z₁ : blockAt s₃.mem (s₀.gpr .r5 + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block2]
    obtain z₂ : blockAt s₃.mem (s₀.gpr .r4 + BitVec.ofNat 64 240) = 0 := by
      rw [blockAt_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))),
        hm₂', zero_block2]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    simp only [Spec.Sm4.gcmCipherOfKey, ks₃]

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-! ### `Sm4Gcm.PPC64LE.CTCrypt`, which the modules that import this one used -/

section

/-!
# SM4-GCM on PPC64LE: `crypt` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTCrypt.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the data's address and length, and the length
of the text so far modulo 16; SM4's counter mode is constant time by its own
proof (`CT.ctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov cryptFill splitWhole xorLoop)
open VG.Proof.AesGcm.PPC64LE (CT Env Lay DataW eval_zero split_ok)

/-- Before `crypt`. -/
def CrI (c st w x sp : Addr) (D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ P % 16 = q ∧ CrIn V sp icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w x sp : Addr) (D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ P % 16 = q ∧ CrMid V sp icb P D n m₀ j s

/-- Environments that agree on `r28` to `r31` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h29 : V₁ .r29 = V₂ .r29) (h30 : V₁ .r30 = V₂ .r30) (h31 : V₁ .r31 = V₂ .r31) (h28 : V₁ .r28 = V₂ .r28)
    {r : Reg} (hr : r ∈ [Reg.r28, .r29, .r30, .r31]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), h28]
  · rw [e₁.r29, e₂.r29, h29]
  · rw [e₁.r30, e₂.r30, h30]
  · rw [e₁.r31, e₂.r31, h31]

section
variable {c st w x sp : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem cryptWhole_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w x sp D n q j) cryptWhole := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧ Covers [xR (V .r28)] s.wr ∧
    (⟨D, n⟩ : Region).Disjoint (xR (V .r28)) ∧
    s.gpr .r5 = D + BitVec.ofNat 64 j ∧ s.gpr .r6 = BitVec.ofNat 64 nb
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25]) (.block splitWhole)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
  · refine WP.mono (split_ok hs.le hs.data.ok.lt hs.r24 hs.r25) fun s₁ ⟨h5, h6, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, h28, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le,
      by rw [hk₁.wr]; exact hs.xw, hs.dx, h5, by rw [h6, hnb]⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, _, hd, _, _, _, _, h6⟩ =>
      eval_zero h6 (by have := hd.ok.lt; omega_using [hnb, this])) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
      Env V sp s ∧ DataW (V .r29) (V .r30) (V .r31) s D n ∧ j ≤ n ∧ Covers [xR (V .r28)] s.wr ∧
      (⟨D, n⟩ : Region).Disjoint (xR (V .r28)) ∧
      s.gpr .r3 = V .r29 ∧ s.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧
      s.gpr .r5 = D + BitVec.ofNat 64 j ∧ s.gpr .r6 = BitVec.ofNat 64 nb ∧
      s.gpr .r7 = V .r28
    refine CT.seq (J := J₂) ?_ (fun s ⟨V, h29, h30, h31, h28, he, hd, hj, hxw, hdx, h5, h6⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
          (.block (ctrArgs 48)) h).isSome = true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, a29, a30, a31, a28, e₁, _⟩ ⟨_, b29, b30, b31, b28, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => pinK e₁ e₂ (a29.trans b29.symm)
          (a30.trans b30.symm) (a31.trans b31.symm) (a28.trans b28.symm) hr⟩) hc
    · refine WP.mono (ctrArgs_ok he) fun s₂ ⟨a3, a4, a7, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, h28, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, by rw [hk₂.wr]; exact hxw, hdx,
        a3, a4, by rw [hg₂ _ (by decide) (by decide) (by decide), h5],
        by rw [hg₂ _ (by decide) (by decide) (by decide), h6], a7⟩
    · refine CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, a28, he₁, hd₁, hj₁, ax, adx, a3, a4, a5, a6, a7⟩
        ⟨V₂, b29, b30, b31, b28, he₂, hd₂, _, bx, bdx, b3, b4, b5, b6, b7⟩ => ?_
      have hn₁ := hd₁.ok.lt
      have g₁ := ctrWhole_mk (L.v a29 a30 a31) (by rw [a29, a30, a31, a28]; exact X) he₁ a3 a4 a5 a6 a7 (by omega_using [hnb, hn₁])
        (hd₁.sub (j := j) (k := 16 * nb) (by omega_using [hnb, h0]) (by omega_using [h0])) ax (adx.sub_left (VG.Offset.sub_base _ (by omega_using [hnb, h0])))
      have g₂ := ctrWhole_mk (L.v b29 b30 b31) (by rw [b29, b30, b31, b28]; exact X) he₂ b3 b4 b5 b6 b7 (by omega_using [hnb, hn₁])
        (hd₂.sub (j := j) (k := 16 * nb) (by omega_using [hnb, h0]) (by omega_using [h0])) bx (bdx.sub_left (VG.Offset.sub_base _ (by omega_using [hnb, h0])))
      rw [a29, a30, a28] at g₁
      rw [b29, b30, b28] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w x sp D n q j) cryptTail := by
  refine CT.ite (decide (n - j = 0)) (fun s ⟨_, _, _, _, _, _, _, _, _, hs⟩ =>
    eval_zero hs.r25 (by have := hs.data.ok.lt; omega_using [this])) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    Env V sp s ∧ Covers [xR (V .r28)] s.wr ∧ s.gpr .r3 = V .r29 ∧
    s.gpr .r4 = V .r30 + BitVec.ofNat 64 48 ∧ s.gpr .r5 = V .r30 + BitVec.ofNat 64 64 ∧
    s.gpr .r6 = BitVec.ofNat 64 1 ∧ s.gpr .r7 = V .r28
  let J₂ : State → Prop := fun s => ∃ V icb P m₀ s₀, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧
    TailKs V sp icb P D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ => ?_) ?_)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ =>
      WP.mono (tailKs_ok (L.v h29 h30 h31) (by rw [h29, h30, h31, h28]; exact X) hs) fun s' h =>
        ⟨V, icb, P, m₀, s, h29, h30, h31, h28, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
        (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a29, a30, a31, a28, _, h₁⟩ ⟨_, _, _, _, b29, b30, b31, b28, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env
        (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) (a28.trans b28.symm) hr⟩) hc
  · refine WP.mono (tailArgs_ok hs.env) fun s₂ ⟨_, a3, a4, a5, a6, a7, hg₂, hk₂⟩ => ?_
    exact ⟨V, h29, h30, h31, h28, hs.env.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd
      hk₂.wr, by rw [hk₂.wr]; exact hs.xw, a3, a4, a5, a6, a7⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a29, a30, a31, a28, he₁, ax, a3, a4, a5, a6, a7⟩
      ⟨V₂, b29, b30, b31, b28, he₂, bx, b3, b4, b5, b6, b7⟩ => by
      have g₁ := ctrTail_mk (L.v a29 a30 a31) (by rw [a29, a30, a31, a28]; exact X) he₁ a3 a4 a5 a6 a7 ax
      have g₂ := ctrTail_mk (L.v b29 b30 b31) (by rw [b29, b30, b31, b28]; exact X) he₂ b3 b4 b5 b6 b7 bx
      rw [a29, a30, a28] at g₁
      rw [b29, b30, b28] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r30])
        (.seq (.block [.addi .r3 .r30 64, mov .r4 .r24, mov .r5 .r25]) xorLoop) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, a30, _, _, h₁⟩ ⟨_, _, _, _, _, _, b30, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.env.r30, h₂.env.r30, a30, b30]

theorem crypt_ct {D : Addr} {n q : Nat} :
    CT (CrI c st w x sp D n q) crypt := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs⟩ => eval_zero hs.r25 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w x sp D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, h28, hP, hs⟩ => WP.mono (cryptFill_ok hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨V, icb, P, s.mem, h29, h30, h31, h28, hP, by subst hj; rw [hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r24, .r25, .r26, .r30]) cryptFill
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, _, hP₁, h₁⟩ ⟨_, _, _, _, b30, _, _, hP₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r24, h₂.r24]
    · rw [h₁.r25, h₂.r25]
    · rw [h₁.r26, h₂.r26, hP₁, hP₂]
    · rw [h₁.env.r30, h₂.env.r30, a30, b30]
  refine CT.seq (J := CrM c st w x sp D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L X)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, hs⟩ =>
      WP.mono (cryptWhole_ok (L.v h29 h30 h31) (by rw [h29, h30, h31, h28]; exact X) hs) fun s' ⟨j, hj, hm, _⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, h28, hP, by subst hj; exact hm⟩) (cryptTail_ct L X)

end

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/InitCT.lean`): the code around SM4's inlined code by
the taint analysis, from the public arguments and the registers the
correctness proof pins; SM4's code by its own proofs (`CT.key`, `CT.ctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (restore)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.taintEq covers_mem covers_prefix)

theorem initPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem initArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r31])
    (.block initArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r31])
    (.block restore) h).isSome = true := ⟨_, by taint_decide⟩

theorem init_ct : ConstantTime isa initPPC64LE.pre initPPC64LE.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hpre₁ := h₁
  obtain ⟨-, -, -, -, dcs, -, fc, fs, -, dcx, dsx, fx⟩ := hpre₁
  generalize hK : σ₁.gpr .r3 = K at *
  generalize hC : σ₁.gpr .r4 = C at *
  generalize hW : σ₁.gpr .r5 = W at *
  generalize hX : σ₁.gpr .r6 = X at *
  generalize hSP : σ₁.sp = SP at *
  let I₀ : State → Prop := fun s => initPPC64LE.pre s ∧ s.gpr .r3 = K ∧ s.gpr .r4 = C ∧ s.gpr .r5 = W ∧
    s.gpr .r6 = X ∧ s.sp = SP
  let I₁ : State → Prop := fun s => KeyCall s K C X ∧
    s.gpr .r29 = C ∧ s.gpr .r31 = W ∧ s.gpr .r28 = X ∧ s.sp = SP ∧
    s.wr = [⟨C, 256⟩, ⟨W, scrBytes⟩, ⟨X, xBytes⟩]
  let I₂ : State → Prop := fun s => s.gpr .r29 = C ∧ s.gpr .r31 = W ∧ s.gpr .r28 = X ∧
    s.sp = SP ∧ s.wr = [⟨C, 256⟩, ⟨W, scrBytes⟩, ⟨X, xBytes⟩]
  let I₃ : State → Prop := fun s => CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240)
    X 1 ∧ s.gpr .r31 = W ∧ s.sp = SP
  let I₄ : State → Prop := fun s => s.gpr .r31 = W ∧ s.sp = SP
  refine ⟨I₀, ⟨h₁, hK, hC, hW, hX, hSP⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := I₁) ?_ (fun s ⟨hs, e3, e4, e5, e6, esp⟩ => WP.mono (is1_wp hs) fun s₁ h1 => ?_) ?_
  · obtain ⟨_, hc⟩ := initPre_taint
    exact CT.taintEq (I := I₀) _
      (fun r => if r = .r3 then K else if r = .r4 then C else if r = .r5 then W else X) SP
      (fun s ⟨_, e3, e4, e5, e6, esp⟩ => ⟨esp, by simp [e3, e4, e5, e6]⟩) hc
  · have kc := init_kc hs h1
    rw [e3, e4, e6] at kc
    obtain ⟨-, hwr, -⟩ := hs
    refine ⟨kc, by rw [h1.r29, e4], by rw [h1.r31, e5], by rw [h1.r28, e6],
      by rw [h1.keeps.sp, esp], by rw [h1.keeps.wr, hwr, e4, e5, e6]⟩
  refine CT.seq (J := I₂) ?_ (fun s ⟨kc, e29, e31, e28, esp, ewr⟩ => WP.mono (key_wp kc) fun s₂ kp =>
    ⟨by rw [kp.saved _ (by decide), e29], by rw [kp.saved _ (by decide), e31],
      by rw [kp.saved _ (by decide), e28], by rw [kp.sp, esp], by rw [kp.wr, ewr]⟩) ?_
  · exact CT.key fun s₁ s₂ h₁ h₂ => ⟨_, _, _, h₁.1, h₂.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm⟩
  refine CT.seq (J := I₃) ?_ (fun s ⟨e29, e31, e28, esp, ewr⟩ =>
    WP.mono (initArgs_ok e29 e31 e28 (by rw [ewr]; exact covers_mem (by simp))
      (by rw [ewr]; exact covers_mem (r := ⟨W, scrBytes⟩) (by simp)))
      fun s₃ ⟨_, a3, a4, a5, a6, a7, hg₃, hk₃⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := initArgs_taint
    exact CT.taintEq (I := I₂) _ (fun r => if r = .r28 then X else if r = .r29 then C else W)
      SP (fun s ⟨e29, e31, e28, esp, _⟩ => ⟨esp, by simp [e29, e31, e28]⟩) hc
  · have hW₃ : Covers [⟨W, scrBytes⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hX₃ : Covers [⟨X, xBytes⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hC₃ : Covers [⟨C, 256⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    exact ⟨init_cc dcs dcx dsx fc fs fx hW₃ hX₃ hC₃ a3 a4 a5 a6 a7,
      by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e31],
      by rw [hk₃.sp, esp]⟩
  refine CT.seq (J := I₄) ?_ (fun s ⟨cc, e31, esp⟩ => WP.mono (ctr_wp cc) fun s₄ cp =>
    ⟨by rw [cp.saved _ (by decide), e31], by rw [cp.sp, esp]⟩) ?_
  · exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq (I := I₄) _ (fun _ => W) SP (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
