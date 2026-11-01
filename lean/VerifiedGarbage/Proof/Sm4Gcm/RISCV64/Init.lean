module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. AES-GCM's `init`
(`Proof/AesGcm/RISCV64/Init.lean`) with SM4's functions, as on PPC64LE
(`Proof/Sm4Gcm/PPC64LE/Init.lean`): `init` saves our caller's registers in
`scratch` (`W`), expands the key into the context's schedule with
`vg_sm4_expand_key`, and computes the hash subkey `CIPH_K(0¹²⁸)` into its
bytes 240–255 with `vg_sm4_ctr32` on a zero block, from a zero counter block
at `W + 96` (`init_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov tO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel KeyCall KeyPost key_call key_rel IS1 is1_wp init_kc IS2 initArgs_ok init_cc
  init_wp initRISCV64 stkOk stkAll
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)

/-- After the entry, from `s₀`. -/
structure IS1 (s₀ s₁ : State) : Prop where
  s0 : s₁.gpr .s0 = s₀.gpr .a2
  s2 : s₁.gpr .s2 = s₀.gpr .a1
  a0 : s₁.gpr .a0 = s₀.gpr .a0
  a1 : s₁.gpr .a1 = s₀.gpr .a1
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem (s₀.gpr .a2) s₀
  frame : Frame [savedR (s₀.gpr .a2)] s₀.mem s₁.mem

theorem is1_wp {s₀ : State} (h : initRISCV64.pre s₀) : WP isa (.block initPre) s₀ (IS1 s₀) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, hal⟩ := h
  have hW : Covers [⟨s₀.gpr .a2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.block_append (WP.mono (save_ok (b := .a2) hW hal) fun s ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e4 : s.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e4, h31]
  exact ⟨by simp [h31], by simp, by simp [hg], by simp [hg], ⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩

theorem init_kc {s₀ s₁ : State} (h : initRISCV64.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .a0) (s₀.gpr .a1) := by
  obtain ⟨hrd, hwr, dkc, -, -, fk, fc, -, ⟨spal, spge, bK, bC, -, -⟩, -, -⟩ := h
  have hC : Covers [⟨s₀.gpr .a1, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hsp := h1.keeps.sp
  have hs : Region.Sub (below s₀.sp 3168) (below s₀.sp 3232) := below_le (by decide) (by decide)
  refine ⟨h1.a0, h1.a1, dkc.sub_right (Region.sub_prefix (by decide)), fk, by omega, by rw [hsp]; exact spal,
    by rw [hsp]; omega, by rw [hsp]; exact bK.sub_left hs,
    by rw [hsp]; exact (bC.sub_left hs).sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [h1.keeps.rd, h1.keeps.wr, hrd]
    exact Covers.cons (Covers.left (covers_mem (by simp))) (Covers.cons
      (Covers.right (covers_prefix hC (by decide))) Covers.nil)
  · rw [h1.keeps.wr]
    exact Covers.cons (covers_prefix hC (by decide)) Covers.nil

/-- `initArgs`: the hash subkey's block and `T` zeroed, and the arguments of
`vg_sm4_ctr32`. -/
theorem initArgs_ok {C W : Addr} {s : State} (h29 : s.gpr .s2 = C) (h31 : s.gpr .s0 = W)
    (hc : Covers [⟨C, 256⟩] s.wr) (hw : Covers [⟨W, 2560⟩] s.wr)
    (hca : C.toNat % 8 = 0) (hwa : W.toNat % 8 = 0) :
    WP isa (.block initArgs) s fun s' =>
      s'.mem = (((s.mem.writeW (C + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
          (C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
          (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .a0 = C ∧ s'.gpr .a1 = W + BitVec.ofNat 64 96 ∧ s'.gpr .a2 = C + BitVec.ofNat 64 240 ∧
      s'.gpr .a3 = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have c₀ := in_off hc (show 240 + 8 ≤ 256 by decide) (by decide)
  have c₁ := in_off hc (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₀ := in_off hw (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₁ := in_off hw (show 104 + 8 ≤ 2560 by decide) (by decide)
  have a₀ := Spill.al8 hca (d := 240) (by decide)
  have a₁ := Spill.al8 hca (d := 248) (by decide)
  have a₂ := Spill.al8 hwa (d := 96) (by decide)
  have a₃ := Spill.al8 hwa (d := 104) (by decide)
  crun [Int.reduceNatCast', initArgs, tO, h29, h31, c₀, c₁, w₀, w₁, a₀, a₁, a₂, a₃, mov, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e => by simp [a, b, c, d, e], ⟨rfl, rfl, rfl⟩⟩

/-- The arguments of `init`'s call of `vg_sm4_ctr32`: the hash subkey's block
encrypted from the counter block `T`. -/
theorem init_cc {C W : Addr} {s : State} (dcs : (⟨C, 256⟩ : Region).Disjoint ⟨W, 2560⟩)
    (fc : C.toNat + 256 ≤ 2 ^ 64) (fs : W.toNat + 2560 ≤ 2 ^ 64) (hW : Covers [⟨W, 2560⟩] s.wr)
    (hC : Covers [⟨C, 256⟩] s.wr) (spal : s.sp.toNat % 16 = 0) (spge : 3232 ≤ s.sp.toNat)
    (bC : (below s.sp 3232).Disjoint ⟨C, 256⟩) (bS : (below s.sp 3232).Disjoint ⟨W, 2560⟩)
    (a3 : s.gpr .a0 = C) (a5 : s.gpr .a1 = W + BitVec.ofNat 64 96) (a6 : s.gpr .a2 = C + BitVec.ofNat 64 240)
    (a7 : s.gpr .a3 = BitVec.ofNat 64 1) :
    CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240) 1 := by
  have fit (p : Addr) (d k : Nat) (hd : d + 16 ≤ k) (hp : p.toNat + k ≤ 2 ^ 64) :
      (p + BitVec.ofNat 64 d).toNat + 16 ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  refine ⟨a3, a5, a6, a7, by decide, ?_, ?_, ?_, by omega, fit W 96 2560 (by decide) fs,
    fit C 240 256 (by decide) fc, spal, spge, bC.sub_right (Region.sub_prefix (by decide)),
    bS.sub_right (Offset.sub_base _ (by decide)), bC.sub_right (Offset.sub_base _ (by decide)), ?_, ?_⟩
  · exact (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · simpa using Offset.disjoint C (d := 0) (n := 128) (e := 240) (k := 16) (.inl (by decide))
      (by decide) (by omega)
  · exact ((dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
  · exact Covers.cons (Covers.right (covers_prefix hC (by decide))) (Covers.cons
      (Covers.right (covers_off hW (by decide) (by decide))) (Covers.cons
        (Covers.right (covers_off hC (by decide) (by decide))) Covers.nil))
  · exact Covers.cons (covers_off hW (by decide) (by decide)) (Covers.cons
      (covers_off hC (by decide) (by decide)) Covers.nil)

/-- `init`. -/
theorem init_wp {s₀ : State} (h : initRISCV64.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initRISCV64.post s₀ s' := by
  have h' := h
  obtain ⟨hrd, hwr, dkc, dks, dcs, fk, fc, fs, ⟨spal, spge, bK, bC, bS, -⟩, hca, hwa⟩ := h'
  have hW : Covers [⟨s₀.gpr .a2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hC : Covers [⟨s₀.gpr .a1, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  -- Regions apart from the saved slots, and from the key schedule.
  have sW : ∀ {d k : Nat}, d + k ≤ 2560 → (d + k ≤ 128 ∨ 232 ≤ d) →
      (savedR (s₀.gpr .a2)).Disjoint ⟨s₀.gpr .a2 + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ => saved_w h₁ h₂
  have sC : ∀ {d k : Nat}, d + k ≤ 256 → (savedR (s₀.gpr .a2)).Disjoint ⟨s₀.gpr .a1 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => ((dcs.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ (by decide))).symm
  have sC0 : (savedR (s₀.gpr .a2)).Disjoint ⟨s₀.gpr .a1, 128⟩ :=
    (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
  have sB : ∀ {k : Nat}, k ≤ 3232 → (savedR (s₀.gpr .a2)).Disjoint (below s₀.sp k) := fun hk =>
    ((bS.sub_left (below_le hk (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
  have kW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨s₀.gpr .a1, 128⟩ : Region).Disjoint ⟨s₀.gpr .a2 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ h₁)
  have kC : (⟨s₀.gpr .a1, 128⟩ : Region).Disjoint ⟨s₀.gpr .a1 + BitVec.ofNat 64 240, 16⟩ := by
    simpa using Offset.disjoint (s₀.gpr .a1) (d := 0) (n := 128) (e := 240) (k := 16)
      (.inl (by decide)) (by decide) (by omega)
  have kB : (⟨s₀.gpr .a1, 128⟩ : Region).Disjoint (below s₀.sp 3232) :=
    (bC.sub_right (Region.sub_prefix (by decide))).symm
  refine WP.seq (WP.mono (is1_wp h) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (key_call (init_kc h h1)) fun s₂ kp => ?_)
  have g31 : s₂.gpr .s0 = s₀.gpr .a2 := (kp.saved _ (by decide)).trans h1.s0
  have g29 : s₂.gpr .s2 = s₀.gpr .a1 := (kp.saved _ (by decide)).trans h1.s2
  have wr₂ : s₂.wr = s₀.wr := kp.wr.trans h1.keeps.wr
  have rd₂ : s₂.rd = s₀.rd := kp.rd.trans h1.keeps.rd
  have sp₂ : s₂.sp = s₀.sp := kp.sp.trans h1.keeps.sp
  have kpf := kp.frame
  rw [h1.keeps.sp] at kpf
  refine WP.seq (WP.mono (initArgs_ok g29 g31 (by rw [wr₂]; exact hC) (by rw [wr₂]; exact hW) hca hwa)
    fun s₃ ⟨hm₃, a3, a5, a6, a7, hg₃, hk₃⟩ => ?_)
  have sp₃ : s₃.sp = s₀.sp := hk₃.sp.trans sp₂
  have cc : CtrCall s₃ (s₀.gpr .a1) (s₀.gpr .a2 + BitVec.ofNat 64 96) (s₀.gpr .a1 + BitVec.ofNat 64 240) 1 :=
    init_cc dcs fc fs (by rw [hk₃.wr, wr₂]; exact hW) (by rw [hk₃.wr, wr₂]; exact hC) (by rw [sp₃]; exact spal)
      (by rw [sp₃]; exact spge) (by rw [sp₃]; exact bC) (by rw [sp₃]; exact bS) a3 a5 a6 a7
  refine WP.seq (WP.mono (ctr_call cc) fun s₄ cp => ?_)
  have cpf := cp.frame
  rw [sp₃] at cpf
  -- The memory along the way.
  obtain ⟨m₂', hm₂'⟩ : ∃ m, m = (s₂.mem.writeW (s₀.gpr .a1 + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
      (s₀.gpr .a1 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := ⟨_, rfl⟩
  rw [← hm₂'] at hm₃
  have fa : Frame [⟨s₀.gpr .a1 + BitVec.ofNat 64 240, 16⟩] s₂.mem m₂' := by
    rw [hm₂']; exact Proof.Cmac.frame_store2 _ _ _
  have fb : Frame [⟨s₀.gpr .a2 + BitVec.ofNat 64 96, 16⟩] m₂' s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store2 _ _ _
  have f₃ : Frame [⟨s₀.gpr .a1 + BitVec.ofNat 64 240, 16⟩, ⟨s₀.gpr .a2 + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem :=
    (fa.mono (by simp)).trans (fb.mono (by simp))
  have sv₄ : SavedAt s₄.mem (s₀.gpr .a2) s₀ := by
    refine ((h1.saved.frame kpf ?_).frame f₃ ?_).frame cpf ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sC0
      · exact sB (by decide)
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
      · exact sB (by decide)
  refine WP.mono (restore_ok (s₀ := s₀) (by rw [cp.saved _ (by decide), hg₃ _ (by decide) (by decide)
      (by decide) (by decide) (by decide), g31]) hwa
    (by rw [cp.rd, cp.wr, hk₃.rd, hk₃.wr, wr₂]; exact Covers.right hW) sv₄
    (by rw [cp.sp, sp₃])) fun s' ⟨hab, hm', _, _, _⟩ => ⟨hab, ?_⟩
  -- The key schedule and the hash subkey.
  have key₁ : Spec.Sm4.blockAt s₁.mem (s₀.gpr .a0) =
      Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .a0) 16).getD i.val 0 := by
    rw [← Proof.Sm4.ofFn_toList (Spec.Sm4.blockAt s₁.mem _), ← Proof.Sm4.bytesAt_eq_blockAt,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Offset.sub_base _ (by decide))) (by decide)]
  have ks₃ : Spec.Sm4.scheduleAt s₃.mem (s₀.gpr .a1) =
      Spec.Sm4.expandKey (Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .a0) 16).getD i.val 0) := by
    rw [Proof.Sm4.scheduleAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact kC
        · exact kW (by decide)), kp.out, key₁]
  simp only [initRISCV64, KeyRepr, hm']
  refine ⟨?_, ?_⟩
  · rw [Proof.Sm4.scheduleAt_frame cpf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact kW (by decide)
        · simpa using kC
        · exact kB), ks₃]
  · have cout := cp.out
    rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at cout
    have z₁ : blockAt s₃.mem (s₀.gpr .a2 + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block2]
    have z₂ : blockAt s₃.mem (s₀.gpr .a1 + BitVec.ofNat 64 240) = 0 := by
      rw [blockAt_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))),
        hm₂', zero_block2]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    simp only [Spec.Sm4.gcmCipherOfKey, ks₃]

end VG.Proof.Sm4Gcm.RISCV64
