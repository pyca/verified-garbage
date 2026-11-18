module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTOpen
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTFin
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Gcm
meta import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush

/-! ### `Sm4Gcm.RISCV64.InitCT`, which only this module used -/

section

/-! ### `Sm4Gcm.RISCV64.Init`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. AES-GCM's `init`
(`Proof/AesGcm/RISCV64/Init.lean`) with SM4's functions, as on PPC64LE
(`Proof/Sm4Gcm/PPC64LE/InitCT.lean`): `init` saves our caller's registers in
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
  obtain hW : Covers [⟨s₀.gpr .a2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.block_append (WP.mono (save_ok (b := .a2) hW hal) fun s ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  obtain e4 : s.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e4, h31]
  exact ⟨by simp [h31], by simp, by simp [hg], by simp [hg], ⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩

theorem init_kc {s₀ s₁ : State} (h : initRISCV64.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .a0) (s₀.gpr .a1) := by
  obtain ⟨hrd, hwr, dkc, -, -, fk, fc, -, ⟨spal, spge, bK, bC, -, -⟩, -, -⟩ := h
  obtain hC : Covers [⟨s₀.gpr .a1, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hsp := h1.keeps.sp
  obtain hs : Region.Sub (below s₀.sp 3168) (below s₀.sp 3248) := below_le (by decide) (by decide)
  refine ⟨h1.a0, h1.a1, dkc.sub_right (Region.sub_prefix (by decide)), fk, by omega_using [fc], by rw [hsp]; exact spal,
    by rw [hsp]; omega_using [spge], by rw [hsp]; exact bK.sub_left hs,
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
  obtain c₀ := in_off hc (show 240 + 8 ≤ 256 by decide) (by decide)
  obtain c₁ := in_off hc (show 248 + 8 ≤ 256 by decide) (by decide)
  obtain w₀ := in_off hw (show 96 + 8 ≤ 2560 by decide) (by decide)
  obtain w₁ := in_off hw (show 104 + 8 ≤ 2560 by decide) (by decide)
  obtain a₀ := Spill.al8 hca (d := 240) (by decide)
  obtain a₁ := Spill.al8 hca (d := 248) (by decide)
  obtain a₂ := Spill.al8 hwa (d := 96) (by decide)
  obtain a₃ := Spill.al8 hwa (d := 104) (by decide)
  crun [Int.reduceNatCast', initArgs, tO, h29, h31, c₀, c₁, w₀, w₁, a₀, a₁, a₂, a₃, mov, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e => by simp [a, b, c, d, e], ⟨rfl, rfl, rfl⟩⟩

/-- The arguments of `init`'s call of `vg_sm4_ctr32`: the hash subkey's block
encrypted from the counter block `T`. -/
theorem init_cc {C W : Addr} {s : State} (dcs : (⟨C, 256⟩ : Region).Disjoint ⟨W, 2560⟩)
    (fc : C.toNat + 256 ≤ 2 ^ 64) (fs : W.toNat + 2560 ≤ 2 ^ 64) (hW : Covers [⟨W, 2560⟩] s.wr)
    (hC : Covers [⟨C, 256⟩] s.wr) (spal : s.sp.toNat % 16 = 0) (spge : 3248 ≤ s.sp.toNat)
    (bC : (below s.sp 3248).Disjoint ⟨C, 256⟩) (bS : (below s.sp 3248).Disjoint ⟨W, 2560⟩)
    (a3 : s.gpr .a0 = C) (a5 : s.gpr .a1 = W + BitVec.ofNat 64 96) (a6 : s.gpr .a2 = C + BitVec.ofNat 64 240)
    (a7 : s.gpr .a3 = BitVec.ofNat 64 1) :
    CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240) 1 := by
  have fit (p : Addr) (d k : Nat) (hd : d + 16 ≤ k) (hp : p.toNat + k ≤ 2 ^ 64) :
      (p + BitVec.ofNat 64 d).toNat + 16 ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  refine ⟨a3, a5, a6, a7, by decide, ?_, ?_, ?_, by omega_using [fc], fit W 96 2560 (by decide) fs,
    fit C 240 256 (by decide) fc, spal, spge, bC.sub_right (Region.sub_prefix (by decide)),
    bS.sub_right (Offset.sub_base _ (by decide)), bC.sub_right (Offset.sub_base _ (by decide)), ?_, ?_⟩
  · exact (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · simpa using Offset.disjoint C (d := 0) (n := 128) (e := 240) (k := 16) (.inl (by decide))
      (by decide) (by omega_using [])
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
  obtain hW : Covers [⟨s₀.gpr .a2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hC : Covers [⟨s₀.gpr .a1, 256⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  -- Regions apart from the saved slots, and from the key schedule.
  obtain sW : ∀ {d k : Nat}, d + k ≤ 2560 → (d + k ≤ 128 ∨ 232 ≤ d) →
      (savedR (s₀.gpr .a2)).Disjoint ⟨s₀.gpr .a2 + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ => saved_w h₁ h₂
  obtain sC : ∀ {d k : Nat}, d + k ≤ 256 → (savedR (s₀.gpr .a2)).Disjoint ⟨s₀.gpr .a1 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => ((dcs.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ (by decide))).symm
  obtain sC0 : (savedR (s₀.gpr .a2)).Disjoint ⟨s₀.gpr .a1, 128⟩ :=
    (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
  obtain sB : ∀ {k : Nat}, k ≤ 3248 → (savedR (s₀.gpr .a2)).Disjoint (below s₀.sp k) := fun hk =>
    ((bS.sub_left (below_le hk (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
  obtain kW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨s₀.gpr .a1, 128⟩ : Region).Disjoint ⟨s₀.gpr .a2 + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (dcs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ h₁)
  obtain kC : (⟨s₀.gpr .a1, 128⟩ : Region).Disjoint ⟨s₀.gpr .a1 + BitVec.ofNat 64 240, 16⟩ := by
    simpa using Offset.disjoint (s₀.gpr .a1) (d := 0) (n := 128) (e := 240) (k := 16)
      (.inl (by decide)) (by decide) (by omega_using [])
  obtain kB : (⟨s₀.gpr .a1, 128⟩ : Region).Disjoint (below s₀.sp 3248) :=
    (bC.sub_right (Region.sub_prefix (by decide))).symm
  refine WP.seq (WP.mono (is1_wp h) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (key_call (init_kc h h1)) fun s₂ kp => ?_)
  obtain g31 : s₂.gpr .s0 = s₀.gpr .a2 := (kp.saved _ (by decide)).trans h1.s0
  obtain g29 : s₂.gpr .s2 = s₀.gpr .a1 := (kp.saved _ (by decide)).trans h1.s2
  obtain wr₂ : s₂.wr = s₀.wr := kp.wr.trans h1.keeps.wr
  obtain rd₂ : s₂.rd = s₀.rd := kp.rd.trans h1.keeps.rd
  obtain sp₂ : s₂.sp = s₀.sp := kp.sp.trans h1.keeps.sp
  have kpf := kp.frame
  rw [h1.keeps.sp] at kpf
  refine WP.seq (WP.mono (initArgs_ok g29 g31 (by rw [wr₂]; exact hC) (by rw [wr₂]; exact hW) hca hwa)
    fun s₃ ⟨hm₃, a3, a5, a6, a7, hg₃, hk₃⟩ => ?_)
  obtain sp₃ : s₃.sp = s₀.sp := hk₃.sp.trans sp₂
  obtain cc : CtrCall s₃ (s₀.gpr .a1) (s₀.gpr .a2 + BitVec.ofNat 64 96) (s₀.gpr .a1 + BitVec.ofNat 64 240) 1 :=
    init_cc dcs fc fs (by rw [hk₃.wr, wr₂]; exact hW) (by rw [hk₃.wr, wr₂]; exact hC) (by rw [sp₃]; exact spal)
      (by rw [sp₃]; exact spge) (by rw [sp₃]; exact bC) (by rw [sp₃]; exact bS) a3 a5 a6 a7
  refine WP.seq (WP.mono (ctr_call cc) fun s₄ cp => ?_)
  have cpf := cp.frame
  rw [sp₃] at cpf
  -- The memory along the way.
  obtain ⟨m₂', hm₂'⟩ : ∃ m, m = (s₂.mem.writeW (s₀.gpr .a1 + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
      (s₀.gpr .a1 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := ⟨_, rfl⟩
  rw [← hm₂'] at hm₃
  obtain fa : Frame [⟨s₀.gpr .a1 + BitVec.ofNat 64 240, 16⟩] s₂.mem m₂' := by
    rw [hm₂']; exact Proof.Cmac.frame_store2 _ _ _
  obtain fb : Frame [⟨s₀.gpr .a2 + BitVec.ofNat 64 96, 16⟩] m₂' s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store2 _ _ _
  obtain f₃ : Frame [⟨s₀.gpr .a1 + BitVec.ofNat 64 240, 16⟩, ⟨s₀.gpr .a2 + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem :=
    (fa.mono (by simp)).trans (fb.mono (by simp))
  obtain sv₄ : SavedAt s₄.mem (s₀.gpr .a2) s₀ := by
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
  obtain key₁ : Spec.Sm4.blockAt s₁.mem (s₀.gpr .a0) =
      Vector.ofFn fun i => (bytesAt s₀.mem (s₀.gpr .a0) 16).getD i.val 0 := by
    rw [← Proof.Sm4.ofFn_toList (Spec.Sm4.blockAt s₁.mem _), ← Proof.Sm4.bytesAt_eq_blockAt,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Offset.sub_base _ (by decide))) (by decide)]
  obtain ks₃ : Spec.Sm4.scheduleAt s₃.mem (s₀.gpr .a1) =
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
    obtain z₁ : blockAt s₃.mem (s₀.gpr .a2 + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block2]
    obtain z₂ : blockAt s₃.mem (s₀.gpr .a1 + BitVec.ofNat 64 240) = 0 := by
      rw [blockAt_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dcs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))),
        hm₂', zero_block2]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    simp only [Spec.Sm4.gcmCipherOfKey, ks₃]

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/InitCT.lean`): the code around the calls by the taint
analysis, from the public arguments and the registers the correctness proof
pins; SM4's code by its own proofs (`CT.skey`, `CT.sctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (restore)
open VG.Proof.AesGcm.RISCV64 (CT ct_of CT.taintEq covers_mem restore_taint)

theorem initPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.a0, .a1, .a2])
    (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem initArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s2, .s0])
    (.block initArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem init_ct : ConstantTime isa initRISCV64.pre initRISCV64.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, qsp⟩ := hq
  have hpre₁ := h₁
  obtain ⟨-, -, -, -, dcs, -, fc, fs, ⟨spal, spge, -, bC, bS, -⟩, hca, hwa⟩ := hpre₁
  generalize hK : σ₁.gpr .a0 = K at *
  generalize hC : σ₁.gpr .a1 = C at *
  generalize hW : σ₁.gpr .a2 = W at *
  generalize hSP : σ₁.sp = SP at *
  let I₀ : State → Prop := fun s => initRISCV64.pre s ∧ s.gpr .a0 = K ∧ s.gpr .a1 = C ∧ s.gpr .a2 = W ∧
    s.sp = SP
  let I₁ : State → Prop := fun s => KeyCall s K C ∧ s.gpr .s2 = C ∧ s.gpr .s0 = W ∧ s.sp = SP ∧
    s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₂ : State → Prop := fun s => s.gpr .s2 = C ∧ s.gpr .s0 = W ∧ s.sp = SP ∧ s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₃ : State → Prop := fun s => CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240) 1 ∧
    s.gpr .s0 = W ∧ s.sp = SP
  let I₄ : State → Prop := fun s => s.gpr .s0 = W ∧ s.sp = SP
  refine ⟨I₀, ⟨h₁, hK, hC, hW, hSP⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := I₁) ?_ (fun s ⟨hs, e3, e4, e5, esp⟩ => WP.mono (is1_wp hs) fun s₁ h1 => ?_) ?_
  · obtain ⟨_, hc⟩ := initPre_taint
    exact CT.taintEq (I := I₀) _ (fun r => if r = .a0 then K else if r = .a1 then C else W) SP
      (fun s ⟨_, e3, e4, e5, esp⟩ => ⟨esp, by simp [e3, e4, e5]⟩) hc
  · have kc := init_kc hs h1
    rw [e3, e4] at kc
    obtain ⟨-, hwr, -⟩ := hs
    refine ⟨kc, by rw [h1.s2, e4], by rw [h1.s0, e5], by rw [h1.keeps.sp, esp], by rw [h1.keeps.wr, hwr, e4, e5]⟩
  refine CT.seq (J := I₂) ?_ (fun s ⟨kc, e29, e31, esp, ewr⟩ => WP.mono (key_call kc) fun s₂ kp =>
    ⟨by rw [kp.saved _ (by decide), e29], by rw [kp.saved _ (by decide), e31], by rw [kp.sp, esp],
      by rw [kp.wr, ewr]⟩) ?_
  · exact CT.skey fun s₁ s₂ h₁ h₂ => ⟨_, _, h₁.1, h₂.1, h₁.2.2.2.1.trans h₂.2.2.2.1.symm⟩
  refine CT.seq (J := I₃) ?_ (fun s ⟨e29, e31, esp, ewr⟩ =>
    WP.mono (initArgs_ok e29 e31 (by rw [ewr]; exact covers_mem (by simp))
      (by rw [ewr]; exact covers_mem (by simp)) hca hwa) fun s₃ ⟨_, a3, a4, a5, a6, hg₃, hk₃⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := initArgs_taint
    exact CT.taintEq (I := I₂) _ (fun r => if r = .s2 then C else W)
      SP (fun s ⟨e29, e31, esp, _⟩ => ⟨esp, by simp [e29, e31]⟩) hc
  · have hW₃ : Covers [⟨W, 2560⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hC₃ : Covers [⟨C, 256⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have sp₃ : s₃.sp = SP := by rw [hk₃.sp, esp]
    exact ⟨init_cc dcs fc fs hW₃ hC₃ (by rw [sp₃]; exact spal) (by rw [sp₃]; exact spge)
      (by rw [sp₃]; exact bC) (by rw [sp₃]; exact bS) a3 a4 a5 a6,
      by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), e31], sp₃⟩
  refine CT.seq (J := I₄) ?_ (fun s ⟨cc, e31, esp⟩ => WP.mono (ctr_call cc) fun s₄ cp =>
    ⟨by rw [cp.saved _ (by decide), e31], by rw [cp.sp, esp]⟩) ?_
  · exact CT.sctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq (I := I₄) _ (fun _ => W) SP (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-! ### `Sm4Gcm.RISCV64.CTCryptFn`, which only this module used -/

section

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/Verified.lean`): the entry by the taint analysis
from the public arguments, which it keeps in registers the pieces preserve
(`DI`); then `crypt` (`crypt_ct`) and `textAbsorb` (`textAbsorb_ct`), in
either order, from the invariants their correctness gives; then the exit
from `W`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (textArgs textAbsorb restore)
open VG.Proof.AesGcm.RISCV64 (CT ct_of CT.taintEq Env Lay DataW TA textAbsorb_ct textAbsorb_ok textArgs_ok
  restore_taint)

/-- After the entry: the arguments kept, `len` (`N`) bytes at `data` (`D`),
after `aad_len` (`A`) bytes of additional data and `text_len` (`T`) of
text. -/
def DI (c st w sp D : Addr) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧
    V .s11 = T ∧ Env V sp s ∧ Big V sp ∧ (below sp 3248).Disjoint ⟨D, N.toNat⟩ ∧ DataW c st w s D N.toNat

/-- Before `crypt`, with the arguments kept. -/
def CI (c st w sp D : Addr) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧ V .s11 = T ∧
    P % 16 = T.toNat % 16 ∧ CrIn V sp icb P D N.toNat s

theorem cryptEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (.block cryptEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptEntryArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (.block (cryptEntry ++ textArgs)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem textArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s11])
    (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩

/-- The entry. -/
theorem sc_DI {s₀ : State} (h : streamCryptPre s₀) :
    WP isa (.block cryptEntry) s₀ (DI (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₀.sp (s₀.gpr .a4)
      (s₀.gpr .a5) (s₀.gpr .a2) (s₀.gpr .a3)) :=
  WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ⟨s₁.gpr, h1.s2, h1.s1, h1.s0, h1.s9, h1.s8, h1.s10, h1.s11,
    sc_env h h1, sc_big h h1.s2 h1.s1 h1.s0, sc_bd h, sc_dataW h h1.en.keeps.wr h1.en.keeps.sp⟩

section
variable {c st w sp D : Addr} {N A T : BitVec 64}

theorem di_ta {s : State} (h : DI c st w sp D N A T s) : TA c st w sp D N A T s :=
  let ⟨V, h29, h30, h31, h20, h19, h22, h23, he, _, _, hd⟩ := h
  ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd.ok⟩

theorem ci_cr {s : State} (h : CI c st w sp D N A T s) : CrI c st w sp D N.toNat (T.toNat % 16) s :=
  let ⟨V, icb, P, h29, h30, h31, _, _, _, _, hP, ci⟩ := h
  ⟨V, icb, P, h29, h30, h31, hP, ci⟩

theorem ta_exit {s : State} (h : TA c st w sp D N A T s) : s.gpr .s0 = w ∧ s.sp = sp :=
  let ⟨_, _, _, h31, _, _, _, _, he, _⟩ := h
  ⟨(he.fr _ (by decide)).trans h31, he.sp⟩

/-- The arguments of `crypt`. -/
theorem di_textArgs {s : State} (h : DI c st w sp D N A T s) :
    WP isa (.block textArgs) s (CI c st w sp D N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hb, hbd, hd⟩ := h
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg, hk⟩ => ?_
  have he₂ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    hk.sp hk.rd hk.wr
  exact ⟨V, 0, T.toNat, h29, h30, h31, h20, h19, h22, h23, rfl, he₂, by rw [h24, he.fr _ (by decide), h20],
    by rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [h26, he.fr _ (by decide), h23], hb, hbd, by rw [h29, h30, h31]; exact hd.of_eq hk.rd hk.wr hk.sp⟩

variable (L : Lay c st w)
include L

theorem ci_crypt {s : State} (h : CI c st w sp D N A T s) : WP isa crypt s (TA c st w sp D N A T) := by
  obtain ⟨V, icb, P, h29, h30, h31, h20, h19, h22, h23, _, ci⟩ := h
  refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (crypt_ok (L.v h29 h30 h31) ci)) fun s' ⟨co, rd, wr, sp'⟩ =>
    ⟨V, h29, h30, h31, h20, h19, h22, h23, co.env, ?_⟩
  have := ci.data.ok.of_eq rd wr sp'
  rw [h30, h31] at this
  exact this

theorem di_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : DI c st w sp D N A T s) :
    WP isa textAbsorb s (DI c st w sp D N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hb, hbd, hd⟩ := h
  refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd.ok) (by simp [h22])
    (by simp [h23]))) fun s' ⟨ta, rd, wr, sp'⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, ta.env, hb, hbd,
      hd.of_eq rd wr sp'⟩

theorem ta_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : TA c st w sp D N A T s) :
    WP isa textAbsorb s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ := h
  exact WP.mono (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd) (by simp [h22])
    (by simp [h23])) fun s' ta => ⟨(ta.env.fr _ (by decide)).trans h31, ta.env.sp⟩

end

/-- The invariant of the entry, from the public arguments of `σ`. -/
abbrev SCI (σ : State) (s : State) : Prop :=
  streamCryptPre s ∧ s.gpr .a0 = σ.gpr .a0 ∧ s.gpr .a1 = σ.gpr .a1 ∧ s.gpr .a2 = σ.gpr .a2 ∧
    s.gpr .a3 = σ.gpr .a3 ∧ s.gpr .a4 = σ.gpr .a4 ∧ s.gpr .a5 = σ.gpr .a5 ∧ s.gpr .a6 = σ.gpr .a6 ∧
    s.sp = σ.sp

theorem sci_of {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂) (hq : streamCryptPub σ₁ σ₂) :
    SCI σ₁ σ₁ ∧ SCI σ₁ σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  exact ⟨⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, qsp.symm⟩⟩

theorem sci_DI {σ s : State} (h : SCI σ s) :
    WP isa (.block cryptEntry) s (DI (σ.gpr .a0) (σ.gpr .a1) (σ.gpr .a6) σ.sp (σ.gpr .a4)
      (σ.gpr .a5) (σ.gpr .a2) (σ.gpr .a3)) := by
  obtain ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ := h
  have := sc_DI hs
  rw [e3, e4, e5, e6, e7, e8, e9, esp] at this
  exact this

theorem streamEncrypt_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamEncryptRISCV64.pre streamEncryptRISCV64.pub streamEncrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := CI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a6) σ₁.sp (σ₁.gpr .a4)
    (σ₁.gpr .a5) (σ₁.gpr .a2) (σ₁.gpr .a3)) ?_
    (fun s h => WP.block_append (WP.mono (sci_DI h) fun _ h' => di_textArgs h')) ?_
  · obtain ⟨_, hc⟩ := cryptEntryArgs_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp) (textAbsorb_ct L)
    (fun _ h => ta_textAbsorb L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a6) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamDecrypt_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamDecryptRISCV64.pre streamDecryptRISCV64.pub streamDecrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := DI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a6) σ₁.sp (σ₁.gpr .a4)
    (σ₁.gpr .a5) (σ₁.gpr .a2) (σ₁.gpr .a3)) ?_ (fun s h => sci_DI h) ?_
  · obtain ⟨_, hc⟩ := cryptEntry_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  refine CT.seq ((textAbsorb_ct L).mono fun _ h => di_ta h) (fun _ h => di_textAbsorb L h) ?_
  refine CT.seq ?_ (fun _ h => di_textArgs h) ?_
  · obtain ⟨_, hc⟩ := textArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, e₁, _⟩
      ⟨_, _, _, _, b20, b19, _, b23, e₂, _⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a6) σ₁.sp (fun s h => ⟨(ta_exit h).2, by simp [(ta_exit h).1]⟩) hc

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-!
# SM4-GCM on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with the working space as a last argument
(`Proof/Sm4Gcm/Scratch.lean`), with the 3248 bytes of stack that
`vg_sm4_ctr32`'s frame takes (the deepest of the callees'). Then each
function in a frame that allocates its working space, as AES-GCM's
(`Proof/AesGcm/RISCV64/Verified.lean`); `vg_sm4_gcm_stream_init` and
`vg_sm4_gcm_stream_aad` are AES-GCM's.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Proof.AesGcm.RISCV64 (args onePub)

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' :=
  init_wp hs

theorem streamEncrypt_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamEncryptRISCV64.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptRISCV64.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamDecryptRISCV64.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptRISCV64.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamFinishRISCV64.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishRISCV64.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamVerifyRISCV64.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyRISCV64.post s s' :=
  streamVerify_wp hs

theorem seal_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hs

theorem open_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a4 => 0x2000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a4 => 0x5000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a4 => 0x5000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified RISCV64.target init (Proof.Sm4Gcm.initScratchContract RISCV64.abi 3248) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.Sm4Gcm.initScratchContract, Proof.Sm4Gcm.initScratchSig, Spec.Sm4.Gcm.initPost,
      initRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [initSat] using initSat)

theorem streamEncrypt_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamEncrypt (Proof.Sm4Gcm.streamEncryptScratchContract RISCV64.abi 3248) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.Sm4Gcm.streamEncryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamEncryptPost, streamEncryptRISCV64, streamCryptPre, streamCryptPub, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamDecrypt (Proof.Sm4Gcm.streamDecryptScratchContract RISCV64.abi 3248) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.Sm4Gcm.streamDecryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamDecryptPost, streamDecryptRISCV64, streamCryptPre, streamCryptPub, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamFinish (Proof.Sm4Gcm.streamFinishScratchContract RISCV64.abi 3248) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.Sm4Gcm.streamFinishScratchContract, Proof.Sm4Gcm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishPost, streamFinishRISCV64, finPre, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [finSat] using finSat)

theorem streamVerify_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamVerify (Proof.Sm4Gcm.streamVerifyScratchContract RISCV64.abi 3248) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
      Spec.Sm4.Gcm.streamVerifyPost, streamVerifyRISCV64, verPre, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true] [verSat] using verSat)

/-- The working space at `0x6000`, the stack argument. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | .a7 => 0x5000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem seal_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target «seal» (Proof.Sm4Gcm.sealScratchContract RISCV64.abi 3248) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.Sm4Gcm.sealScratchContract, Proof.Sm4Gcm.sealScratchSig, Spec.Sm4.Gcm.sealPost,
      sealRISCV64, sealPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag_len` 0 and the working space at `0x6000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | .a7 => 0x5000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9009 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `a0`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target «open» (Proof.Sm4Gcm.openScratchContract RISCV64.abi 3248) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          openRISCV64, openPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openPost,
          RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openRISCV64] at h
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openLeak,
          openRISCV64, openPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 by omega_using [hi]) with rfl | rfl
        · exact a0
        · exact a1
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig, Spec.Sm4.Gcm.openPost,
          openRISCV64, openPre, onePub, args, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk3, stkAll3, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## With the working space on the stack

Each function runs its code, proved with the working space as an argument,
in a frame that allocates it: the functions whose arguments all arrive in
registers in a frame of 2560 bytes, the working space in the next register
(`Verified.stackScratchL`); `seal` and `open`, whose last arguments arrive
on the stack, in a frame that copies them and then passes the working
space's address (`Verified.stackScratchArgs`): `seal`'s first, as its only
stack argument.
-/

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract RISCV64.abi 5808).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a2 init)
      (Spec.Sm4.Gcm.initContract RISCV64.abi 5808) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.initPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 3248) (bytes := 2560) init_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.initPostOut_local _ vs m m₁ m₂ r hl)
    initFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract RISCV64.abi 5808).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost,
    RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat] using streamCryptFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamEncrypt)
      (Spec.Sm4.Gcm.streamEncryptContract RISCV64.abi 5808) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamEncryptPost RISCV64.abi.ptrBits) (wa := true) (stack := 3248)
    (bytes := 2560) streamEncrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamEncryptPostOut_local _ vs m m₁ m₂ r hl)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract RISCV64.abi 5808).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost,
    RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat] using streamCryptFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamDecrypt)
      (Spec.Sm4.Gcm.streamDecryptContract RISCV64.abi 5808) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamDecryptPost RISCV64.abi.ptrBits) (wa := true) (stack := 3248)
    (bytes := 2560) streamDecrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamDecryptPostOut_local _ vs m m₁ m₂ r hl)
    streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract RISCV64.abi 5808).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig,
    Spec.Sm4.Gcm.streamFinishPost, RISCV64.abi, RISCV64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 streamFinish)
      (Spec.Sm4.Gcm.streamFinishContract RISCV64.abi 5808) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamFinishPost RISCV64.abi.ptrBits) (wa := true) (stack := 3248)
    (bytes := 2560) streamFinish_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamFinishPostOut_local _ vs m m₁ m₂ r hl)
    finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract RISCV64.abi 5808).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig,
    Spec.Sm4.Gcm.streamVerifyPost, RISCV64.abi, RISCV64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamVerify)
      (Spec.Sm4.Gcm.streamVerifyContract RISCV64.abi 5808) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Sm4.Gcm.streamVerifyPost RISCV64.abi.ptrBits) (wa := true) (stack := 3248)
    (bytes := 2560) streamVerify_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamVerifyPostOut_local _ vs m m₁ m₂ r hl)
    verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract RISCV64.abi 5824).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose working space is its only stack argument: the frame passes
its address above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2576 0 «seal»)
      (Spec.Sm4.Gcm.sealContract RISCV64.abi 5824) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.sealPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 3248) (bytes := 2576) (m := 0) seal_verified (by decide) (by decide)
    (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.sealPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.sealPostOut_local _ vs m m₁ m₂ r hl)
    sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 8⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract RISCV64.abi 5824).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag_len` arrives on the stack before the working space. -/
theorem open_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 «open»)
      (Spec.Sm4.Gcm.openContract RISCV64.abi 5824) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.openPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 3248) (bytes := 2576) (m := 1)
    (leak := some (Spec.Sm4.Gcm.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.openPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.openPostOut_local _ vs m m₁ m₂ r hl)
    openFrameSat_pre (hleak := Proof.Sm4Gcm.openLeak_local _)

end VG.Proof.Sm4Gcm.RISCV64
