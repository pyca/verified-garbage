module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.OneShot
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! ### `Sm4Gcm.PPC64LE.OneEntry`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on PPC64LE: the entry of `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/OneEntry.lean`): `oneEntry off` loads the working
space `W`, the stack argument at `sp + off`, saves our caller's registers
there and keeps the arguments in nonvolatile registers, the tag's address
(`r10`) in `r20`, and SM4's working space, the stack argument after `W`, in
`r28` (`one1_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Proof.AesGcm.PPC64LE (Keeps Entered SavedAt savedR save_ok SavedAt.congr)

/-- After the entry of `seal` or `open`, from `s₀`. -/
structure SO1 (W X : Addr) (s₀ s₁ : State) : Prop where
  en : Entered s₀ W s₁
  r31 : s₁.gpr .r31 = W
  r30 : s₁.gpr .r30 = W + BitVec.ofNat 64 16
  r29 : s₁.gpr .r29 = s₀.gpr .r3
  r24 : s₁.gpr .r24 = s₀.gpr .r4
  r25 : s₁.gpr .r25 = s₀.gpr .r5
  r18 : s₁.gpr .r18 = s₀.gpr .r5
  r21 : s₁.gpr .r21 = s₀.gpr .r6
  r22 : s₁.gpr .r22 = s₀.gpr .r7
  r27 : s₁.gpr .r27 = s₀.gpr .r8
  r23 : s₁.gpr .r23 = s₀.gpr .r9
  r20 : s₁.gpr .r20 = s₀.gpr .r10
  r28 : s₁.gpr .r28 = X

/-- A doubleword above the stack pointer into `t`, through `r12`. -/
theorem ldSp_ok {s : State} {t : Reg} {off : Nat} {v : BitVec 64} (ho4 : off % 4 = 0)
    (ho15 : off < 2 ^ 15) (hi : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8)
    (hv : s.mem.readW (s.sp + BitVec.ofNat 64 off) 64 = v) :
    WP isa (.block [.addSp .r12 0, .load .d t .r12 off]) s fun s' =>
      s'.gpr t = v ∧ (∀ r, r ≠ .r12 → r ≠ t → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.write, Size.bytes,
    hi, ho4, ho15, Proof.Gcm.PPC64LE.read_8, hv, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true, Nat.reduceLT, Nat.reducePow, ↓reduceIte,
    and_self, implies_true, BitVec.setWidth_eq, BitVec.add_zero]
  exact ⟨by simp, fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The head of the entry: `W`, the stack argument at `sp + off`, into `r12`. -/
theorem oneA_ok {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 96 ∨ off = 104)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block [.addSp .r12 0, .load .d .r12 .r12 off]) s₀ fun sA =>
      sA.gpr .r12 = W ∧ (∀ r, r ≠ .r12 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  have ho4 : off % 4 = 0 := by omega_using [hoff]
  have ho15 : off < 2 ^ 15 := by omega_using [hoff]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.write, Size.bytes,
    hWi, ho4, ho15, Proof.Gcm.PPC64LE.read_8, hWv, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true, Nat.reduceLT, Nat.reducePow, ↓reduceIte,
    and_self, implies_true, BitVec.setWidth_eq, BitVec.add_zero]
  exact ⟨trivial, fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem one1_wp {s₀ : State} {off : Nat} {W X : Addr} (hoff : off = 96 ∨ off = 104)
    (hW : Covers [⟨W, 2560⟩] s₀.wr) (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W)
    (hXi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (off + 8)) 8)
    (hXv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 (off + 8)) 64 = X)
    (hXd : (⟨s₀.sp + BitVec.ofNat 64 (off + 8), 8⟩ : Region).Disjoint (savedR W)) :
    WP isa (.block (oneEntry off)) s₀ (SO1 W X s₀) := by
  simp only [oneEntry]
  rw [show ([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5, mov .r21 .r6,
      mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0, .load .d .r28 .r12 (off + 8)] :
      List Instr) = ([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5, mov .r21 .r6,
      mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10] : List Instr) ++
      ([.addSp .r12 0, .load .d .r28 .r12 (off + 8)] : List Instr) from rfl]
  refine WP.block_append (WP.block_append ?_)
  have hA := oneA_ok hoff hWi hWv
  refine WP.mono hA fun sA ⟨a12, gA, kA⟩ => ?_
  refine WP.mono (save_ok (b := .r12) (by decide) (by rw [a12, kA.wr]; exact hW))
    fun s₂ ⟨hg, h31, hk, hsv, hf⟩ => ?_
  rw [a12] at h31 hsv hf
  have e : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r31 → s₂.gpr r = s₀.gpr r := fun r a b c => by rw [hg r a c, gA r b]
  have e3 := e .r3 (by decide) (by decide) (by decide)
  have e4 := e .r4 (by decide) (by decide) (by decide)
  have e5 := e .r5 (by decide) (by decide) (by decide)
  have e6 := e .r6 (by decide) (by decide) (by decide)
  have e7 := e .r7 (by decide) (by decide) (by decide)
  have e8 := e .r8 (by decide) (by decide) (by decide)
  have e9 := e .r9 (by decide) (by decide) (by decide)
  have e10 := e .r10 (by decide) (by decide) (by decide)
  have hB : WP isa (.block ([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5,
      mov .r18 .r5, mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10] : List Instr)) s₂
      fun s₁ =>
      s₁.gpr .r31 = W ∧ s₁.gpr .r30 = W + BitVec.ofNat 64 16 ∧ s₁.gpr .r29 = s₀.gpr .r3 ∧
      s₁.gpr .r24 = s₀.gpr .r4 ∧ s₁.gpr .r25 = s₀.gpr .r5 ∧
      s₁.gpr .r18 = s₀.gpr .r5 ∧ s₁.gpr .r21 = s₀.gpr .r6 ∧ s₁.gpr .r22 = s₀.gpr .r7 ∧
      s₁.gpr .r27 = s₀.gpr .r8 ∧ s₁.gpr .r23 = s₀.gpr .r9 ∧ s₁.gpr .r20 = s₀.gpr .r10 ∧
      (∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s₁.gpr r = s₂.gpr r) ∧ Keeps s₂ s₁ := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.write, mov, BitVec.or_self, e3, e4, e5,
      e6, e7, e8, e9, e10, h31, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq,
      not_false_eq_true, Nat.reduceLT, Nat.reducePow, ↓reduceIte, and_self]
    and_intros
    all_goals first
      | trivial
      | rfl
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine WP.block_append (WP.mono hB fun s₁ ⟨b31, b30, b29, b24, b25, b18, b21, b22, b27, b23, b20, bl, bk⟩ => ?_)
  have k₁ : VG.Proof.AesGcm.PPC64LE.Keeps' s₀ s₁ := ⟨bk.rd.trans (hk.rd.trans kA.rd),
    bk.wr.trans (hk.wr.trans kA.wr), bk.sp.trans (hk.sp.trans kA.sp), bk.lr.trans (hk.lr.trans kA.lr)⟩
  have hX₁ : s₁.mem.readW (s₁.sp + BitVec.ofNat 64 (off + 8)) 64 = X := by
    rw [k₁.sp, bk.mem, Frame.readW hf (r := ⟨s₀.sp + BitVec.ofNat 64 (off + 8), 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hXd) (by decide), kA.mem]
    exact hXv
  refine WP.mono (ldSp_ok (t := .r28) (off := off + 8) (by omega_using [hoff]) (by omega_using [hoff])
    (by rw [k₁.sp, k₁.rd, k₁.wr]; exact hXi) hX₁) fun s₃ ⟨c28, g₃, k₃⟩ => ?_
  have q : ∀ r, r ≠ .r12 → r ≠ .r28 → s₃.gpr r = s₁.gpr r := g₃
  refine ⟨⟨fun r hr => ?_, ⟨k₃.rd.trans k₁.rd, k₃.wr.trans k₁.wr, k₃.sp.trans k₁.sp, k₃.lr.trans k₁.lr⟩, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c28⟩
  · rw [q r (by revert hr; revert r; decide) (by revert hr; revert r; decide), bl r hr]
    exact e r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  · rw [k₃.mem, bk.mem]
    exact hsv.congr (fun p hp => (gA p.1 (by revert hp; revert p; decide)).symm) kA.lr.symm
  · rw [k₃.mem, bk.mem, ← kA.mem]; exact hf
  · rw [q _ (by decide) (by decide)]; exact b31
  · rw [q _ (by decide) (by decide)]; exact b30
  · rw [q _ (by decide) (by decide)]; exact b29
  · rw [q _ (by decide) (by decide)]; exact b24
  · rw [q _ (by decide) (by decide)]; exact b25
  · rw [q _ (by decide) (by decide)]; exact b18
  · rw [q _ (by decide) (by decide)]; exact b21
  · rw [q _ (by decide) (by decide)]; exact b22
  · rw [q _ (by decide) (by decide)]; exact b27
  · rw [q _ (by decide) (by decide)]; exact b23
  · rw [q _ (by decide) (by decide)]; exact b20

/-- After a step that changes no register the entry set but `r12`, `r19` (and `r0`). -/
theorem SO1.keep {W X : Addr} {s₀ s₁ s₂ : State} (h1 : SO1 W X s₀ s₁)
    (hg : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r19 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 W X s₀ s₂ :=
  ⟨⟨fun r hr => by
      rw [hg r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)]
      exact h1.en.low r hr,
    ⟨hk.rd.trans h1.en.keeps.rd, hk.wr.trans h1.en.keeps.wr, hk.sp.trans h1.en.keeps.sp,
      hk.lr.trans h1.en.keeps.lr⟩, hk.mem ▸ h1.en.saved, hk.mem ▸ h1.en.frame⟩,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r31,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r30,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r29,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r24,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r25,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r18,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r21,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r22,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r27,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r23,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r20,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.r28⟩

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/Seal.lean`), with SM4's counter mode, which uses the
working space past AES-GCM's 2560 bytes: the entry, `oneAad`, `oneCrypt`,
`oneTag 0` and the tag copied out to `tag` (`seal_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Proof.AesGcm.PPC64LE (Env Lay Perm DataW DataOk SavedAt savedR restore_ok covers_mem covers_left
  covers_off covers_prefix bytesAt_frame blockAt_frame ctx_saved ctxH_keep saved_w Lay.saved_st WP.with_rdwr
  tagOut_ok saved_j0Frame data_j0 oneAad_ok oneLay args_in j0Frame length_bytesAt add_ofNat_assoc)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed)

/-- After the entry, the environment. -/
theorem one_env {s₀ s₁ : State} {W X : Addr} (h1 : SO1 W X s₀ s₁)
    (hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr) :
    Env s₁.gpr s₀.sp s₁ := by
  obtain perm : Perm (s₀.gpr .r3) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .r3) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

/-- SM4's working space, apart from the context and `W`, with the state at `W + 16`. -/
theorem oneX {c W X : Addr} (fx : X.toNat + xBytes ≤ 2 ^ 64) (dcx : (⟨c, 256⟩ : Region).Disjoint ⟨X, xBytes⟩)
    (dwx : (⟨W, scrBytes⟩ : Region).Disjoint ⟨X, xBytes⟩) : XOk c (W + BitVec.ofNat 64 16) W X :=
  ⟨fx, dcx, dwx.sub_left (VG.Offset.sub_base _ (by decide)), dwx⟩

section
variable {c st w x : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem saved_otFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ otFrame st w x o, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 48) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega_using [ho]) (.inl (by omega_using [ho]))
  · exact saved_w (by decide) (.inr (by decide))
  · exact X.wx.sub_left (Lay.wSub (by decide))

end

theorem seal_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : sealPPC64LE.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealPPC64LE.post s₀ s' := by
  have h' : sealPre s₀ := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, -, fW, fsp, dcx, -,
    -, ddx, -, dwx, -, fx⟩ := h'
  obtain L₀ := oneLay fc fW dcW
  obtain X₀ := oneX fx dcx dwx
  obtain hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hW : Covers [⟨stackArg s₀ 0, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hXw : Covers [xR (stackArg s₀ 1)] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hXd : (⟨s₀.sp + BitVec.ofNat 64 (96 + 8), 8⟩ : Region).Disjoint (savedR (stackArg s₀ 0)) := by
    obtain hs := VG.Offset.sub_base (s₀.sp + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide)
    rw [add_ofNat_assoc] at hs
    exact ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm).sub_left hs
  refine WP.seq (WP.mono (one1_wp (off := 96) (W := stackArg s₀ 0) (X := stackArg s₀ 1) (.inl rfl) hW
    (args_in hA (by decide) (i := 0) (by decide)) rfl (args_in hA (by decide) (i := 1) (by decide)) rfl hXd)
    fun s₁ h1 => ?_)
  obtain he₁ := one_env h1 hC hW
  obtain L := L₀.v h1.r29 h1.r30 h1.r31
  obtain X : XOk (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) (s₁.gpr .r28) := by
    rw [h1.r29, h1.r30, h1.r31, h1.r28]; exact X₀
  have f₁ := h1.en.frame
  have hk₁ := h1.en.keeps
  -- `oneAad`
  obtain hH₁ : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
    rw [h1.r29]; exact ctxH_keep f₁ (ctx_saved L₀)
  obtain hN : DataOk (s₁.gpr .r30) (s₁.gpr .r31) s₁ (s₀.gpr .r4) (s₀.gpr .r5).toNat := by
    rw [h1.r30, h1.r31]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .r5).isLt,
      fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  obtain hAd : DataOk (s₁.gpr .r30) (s₁.gpr .r31) s₁ (s₁.gpr .r21) (s₁.gpr .r22).toNat := by
    rw [h1.r30, h1.r31, h1.r21, h1.r22]
    exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)), (s₀.gpr .r7).isLt,
      fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₁ hH₁ h1.r24 (by rw [h1.r25]; exact toN)
    (by rw [h1.r18]; exact toN) hN hAd)) fun s₂ ⟨oa, rd₂, wr₂, _⟩ => ?_)
  -- `oneCrypt`
  obtain hd₂ : DataW (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) s₂ (s₁.gpr .r27) (s₁.gpr .r23).toNat := by
    rw [h1.r29, h1.r30, h1.r31, h1.r27, h1.r23]
    obtain hDw : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] s₂.wr := by
      rw [wr₂, hk₁.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hDw, (s₀.gpr .r9).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw, dcd⟩
  obtain hxw₂ : Covers [xR (s₁.gpr .r28)] s₂.wr := by rw [wr₂, hk₁.wr, h1.r28]; exact hXw
  obtain hdx : (⟨s₁.gpr .r27, (s₁.gpr .r23).toNat⟩ : Region).Disjoint (xR (s₁.gpr .r28)) := by
    rw [h1.r27, h1.r23, h1.r28]; exact ddx
  refine WP.seq (WP.mono (WP.with_rdwr (oneCrypt_ok L X oa.env hd₂ hxw₂ hdx oa.cb))
    fun s₃ ⟨oc, rd₃, wr₃, _⟩ => ?_)
  -- `oneTag 0`
  obtain hH₃ : blockAt s₃.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
    rw [blockAt_frame oc.frame (fun r hr => (ctx_crFrame L X hd₂ r hr).sub_left (Lay.ctxSub (by decide)))]
    exact oa.hH
  obtain hb := Nat.mod_lt (bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat ++
    zeros (padLen (bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat).length)).length (show 16 > 0 by decide)
  obtain hab₃ := oa.abs.congr (blockAt_frame oc.frame (stp_crFrame X hd₂ (by decide)))
    (bytesAt_frame oc.frame (stp_crFrame X hd₂ (by omega_using [])) (by omega_using []))
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L X (o := 0) (.inl rfl) oc.env (by rw [wr₃]; exact hxw₂) hH₃
    (length_bytesAt _ _ _).symm hab₃ (hd₂.ok.of_eq rd₃ wr₃))) fun s₄ ⟨ot, rd₄, wr₄, _⟩ => ?_)
  -- the tag copied out
  obtain hTw : Covers [⟨s₁.gpr .r20, 16⟩] s₄.wr := by
    rw [wr₄, wr₃, wr₂, hk₁.wr, h1.r20, hwr]; exact covers_mem (by simp)
  obtain hTd' : (⟨s₁.gpr .r20, 16⟩ : Region).Disjoint ⟨s₁.gpr .r31, 16⟩ := by
    rw [h1.r20, h1.r31]; exact dtW.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (tagOut_ok ot.env hTw hTd') fun s₅ ⟨hb₅, hf₅, g₅, k₅⟩ => ?_)
  obtain he₅ := ot.env.keep (fun r hr => g₅ r (by revert r; decide)) k₅.sp k₅.rd k₅.wr
  have of₄ := ot.frame
  rw [h1.r30, h1.r31, h1.r28] at of₄
  have cf₃ := oc.frame
  rw [h1.r30, h1.r28, h1.r27, h1.r23] at cf₃
  have jf₂ := oa.frame
  rw [h1.r30, h1.r31] at jf₂
  obtain hd₂₀ : DataW (s₀.gpr .r3) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₂ (s₀.gpr .r8)
      (s₀.gpr .r9).toNat := by rw [← h1.r29, ← h1.r30, ← h1.r31, ← h1.r27, ← h1.r23]; exact hd₂
  obtain sv₅ : SavedAt s₅.mem (stackArg s₀ 0) s₀ :=
    (((h1.en.saved.frame jf₂ (saved_j0Frame L₀)).frame cf₃ (saved_crFrame L₀ X₀ hd₂₀)).frame of₄
      (saved_otFrame L₀ X₀ (.inl rfl))).frame (by rw [h1.r20] at hf₅; exact hf₅) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dtW.sub_right (Lay.wSub (by decide))).symm)
  obtain e31 : s₅.gpr .r31 = stackArg s₀ 0 := (he₅.fr _ (by decide)).trans h1.r31
  refine WP.mono (restore_ok e31 (by have := he₅.perm.w; rw [h1.r31] at this; exact Covers.right this) sv₅
    he₅.sp (fun r hr => by rw [he₅.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  -- the results
  obtain f₂ : Frame (savedR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0))
      s₀.mem s₂.mem :=
    (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      (jf₂.mono fun r hr => List.mem_cons_of_mem _ hr)
  obtain dc₂ : ∀ r ∈ savedR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0),
      (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dcW.sub_right (Lay.wSub (by decide))
    · simp only [j0Frame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L₀.cs
      · exact dcW.sub_right (Lay.wSub (by decide))
      · exact dcW.sub_right (Lay.wSub (by decide))
  obtain dD : ∀ r ∈ savedR (stackArg s₀ 0) :: j0Frame (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0),
      (⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact data_j0 hd₂₀.ok r hr
  obtain hc₂ := ciph_keep f₂ dc₂
  obtain hc₃ : ciphOf s₃.mem (s₀.gpr .r3) = ctxCiph s₀.mem (s₀.gpr .r3) := by
    rw [ciph_frame cf₃ (ctx_crFrame' L₀ X₀ hd₂₀), hc₂]
  obtain hD₂ : bytesAt s₂.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat :=
    bytesAt_frame f₂ dD (by have := (s₀.gpr .r9).isLt; omega_using [])
  obtain hiv : bytesAt s₁.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat = bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .r5).isLt; omega_using [])
  obtain haad : bytesAt s₁.mem (s₁.gpr .r21) (s₁.gpr .r22).toNat = bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat := by
    rw [h1.r21, h1.r22]
    exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide)))
      (by have := (s₀.gpr .r7).isLt; omega_using [])
  obtain hj₃ : blockAt s₃.mem (stackArg s₀ 0 + BitVec.ofNat 64 16) =
      j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat) := by
    rw [blockAt_frame cf₃ (by simpa using stp_crFrame X₀ hd₂₀ (d := 0) (k := 16) (by decide)), ← hiv, ← h1.r30]
    exact oa.j
  obtain hD₃ : bytesAt s₃.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .r3))
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat)))
        (bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat) := by
    have := oc.out
    rw [h1.r27, h1.r23, h1.r29, hc₂, hD₂, hiv] at this
    exact this
  obtain hD₄ : bytesAt s₄.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₃.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat := by
    refine bytesAt_frame of₄ (fun r hr => ?_) (by have := (s₀.gpr .r9).isLt; omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddW.sub_right (Lay.wSub (by decide))
    · exact ddx
  obtain hD₅ : bytesAt s₅.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₄.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h1.r20]; exact ddt)
      (by have := (s₀.gpr .r9).isLt; omega_using [])
  have ho := ot.out
  rw [h1.r29, h1.r30, h1.r27, h1.r23, h1.r31, hc₃, hj₃, haad, BitVec.add_zero, ← Proof.Gcm.fullTag_eq] at ho
  rw [h1.r31, h1.r20] at hb₅
  simp only [sealPPC64LE, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Proof.Cmac.toBytes_length])

end VG.Proof.Sm4Gcm.PPC64LE
