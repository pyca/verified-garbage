module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Env
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn

/-!
# AES-OCB on PPC64LE: the entry (`entry`)

Untrusted: everything here is checked by Lean. `entry` is AES-GCM's
(`Proof.AesGcm.PPC64LE.one1_wp`: our caller's registers and return address
saved in `W`, the arguments in their registers, `tag_len` in `r19`), then
`L_$ = double(L_*)`, `L_0 = double(L_$)` and the checksum zeroed
(`entry_ok`). The environment after it is the state's own registers
(`EntryPost.env`), as AES-GCM's (`Proof.AesGcm.PPC64LE.one_env`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxLstar lDollar lAt)
open VG.Proof.AesGcm.PPC64LE (SO1 SavedAt savedR one1_wp ld_ok Keeps Keeps' in_left in_off)
open VG.Proof.Ocb (blockAtMem_frame)

/-- What `entry` leaves, from `s₀`, with `W` and the tag's address `T`. -/
structure EntryPost (W T : Addr) (s₀ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  r31 : s.gpr .r31 = W
  r29 : s.gpr .r29 = s₀.gpr .r3
  r28 : s.gpr .r28 = s₀.gpr .r4
  r24 : s.gpr .r24 = s₀.gpr .r5
  r25 : s.gpr .r25 = s₀.gpr .r6
  r18 : s.gpr .r18 = s₀.gpr .r6
  r21 : s.gpr .r21 = s₀.gpr .r7
  r22 : s.gpr .r22 = s₀.gpr .r8
  r27 : s.gpr .r27 = s₀.gpr .r9
  r23 : s.gpr .r23 = s₀.gpr .r10
  r20 : s.gpr .r20 = T
  r19 : s.gpr .r19 = stackArg s₀ 1
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  keeps : Keeps' s₀ s
  saved : SavedAt s.mem W s₀
  ld : blockAtMem s.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s₀.mem (s₀.gpr .r3))
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem (s₀.gpr .r3)) 0
  ck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [savedR W, ⟨W + BitVec.ofNat 64 32, 64⟩] s₀.mem s.mem

theorem stackArg_eq' (s : State) (i : Nat) :
    stackArg s i = s.mem.readW (s.sp + BitVec.ofNat 64 (96 + 8 * i)) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 = _
  rw [show 32 + 8 * (8 + i) = 96 + 8 * i by omega]

/-- `entry`. -/
theorem entry_ok {s₀ : State} {W T : Addr} (L : Lay (s₀.gpr .r3) W) (hW : Covers [⟨W, 2560⟩] s₀.wr)
    (hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr)) (hWv : stackArg s₀ 2 = W) (hTv : stackArg s₀ 0 = T)
    (hA : Covers [⟨s₀.sp + BitVec.ofNat 64 96, 24⟩] (s₀.rd ++ s₀.wr))
    (hAW : (⟨s₀.sp + BitVec.ofNat 64 96, 24⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.block entry) s₀ (EntryPost W T s₀) := by
  have hAi : ∀ {i : Nat}, i < 3 → InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (96 + 8 * i)) 8 :=
    fun {i} hi => by
      have := in_off hA (d := 8 * i) (n := 8) (by omega) (by decide)
      rwa [Proof.AesGcm.PPC64LE.add_ofNat_assoc] at this
  have hAs : ∀ {i : Nat}, i < 3 → (⟨s₀.sp + BitVec.ofNat 64 (96 + 8 * i), 8⟩ : Region).Disjoint (savedR W) :=
    fun {i} hi => by
      have := (hAW.sub_left (Offset.sub_base _ (d := 8 * i) (n := 8) (k := 24) (by omega))).sub_right
        (Lay.wSub (W := W) (d := 128) (n := 120) (by decide))
      rwa [Proof.AesGcm.PPC64LE.add_ofNat_assoc] at this
  simp only [entry, Impl.AesGcm.PPC64LE.openEntry, lsetup, List.append_assoc]
  refine WP.block_append (WP.mono (one1_wp (off := 112) (W := W) (T := T) (.inr rfl) hW (hAi (i := 2) (by decide))
    (by rw [← hWv, stackArg_eq']) (hAi (i := 0) (by decide)) (by rw [← hTv, stackArg_eq'])
    (hAs (i := 0) (by decide))) fun s₁ h1 => ?_)
  have k₁ := h1.en.keeps
  have hv : s₁.mem.readW (s₁.gpr .r12 + BitVec.ofNat 64 104) 64 = stackArg s₀ 1 := by
    rw [h1.r12, stackArg_eq', h1.en.frame.readW (r := ⟨s₀.sp + BitVec.ofNat 64 (96 + 8 * 1), 8⟩)
      (Region.contains_self _ _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hAs (by decide))
      (by decide)]
  refine WP.block_append (WP.mono (ld_ok (t := .r19) (b := .r12) (off := 104) (by decide) (by decide) (by decide)
    (by rw [h1.r12, k₁.rd, k₁.wr]; exact hAi (i := 1) (by decide)) hv) fun s₂ ⟨r19₂, g₂, k₂⟩ => ?_)
  have e : ∀ r, r ≠ .r19 → s₂.gpr r = s₁.gpr r := g₂
  have h31₂ : s₂.gpr .r31 = W := by rw [e _ (by decide), h1.r31]
  have h29₂ : s₂.gpr .r29 = s₀.gpr .r3 := by rw [e _ (by decide), h1.r29]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, k₁.wr]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, k₁.rd]
  have hw₂ : Covers [⟨W, 2560⟩] s₂.wr := by rw [wr₂]; exact hW
  have hc₂ : Covers [⟨s₀.gpr .r3, 256⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂]; exact hC
  have m₂ : s₂.mem = s₁.mem := k₂.mem
  -- `L_$`
  refine WP.block_append (WP.mono (dbl_ok (s := s₂) (b := .r29) (a := 240) (d := ldO) (by decide) (by decide)
    h31₂ h29₂ (by decide) (in_off hc₂ (by decide) (by decide)) (in_off hc₂ (by decide) (by decide))
    (in_off hw₂ (by decide) (by decide)) (in_off hw₂ (by decide) (by decide))) fun s₃ B₃ => ?_)
  have h31₃ : s₃.gpr .r31 = W := by rw [B₃.gpr _ (by decide), h31₂]
  have hw₃ : Covers [⟨W, 2560⟩] s₃.wr := by rw [B₃.wr]; exact hw₂
  -- `L_0`
  refine WP.block_append (WP.mono (dbl_ok (s := s₃) (b := .r31) (a := ldO) (d := l0O) (by decide) (by decide)
    h31₃ h31₃ (by decide) (in_left (in_off hw₃ (by decide) (by decide))) (in_left (in_off hw₃ (by decide) (by decide)))
    (in_off hw₃ (by decide) (by decide)) (in_off hw₃ (by decide) (by decide))) fun s₄ B₄ => ?_)
  have h31₄ : s₄.gpr .r31 = W := by rw [B₄.gpr _ (by decide), h31₃]
  have hw₄ : Covers [⟨W, 2560⟩] s₄.wr := by rw [B₄.wr]; exact hw₃
  -- the checksum
  refine WP.mono (zero16_ok (s := s₄) (d := ckO) (by decide) h31₄ (in_off hw₄ (by decide) (by decide))
    (in_off hw₄ (by decide) (by decide))) fun s₅ B₅ => ?_
  have g₅ : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r19 → s₅.gpr r = s₁.gpr r :=
    fun r a b c d f g => by
      rw [B₅.gpr r (by simp [a]), B₄.gpr r (by simp [a, b, c, d, f]), B₃.gpr r (by simp [a, b, c, d, f]), e r g]
  have rd₅ : s₅.rd = s₀.rd := by rw [B₅.rd, B₄.rd, B₃.rd, rd₂]
  have wr₅ : s₅.wr = s₀.wr := by rw [B₅.wr, B₄.wr, B₃.wr, wr₂]
  have frW : Frame [⟨W + BitVec.ofNat 64 32, 64⟩] s₂.mem s₅.mem :=
    ((B₃.frame.sub fun r hr => ?_).trans (B₄.frame.sub fun r hr => ?_)).trans (B₅.frame.sub fun r hr => ?_)
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  have lst : blockAtMem s₂.mem (s₀.gpr .r3 + BitVec.ofNat 64 240) = ctxLstar s₀.mem (s₀.gpr .r3) := by
    rw [m₂, blockAtMem_frame h1.en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (W := W) (d := 128) (n := 120)
        (by decide)))]
    rfl
  have perm : Perm (s₀.gpr .r3) W s₅ := (⟨hC, hW⟩ : Perm (s₀.gpr .r3) W s₀).of_eq rd₅ wr₅
  refine
    { env := ⟨fun _ _ => rfl, by rw [B₅.sp, B₄.sp, B₃.sp, k₂.sp, k₁.sp], by
        rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r29,
          g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r31]; exact perm⟩
      r31 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r31]
      r29 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r29]
      r28 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r28]
      r24 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r24]
      r25 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r25]
      r18 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r18]
      r21 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r21]
      r22 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r22]
      r27 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r27]
      r23 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r23]
      r20 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r20]
      r19 := by rw [B₅.gpr _ (by decide), B₄.gpr _ (by decide), B₃.gpr _ (by decide), r19₂]
      low := fun r hr => by
        rw [g₅ r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
          (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)]
        exact h1.en.low r hr
      keeps := ⟨rd₅, wr₅, by rw [B₅.sp, B₄.sp, B₃.sp, k₂.sp, k₁.sp], by rw [B₅.lr, B₄.lr, B₃.lr, k₂.lr, k₁.lr]⟩
      saved := by
        have sv := h1.en.saved
        rw [← m₂] at sv
        exact sv.frame frW fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Proof.AesGcm.PPC64LE.saved_w (by decide) (.inl (by decide))
      ld := by
        rw [blockAtMem_frame B₅.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
          B₃.val, lst]
        rfl
      l0 := by
        rw [blockAtMem_frame B₅.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          B₄.val, B₃.val, lst]
        rfl
      ck := B₅.val
      frame := by
        have f := h1.en.frame
        rw [← m₂] at f
        exact (f.mono (by simp)).trans (frW.mono (by simp)) }

end VG.Proof.AesOcb.PPC64LE
