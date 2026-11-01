module

-- separate module: its proofs (about 2 s) build in parallel with those of `Hash` and `Body`, which `Seal` also imports

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn

/-!
# AES-OCB on RISC-V: the entry (`entry`)

Untrusted: everything here is checked by Lean. `entry` is AES-GCM's
(`Proof.AesGcm.RISCV64.one1_wp`: our caller's registers and return address
saved in `W`, the arguments in their registers, the addresses of the
associated data and the data in their slots in `W`), `tag_len` loaded into
`s8`, then `L_$ = double(L_*)`, `L_0 = double(L_$)` and the checksum zeroed
(`entry_ok`). The environment after it is the state's own registers
(`EntryPost.env`). As on PPC64LE (`Proof/AesOcb/PPC64LE/Entry.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxLstar lDollar lAt)
open VG.Proof.AesGcm.RISCV64 (SO1 SavedAt savedR oneR one1_wp Keeps Keeps' in_left in_off add_ofNat_assoc)
open VG.Proof.Ocb (blockAtMem_frame)

/-- What `entry` leaves, from `s₀`, with `W` and the tag's address `T`. -/
structure EntryPost (W T : Addr) (s₀ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  s0 : s.gpr .s0 = W
  s2 : s.gpr .s2 = s₀.gpr .a0
  s3 : s.gpr .s3 = s₀.gpr .a1
  s4 : s.gpr .s4 = s₀.gpr .a2
  s5 : s.gpr .s5 = s₀.gpr .a3
  s7 : s.gpr .s7 = s₀.gpr .a3
  s10 : s.gpr .s10 = s₀.gpr .a5
  s11 : s.gpr .s11 = s₀.gpr .a7
  s9 : s.gpr .s9 = T
  s8 : s.gpr .s8 = stackArg s₀ 1
  slots : Slots W (s₀.gpr .a4) (s₀.gpr .a6) s.mem
  keeps : Keeps' s₀ s
  saved : SavedAt s.mem W s₀
  ld : blockAtMem s.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s₀.mem (s₀.gpr .a0))
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem (s₀.gpr .a0)) 0
  ck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [oneR W, ⟨W + BitVec.ofNat 64 32, 64⟩] s₀.mem s.mem

/-- A stack argument's doubleword is readable. -/
theorem stk_in {s : State} (h : Covers [⟨stackArgAddr s 0, 24⟩] (s.rd ++ s.wr)) {i : Nat} (hi : i < 3) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8 := by
  have := in_off h (d := 8 * i) (n := 8) (by omega) (by decide)
  rwa [stackArgAddr, add_ofNat_assoc, Nat.zero_add] at this

/-- `entry`. -/
theorem entry_ok {s₀ : State} {W T : Addr} (L : Lay (s₀.gpr .a0) W) (hW : Covers [⟨W, 2560⟩] s₀.wr)
    (hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)) (hsa : s₀.sp.toNat % 16 = 0)
    (hWv : stackArg s₀ 2 = W) (hTv : stackArg s₀ 0 = T)
    (hA : Covers [⟨stackArgAddr s₀ 0, 24⟩] (s₀.rd ++ s₀.wr))
    (hAW : (⟨stackArgAddr s₀ 0, 24⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.block entry) s₀ (EntryPost W T s₀) := by
  have dA : (⟨stackArgAddr s₀ 0, 24⟩ : Region).Disjoint (oneR W) := hAW.sub_right (Lay.wSub (by decide))
  have dAi : ∀ {i : Nat}, i < 3 → (⟨s₀.sp + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (oneR W) :=
    fun {i} hi => by
      have hs := Offset.sub_base (stackArgAddr s₀ 0) (d := 8 * i) (n := 8) (k := 24) (by omega)
      rw [stackArgAddr, add_ofNat_assoc, Nat.zero_add] at hs
      exact dA.sub_left hs
  simp only [entry, Impl.AesGcm.RISCV64.openEntry, lsetup, List.append_assoc]
  refine WP.block_append (WP.mono (one1_wp (off := 16) (W := W) (T := T) (.inr rfl) hW L.wal hsa
    (stk_in hA (i := 2) (by decide)) (by rw [← hWv]; rfl) (stk_in hA (i := 0) (by decide))
    (by rw [← hTv]; rfl) (dAi (i := 0) (by decide))) fun s₁ h1 => ?_)
  have k₁ := h1.keeps
  have hv : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 8) 64 = stackArg s₀ 1 := by
    rw [Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 (8 * 1), 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAi (by decide)) (by decide)]
    rfl
  refine WP.block_append (Steps.wp_ld (off := 8) (a := s₀.sp + BitVec.ofNat 64 8) (by decide) (by rw [h1.t1])
    (Spill.al8 (by omega) (by decide)) (by rw [k₁.rd, k₁.wr]; exact stk_in hA (i := 1) (by decide))
    fun s₂ u₂ => WP.block_nil ?_)
  have e : ∀ r, r ≠ .s8 → s₂.gpr r = s₁.gpr r := u₂.other
  have h0₂ : s₂.gpr .s0 = W := by rw [e _ (by decide), h1.s0]
  have h2₂ : s₂.gpr .s2 = s₀.gpr .a0 := by rw [e _ (by decide), h1.s2]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, k₁.wr]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, k₁.rd]
  have hw₂ : Covers [⟨W, 2560⟩] s₂.wr := by rw [wr₂]; exact hW
  have hc₂ : Covers [⟨s₀.gpr .a0, 256⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂]; exact hC
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  -- `L_$`
  refine WP.block_append (WP.mono (dbl_ok (s := s₂) (b := .s2) (a := 240) (d := ldO) (by decide) (by decide)
    h0₂ h2₂ (by decide) (in_off hc₂ (by decide) (by decide)) (in_off hc₂ (by decide) (by decide))
    (in_off hw₂ (by decide) (by decide)) (in_off hw₂ (by decide) (by decide))) fun s₃ B₃ => ?_)
  have h0₃ : s₃.gpr .s0 = W := by rw [B₃.gpr _ (by decide), h0₂]
  have hw₃ : Covers [⟨W, 2560⟩] s₃.wr := by rw [B₃.wr]; exact hw₂
  -- `L_0`
  refine WP.block_append (WP.mono (dbl_ok (s := s₃) (b := .s0) (a := ldO) (d := l0O) (by decide) (by decide)
    h0₃ h0₃ (by decide) (in_left (in_off hw₃ (by decide) (by decide))) (in_left (in_off hw₃ (by decide) (by decide)))
    (in_off hw₃ (by decide) (by decide)) (in_off hw₃ (by decide) (by decide))) fun s₄ B₄ => ?_)
  have h0₄ : s₄.gpr .s0 = W := by rw [B₄.gpr _ (by decide), h0₃]
  have hw₄ : Covers [⟨W, 2560⟩] s₄.wr := by rw [B₄.wr]; exact hw₃
  -- the checksum
  refine WP.mono (zero16_ok (s := s₄) (d := ckO) L.wal (by decide) h0₄ (in_off hw₄ (by decide) (by decide))
    (in_off hw₄ (by decide) (by decide))) fun s₅ B₅ => ?_
  have g₅ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .s8 → s₅.gpr r = s₁.gpr r :=
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
  have dOW : (oneR W).Disjoint ⟨W + BitVec.ofNat 64 32, 64⟩ := L.w_w (.inr (by decide)) (by decide) (by decide)
  have lst : blockAtMem s₂.mem (s₀.gpr .a0 + BitVec.ofNat 64 240) = ctxLstar s₀.mem (s₀.gpr .a0) := by
    rw [m₂, blockAtMem_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (W := W) (d := 128) (n := 120)
        (by decide)))]
    rfl
  have perm : Perm (s₀.gpr .a0) W s₅ := (⟨hC, hW⟩ : Perm (s₀.gpr .a0) W s₀).of_eq rd₅ wr₅
  have gg : ∀ r, r ∈ [Reg.s0, .s2, .s3, .s4, .s5, .s7, .s9, .s10, .s11] → s₅.gpr r = s₁.gpr r := fun r hr =>
    g₅ r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  have m₅r : ∀ d, 128 ≤ d → d + 8 ≤ 248 →
      s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [← m₂]
    exact frW.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
  refine
    { env := ⟨fun _ _ => rfl, by rw [B₅.sp, B₄.sp, B₃.sp, u₂.sp, k₁.sp], by
        rw [gg _ (by decide), h1.s2, gg _ (by decide), h1.s0]; exact perm⟩
      s0 := by rw [gg _ (by decide), h1.s0]
      s2 := by rw [gg _ (by decide), h1.s2]
      s3 := by rw [gg _ (by decide), h1.s3]
      s4 := by rw [gg _ (by decide), h1.s4]
      s5 := by rw [gg _ (by decide), h1.s5]
      s7 := by rw [gg _ (by decide), h1.s7]
      s10 := by rw [gg _ (by decide), h1.s10]
      s11 := by rw [gg _ (by decide), h1.s11]
      s9 := by rw [gg _ (by decide), h1.s9]
      s8 := by rw [B₅.gpr _ (by decide), B₄.gpr _ (by decide), B₃.gpr _ (by decide), u₂.gpr, hv]
      slots := ⟨by rw [m₅r 232 (by decide) (by decide)]; exact h1.aad,
        by rw [m₅r 240 (by decide) (by decide)]; exact h1.dat⟩
      keeps := ⟨rd₅, wr₅, by rw [B₅.sp, B₄.sp, B₃.sp, u₂.sp, k₁.sp]⟩
      saved := by
        have sv := h1.saved
        rw [← m₂] at sv
        exact sv.frame frW fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact L.w_w (.inr (by decide)) (by decide) (by decide)
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
        have f := h1.frame
        rw [← m₂] at f
        exact (f.mono (by simp)).trans (frW.mono (by simp)) }

end VG.Proof.AesOcb.RISCV64
