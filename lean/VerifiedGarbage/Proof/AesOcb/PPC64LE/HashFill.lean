module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Env
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.AesOcb.PPC64LE.LNtz
import VerifiedGarbage.Proof.AesOcb.PPC64LE.PadTo
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on PPC64LE: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xorB_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`). As on AArch64
(`Proof/AesOcb/AArch64/HashFill.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (in_left in_off)
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r11, .r12, .r24, .r25, .r26]

/-- What one `hashFill` leaves. -/
structure FillPost (W A : Addr) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
    blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  r24 : t'.gpr .r24 = A + BitVec.ofNat 64 (16 * (j + i + 1))
  r26 : t'.gpr .r26 = BitVec.ofNat 64 (j + i + 2)
  r11 : t'.gpr .r11 = W + BitVec.ofNat 64 (384 + 16 * (i + 1))
  r25 : t'.gpr .r25 = BitVec.ofNat 64 (c - (i + 1))
  gpr : ∀ r, r ∉ fillRegs → t'.gpr r = t.gpr r
  sp : t'.sp = t.sp
  lr : t'.lr = t.lr
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {K W : Addr} (L : Lay K W) {t : State} (h31 : t.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {A : Addr} {l : Block} {j i c : Nat} (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 61)
    (h26 : t.gpr .r26 = BitVec.ofNat 64 (j + i + 1)) (h24 : t.gpr .r24 = A + BitVec.ofNat 64 (16 * (j + i)))
    (h11 : t.gpr .r11 = W + BitVec.ofNat 64 (384 + 16 * i)) (h25 : t.gpr .r25 = BitVec.ofNat 64 (c - i))
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr))
    (hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa hashFill t (FillPost W A l j i c t) := by
  unfold hashFill xorW
  rw [List.append_assoc]
  refine WP.seq (WP.mono (lNtz_ok (i := j + i + 1) h31 hw (by omega) (by omega) h26 hl0) fun t₁ P₁ => ?_)
  have h31₁ : t₁.gpr .r31 = W := by rw [P₁.gpr _ (by decide), h31]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [P₁.wr]; exact in_off hw h (by decide)
  refine WP.block_append (WP.mono (xorB_ok (s := t₁) (pd := ohO) (qd := lO) (cd := ohO) (by decide) (by decide)
    (by decide) h31₁ h31₁ h31₁ (by decide) (by decide) (by decide) (in_left (ww (by decide)))
    (in_left (ww (by decide))) (in_left (ww (by decide))) (in_left (ww (by decide))) (ww (by decide))
    (ww (by decide)) (Offset.sep W (by decide) (by decide) (by decide))
    (Offset.sep W (by decide) (by decide) (by decide))) fun t₂ B₂ => ?_)
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [B₂.val, P₁.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  have g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])),
      P₁.gpr r hr]
  have h24₂ : t₂.gpr .r24 = A + BitVec.ofNat 64 (16 * (j + i)) := by rw [g₂ _ (by decide), h24]
  have h11₂ : t₂.gpr .r11 = W + BitVec.ofNat 64 (384 + 16 * i) := by rw [g₂ _ (by decide), h11]
  have h31₂ : t₂.gpr .r31 = W := by rw [g₂ _ (by decide), h31]
  have h26₂ : t₂.gpr .r26 = BitVec.ofNat 64 (j + i + 1) := by rw [g₂ _ (by decide), h26]
  have h25₂ : t₂.gpr .r25 = BitVec.ofNat 64 (c - i) := by rw [g₂ _ (by decide), h25]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have eA : blockAtMem t₂.mem (A + BitVec.ofNat 64 (16 * (j + i))) =
      blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) :=
    blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hAW.sub_right (Lay.wSub (by decide))
  have hb : 384 + 16 * i + 16 ≤ 2560 := by omega
  have dS : (⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩ : Region).Disjoint ⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ :=
    (hAW.sub_right (Lay.wSub hb)).symm
  have hS0 : W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * i) :=
    BitVec.add_zero _
  refine WP.block_append (WP.mono (xorB_ok (s := t₂) (P := A + BitVec.ofNat 64 (16 * (j + i))) (Q := W)
    (C := W + BitVec.ofNat 64 (384 + 16 * i)) (pd := 0) (qd := ohO) (cd := 0) (by decide) (by decide)
    (by decide) h24₂ h31₂ h11₂ (by decide) (by decide) (by decide)
    (by rw [rd₂, wr₂]; simpa using in_off (d := 0) (n := 8) hA (by decide) (by decide))
    (by rw [rd₂, wr₂]; exact in_off (d := 8) (n := 8) hA (by decide) (by decide))
    (by rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide)))
    (by rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide)))
    (by rw [wr₂, hS0]; exact in_off hw (by omega) (by decide))
    (by rw [wr₂, Offset.add_add]; exact in_off hw (by omega) (by decide))
    (by rw [hS0]; exact dS.symm.sep (Offset.contains_base _ (by decide) (by decide)) (contains_pre _ (by decide)))
    (by rw [hS0]; exact (L.w_w (a := ohO + 8) (n := 8) (d := 384 + 16 * i) (k := 8) (.inl (by simp only [ohO]; omega))
      (by decide) (by omega)).sep (Region.contains_self _ _) (contains_pre _ (by decide)))) fun t₃ B₃ => ?_)
  have v₃ := B₃.val
  rw [hS0] at v₃
  refine wp_addi (by decide) (by decide) fun t₄ u₄ => wp_addi (by decide) (by decide) fun t₅ u₅ =>
    wp_addi (by decide) (by decide) fun t₆ u₆ => wp_subi (by decide) (by decide) fun t₇ u₇ => WP.block_nil ?_
  have g₃ : ∀ r, r ∉ ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    rw [B₃.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])), g₂ r hr]
  have fs : Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t₂.mem t₃.mem := by
    have := B₃.frame; rwa [hS0] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
    exact (fr₂.mono (by simp)).trans (fs.mono (by simp))
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, blockAtMem_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := ohO) (n := 16) (d := 384 + 16 * i) (k := 16) (.inl (by simp only [ohO]; omega)) (by decide)
        (by omega)), oh₂]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, v₃, BitVec.add_zero, eA, oh₂]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), B₃.gpr _ (by decide), h24₂,
      Offset.add_add, show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), B₃.gpr _ (by decide), h26₂,
      ← BitVec.ofNat_add]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, B₃.gpr _ (by decide), h11₂,
      Offset.add_add, show 384 + 16 * i + 16 = 384 + 16 * (i + 1) by omega]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), B₃.gpr _ (by decide), h25₂,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.2.2.2.2.2.2.2.2.1, u₆.other _ hr.2.2.2.2.2.2.2.2.2, u₅.other _ hr.2.2.2.2.2.2.2.1,
      u₄.other _ hr.2.2.2.2.2.1, g₃ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.1])]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, B₃.sp, B₂.sp, P₁.sp]
  · rw [u₇.lr, u₆.lr, u₅.lr, u₄.lr, B₃.lr, B₂.lr, P₁.lr]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, B₃.rd, rd₂]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, B₃.wr, wr₂]

end VG.Proof.AesOcb.PPC64LE
