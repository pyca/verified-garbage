import VerifiedGarbage.Proof.AesOcb.AArch64.Nonce

/-!
# AES-OCB on AArch64: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xor16_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x23, .x25, .x27]

/-- What one `hashFill` leaves. -/
structure FillPost (W A : Addr) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
    blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  x23 : t'.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i + 1))
  x25 : t'.gpr .x25 = BitVec.ofNat 64 (j + i + 2)
  x27 : t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * (i + 1))
  x15 : t'.gpr .x15 = BitVec.ofNat 64 (c - (i + 1))
  gpr : ∀ r, r ∉ fillRegs → t'.gpr r = t.gpr r
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {K W : Addr} (L : Lay K W) {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {A : Addr} {l : Block} {j i c : Nat} (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 61)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 (j + i + 1)) (h23 : t.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i)))
    (h27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i)) (h15 : t.gpr .x15 = BitVec.ofNat 64 (c - i))
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr))
    (hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa hashFill t (FillPost W A l j i c t) := by
  unfold hashFill
  refine WP.seq (WP.mono (lNtz_ok (i := j + i + 1) h19 hw (by omega) (by omega) h25 hl0) fun t₁ P₁ => ?_)
  have h19₁ : t₁.gpr .x19 = W := by rw [P₁.gpr _ (by decide), h19]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [P₁.wr]; exact in_off hw h (by decide)
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .x19) (a := lO) (d := ohO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (in_left (ww (by decide))) (in_left (ww (by decide)))
    (ww (by decide)) (ww (by decide))
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [B₂.val, P₁.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  have g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      P₁.gpr r hr]
  have h23₂ : t₂.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i)) := by rw [g₂ _ (by decide), h23]
  have h27₂ : t₂.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i) := by rw [g₂ _ (by decide), h27]
  have h19₂ : t₂.gpr .x19 = W := by rw [g₂ _ (by decide), h19]
  have h25₂ : t₂.gpr .x25 = BitVec.ofNat 64 (j + i + 1) := by rw [g₂ _ (by decide), h25]
  have h15₂ : t₂.gpr .x15 = BitVec.ofNat 64 (c - i) := by rw [g₂ _ (by decide), h15]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have eA : blockAtMem t₂.mem (A + BitVec.ofNat 64 (16 * (j + i))) = blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) :=
    blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hAW.sub_right (Lay.wSub (by decide))
  have rA₀ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i))) 8 := by
    rw [rd₂, wr₂]; simpa using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  have rA₈ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i)) + BitVec.ofNat 64 8) 8 := by
    rw [rd₂, wr₂]; exact in_off (d := 8) (n := 8) hA (by decide) (by decide)
  have rO₀ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 144) 8 := by
    rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide))
  have rO₈ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 152) 8 := by
    rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide))
  have wS₀ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i)) 8 := by rw [wr₂]; exact in_off hw (by omega) (by decide)
  have wS₈ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 8) 8 := by
    rw [wr₂, Offset.add_add]; exact in_off hw (by omega) (by decide)
  refine WP.of_runBlock ⟨_, by rw [runBlock_append, run₂, Option.bind_some]; orun [h23₂, h27₂, h19₂, h25₂, h15₂,
    rA₀, rA₈, rO₀, rO₈, wS₀, wS₈], ?_⟩
  have fs : ∀ (M : Mem) (v₀ v₁ : BitVec 64), Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 (384 + 16 * i)) v₀).writeW (W + BitVec.ofNat 64 (384 + 16 * i) + 8#64) v₁) :=
    fun M v₀ v₁ => Proof.Cmac.frame_store2 _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ <;> try dsimp only
  · simp only [mem_write]
    exact (fr₂.mono (by simp)).trans ((fs _ _ _).mono (by simp))
  · simp only [mem_write]
    rw [blockAtMem_frame (fs _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 144) (n := 16) (d := 384 + 16 * i) (k := 16) (.inl (by omega)) (by decide) (by omega)), oh₂]
  · simp only [mem_write]
    rw [blockAtMem_store2, show W + 152#64 = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 from (addr8 W 144).symm,
      blockAtMem_xor_words, eA, show W + BitVec.ofNat 64 144 = W + BitVec.ofNat 64 ohO from rfl, oh₂]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h23₂, Offset.add_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h25₂, ← BitVec.ofNat_add]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, Offset.add_add]
    rw [show 384 + 16 * i + 16 = 384 + 16 * (i + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15₂]
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2, ite_false]
    exact g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1])
  · simp only [sp_write]; rw [B₂.sp, P₁.sp]
  · simp only [rd_write]; exact rd₂
  · simp only [wr_write]; exact wr₂

end VG.Proof.AesOcb.AArch64
