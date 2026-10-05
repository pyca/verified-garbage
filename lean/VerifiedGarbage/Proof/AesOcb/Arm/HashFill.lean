import VerifiedGarbage.Proof.AesOcb.Arm.Nonce

/-!
# AES-OCB on ARMv7: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xorB_wp`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`), as on AArch64
(`Proof.AesOcb.AArch64.hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (z_subFlags dec32 z_dec)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r8, .r12, .lr]

theorem w_A {p : Prm} (L : Lay p) {k : Nat} (h : 16 + k ≤ p.al) :
    State.addr (p.A + BitVec.ofNat 32 k) = State.addr p.A + BitVec.ofNat 64 k :=
  addr_add (by have := L.aw; omega)

/-- What one `hashFill` leaves. -/
structure FillPost (p : Prm) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i)) =
    blockAtMem t.mem (State.addr p.A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  r4 : t'.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i + 1))
  r6 : t'.gpr .r6 = BitVec.ofNat 32 (j + i + 2)
  r8 : t'.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1))
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (c - (i + 1))
  z : t'.z = decide (i + 1 = c)
  gpr : Others fillRegs t t'
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {l : Block} {j i c : Nat} (hi : i < c)
    (hc : c ≤ 16) (hj : 16 * (j + i + 1) ≤ p.al)
    (h6 : t.gpr .r6 = BitVec.ofNat 32 (j + i + 1)) (h4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)))
    (h8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i)) (h5 : t.gpr .r5 = BitVec.ofNat 32 (c - i))
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)) :
    WP isa hashFill t (FillPost p l j i c t) := by
  have fw := L.ww
  have fa := L.aw
  have al32 := L.al_lt
  have hb : bufO + 16 * i + 16 ≤ 512 := by simp only [bufO]; omega
  unfold hashFill
  refine WP.seq (WP.mono (lNtz_ok (i := j + i + 1) L E (by omega) (by omega) h6 hl0) fun t₁ P₁ => ?_)
  have E₁ : Env p t₁ := E.of_others P₁.gpr P₁.sp P₁.rd P₁.wr
  have g₁ : Others ntzRegs t t₁ := P₁.gpr
  -- the offset
  refine WP.block_append (WP.block_append (WP.mono (xorB_wp (s := t₁) (pb := .r11) (qb := .r11) (cb := .r11)
    (pd := ohO) (qd := lO) (cd := ohO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [E₁.r11]; simp only [ohO]; omega)
    (by rw [E₁.r11]; simp only [lO]; omega) (by rw [E₁.r11]; simp only [ohO]; omega)
    (by rw [E₁.r11]; exact E₁.perm.wCR (by decide)) (by rw [E₁.r11]; exact E₁.perm.wCR (by decide))
    (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_))
  rw [E₁.r11] at R₂
  have E₂ : Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have oh₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by decide)) (by decide) (by decide))), P₁.val,
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  have g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    have h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [R₂.gpr r h', g₁ r hr]
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]; exact (P₁.frame.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  -- the block of the associated data
  have eA : State.addr (p.A + BitVec.ofNat 32 (16 * (j + i))) = State.addr p.A + BitVec.ofNat 64 (16 * (j + i)) :=
    w_A L (by omega)
  have eB : State.addr (p.W + BitVec.ofNat 32 (bufO + 16 * i)) = State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i) :=
    L.wA (by omega)
  have r4₂ : t₂.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [g₂ _ (by decide), h4]
  have r8₂ : t₂.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [g₂ _ (by decide), h8]
  have hj' : 16 * (j + i) + 16 ≤ p.al := by omega
  have dA : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Sub ⟨State.addr p.A, p.al⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.mono (xorB_wp (s := t₂) (pb := .r4) (qb := .r11) (cb := .r8) (pd := 0) (qd := ohO) (cd := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [r4₂, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (j + i)) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (by rw [E₂.r11]; simp only [ohO]; omega) (by rw [r8₂, L.wN (by omega)]; omega)
    (by rw [r4₂, eA, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_off E₂.perm.aad hj' (by omega))
    (by rw [E₂.r11]; exact E₂.perm.wCR (by decide))
    (by rw [r8₂, eB, BitVec.add_zero]; exact E₂.perm.wC (by omega))) fun t₃ R₃ => ?_
  rw [r4₂, r8₂, E₂.r11, eA, eB, BitVec.add_zero, BitVec.add_zero] at R₃
  have fB : Frame [⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t₂.mem t₃.mem := by
    rw [R₃.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have dAW : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩ := (L.a_w' (by omega)).sub_left dA
  have g₃ : ∀ r, r ∉ fillRegs → t₃.gpr r = t.gpr r := fun r hr => by
    simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.1, hr.2.1]), g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2])]
  have r4₃ : t₃.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [R₃.gpr _ (by decide), r4₂]
  have r8₃ : t₃.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [R₃.gpr _ (by decide), r8₂]
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (j + i + 1) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h6]
  have r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 (c - i) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h5]
  refine WP.of_runBlock ⟨_, by orun [r4₃, r8₃, r6₃, r5₃], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact (fr₂.mono (by simp)).trans (fB.mono (by simp))
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [blockAtMem_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by simp only [ohO, bufO]; omega)) (by decide) (by omega)), oh₂]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [R₃.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.of_disjoint dAW.symm)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by simp only [ohO, bufO]; omega)) (by omega) (by decide))),
      blockAtMem_frame fr₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (L.a_w' (by decide)).sub_left dA), oh₂]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ← BitVec.ofNat_add]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 256 + 16 * i + 16 = bufO + 16 * (i + 1) by simp only [bufO]; omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hi (by omega)]
  · simp only [z_setReg, z_subFlags, dec32 hi (by omega), z_dec hi (by omega)]
  · simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, ite_false,
      Proof.AesGcm.Arm.gpr_subFlags]
    exact g₃ r (by simp [fillRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2])
  · simp only [sp_setReg, Proof.AesGcm.Arm.sp_subFlags]; rw [R₃.sp, R₂.sp, P₁.sp]
  · simp only [rd_setReg, Proof.AesGcm.Arm.rd_subFlags]; rw [R₃.rd, R₂.rd, P₁.rd]
  · simp only [wr_setReg, Proof.AesGcm.Arm.wr_subFlags]; rw [R₃.wr, R₂.wr, P₁.wr]

end VG.Proof.AesOcb.Arm
